/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Sint Nicolaas
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Counting tables with a bad query

`prEvent_tableQueryLog_bad_le` bounds the probability that an adaptive computation meets a bad
queried cell of a uniform answer table. On a finite key domain with one finite answer type, a
uniform table is a uniform function, so the bound is a count of functions: if resampling any
one cell, with the rest of the table fixed, makes it bad for at most `b` answers, then at most
`n * b * |R| ^ (|D| - 1)` of the `|R| ^ |D|` tables let an `n`-query computation meet a bad
queried cell. Counting statements of this shape appear in Fiat–Shamir soundness proofs that
charge each oracle query of an algebraic prover separately.

## Main results

* `card_tableQueryLog_bad_mul_le`: the count, multiplied out by `|R|` so that it also covers an
  empty key domain.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleComp

variable {D R α : Type} [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]

/-- An `n`-query computation against a table of `R` answers on the finite domain `D` meets a
bad queried cell on at most `n * b` of every `|R|` tables, counted as
`card * |R| ≤ n * b * |R| ^ |D|`, when resampling any one cell with the rest of the table fixed
makes it bad for at most `b` answers. The bad predicate may read every cell. -/
theorem card_tableQueryLog_bad_mul_le (oa : OracleComp (ofFn fun _ : D => R) α) (n : ℕ)
    (hbound : IsTotalQueryBound oa n) (bad : D → (D → R) → Prop) (b : ℕ)
    [∀ t g, DecidablePred fun u : R => bad t (Function.update g t u)]
    [DecidablePred fun g : D → R => ∃ q ∈ tableQueryLog oa g, bad q.1 g]
    (hbad : ∀ t g, (Finset.univ.filter fun u : R => bad t (Function.update g t u)).card ≤ b) :
    (Finset.univ.filter fun g : D → R => ∃ q ∈ tableQueryLog oa g, bad q.1 g).card *
        Fintype.card R ≤ n * b * Fintype.card R ^ Fintype.card D := by
  let : SampleableType R := SampleableType.ofFintype R
  let : SampleableType (D → R) := SampleableType.ofFintype (D → R)
  have hpr := prEvent_tableQueryLog_bad_le oa n hbound bad
    ((b : ℝ≥0∞) / (Fintype.card R : ℝ≥0∞))
    (fun t g => (SampleableType.prEvent_uniformSample_le_div_iff _).2 (hbad t g))
  rw [SampleableType.prEvent_uniformSample, Fintype.card_fun] at hpr
  have hR : (Fintype.card R : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hRt : (Fintype.card R : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpow : (Fintype.card R : ℝ≥0∞) ^ Fintype.card D ≠ 0 := pow_ne_zero _ hR
  rw [Nat.cast_pow, ENNReal.div_le_iff hpow (ENNReal.pow_ne_top hRt)] at hpr
  have h := mul_le_mul_left hpr (Fintype.card R : ℝ≥0∞)
  rw [mul_comm, mul_assoc, mul_comm _ (Fintype.card R : ℝ≥0∞), ← mul_assoc,
    mul_assoc (n : ℝ≥0∞), ENNReal.div_mul_cancel hR hRt] at h
  rw [mul_comm]
  exact_mod_cast h

end OracleComp
