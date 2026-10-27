module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace NoOffRest

open TableBExc.E6Three TableBExc.Three

local instance noOffRestNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

local instance noOffRestFactThreeM : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

section HypMinor

theorem add_smul_single_eq_self_iff {p : ℕ} [Fact (1 < p)] {r : ℕ} [NeZero r]
    (x : Fin r → ZMod p) (c : ZMod p) : x + c • Pi.single 0 1 = x ↔ c = 0 := by
  constructor
  · intro h
    simpa using congrFun h 0
  · rintro rfl
    simp

@[expose] noncomputable def kLin : (Fin Tag.E6.rank → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun := kDotP 3
  map_add' := kDotP_add
  map_smul' c x := kDotP_smul c x

@[expose] def hypShift (x : Fin Tag.E6.rank → ZMod 3) : Fin Tag.E6.rank → ZMod 3 :=
  x + kDotP 3 x • Pi.single 0 1

@[expose] noncomputable def hypShiftLin :
    (Fin Tag.E6.rank → ZMod 3) →ₗ[ZMod 3] (Fin Tag.E6.rank → ZMod 3) :=
  LinearMap.id + kLin.smulRight (Pi.single 0 1)

theorem hypShift_eq_self_iff (x : Fin Tag.E6.rank → ZMod 3) : hypShift x = x ↔ kDotP 3 x = 0 :=
  have : Fact (1 < 3) := ⟨by norm_num⟩
  add_smul_single_eq_self_iff x (kDotP 3 x)

@[expose] def hypFam (ω : List (Fin Tag.E6.rank)) :
    Fin 2 → (Fin Tag.E6.rank → ZMod 3) → Fin Tag.E6.rank → ZMod 3 :=
  ![adWord .E6 3 ω, hypShift]

@[expose] noncomputable def hypFamLin (ω : List (Fin Tag.E6.rank)) :
    Fin 2 → (Fin Tag.E6.rank → ZMod 3) →ₗ[ZMod 3] (Fin Tag.E6.rank → ZMod 3) :=
  ![adWordLin .E6 3 ω, hypShiftLin]

theorem hypFamLin_apply (ω : List (Fin Tag.E6.rank)) (t : Fin 2) (x : Fin Tag.E6.rank → ZMod 3) :
    hypFamLin ω t x = hypFam ω t x := by
  fin_cases t
  · exact adWordLin_apply ω x
  · rfl

theorem card_fix_adWord_hyp_le (ω : List (Fin Tag.E6.rank)) {k : ℕ}
    (R : Fin k → Fin 2 × Fin Tag.E6.rank) (C : Fin k → Fin Tag.E6.rank)
    (hC : Function.Injective C) (N : Fin k → Fin k → ZMod 3)
    (hN : ∀ a b : Fin k, ∑ c, N a c * (hypFam ω (R c).1 (Pi.single (C b) 1) (R c).2 -
      if (R c).2 = C b then 1 else 0) = if a = b then 1 else 0) :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 ω x = x ∧ kDotP 3 x = 0} ≤
      3 ^ (Tag.E6.rank - k) := by
  have h := card_fixAll_le_of_leftInverse (hypFamLin ω) R C hC N
    (by simpa only [hypFamLin_apply] using hN)
  rw [ZMod.card] at h
  refine le_of_eq_of_le (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)) h
  rw [Fin.forall_fin_two, hypFamLin_apply, hypFamLin_apply]
  exact and_congr Iff.rfl (hypShift_eq_self_iff x).symm

end HypMinor

section Bounds

theorem card_fix_hyp_wordE6G : ∀ i : Fin 3,
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // adWord .E6 3 (wordE6G i) x = x ∧ kDotP 3 x = 0} ≤
      3 ^ (6 - 3) := by
  intro i
  fin_cases i
  · exact card_fix_adWord_hyp_le _ ![(0, 0), (0, 3), (1, 0)] ![0, 2, 4] (by decide)
      ![![1, 1, 0], ![0, 1, 0], ![2, 0, 1]] (by decide +kernel)
  · exact card_fix_adWord_hyp_le _ ![(0, 3), (0, 4), (1, 0)] ![0, 4, 5] (by decide)
      ![![0, 1, 1], ![1, 0, 0], ![1, 1, 0]] (by decide +kernel)
  · exact card_fix_adWord_hyp_le _ ![(0, 1), (0, 3), (1, 0)] ![0, 1, 4] (by decide)
      ![![1, 0, 2], ![0, 1, 0], ![2, 0, 2]] (by decide +kernel)

theorem card_fixAll_adWordE6N :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ t, adWord .E6 3 (![wordE6G0, wordE6G1, wordE6G2] t) x = x} ≤ 3 ^ (6 - 5) :=
  card_fixAll_adWord_le (τ := .E6) ![wordE6G0, wordE6G1, wordE6G2]
    ![(0, 0), (0, 3), (1, 3), (1, 4), (2, 3)] ![0, 1, 2, 4, 5] (by decide)
    ![![1, 1, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 1, 0]]
    (by decide +kernel)

theorem card_fixAll_adWordE6CZ1 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ t, adWord .E6 3 (![wordE6C, nfWordE6 1 1 1] t) x = x} ≤ 3 ^ (6 - 4) :=
  card_fixAll_adWord_le (τ := .E6) ![wordE6C, nfWordE6 1 1 1]
    ![(0, 0), (0, 1), (0, 2), (1, 0)] ![0, 1, 2, 4] (by decide)
    ![![1, 2, 1, 0], ![1, 2, 2, 2], ![1, 2, 1, 2], ![1, 0, 2, 2]] (by decide +kernel)

theorem card_fixAll_adWordE6CZ2 :
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 //
      ∀ t, adWord .E6 3 (![wordE6C, nfWordE6 2 2 2] t) x = x} ≤ 3 ^ (6 - 4) :=
  card_fixAll_adWord_le (τ := .E6) ![wordE6C, nfWordE6 2 2 2]
    ![(0, 0), (0, 1), (0, 2), (1, 0)] ![0, 1, 2, 4] (by decide)
    ![![1, 2, 1, 0], ![1, 2, 2, 1], ![1, 2, 1, 1], ![1, 0, 2, 1]] (by decide +kernel)

theorem eq_of_shiftAut_eq : ∀ a b c : ZMod 3,
    shiftAut piE7 (Multiplicative.ofAdd ![a, b, c]) = Multiplicative.ofAdd ![a, b, c] →
    (Multiplicative.ofAdd ![a, b, c] : Multiplicative (Fin 3 → ZMod 3)) ≠ 1 →
    (Multiplicative.ofAdd ![a, b, c] : Multiplicative (Fin 3 → ZMod 3)) = .ofAdd ![1, 1, 1] ∨
      (Multiplicative.ofAdd ![a, b, c] : Multiplicative (Fin 3 → ZMod 3)) = .ofAdd ![2, 2, 2] := by
  decide +kernel

end Bounds

end NoOffRest

end CFSG.StandardType
