module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslCover
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslLabelExt
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslLEnd
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslNatural
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOrthSix
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslRangeL42
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslL42Irred
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslL42None
import CFSG.LieType.SpecialLinear.ExteriorModel.WeightDim

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open Matrix

theorem chev2SmallModules_psl_l42
    {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hQ : IsQuasisimple ↥L)
    (hirr : IsIrrOn L ⊤ ⊥) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 4 2 1) {k d : ℕ}
    (hk : Nat.card (LEnd L) = 2 ^ k) (hrk : rk W = k * d)
    (hrange : (k = 1 ∧ d ≤ 3 * gs03Bound .PSL 4 1) ∨
      ((k = 2 ∨ k = 3) ∧ d ≤ gs03Bound .PSL 4 1)) :
    Chev2Natural W L ∨ Chev2Item3 W L ∨ Chev2RowIdx .PSL 4 1 (k * d) := by
  classical
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  obtain ⟨_, K, _, _, _, hKcard, φ, hφs, hker, -⟩ := w135c2_psl_cover hW hQ hirr hlie
  have hK : Fintype.card K = 2 := by simpa using hKcard
  have hirrρ := w135c2_psl_rep_irreducible hirr φ hφs
  have hne := w135c2_psl_rep_ne_one hQ φ hφs
  have hEnd := w135c2_psl_lend_card φ hφs
  have hcard2 : Nat.card W = 2 ^ (k * d) := by rw [w135_card_eq_two_pow_rk hW, hrk]
  have hcardA : Nat.card W = Nat.card (Additive W) := (Nat.card_congr Additive.toMul).symm
  obtain ⟨s, ε, hs1, hEs, h0, hact, hper, -, ⟨k', _, _, hcardW⟩, hdesc, hrot, hmin⟩ :=
    w135c2_psl_label_ext (m := 3) (f := 1) (by omega) hKcard (pslRep φ) hirrρ hne
  have hsk : s = k := by
    have h : 2 ^ k = 2 ^ s := by rw [← hk, hEnd, hEs]
    exact (Nat.pow_right_injective le_rfl h).symm
  subst hsk
  have hD : d = Module.finrank k' (BModel k' ε) := by
    have h : 2 ^ (s * d) = 2 ^ (s * Module.finrank k' (BModel k' ε)) := by
      rw [← hcard2, hcardA, hcardW]
    exact Nat.eq_of_mul_eq_mul_left hs1 (Nat.pow_right_injective le_rfl h)
  have hlow : ∏ r ∈ univ.filter (fun r => ε r ≠ ∅), orbitSize (ε r) ≤ d := by
    rw [hD]
    exact prod_orbitSize_le_finrank (k := k') ε
  have hrange7 : (s = 1 ∧ d ≤ 3 * 7) ∨ ((s = 2 ∨ s = 3) ∧ d ≤ 7) := by
    simpa [gs03Bound] using hrange
  rcases w135c2_psl_range_l42 (f := 1) rfl hs1 ε h0 hact hmin hlow hrange7 with
    ⟨hs, ⟨r₀, j, hone, hεj, hj0⟩ | ⟨h12, h21⟩⟩
  · obtain ⟨β, hβ⟩ := hdesc r₀ j hone hεj
    have hjcases : (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ (j : ℕ) = 3 := by
      have := j.isLt
      omega
    rcases hjcases with hj1 | hj2 | hj3
    · exact Or.inl (w135c2_psl_natural (by omega) hKcard φ hφs hker (Or.inl hj1) β hβ)
    · exact Or.inl (w135c2_psl_orth_six hKcard φ hφs hker hj2 β hβ)
    · exact Or.inl (w135c2_psl_natural (by omega) hKcard φ hφs hker (Or.inr (by omega)) β hβ)
  · right
    right
    have hd : d = 14 ∨ d = 20 := by
      by_contra h
      have hne14 : d ≠ 14 := fun h14 => h (Or.inl h14)
      have hne20 : d ≠ 20 := fun h20 => h (Or.inr h20)
      have hmem : d ∈ CFSG.LargeExtraspecial.SL4Mod.Native.noneDims := by
        simp only [CFSG.LargeExtraspecial.SL4Mod.Native.noneDims, List.mem_cons,
          List.not_mem_nil, or_false]
        omega
      haveI : Finite (Additive W) := ‹Finite W›
      haveI : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
      have hV : Module.finrank (ZMod 2) (Additive W) = d := by
        haveI : Fintype (Additive W) := Fintype.ofFinite _
        have h1 : Fintype.card (Additive W) = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
          rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
        have hcardAd : Nat.card (Additive W) = 2 ^ d := by
          rw [← hcardA, hcard2, hs]
          simp
        rw [Nat.card_eq_fintype_card, h1] at hcardAd
        exact Nat.pow_right_injective le_rfl hcardAd
      obtain ⟨ρ, hρ⟩ := w135c2_psl_l42_isIrredGen hK φ hirrρ
      exact w135c2_psl_l42_no_irred hmem hV hρ
    have hkd : s * d = 14 ∨ s * d = 20 := by
      rcases hd with h | h
      · exact Or.inl (by rw [hs, one_mul]; exact h)
      · exact Or.inr (by rw [hs, one_mul]; exact h)
    rcases hkd with h | h
    · rw [h]
      exact (trivial : Chev2RowIdx .PSL 4 1 14)
    · rw [h]
      exact (trivial : Chev2RowIdx .PSL 4 1 20)

end CFSG.LocalAnalysis.WeakClosure81
