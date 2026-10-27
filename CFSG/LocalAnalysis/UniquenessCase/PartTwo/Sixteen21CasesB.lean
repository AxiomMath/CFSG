module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Nat
public import CFSG.LocalAnalysis.GLTheoremB.I2810.AltDegree
public import CFSG.HardMathSupport.Foote.E27.Q2OrthMinus
public import CFSG.Quasithin.H13.U3S1347Y
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.HardMathSupport.Foote.E27.Q2OrthModel
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.HardMathSupport.Foote.E27

variable {G : Type} [Group G] [Finite G]

namespace Sixteen21

theorem card_lBar_of_case1 {D : Data G} {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Case167_1 D V₀ V hV L) : Nat.card (lBar V₀ V hV L) = 25920 := by
  have hdiv : (6 : ℕ) / 2 = 3 := by norm_num
  simp only [Case167_1, IsOmegaMinus, hdiv] at hc
  obtain ⟨-, K, hKfield, hKfinite, b, c, hKcard, hirr, ⟨e⟩⟩ := hc.1
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hF : Nat.card K = 2 := by rw [hKcard, pow_one]
  let eJ := e.trans (Q2.statedProjOmegaEquiv (StatedQuadMinus 3 K b c) hF
    (StatedQuadMinus 3 (ZMod 2) 1 1) (fun v σ => Q2.quadMinus_comp 3 σ hirr v))
  rw [Nat.card_congr eJ.toEquiv]
  exact (CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.AltDegree.card_omegaMinusSix).2

theorem card_vTil_of_case1 {D : Data G} {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Case167_1 D V₀ V hV L) : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
  have hdiv : (6 : ℕ) / 2 = 3 := by norm_num
  simp only [Case167_1, NatOmegaMinus, hdiv] at hc
  obtain ⟨-, K, hKfield, hKfinite, b, c, hKcard, hirr, hR⟩ := hc.2.1
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  rw [card_eq_of_realizes_nat hR, hKcard]
  simp only [Fintype.card_fin, Fintype.card_sum]
  norm_num

theorem one_le_pRank_of_case1 {D : Data G} {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h16 : Hyp16 D V₀ V) (h151 : Hyp151 D V₀ V L) (hc : Case167_1 D V₀ V hV L) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
  unfold Case167_1 at hc
  have h81 : 3 ^ 4 ∣ Nat.card (lBar V₀ V hV L) := by
    rw [card_lBar_of_case1 hV hc]
    norm_num
  have h64 : Nat.card (Vtil V₀ V hV) ≤ 3 ^ 4 := by
    rw [card_vTil_of_case1 hV hc]
    norm_num
  refine one_le_pRank_of_forall_fix_vTil (X := L) hV h16 h151.le Nat.prime_three (by norm_num)
    ?_ ?_
  · rw [hc.2.2.2]
    norm_num
  · intro w hw
    exact exists_orderOf_fix_of_card_le (X := lBar V₀ V hV L) Nat.prime_three h81 h64 hw

theorem card_vTil_of_case5 {D : Data G} {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Case167_5 D V₀ V hV L) : Nat.card (Vtil V₀ V hV) = 2 ^ 8 := by
  have hdiv : (4 : ℕ) / 2 = 2 := by norm_num
  simp only [Case167_5, NatOmegaPlus, hdiv] at hc
  obtain ⟨-, K, hKfield, hKfinite, hKcard, hR⟩ := hc.2.1
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  rw [card_eq_of_realizes_nat hR, hKcard]
  simp only [Fintype.card_fin, Fintype.card_sum]
  norm_num

theorem not_five_pow_three_dvd_card_mulAut {W : Type*} [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 2 ^ 8) : ¬ 5 ^ 3 ∣ Nat.card (MulAut W) := by
  let _ : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      show Additive.ofMul ((Additive.toMul x) ^ 2) = 0
      rw [hW2]; rfl
  rw [CFSG.Quasithin.H13.U3.card_mulAut_eq_card_GL hW2]
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  set n := Module.finrank (ZMod 2) (Additive W) with hn
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive W) hn.symm
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv, Matrix.card_GL_field,
    ZMod.card]
  have hcard : Nat.card (Additive W) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hW' : Nat.card (Additive W) = 2 ^ 8 := by
    rw [← Nat.card_congr (Additive.ofMul (α := W))]
    exact hW
  have h8 : n = 8 := by
    have hpow : 2 ^ n = 2 ^ 8 := by
      rw [← hcard]
      exact hW'
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  rw [h8]
  decide

theorem one_le_pRank_of_case5 {D : Data G} (hSg : UC6S846.SigmaStd D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h16 : Hyp16 D V₀ V) (hc : Case167_5 D V₀ V hV L) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer ({v} : Set G)) := by
  unfold Case167_5 at hc
  have h5 : 5 ∈ D.sig := by rw [hc.2.2]; simp
  have hcard : ¬ 5 ^ 3 ∣ Nat.card (Mbar D.M V₀ V hV) := by
    intro hd
    exact not_five_pow_three_dvd_card_mulAut (W := Vtil V₀ V hV)
      (s15_Infra_vtil_sq_eq_one V₀ V hV) (card_vTil_of_case5 hV hc)
      (hd.trans (Subgroup.card_subgroup_dvd_card (Mbar D.M V₀ V hV)))
  exact one_le_pRank_of_not_dvd_mbar hV h16 (p := 5) (k := 3) Nat.prime_five (by norm_num)
    (D.sig_rank 5 h5) (hSg.three_le 5 h5) hcard

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
