module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R56a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4ModelOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R53

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c4_r53_all (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (F : UFrame V₀ V hV L)
    (hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V)
    (h51 : ∀ A ∈ E3.gammaSet V 0 D.M, barSub V₀ V hV A ≠ ⊥ →
      barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV ∧ barSub V₀ V hV A ≤ lBar V₀ V hV L)
    (h52 : ∀ g : G, conjSubgroup V g ≤ D.M → V ≤ conjSubgroup D.M g →
      ⁅V, conjSubgroup V g⁆ = ⊥) :
    ∀ g : G, conjSubgroup V g ≤ D.M → ⁅V, conjSubgroup V g⁆ = ⊥ := by
  intro g hAM
  by_cases hVM : V ≤ conjSubgroup D.M g
  · exact h52 g hAM hVM
  · by_contra hne
    exact s16c4_r53_core D h22 hS F hr h51 hAM hVM hne

theorem s16c4_r56_core (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (F : UFrame V₀ V hV L)
    (hr : ((mSub V₀ + 5 : ℕ) : ℕ∞) ≤ rMV D.M V) {B : Subgroup G}
    (hB : B ∈ E3.gammaSet V 1 D.M) {g : G} (hBg : B ≤ conjSubgroup V g)
    (hVg : ¬ V ≤ conjSubgroup D.M g) : False := by
  have hBel : IsElemAbelian 2 B :=
    B2F.isElemAbelian_mono hBg (E3.isElemAbelian_conjSubgroup hV g)
  have hE2 : IsElemAbelian2 (barSub V₀ V hV B) := isElemAbelian2_barSub hV hBel
  have hE2' : IsPGroup 2 (barSub V₀ V hV B) := E3.isPGroup_of_isElemAbelian2 hE2
  have hEN : barSub V₀ V hV B ≤
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hB.1).trans (F.Mbar_le_normalizer hS)
  have hk4 : 4 ≤ E3.mQuot (barSub V₀ V hV B) ⊥ := by
    refine s16c4_r53a D h22 hS hB hBg ?_ hVg
    have e : 4 + 1 + mSub V₀ = mSub V₀ + 5 := by omega
    rw [e]
    exact hr
  have hcard : Nat.card (barSub V₀ V hV B) = 2 ^ 4 := by
    have hle := F.s16c4_card_le_sixteen hEN hE2
    have hge : 2 ^ 4 ≤ Nat.card (barSub V₀ V hV B) := by
      have h := E3.card_eq_two_pow_mul hE2'
        (bot_le : (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) ≤ barSub V₀ V hV B)
      rw [Subgroup.card_bot, mul_one] at h
      rw [h]
      exact Nat.pow_le_pow_right (by norm_num) hk4
    omega
  by_cases hEL : barSub V₀ V hV B ≤ lBar V₀ V hV L
  · obtain ⟨B₁, B₂, hB₁, hB₂, hB₁c, hB₂c, hcov⟩ := s16c4_two_root_bars F hEL hE2 hcard
    have hm : ∀ Q : Subgroup (MulAut (Vtil V₀ V hV)), Q ≤ barSub V₀ V hV B → Nat.card Q = 2 →
        preTil V₀ V hV (fixV Q) ≤ conjSubgroup D.M g := by
      intro Q hQX hQc
      have h := E3.card_eq_two_pow_mul hE2' hQX
      rw [hcard, hQc] at h
      have hm3 : E3.mQuot (barSub V₀ V hV B) Q = 3 := by
        have h' : 2 ^ 4 = 2 ^ (E3.mQuot (barSub V₀ V hV B) Q + 1) := by
          rw [pow_succ]
          exact h
        have := Nat.pow_right_injective (le_refl 2) h'
        omega
      refine s16c4_preTil_fixV_le D h22 hS hB hBg hQX ?_
      rw [hm3]
      refine lt_of_lt_of_le ?_ hr
      exact_mod_cast (by omega : 1 + 3 + mSub V₀ < mSub V₀ + 5)
    exact hVg (s16c4_le_of_preTil_cover hV hcov (hm B₁ hB₁ hB₁c) (hm B₂ hB₂ hB₂c))
  · exact F.s16c4_modelOut hEN hE2 (le_of_eq hcard.symm) hEL
      (s16c4_r56_hcom D h22 hS hB hBg hcard hr)

theorem r16_56_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hV1 : Case167_4_V1Eq D) :
    R16_56 D := by
  intro V₀ V L hV hS h4 hV0
  obtain ⟨F⟩ := exists_uFrame D h4 (hV1.v1Sub_eq hS h4)
  have h50 := r16_50_holds D h61 hV1 V₀ V L hV hS h4
  have hr4 := h50.1
  have hr5 : ((mSub V₀ + 5 : ℕ) : ℕ∞) ≤ rMV D.M V := by
    have h4' := h50.2.2 hV0
    have e : ((mSub V₀ + 5 : ℕ) : ℕ∞) = 4 + 1 := by
      have : mSub V₀ = 0 := by rw [hV0]; exact rk_bot
      rw [this]
      norm_num
    rw [e]
    exact Order.add_one_le_of_lt h4'
  have h51 := r16_51_holds D hSg h1219 h21 h22 h61 hV1 V₀ V L hV hS h4
  have h52 := r16_52_holds D hSg h1219 h21 h22 h61 hV1 V₀ V L hV hS h4
  have h53 := s16c4_r53_all D h22 hS F hr4 h51 h52
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine E3.wClos_le_of_forall (fun B hB => ?_)
  obtain ⟨hBT, g, hBg, hmg⟩ := hB
  have hBM : B ∈ E3.gammaSet V 1 D.M := ⟨hBT.trans D.sylowM.le, g, hBg, hmg⟩
  by_cases hVg : V ≤ conjSubgroup D.M g
  · have hAM : conjSubgroup V g⁻¹ ≤ D.M := (E3.le_conjSubgroup_iff_inv_le g).1 hVg
    have hcomm := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (h53 g⁻¹ hAM)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hax : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 (hBg ha)
    have hvy : g * v * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
      rw [e]
      exact hv
    have h := Subgroup.mem_centralizer_iff.1 (hcomm hax) _ hvy
    have h' : g * v * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * v * g⁻¹) := h
    have h'' : g * (v * a) * g⁻¹ = g * (a * v) * g⁻¹ := by
      simpa [mul_assoc] using h'
    exact mul_left_cancel (mul_right_cancel h'')
  · exact (s16c4_r56_core D h22 hS F hr5 hBM hBg hVg).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
