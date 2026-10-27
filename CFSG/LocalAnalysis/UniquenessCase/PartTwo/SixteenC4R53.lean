module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R53a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R52e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c4_two_root_bars {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (F : UFrame V₀ V hV L) {X : Subgroup (MulAut (Vtil V₀ V hV))}
    (hXL : X ≤ lBar V₀ V hV L) (hX2 : IsElemAbelian2 X) (hXc : Nat.card X = 2 ^ 4) :
    ∃ B₁ B₂ : Subgroup (MulAut (Vtil V₀ V hV)), B₁ ≤ X ∧ B₂ ≤ X ∧ Nat.card B₁ = 2 ∧
      Nat.card B₂ = 2 ∧
      ∀ w : Vtil V₀ V hV, ∃ w₁ ∈ fixV B₁, ∃ w₂ ∈ fixV B₂, w = w₁ * w₂ := by
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  obtain ⟨hE2, hEc⟩ := F.suSub_sq_comm hXL hX2
  have hcard : Nat.card ↥(F.suSub X) = 2 ^ (4 * 1) := by
    rw [F.card_suSub hXL, hXc]
  obtain ⟨B₁, B₂, hB₁E, hB₂E, hB₁c, hB₂c, -, -, -, -, hsup⟩ :=
    s16_C4ModelTv_two_root_groups F.isUnitary F.two_eq_zero (E := F.suSub X) hE2 hEc
      (n := 1) le_rfl hF hcard
  obtain ⟨C₁, hC₁L, hC₁su⟩ := F.exists_suSub_eq B₁
  obtain ⟨C₂, hC₂L, hC₂su⟩ := F.exists_suSub_eq B₂
  refine ⟨C₁, C₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact F.le_of_suSub_le hC₁L hXL (by rw [hC₁su]; exact hB₁E)
  · exact F.le_of_suSub_le hC₂L hXL (by rw [hC₂su]; exact hB₂E)
  · rw [← F.card_suSub hC₁L, hC₁su, hB₁c]; norm_num
  · rw [← F.card_suSub hC₂L, hC₂su, hB₂c]; norm_num
  · intro w
    have hw : F.vec w ∈ fixSp B₁ ⊔ fixSp B₂ := by rw [hsup]; trivial
    obtain ⟨x₁, hx₁, x₂, hx₂, hsum⟩ := Submodule.mem_sup.1 hw
    refine ⟨F.ofVec x₁, ?_, F.ofVec x₂, ?_, ?_⟩
    · rw [F.mem_fixV_iff_fixSp hC₁L, F.vec_ofVec, hC₁su]; exact hx₁
    · rw [F.mem_fixV_iff_fixSp hC₂L, F.vec_ofVec, hC₂su]; exact hx₂
    · apply F.vec_injective
      rw [F.vec_mul, F.vec_ofVec, F.vec_ofVec, hsum]

theorem s16c4_le_of_preTil_cover {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {S₁ S₂ : Subgroup (Vtil V₀ V hV)} {K : Subgroup G}
    (hcov : ∀ w : Vtil V₀ V hV, ∃ w₁ ∈ S₁, ∃ w₂ ∈ S₂, w = w₁ * w₂)
    (h₁ : preTil V₀ V hV S₁ ≤ K) (h₂ : preTil V₀ V hV S₂ ≤ K) : V ≤ K := by
  intro v hv
  set x : IntMod V hV := IntMod.mk hV ⟨v, hv⟩ with hx
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := hcov (mkTil V₀ V hV x)
  obtain ⟨u₁, rfl⟩ := mkTil_surjective V₀ V hV w₁
  obtain ⟨u₂, rfl⟩ := mkTil_surjective V₀ V hV w₂
  have hu₁ : u₁.val ∈ K := h₁ ((mem_preTil V₀ V hV S₁).2 ⟨u₁, rfl, hw₁⟩)
  have hu₂ : u₂.val ∈ K := h₂ ((mem_preTil V₀ V hV S₂).2 ⟨u₂, rfl, hw₂⟩)
  have hz : mkTil V₀ V hV (x * (u₁ * u₂)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, hw, mul_inv_cancel]
  have hzK : (x * (u₁ * u₂)⁻¹).val ∈ K := by
    refine h₁ ((mem_preTil V₀ V hV S₁).2 ⟨x * (u₁ * u₂)⁻¹, rfl, ?_⟩)
    rw [hz]
    exact S₁.one_mem
  have hvK : v = (x * (u₁ * u₂)⁻¹).val * (u₁.val * u₂.val) := by
    rw [IntMod.val_mul, IntMod.val_inv, IntMod.val_mul, inv_mul_cancel_right]
    rfl
  rw [hvK]
  exact K.mul_mem hzK (K.mul_mem hu₁ hu₂)

theorem s16c4_r53_core (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (F : UFrame V₀ V hV L)
    (hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V)
    (h51 : ∀ A ∈ E3.gammaSet V 0 D.M, barSub V₀ V hV A ≠ ⊥ →
      barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV ∧ barSub V₀ V hV A ≤ lBar V₀ V hV L)
    {g : G} (hAM : conjSubgroup V g ≤ D.M) (hVg : ¬ V ≤ conjSubgroup D.M g)
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) : False := by
  have hA : conjSubgroup V g ∈ E3.gammaSet V 0 D.M := ⟨hAM, g, le_rfl, E3.mQuot_self _⟩
  have hne' := s16c4_r52_barSub_ne_bot D h22 hS hr hAM hne
  obtain ⟨hcal, hAL⟩ := h51 _ hA hne'
  have hX2 : IsElemAbelian2 (barSub V₀ V hV (conjSubgroup V g)) := hcal.2.2.1
  have hk4 : 4 ≤ E3.mQuot (barSub V₀ V hV (conjSubgroup V g)) ⊥ := by
    refine s16c4_r53a D h22 hS hA (g := g) le_rfl ?_ hVg
    have e : 4 + 0 + mSub V₀ = mSub V₀ + 4 := by omega
    rw [e]
    exact hr
  have hA2 : IsPGroup 2 (barSub V₀ V hV (conjSubgroup V g)) :=
    E3.isPGroup_of_isElemAbelian2 hX2
  have hcard : Nat.card (barSub V₀ V hV (conjSubgroup V g)) = 2 ^ 4 := by
    have hle : Nat.card (barSub V₀ V hV (conjSubgroup V g)) ≤ 2 ^ (4 * 1) := by
      obtain ⟨hE2, hEc⟩ := F.suSub_sq_comm hAL hX2
      have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
      rw [← F.card_suSub hAL]
      exact card_le_two_pow_four F.isUnitary hE2 hEc le_rfl hF
    have hge : 2 ^ 4 ≤ Nat.card (barSub V₀ V hV (conjSubgroup V g)) := by
      have h := E3.card_eq_two_pow_mul hA2
        (bot_le : (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) ≤ barSub V₀ V hV (conjSubgroup V g))
      rw [Subgroup.card_bot, mul_one] at h
      rw [h]
      exact Nat.pow_le_pow_right (by norm_num) hk4
    omega
  obtain ⟨B₁, B₂, hB₁, hB₂, hB₁c, hB₂c, hcov⟩ := s16c4_two_root_bars F hAL hX2 hcard
  have hm : ∀ B : Subgroup (MulAut (Vtil V₀ V hV)), B ≤ barSub V₀ V hV (conjSubgroup V g) →
      Nat.card B = 2 → preTil V₀ V hV (fixV B) ≤ conjSubgroup D.M g := by
    intro B hBX hBc
    have h := E3.card_eq_two_pow_mul hA2 hBX
    rw [hcard, hBc] at h
    have hm3 : E3.mQuot (barSub V₀ V hV (conjSubgroup V g)) B = 3 := by
      have h' : 2 ^ 4 = 2 ^ (E3.mQuot (barSub V₀ V hV (conjSubgroup V g)) B + 1) := by
        rw [pow_succ]
        exact h
      have := Nat.pow_right_injective (le_refl 2) h'
      omega
    refine s16c4_preTil_fixV_le D h22 hS hA (g := g) le_rfl hBX ?_
    rw [hm3]
    refine lt_of_lt_of_le ?_ hr
    exact_mod_cast (by omega : 0 + 3 + mSub V₀ < mSub V₀ + 4)
  exact hVg (s16c4_le_of_preTil_cover hV hcov (hm B₁ hB₁ hB₁c) (hm B₂ hB₂ hB₂c))

theorem r16_53_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hV1 : Case167_4_V1Eq D) :
    R16_53 D := by
  intro V₀ V L hV hS h4
  obtain ⟨F⟩ := exists_uFrame D h4 (hV1.v1Sub_eq hS h4)
  have hr := (r16_50_holds D h61 hV1 V₀ V L hV hS h4).1
  have h51 := r16_51_holds D hSg h1219 h21 h22 h61 hV1 V₀ V L hV hS h4
  have h52 := r16_52_holds D hSg h1219 h21 h22 h61 hV1 V₀ V L hV hS h4
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine s15_Glue_wClos_zero_le hV (fun g hgT => ?_)
  have hAM : conjSubgroup V g ≤ D.M := hgT.trans D.sylowM.le
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  by_cases hVM : V ≤ conjSubgroup D.M g
  · exact h52 g hAM hVM
  · by_contra hne
    exact s16c4_r53_core D h22 hS F hr h51 hAM hVM hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
