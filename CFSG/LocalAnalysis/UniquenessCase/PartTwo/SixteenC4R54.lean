module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4LemX
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R50
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24C4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c4_calO2_one_eq_empty_of_mBarGT (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hm : MBarGT D.M ⊥ V 1) : calO2 1 D.M ⊥ V = ∅ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hV2 : IsPGroup 2 V := hV.isPGroup
  refine Set.eq_empty_of_forall_notMem ?_
  rintro X ⟨g, rfl, -, ⟨I, hI, hb⟩, -, -⟩
  obtain ⟨hIX, g', hIg', hmI⟩ := hI
  have hIV : I ≤ V := hIX.trans inf_le_left
  obtain ⟨b, hbmem, hbV⟩ := SetLike.not_le_iff_exists.1 hb
  obtain ⟨⟨hbVg, hbM⟩, hbI⟩ := hbmem
  have hb2 : b * b = 1 := by
    have := (E3.isElemAbelian_conjSubgroup hV g).2 b hbVg
    simpa [pow_two] using this
  have hnc : ¬ CentralizesMod ⊥ V b := by
    intro hc
    apply hbV
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := Subgroup.mem_bot.1 (hc v hv)
    have h2 : b * v * b⁻¹ = v := mul_inv_eq_one.1 h1
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hsq : CentralizesMod ⊥ V (b * b) := by
    intro v hv
    simp [hb2]
  have hle := hm.1 b hbM hnc hsq
  have hsub : (I : Set G) ⊆ centMod ⊥ V b := by
    intro x hx
    refine ⟨hIV hx, ?_⟩
    have hxb : x * b = b * x := Subgroup.mem_centralizer_iff.1 hbI x hx
    rw [Subgroup.mem_bot]
    calc b * x * b⁻¹ * x⁻¹ = x * b * b⁻¹ * x⁻¹ := by rw [← hxb]
      _ = 1 := by simp
  have hcard : Nat.card I ≤ Nat.card (centMod ⊥ V b) := Nat.card_mono (Set.toFinite _) hsub
  have hq : E3.mQuot V I = 1 := by
    rw [E3.mQuot_conj_eq hV hIV hIg', hmI]
  have hVI := E3.card_eq_two_pow_mul hV2 hIV
  rw [hq] at hVI
  have hpos : 0 < Nat.card I := Nat.card_pos
  have h3 : 2 ^ (1 + 1) * Nat.card I ≤ 2 ^ 1 * Nat.card I := by
    calc 2 ^ (1 + 1) * Nat.card I ≤ 2 ^ (1 + 1) * Nat.card (centMod ⊥ V b) :=
          Nat.mul_le_mul_left _ hcard
      _ ≤ Nat.card V := hle
      _ = 2 ^ 1 * Nat.card I := hVI
  have h4 := Nat.le_of_mul_le_mul_right h3 hpos
  omega

section Certified


theorem s16c4_r54_core (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (h4 : Case167_4 D V₀ V hV L) (hV0 : V₀ ≠ ⊥) {g : G}
    (hO : InCalO 1 D.M V₀ V g) : False := by
  have hH : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 (r1114_holds D hx h61) hH hV0
  have hH6 := hW.hyp6H
  obtain ⟨F⟩ := exists_uFrame D h4 (v1Sub_of_ne_bot D.M V₀ V hV L hV0)
  have hr4 := s16c4_r50_one D h61 hS h4 F
  have hr : ((mSub V₀ + 1 : ℕ) : ℕ∞) < rMV D.M V := by
    refine lt_of_lt_of_le ?_ hr4
    exact_mod_cast (by omega : mSub V₀ + 1 < mSub V₀ + 4)
  have hm : 1 < mBar D.M V₀ V hH.isElemAbelian :=
    (hH.mBarGT_iff_lt_mBar 1).1 (Sixteen24.mBarGT_one_of_case4 D h1217 hS h4)
  have hM : D.M ≤ normalizer (V : Set G) := hH6.normalizer_eq.symm.le
  have hM₀ := hH6.le_normalizer₀
  have hO1 : InCalO1 1 D.M V₀ V g := (six_six hH.isElemAbelian hH6.le hM hM₀ hm g).1 hO
  have hOS : InCalOStar 1 D.M V₀ V g := (hH6.hyp65 hV0 hO1).inCalOStar_of_lt_rMV hr
  exact s16c4_lemX D hS F (hH6.hyp64 hOS)

theorem r16_54_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1217 : R1217 D) : R16_54 D := by
  intro V₀ V L hV hS h4
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    exact s16c4_calO2_one_eq_empty_of_mBarGT D hS.setting.hyp16.hyp125
      (Sixteen24.mBarGT_one_of_case4 D h1217 hS h4)
  · refine Set.eq_empty_of_forall_notMem ?_
    rintro X ⟨g, rfl, hO2⟩
    exact s16c4_r54_core D hx h61 h127 h1217 hS h4 hV0 hO2.1

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
