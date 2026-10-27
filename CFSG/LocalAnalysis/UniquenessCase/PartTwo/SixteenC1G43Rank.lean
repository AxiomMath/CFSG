module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1G43_card_barSub_le {D : Data G} (hkitB : OmegaKitB) (hkitC : OmegaKitC)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) {A : Subgroup G} {g : G} (hAM : A ≤ D.M)
    (hAg : A ≤ conjSubgroup V g) : Nat.card (barSub V₀ V hV A) ≤ 16 := by
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hA_stab : A ≤ stabTil V₀ V := hAM.trans hMstab
  have hAel2 : IsElemAbelian2 (barSub V₀ V hV A) :=
    s16c1G44_isElemAbelian2_barSub hAg hA_stab
  have hbarNorm : barSub V₀ V hV A ≤
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hAM).trans (s16c1_Mbar_le_normalizer hkitB hS hc)
  exact (hkitC (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.2.2.1
    (barSub V₀ V hV A) hbarNorm hAel2

theorem s16c1G43_rank {D : Data G} (h42 : R16_42 D) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L) {i : ℕ} {A : Subgroup G} {g : G}
    (hy : Hyp1643 D ⊥ V i A g) (hnot : ¬ V ≤ conjSubgroup D.M g) :
    32 ≤ 2 ^ i * Nat.card (barSub ⊥ V hV A) := by
  by_contra h32
  have hlt : 2 ^ i * Nat.card (barSub ⊥ V hV A) < 32 := not_le.1 h32
  have hAM : A ≤ D.M := hy.2.1.1
  have hAg : A ≤ conjSubgroup V g := hy.2.2
  have hMstab : D.M ≤ stabTil ⊥ V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hA_stab : A ≤ stabTil ⊥ V := hAM.trans hMstab
  have hA2 : IsPGroup 2 A := ((E3.isElemAbelian_conjSubgroup hV g).mono hAg).isPGroup
  let X₀ : Subgroup G := A ⊓ preBarSub D.M ⊥ V hV ⊥
  have hX₀A : X₀ ≤ A := inf_le_left
  have hX₀M : X₀ ≤ D.M := hX₀A.trans hAM
  have hX₀g : X₀ ≤ conjSubgroup V g := hX₀A.trans hAg
  have hmQA : E3.mQuot (conjSubgroup V g) A = i :=
    mQuot_eq_of_mem_gammaSet hy.2.1 hy.2.2
  have hX₀gam : X₀ ∈ E3.gammaSet V (i + E3.mQuot A X₀) D.M := by
    refine ⟨hX₀M, g, hX₀g, ?_⟩
    rw [E3.mQuot_add hX₀A hAg, hmQA]
    exact Nat.add_comm _ _
  have hrel : X₀.relIndex A = Nat.card (barSub ⊥ V hV A) :=
    s16c1G44_relIndex_inf_preBarSub_eq_card_barSub (V₀ := ⊥) (V := V) (hV := hV) hAM hA_stab
  have hcard : Nat.card (barSub ⊥ V hV A) = 2 ^ E3.mQuot A X₀ := by
    rw [← hrel, E3.relIndex_eq_two_pow hA2 X₀]
  have hik : i + E3.mQuot A X₀ ≤ 4 := by
    have hpow : 2 ^ (i + E3.mQuot A X₀) < 2 ^ 5 := by
      rw [pow_add]
      rw [hcard, show (32 : ℕ) = 2 ^ 5 by norm_num] at hlt
      exact hlt
    have hlt5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hpow
    omega
  have hr : ((i + E3.mQuot A X₀ + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
    have h42' := h42 ⊥ V L hV hS hc
    have hle : i + E3.mQuot A X₀ + mSub (⊥ : Subgroup G) ≤ 4 := by
      simp only [mSub, rk_bot]
      omega
    exact lt_of_le_of_lt (WithTop.coe_le_coe.mpr hle) (h42'.2.2 rfl)
  have h23 := sixteen_twentyThree_one_bot D hS.setting.hyp16 hX₀gam hX₀g hr
  apply hnot
  refine le_trans ?_ h23.2.2
  intro v hv
  refine Subgroup.mem_inf.2 ⟨hv, h23.2.1 v hv ?_⟩
  intro a ha
  obtain ⟨-, hpre⟩ := Subgroup.mem_inf.1 ha
  obtain ⟨-, hstab, hact⟩ := (mem_preBarSub D.M ⊥ V hV ⊥).1 hpre
  have hact1 : actTil ⊥ V hV (⟨a, hstab⟩ : ↥(stabTil ⊥ V)) = 1 := Subgroup.mem_bot.1 hact
  have hcomm : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) :=
    (actTil_eq_one_iff ⊥ V hV ⟨a, hstab⟩).1 hact1 v hv
  rw [commutatorElement_def]
  have heq : v * a * v⁻¹ * a⁻¹ = ((a : G) * v * (a : G)⁻¹ * v⁻¹)⁻¹ := by group
  rw [heq]
  exact (⊥ : Subgroup G).inv_mem hcomm

theorem s16c1G43_prim {D : Data G} (h42 : R16_42 D) (hkitB : OmegaKitB) (hkitC : OmegaKitC)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) {i : ℕ} {A : Subgroup G} {g : G} (hy : Hyp1643 D ⊥ V i A g)
    (hnot : ¬ V ≤ conjSubgroup D.M g) :
    ¬ conjSubgroup V g ≤ D.M ∧
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) = 1 ∧
        Nat.card (barSub ⊥ V hV (conjSubgroup V g ⊓ D.M)) = 16 := by
  let B : Subgroup G := conjSubgroup V g ⊓ D.M
  let i' : ℕ := E3.mQuot (conjSubgroup V g) B
  have hAB : A ≤ B := le_inf hy.2.2 hy.2.1.1
  have hBg : B ≤ conjSubgroup V g := inf_le_left
  have hBM : B ≤ D.M := inf_le_right
  have hmQA : E3.mQuot (conjSubgroup V g) A = i :=
    mQuot_eq_of_mem_gammaSet hy.2.1 hy.2.2
  have hi'le : i' ≤ i := by
    show E3.mQuot (conjSubgroup V g) B ≤ i
    rw [← hmQA]
    exact E3.mQuot_mono hAB
  have hi'le1 : i' ≤ 1 := by
    rcases hy.1 with h0 | ⟨-, h1⟩
    · omega
    · omega
  have hyB : Hyp1643 D ⊥ V i' B g := by
    have hi01 : i' = 0 ∨ i' = 1 := by omega
    refine ⟨?_, ⟨hBM, g, hBg, rfl⟩, hBg⟩
    rcases hi01 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  have hrank := s16c1G43_rank h42 hS hc hyB hnot
  have hcard := s16c1G43_card_barSub_le hkitB hkitC hS hc hBM hBg
  have hi'1 : i' = 1 := by
    by_contra hne
    have h0 : i' = 0 := by omega
    rw [h0] at hrank
    simp only [pow_zero, one_mul] at hrank
    omega
  have hBcard : Nat.card (barSub ⊥ V hV B) = 16 := by
    have h32 : 32 ≤ 2 * Nat.card (barSub ⊥ V hV B) := by simpa [hi'1] using hrank
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro hVle
    have hB_eq : B = conjSubgroup V g := inf_eq_left.2 hVle
    have h0 : i' = 0 := by
      rw [show i' = E3.mQuot (conjSubgroup V g) B from rfl, hB_eq, E3.mQuot_self]
    omega
  · exact hi'1
  · exact hBcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
