module

public import CFSG.LocalAnalysis.WeakClosure81.EightSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_cClos_eq_bot_of_lt (D : Data G) {W : Subgroup G} (hW : InCalV D.M W)
    (hTI : IsTI W) {i : ℕ} (hi : i < rk ↥W) {X : Subgroup G}
    (hXM : ∀ g : G, g ∉ D.M → W ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥)
    (h1 : ¬ normalizer (E3.wClos W i D.T : Set G) ≤ D.M) :
    X ⊓ centralizer (E3.cClos W i D.T : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer (W : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have hsyl : IsSylowIn 2 D.T (normalizer (W : Set G)) := by
    rw [hN]
    exact TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hWnorm : (W.subgroupOf (normalizer (W : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hWp : IsPGroup 2 W := B2F.isPGroup_of_isElemAbelian hW.2.2.2
  have hWT : W ≤ D.T := hsyl.le_of_normal Subgroup.le_normalizer hWnorm hWp
  have hWW : W ≤ E3.wClos W i D.T := E3.le_wClos_of_mQuot_le_self hW.2.2.2 hWT le_rfl
    (k := i) (by rw [E3.mQuot_self]; exact Nat.zero_le _) hi
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.1 h1
  have hW1g : conjSubgroup (E3.wClos W i D.T) g = E3.wClos W i D.T :=
    conjSubgroup_eq_iff_mem_normalizer.2 hgN
  have hW1T : E3.wClos W i D.T ≤ D.T := E3.wClos_le i D.T
  have hW1two : IsPGroup 2 (E3.wClos W i D.T) := hsyl.isPGroup.to_le hW1T
  have hW1N : E3.wClos W i D.T ≤ normalizer (W : Set G) := hW1T.trans hsyl.le
  have : Group.IsNilpotent (E3.wClos W i D.T) := hW1two.isNilpotent
  have : (W.subgroupOf (E3.wClos W i D.T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hW1N
  have hne : W.subgroupOf (E3.wClos W i D.T) ≠ ⊥ := by
    intro hb
    apply hW.1
    rw [← Subgroup.map_subgroupOf_eq_of_le hWW, hb, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyW : (y : G) ∈ W := hy.1
  have hyC : (y : G) ∈ centralizer (E3.wClos W i D.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have hy1' : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  set b : G := g⁻¹ * (y : G) * g with hbdef
  have hbW : b ∈ conjSubgroup W g := by
    rw [mem_conjSubgroup_iff, hbdef, show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y by group]
    exact hyW
  have hb1 : b ≠ 1 := by
    intro hb
    apply hy1'
    have h1' : (y : G) = g * b * g⁻¹ := by rw [hbdef]; group
    rw [hb] at h1'
    simpa using h1'
  have hbC : b ∈ centralizer (E3.wClos W i D.T : Set G) := by
    have h1' : b ∈ conjSubgroup (centralizer (E3.wClos W i D.T : Set G)) g := by
      rw [mem_conjSubgroup_iff, hbdef, show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y by group]
      exact hyC
    rwa [E3.conjSubgroup_centralizer, hW1g] at h1'
  have hWgW1 : conjSubgroup W g ≤ E3.wClos W i D.T := by
    have h' := E3.conjSubgroup_mono_left g hWW
    rwa [hW1g] at h'
  have hbC1 : b ∈ E3.cClos W i D.T := ⟨hW1T (hWgW1 hbW), hbC⟩
  have hCb : centralizer ({b} : Set G) ≤ conjSubgroup D.M g := by
    rw [← hN, E3.conjSubgroup_normalizer]
    exact centralizer_le_normalizer_conj hTI g hbW hb1
  have hWb : W ≤ conjSubgroup D.M g := by
    refine le_trans ?_ hCb
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact ((Subgroup.mem_centralizer_iff.1 hbC) w (hWW hw)).symm
  have hbot := hXM g hgM hWb
  rw [eq_bot_iff]
  intro x hx
  have hxb : x ∈ X ⊓ conjSubgroup D.M g := by
    refine ⟨hx.1, hCb ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (Subgroup.mem_centralizer_iff.1 hx.2) b hbC1
  rwa [hbot] at hxb

theorem normalizer_wClos_not_le_of_isCalH0 (D : Data G) (h126 : R126 D) {H₀ U : Subgroup G}
    (hH₀ : Hyp124Min D H₀) (hU : InCalV D.M U) (hU7 : Hyp7 U) (h0 : IsCalH0 U H₀) {i : ℕ}
    (hi : D.k + i < rk ↥U) :
    ¬ normalizer (E3.wClos U i D.T : Set G) ≤ D.M := by
  intro hNW
  have hNU : normalizer (U : Set G) = D.M := normalizer_eq_of_inCalV D hU
  have hH := hH₀.1
  have hHE : E1.InE D.k H₀ := h126 H₀ hH₀
  have hTH : D.T ≤ H₀ ⊓ normalizer (U : Set G) := le_inf hH.1 (hNU ▸ D.sylowM.le)
  have hT : IsSylowIn 2 D.T (H₀ ⊓ normalizer (U : Set G)) := TwelveShort.isSylowIn_of_le D hTH
  have hjoin : (H₀ ⊓ normalizer (U : Set G)) ⊔
      (H₀ ⊓ normalizer (E3.wClos U i D.T : Set G)) ≤ D.M :=
    sup_le (inf_le_right.trans hNU.le) (inf_le_right.trans hNW)
  have heq := eight_seven_of_isCalH0 (i := i) hU7 h0 hT hi hHE
  exact hH.2.1 (heq ▸ hjoin)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
