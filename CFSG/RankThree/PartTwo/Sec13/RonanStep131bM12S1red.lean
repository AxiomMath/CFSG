module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

theorem s1red_isMaxThreeSub_map {G : Type} [Group G] (B : Subgroup G) (Q : Sylow 3 ↥B) :
    IsMaxThreeSub B ((Q : Subgroup B).map B.subtype) := by
  unfold IsMaxThreeSub
  refine ⟨Q.isPGroup'.map B.subtype, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · intro R hR hRB hQR
    have hR' : IsPGroup 3 (R.subgroupOf B) := hR.comap_subtype
    have hle : (Q : Subgroup B) ≤ R.subgroupOf B := by
      intro y hy
      have hyR : (y : G) ∈ R := hQR (Subgroup.mem_map_of_mem B.subtype hy)
      exact Subgroup.mem_subgroupOf.mpr hyR
    have heq : R.subgroupOf B = (Q : Subgroup B) := Q.is_maximal' hR' hle
    refine le_antisymm ?_ hQR
    intro g hg
    have hgB : g ∈ B := hRB hg
    have hmem : (⟨g, hgB⟩ : B) ∈ (Q : Subgroup B) := by
      rw [← heq]
      exact Subgroup.mem_subgroupOf.mpr hg
    exact Subgroup.mem_map_of_mem B.subtype hmem

theorem s1red_conj_pow_three {G : Type} [Group G] (g x : G) (hx : x ^ 3 = 1) :
    (g⁻¹ * x * g) ^ 3 = 1 := by
  have h : (g⁻¹ * x * g) ^ 3 = g⁻¹ * x ^ 3 * g := by
    simp [pow_succ, mul_assoc]
  rw [h, hx]
  simp

theorem s1red_conj_mem {G : Type} [Group G] [Finite G] (B X : Subgroup G) (Q : Sylow 3 ↥B)
    (hX : IsPGroup 3 X) (hXB : X ≤ B) :
    ∃ g : G, ∀ x ∈ X, g⁻¹ * x * g ∈ (Q : Subgroup B).map B.subtype := by
  have hX' : IsPGroup 3 (X.subgroupOf B) := hX.comap_subtype
  obtain ⟨Q₁, hQ₁⟩ := IsPGroup.exists_le_sylow hX'
  haveI : Finite (Sylow 3 ↥B) := Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥B) Q Q₁
  refine ⟨(g : G), fun x hx => ?_⟩
  have hxB : (⟨x, hXB hx⟩ : B) ∈ X.subgroupOf B := Subgroup.mem_subgroupOf.mpr hx
  have hxQ : (⟨x, hXB hx⟩ : B) ∈ (Q₁ : Subgroup B) := hQ₁ hxB
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  exact Subgroup.mem_map_of_mem B.subtype hxQ

theorem s1red_holds : S1red := by
  unfold S1red
  intro G _ _ B F hF hFB hmax X hX hXB
  have hF' : IsPGroup 3 (F.subgroupOf B) := hF.comap_subtype
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hF'
  have hFQ : F ≤ (Q : Subgroup B).map B.subtype := by
    intro g hg
    have hgB : g ∈ B := hFB hg
    have h1 : (⟨g, hgB⟩ : B) ∈ F.subgroupOf B := Subgroup.mem_subgroupOf.mpr hg
    exact Subgroup.mem_map_of_mem B.subtype (hQ h1)
  have hbound := hmax _ (s1red_isMaxThreeSub_map B Q) hFQ
  obtain ⟨g, hg⟩ := s1red_conj_mem B X Q hX hXB
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : {x : G // x ∈ X ∧ x ^ 3 = 1} =>
      (⟨g⁻¹ * x.1 * g, hg x.1 x.2.1, s1red_conj_pow_three g x.1 x.2.2⟩ :
        {x : G // x ∈ (Q : Subgroup B).map B.subtype ∧ x ^ 3 = 1})) ?_) hbound
  intro a b hab
  apply Subtype.ext
  have h1 := congrArg Subtype.val hab
  simpa using h1

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
