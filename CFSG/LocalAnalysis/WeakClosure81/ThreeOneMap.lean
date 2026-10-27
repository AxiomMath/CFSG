module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

namespace ThreeOne

@[expose] def IsE8L3 {G : Type} [Group G] (K : Subgroup G) : Prop :=
  ∃ (E : Subgroup G) (_ : (E.subgroupOf K).Normal),
    E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ IsL3 (↥K ⧸ E.subgroupOf K) 1

private theorem map_subgroupOf_equivMapOfInjective {G G' : Type} [Group G] [Group G']
    {K E : Subgroup G} (φ : G →* G') (hφ : Function.Injective φ) :
    (E.subgroupOf K).map (Subgroup.equivMapOfInjective K φ hφ).toMonoidHom =
      (E.map φ).subgroupOf (K.map φ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨(y : G), ?_, ?_⟩)
    · exact Subgroup.mem_subgroupOf.mp hy
    · exact (Subgroup.coe_equivMapOfInjective_apply K φ hφ y).symm
  · intro hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hzK : z ∈ K := by
      obtain ⟨k, hk, hkφ⟩ := Subgroup.mem_map.mp x.2
      have hzk : z = k := hφ (hzx.trans hkφ.symm)
      rw [hzk]
      exact hk
    exact ⟨⟨z, hzK⟩, Subgroup.mem_subgroupOf.mpr hz, Subtype.ext (by simpa using hzx)⟩

theorem isL3_of_mulEquiv {X : Type} [Group X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : IsL3 X 1 :=
  Or.inl ⟨by decide, CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two e⟩

theorem IsE8L3.map {G G' : Type} [Group G] [Group G'] {K : Subgroup G} (h : IsE8L3 K)
    (φ : G →* G') (hφ : Function.Injective φ) : IsE8L3 (K.map φ) := by
  obtain ⟨E, hE, hEK, hEab, hEcard, hL⟩ := h
  haveI : (E.subgroupOf K).Normal := hE
  have heq := map_subgroupOf_equivMapOfInjective (K := K) (E := E) φ hφ
  refine ⟨E.map φ, ?_, Subgroup.map_mono hEK, ?_, ?_, ?_⟩
  · rw [← heq]
    exact Subgroup.Normal.map hE _ (Subgroup.equivMapOfInjective K φ hφ).surjective
  · haveI : IsMulCommutative E := hEab.1
    exact ⟨Subgroup.map_isMulCommutative E φ, fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hEab.2 y hy, map_one]⟩
  · rw [Subgroup.card_map_of_injective hφ, hEcard]
  · haveI : ((E.map φ).subgroupOf (K.map φ)).Normal := heq ▸
      Subgroup.Normal.map hE _ (Subgroup.equivMapOfInjective K φ hφ).surjective
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective K φ hφ) heq) hL

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
