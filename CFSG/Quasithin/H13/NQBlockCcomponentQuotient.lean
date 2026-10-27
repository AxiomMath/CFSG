module

public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin.H13.NQBlock

theorem Ccomponent_solvable_quotient_image {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hN : Group.IsSolvable N) {L : Subgroup G} (hL : CFSG.IsCComponent L) :
    CFSG.IsCComponent (L.map (QuotientGroup.mk' N)) := by
  refine mem_cComp_top_iff_isCComponent.mp ?_
  exact map_mem_cComp_top (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (by rw [QuotientGroup.ker_mk']; exact hN) (mem_cComp_top_iff_isCComponent.mpr hL)

theorem Ccomponent_solvable_quotient_bijection {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hN : Group.IsSolvable N) :
    Set.BijOn (Subgroup.map (QuotientGroup.mk' N)) {L : Subgroup G | CFSG.IsCComponent L}
        {J : Subgroup (G ⧸ N) | CFSG.IsCComponent J} ∧
      ∀ J : Subgroup (G ⧸ N), CFSG.IsCComponent J →
        CFSG.IsCComponent ((CFSG.perfectResidual ↥(J.comap (QuotientGroup.mk' N))).map
            (J.comap (QuotientGroup.mk' N)).subtype) ∧
          ((CFSG.perfectResidual ↥(J.comap (QuotientGroup.mk' N))).map
            (J.comap (QuotientGroup.mk' N)).subtype).map (QuotientGroup.mk' N) = J := by
  have hG : {L : Subgroup G | CFSG.IsCComponent L} = cComp (⊤ : Subgroup G) :=
    Set.ext fun _ => mem_cComp_top_iff_isCComponent.symm
  have hQ : {J : Subgroup (G ⧸ N) | CFSG.IsCComponent J} = cComp (⊤ : Subgroup (G ⧸ N)) :=
    Set.ext fun _ => mem_cComp_top_iff_isCComponent.symm
  have hbij := cComp_quotient_bijOn N hN
  refine ⟨by rw [hG, hQ]; exact hbij, fun J hJ => ?_⟩
  obtain ⟨L, hL, rfl⟩ := hbij.surjOn (mem_cComp_top_iff_isCComponent.mpr hJ)
  have hcomap : (L.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = L ⊔ N := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hcore : perfectCore (L ⊔ N) = L :=
    (cComp_commutator_perfectCore hL le_top hN Subgroup.le_normalizer_of_normal).2
  rw [← perfectCore_eq_map_perfectResidual, hcomap, hcore]
  exact ⟨mem_cComp_top_iff_isCComponent.mp hL, rfl⟩

end CFSG.Quasithin.H13.NQBlock
