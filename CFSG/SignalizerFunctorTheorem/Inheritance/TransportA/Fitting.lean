module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.Assembly.Subnormal

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.TransportA

variable {A B : Type*} [Group A] [Group B]

theorem isSubnormal_map (ε : A ≃* B) {L K : Subgroup A} (h : IsSubnormal L K) :
    IsSubnormal (L.map (ε : A →* B)) (K.map (ε : A →* B)) :=
  h.map (ε : A →* B)

theorem isQuasisimple_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : IsQuasisimple G) : IsQuasisimple H := by
  obtain ⟨hp, hs⟩ := hG
  have hc : (Subgroup.center G).map (e : G →* H) = Subgroup.center H := Subgroup.map_center_eq e
  refine ⟨?_, (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : G →* H) e.surjective, ← Subgroup.map_commutator, hp]

theorem isComponentOf_map (ε : A ≃* B) {L K : Subgroup A} (h : IsComponentOf L K) :
    IsComponentOf (L.map (ε : A →* B)) (K.map (ε : A →* B)) :=
  ⟨Subgroup.map_mono h.1, isSubnormal_map ε h.2.1,
    isQuasisimple_of_mulEquiv (L.equivMapOfInjective (ε : A →* B) ε.injective) h.2.2⟩

theorem map_generalizedFitting_le (ε : A ≃* B) :
    (signalizerGeneralizedFitting A).map (ε : A →* B) ≤ signalizerGeneralizedFitting B := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le (sSup_le fun K hK => ?_) (sSup_le fun K hK => ?_)
  · rw [← Subgroup.map_le_iff_le_comap]
    refine le_trans (le_sSup ?_) le_sup_left
    exact ⟨hK.1.map _ ε.surjective,
      (Group.isNilpotent_congr (K.equivMapOfInjective (ε : A →* B) ε.injective)).mp hK.2⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    refine le_trans (le_sSup ?_) le_sup_right
    have := isComponentOf_map ε hK
    rwa [Subgroup.map_top_of_surjective _ ε.surjective] at this

theorem map_generalizedFitting (ε : A ≃* B) :
    (signalizerGeneralizedFitting A).map (ε : A →* B) = signalizerGeneralizedFitting B := by
  refine le_antisymm (map_generalizedFitting_le ε) ?_
  have h := map_generalizedFitting_le ε.symm
  rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_equiv_eq_map_symm] at h
  simpa using h

theorem nonempty_mulEquiv_generalizedFitting (ε : A ≃* B) :
    Nonempty (signalizerGeneralizedFitting A ≃* signalizerGeneralizedFitting B) :=
  ⟨(ε.subgroupMap _).trans (MulEquiv.subgroupCongr (map_generalizedFitting ε))⟩

end CFSG.SignalizerFunctorTheorem.TransportA
