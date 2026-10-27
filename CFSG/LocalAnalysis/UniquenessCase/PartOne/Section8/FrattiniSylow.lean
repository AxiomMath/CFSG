module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem eq_sup_normalizer_of_sylow
    {G : Type} [Group G] [Finite G] {K C : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hKC : K ≤ C) (hKnorm : (K.subgroupOf C).Normal)
    (S : Sylow p ↥K) :
    C = K ⊔ (Subgroup.normalizer
      ((((S : Subgroup ↥K).map K.subtype : Subgroup G)) : Set G) ⊓ C) := by
  let Kc : Subgroup C := K.subgroupOf C
  let e : ↥Kc ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  let P : Sylow p ↥Kc :=
    S.mapSurjective (f := e.symm.toMonoidHom) (by
      simpa only [MulEquiv.coe_toMonoidHom] using e.symm.surjective)
  let M : Subgroup G := (S : Subgroup ↥K).map K.subtype
  haveI : Kc.Normal := hKnorm
  haveI : Finite (Sylow p ↥Kc) :=
    Sylow.finite_of_finiteIndex (Classical.arbitrary (Sylow p ↥Kc))
  have hfr : Subgroup.normalizer (((P : Subgroup ↥Kc)).map Kc.subtype) ⊔ Kc = ⊤ :=
    Sylow.normalizer_sup_eq_top P
  have hKc_map : Kc.map C.subtype = K := by
    simp [Kc, hKC]
  have htop_map : (⊤ : Subgroup C).map C.subtype = C := by
    rw [← MonoidHom.range_eq_map, C.range_subtype]
  have hM : M ≤ C := by
    simpa [M] using (Subgroup.map_subtype_le (S : Subgroup ↥K)).trans hKC
  have hQmap : ((P : Subgroup ↥Kc).map Kc.subtype).map C.subtype = M := by
    simp only [P, M, Sylow.coe_mapSurjective, Subgroup.map_map]
    rw [show C.subtype.comp (Kc.subtype.comp e.symm.toMonoidHom) = K.subtype from by
      ext x
      rfl]
  have hQsub : M.subgroupOf C = (P : Subgroup ↥Kc).map Kc.subtype := by
    rw [← hQmap]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hnorm_sub : (Subgroup.normalizer (M : Set G)).subgroupOf C =
      Subgroup.normalizer ((P : Subgroup ↥Kc).map Kc.subtype) := by
    rw [Subgroup.subgroupOf_normalizer_eq hM, hQsub]
  have hnorm_map : (Subgroup.normalizer ((P : Subgroup ↥Kc).map Kc.subtype)).map
        C.subtype = Subgroup.normalizer (M : Set G) ⊓ C := by
    rw [← hnorm_sub, Subgroup.subgroupOf_map_subtype]
  have hfr_map : (Subgroup.normalizer ((P : Subgroup ↥Kc).map Kc.subtype)).map C.subtype ⊔
        K = C := by
    have h := congrArg (Subgroup.map C.subtype) hfr
    rw [Subgroup.map_sup, hKc_map, htop_map] at h
    exact h
  have hC : Subgroup.normalizer (M : Set G) ⊓ C ⊔ K = C := by
    rw [← hnorm_map, hfr_map]
  change C = K ⊔ (Subgroup.normalizer (M : Set G) ⊓ C)
  exact hC.symm.trans (sup_comm _ _)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
