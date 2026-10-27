module

public import CFSG.Walter.Bender1970.S2.OddCentralizer
public import CFSG.Walter.Bender1970.S2.Transport

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

section Transport

variable {G : Type} [Group G] [Finite G]

theorem fittingSubgroupOf_map_subtype (H : Subgroup G) (C : Subgroup H) :
    (CFSG.fittingSubgroupOf C).map H.subtype = CFSG.fittingSubgroupOf (C.map H.subtype) := by
  let D : Subgroup G := C.map H.subtype
  let e : C ≃* D := Subgroup.equivMapOfInjective C H.subtype H.subtype_injective
  have hcomp : H.subtype.comp C.subtype = D.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  calc (CFSG.fittingSubgroupOf C).map H.subtype
      = (CFSG.fittingSubgroup C).map (H.subtype.comp C.subtype) := by
        rw [CFSG.fittingSubgroupOf, Subgroup.map_map]
    _ = ((CFSG.fittingSubgroup C).map e.toMonoidHom).map D.subtype := by
        rw [hcomp, Subgroup.map_map]
    _ = CFSG.fittingSubgroupOf D := by
        rw [map_fittingSubgroup_of_mulEquiv' e]
        rfl

omit [Finite G] in
theorem oddCoreOf_map_subtype (H : Subgroup G) (A : Subgroup H) :
    (oddCoreOf A).map H.subtype = oddCoreOf (A.map H.subtype) := by
  let D : Subgroup G := A.map H.subtype
  let e : A ≃* D := Subgroup.equivMapOfInjective A H.subtype H.subtype_injective
  have hcomp : H.subtype.comp A.subtype = D.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  calc (oddCoreOf A).map H.subtype
      = (pPrimeCore 2 A).map (H.subtype.comp A.subtype) := by
        rw [oddCoreOf, Subgroup.map_map]
    _ = ((pPrimeCore 2 A).map e.toMonoidHom).map D.subtype := by
        rw [hcomp, Subgroup.map_map]
    _ = oddCoreOf D := by
        rw [CFSG.pPrimeCore_map_iso 2 e]
        rfl

end Transport

theorem bender1970_2_5_subgroup
    {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsAStar H) {t : G} (htH : t ∈ H) (ht : orderOf t = 2) (T : Sylow 2 H)
    (htT : (⟨t, htH⟩ : H) ∈ (T : Subgroup H)) {U : Subgroup G}
    (hU : U = oddCoreOf (CFSG.fittingSubgroupOf (H ⊓ Subgroup.centralizer ({t} : Set G)))) :
    U ≤ (oStar H).map H.subtype ∧
      U ⊓ Subgroup.centralizer (((T : Subgroup H).map H.subtype : Subgroup G) : Set G) ≤
        oddCoreOf H ∧
      ∀ E : Subgroup G, IsComponentOf E H →
        U ≤ Subgroup.normalizer (E : Set G) ∧
          ((Subgroup.centralizer (E : Set G)).subgroupOf U).Normal ∧
          (∀ [((Subgroup.centralizer (E : Set G)).subgroupOf U).Normal],
            IsCyclic (U ⧸ (Subgroup.centralizer (E : Set G)).subgroupOf U)) ∧
          (IsTypeL2Even (E ⧸ Subgroup.center E) ∨ IsTypeJR (E ⧸ Subgroup.center E) →
            U ≤ Subgroup.centralizer (E : Set G)) := by
  classical
  set t' : H := ⟨t, htH⟩ with ht'
  have ht'o : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  set C' := Subgroup.centralizer ({t'} : Set H) with hC'
  have hC'map : C'.map H.subtype = H ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show (y : G) ∈ Subgroup.centralizer ({t} : Set G)
      have hy' : y ∈ Subgroup.centralizer ({t'} : Set H) := hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy' ⊢
      exact congrArg Subtype.val hy'
    · rintro ⟨hxH, hxt⟩
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      have hxt' : x ∈ Subgroup.centralizer ({t} : Set G) := hxt
      show (⟨x, hxH⟩ : H) ∈ Subgroup.centralizer ({t'} : Set H)
      rw [Subgroup.mem_centralizer_singleton_iff] at hxt' ⊢
      exact Subtype.ext hxt'
  set U' := oddCoreOf (CFSG.fittingSubgroupOf C') with hU'
  have hUU' : U'.map H.subtype = U := by
    rw [hU', oddCoreOf_map_subtype, fittingSubgroupOf_map_subtype, hC'map, hU]
  obtain ⟨hUO, hCU, hE⟩ := bender1970_2_5 hH ht'o T htT rfl
  have hmemU : ∀ u ∈ U, ∃ u' ∈ U', (u' : G) = u := by
    intro u hu
    rw [← hUU'] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    exact ⟨u', hu', rfl⟩
  refine ⟨?_, ?_, fun E hEH => ?_⟩
  · rw [← hUU']
    exact Subgroup.map_mono hUO
  · rintro u ⟨hu, huT⟩
    obtain ⟨u', hu', rfl⟩ := hmemU u hu
    have hu'T : u' ∈ Subgroup.centralizer ((T : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp huT s ⟨s, hs, rfl⟩
    exact ⟨u', hCU ⟨hu', hu'T⟩, rfl⟩
  set E' := E.subgroupOf H with hE'
  have hE'c : IsComponentOf E' ⊤ := fstar_isComponentOf_subgroupOf_top hEH
  obtain ⟨hN', -, hcyc', htyp'⟩ := hE E' hE'c
  have hUN : U ≤ Subgroup.normalizer (E : Set G) := by
    intro u hu
    obtain ⟨u', hu', rfl⟩ := hmemU u hu
    have h1 := hN' hu'
    rw [hE', ← Subgroup.subgroupOf_normalizer_eq hEH.1, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hcentiff : ∀ u' : H, u' ∈ Subgroup.centralizer (E' : Set H) ↔
      (u' : G) ∈ Subgroup.centralizer (E : Set G) := by
    intro u'
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      exact congrArg Subtype.val (h ⟨x, hEH.1 hx⟩ (show (⟨x, hEH.1 hx⟩ : H) ∈ E' from hx))
    · intro h x hx
      exact Subtype.ext (h x hx)
  refine ⟨hUN, normal_centralizer_subgroupOf hUN, fun {_} => ?_, fun h => ?_⟩
  · have : ((Subgroup.centralizer (E' : Set H)).subgroupOf U').Normal :=
      normal_centralizer_subgroupOf hN'
    have hcyc : IsCyclic (U' ⧸ (Subgroup.centralizer (E' : Set H)).subgroupOf U') := hcyc'
    let eU : U' ≃* U := (U'.equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hUU')
    have hmap : ((Subgroup.centralizer (E' : Set H)).subgroupOf U').map eU.toMonoidHom =
        (Subgroup.centralizer (E : Set G)).subgroupOf U := by
      ext u
      constructor
      · rintro ⟨u', hu', rfl⟩
        have hu'' : u' ∈ (Subgroup.centralizer (E' : Set H)).subgroupOf U' := hu'
        rw [Subgroup.mem_subgroupOf] at hu''
        show eU u' ∈ (Subgroup.centralizer (E : Set G)).subgroupOf U
        rw [Subgroup.mem_subgroupOf]
        exact (hcentiff u').mp hu''
      · intro hu
        obtain ⟨u', hu', hu'u⟩ := hmemU u u.2
        refine ⟨⟨u', hu'⟩, ?_, Subtype.ext hu'u⟩
        show (⟨u', hu'⟩ : U') ∈ (Subgroup.centralizer (E' : Set H)).subgroupOf U'
        have hu2 : u ∈ (Subgroup.centralizer (E : Set G)).subgroupOf U := hu
        rw [Subgroup.mem_subgroupOf] at hu2
        rw [Subgroup.mem_subgroupOf, hcentiff]
        show (u' : G) ∈ Subgroup.centralizer (E : Set G)
        rw [hu'u]
        exact hu2
    let eQ := QuotientGroup.congr _ _ eU hmap
    exact isCyclic_of_surjective eQ.toMonoidHom eQ.surjective
  · have h' : IsTypeL2Even (E' ⧸ Subgroup.center E') ∨ IsTypeJR (E' ⧸ Subgroup.center E') := by
      rcases h with ⟨f, hf, ⟨φ⟩⟩ | hJ
      · exact Or.inl ⟨f, hf, ⟨(subgroupOfQuotientCenterEquiv hEH.1).trans φ⟩⟩
      · exact Or.inr (hJ.of_mulEquiv (subgroupOfQuotientCenterEquiv hEH.1).symm)
    intro u hu
    obtain ⟨u', hu', rfl⟩ := hmemU u hu
    exact (hcentiff u').mp (htyp' h' hu')

end CFSG.Walter
