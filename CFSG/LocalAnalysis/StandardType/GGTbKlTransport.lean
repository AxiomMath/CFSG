module

public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open


theorem nonempty_mulEquiv_largeEvenLayer_inf_centralizer {G H : Type} [Group G] [Group H]
    {L : Subgroup G} (ψ : ↥L ≃* H) {E : Subgroup G} (hE : E ≤ L) :
    Nonempty (↥(LargeEvenLayer (L ⊓ Subgroup.centralizer (E : Set G))) ≃*
      ↥(LargeEvenLayer (Subgroup.centralizer
        (((E.subgroupOf L).map ψ.toMonoidHom : Subgroup H) : Set H)))) := by
  let A : Subgroup ↥L := Subgroup.centralizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L)
  have hM1 : A.map L.subtype = L ⊓ Subgroup.centralizer (E : Set G) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨a.2, ?_⟩
      change a ∈ Subgroup.centralizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) at ha
      rw [Subgroup.mem_centralizer_iff] at ha
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro e he
      have he' : (⟨e, hE he⟩ : ↥L) ∈ (E.subgroupOf L : Set ↥L) := by
        change (⟨e, hE he⟩ : ↥L) ∈ E.subgroupOf L
        rw [Subgroup.mem_subgroupOf]
        exact he
      simpa using congrArg Subtype.val (ha ⟨e, hE he⟩ he')
    · intro hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxL, hxE⟩ := hx
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      change (⟨x, hxL⟩ : ↥L) ∈ Subgroup.centralizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L)
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro e he
      apply Subtype.ext
      rw [Subgroup.mem_centralizer_iff] at hxE
      have heG : (e : G) ∈ E := by
        change e ∈ E.subgroupOf L at he
        rwa [Subgroup.mem_subgroupOf] at he
      simpa using hxE (e : G) heG
  have hM2 : A.map ψ.toMonoidHom =
      Subgroup.centralizer (((E.subgroupOf L).map ψ.toMonoidHom : Subgroup H) : Set H) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      change a ∈ Subgroup.centralizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) at ha
      rw [Subgroup.mem_centralizer_iff] at ha
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro y hy
      change y ∈ Subgroup.map ψ.toMonoidHom (E.subgroupOf L) at hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨e, he, rfl⟩ := hy
      rw [← map_mul ψ.toMonoidHom e a, ← map_mul ψ.toMonoidHom a e, ha e he]
    · intro hx
      rw [Subgroup.mem_map]
      refine ⟨ψ.symm x, ?_, ψ.apply_symm_apply x⟩
      change (ψ.symm x : ↥L) ∈ Subgroup.centralizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L)
      refine (Subgroup.mem_centralizer_iff).mpr ?_
      intro e he
      have he' : (e : ↥L) ∈ E.subgroupOf L := by
        change e ∈ E.subgroupOf L at he
        exact he
      rw [Subgroup.mem_centralizer_iff] at hx
      have hx' : ψ.toMonoidHom e * x = x * ψ.toMonoidHom e := hx (ψ.toMonoidHom e) (by
        change ψ.toMonoidHom e ∈ Subgroup.map ψ.toMonoidHom (E.subgroupOf L)
        rw [Subgroup.mem_map]
        exact ⟨e, he', rfl⟩)
      have := congrArg ψ.symm hx'
      simpa [map_mul] using this
  have h1 := largeEvenLayer_map_of_injective L.subtype L.subtype_injective A
  have h2 := largeEvenLayer_map_of_injective ψ.toMonoidHom ψ.injective A
  rw [hM1] at h1
  rw [hM2] at h2
  refine ⟨?_⟩
  rw [h1, h2]
  exact (Subgroup.equivMapOfInjective (LargeEvenLayer A) L.subtype L.subtype_injective).symm.trans
    (Subgroup.equivMapOfInjective (LargeEvenLayer A) ψ.toMonoidHom ψ.injective)

end CFSG.StandardType

end
