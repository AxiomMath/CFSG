module

public import CFSG.Foundations.Basic
import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG

theorem isComponent_map_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) {R : Subgroup A}
    (h : IsComponent R) : IsComponent (R.map φ.toMonoidHom) :=
  ⟨(IsQuasisimple.congr (R.equivMapOfInjective φ.toMonoidHom φ.injective)).1 h.1,
    h.2.map φ.surjective⟩

theorem isComponent_map_mulEquiv_iff {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (R : Subgroup A) : IsComponent (R.map φ.toMonoidHom) ↔ IsComponent R := by
  refine ⟨fun h => ?_, isComponent_map_mulEquiv φ⟩
  have h2 := isComponent_map_mulEquiv φ.symm h
  have : (R.map φ.toMonoidHom).map φ.symm.toMonoidHom = R := by
    ext a
    simp
  rwa [this] at h2

theorem isComponent_subgroupOf_map_iff {A B : Type*} [Group A] [Group B] (ι : A →* B)
    (hι : Function.Injective ι) {Y : Subgroup A} {Y' : Subgroup B} (hY : Y.map ι = Y')
    (Q : Subgroup A) :
    IsComponent (Q.subgroupOf Y) ↔ IsComponent ((Q.map ι).subgroupOf Y') := by
  subst hY
  let φ : ↥Y ≃* ↥(Y.map ι) := Y.equivMapOfInjective ι hι
  have key : (Q.map ι).subgroupOf (Y.map ι) = (Q.subgroupOf Y).map φ.toMonoidHom := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨q, hq, hqy⟩
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 y.2
      have : a = q := hι (hay.trans hqy.symm)
      subst this
      exact ⟨⟨a, ha⟩, hq, Subtype.ext hay⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [key, isComponent_map_mulEquiv_iff]

end CFSG.RankThree.PartTwo.Sec21.FF79
