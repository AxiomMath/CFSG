module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l48pT_image {G : Type} [Group G] {L : Subgroup G} {x b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    {A : Subgroup ↥L} (hA : A = ggFixSub (L.normalizerMonoidHom ⟨b, hb⟩)) :
    A.map L.subtype = L ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · simpa using a.2
    · have ha' : (L.normalizerMonoidHom ⟨b, hb⟩) a = a := by
        rwa [hA, mem_ggFixSub] at ha
      have hfix : b * (a : G) * b⁻¹ = (a : G) := by
        have h := congrArg Subtype.val ha'
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
        simpa using h
      have hbg : b * (a : G) = (a : G) * b := by
        calc b * (a : G) = (b * (a : G) * b⁻¹) * b := by group
          _ = (a : G) * b := by rw [hfix]
      have hxg : x * (a : G) = (a : G) * x :=
        ((Subgroup.mem_centralizer_iff.mp hxL) a a.2).symm
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      have hHle : (Subgroup.zpowers x ⊔ Subgroup.zpowers b : Subgroup G) ≤
          Subgroup.centralizer ({(a : G)} : Set G) :=
        sup_le (Subgroup.zpowers_le.mpr (by
            rw [Subgroup.mem_centralizer_singleton_iff]; exact hxg))
          (Subgroup.zpowers_le.mpr (by
            rw [Subgroup.mem_centralizer_singleton_iff]; exact hbg))
      exact Subgroup.mem_centralizer_singleton_iff.mp (hHle hh)
  · intro hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgL, hgC⟩ := hg
    rw [Subgroup.mem_map]
    refine ⟨⟨g, hgL⟩, ?_, rfl⟩
    rw [hA, mem_ggFixSub]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hbg : b * g = g * b :=
      (Subgroup.mem_centralizer_iff.mp hgC) b
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
    change b * g * b⁻¹ = g
    rw [hbg]
    group

private theorem l48pT_component {G : Type} [Group G] {L : Subgroup G} {K A : Subgroup ↥L}
    (h : IsComponentOf K A) : IsComponentOf (K.map L.subtype) (A.map L.subtype) :=
  isComponentOf_map_of_injective L.subtype L.subtype_injective h

private theorem l48pT_small {G : Type} [Group G] {L : Subgroup G} (K : Subgroup ↥L) :
    ¬ LargeEvenSmall K → ¬ LargeEvenSmall (K.map L.subtype) := by
  intro h h'
  exact h ((A6InsideSp.largeEvenSmall_map_iff L.subtype_injective K).mp h')

theorem ggB2der_layer_transfer {G : Type} [Group G] {L : Subgroup G} {x b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    {A : Subgroup ↥L} (hA : A = ggFixSub (L.normalizerMonoidHom ⟨b, hb⟩)) :
    A.map L.subtype = L ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers b : Subgroup G) : Set G) ∧
      (LargeEvenLayer A).map L.subtype = LargeEvenLayer (L ⊓ Subgroup.centralizer
        ((Subgroup.zpowers x ⊔ Subgroup.zpowers b : Subgroup G) : Set G)) ∧
      (IsComponentOf (LargeEvenLayer A) A →
        IsComponentOf ((LargeEvenLayer A).map L.subtype) (L ⊓ Subgroup.centralizer
          ((Subgroup.zpowers x ⊔ Subgroup.zpowers b : Subgroup G) : Set G))) ∧
      (¬ LargeEvenSmall (LargeEvenLayer A) →
        ¬ LargeEvenSmall ((LargeEvenLayer A).map L.subtype)) := by
  have hY := l48pT_image hb hxL hA
  refine ⟨hY, ?_, ?_, ?_⟩
  · rw [← largeEvenLayer_map_of_injective L.subtype L.subtype_injective A, hY]
  · intro hcomp
    have hc := l48pT_component hcomp
    rwa [hY] at hc
  · exact l48pT_small (LargeEvenLayer A)

end CFSG.StandardType
