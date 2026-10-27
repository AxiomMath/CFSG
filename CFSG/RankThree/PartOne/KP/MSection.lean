module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial

public section

namespace CFSG.RankThree.PartOne

theorem exists_section_of_equiv_subgroup {T G : Type} [Group T] [Group G] (ψ : T ≃* G)
    (C : Subgroup G) (Z : Subgroup C) [Z.Normal] {B : Type} [Group B] (φ : (C ⧸ Z) ≃* B) :
    ∃ (A : Subgroup T) (N : Subgroup A) (_ : N.Normal), Nonempty ((A ⧸ N) ≃* B) := by
  let A : Subgroup T := C.map ψ.symm.toMonoidHom
  let κ : A ≃* C := (ψ.symm.subgroupMap C).symm
  let N : Subgroup A := Z.comap κ.toMonoidHom
  have hN : N.Normal := Subgroup.Normal.comap inferInstance _
  refine ⟨A, N, hN, ⟨(QuotientGroup.congr N Z κ ?_).trans φ⟩⟩
  exact Subgroup.map_comap_eq_self_of_surjective κ.surjective Z

theorem exists_section_of_equiv_subgroup_of_iso {T G : Type} [Group T] [Group G] (ψ : T ≃* G)
    (C : Subgroup G) {C₀ : Type} [Group C₀] (κ : C₀ ≃* C) (Z : Subgroup C₀) [Z.Normal]
    {B : Type} [Group B] (φ : (C₀ ⧸ Z) ≃* B) :
    ∃ (A : Subgroup T) (N : Subgroup A) (_ : N.Normal), Nonempty ((A ⧸ N) ≃* B) := by
  let Z' : Subgroup C := Z.map κ.toMonoidHom
  have hZ' : Z'.Normal := Subgroup.Normal.map inferInstance κ.toMonoidHom κ.surjective
  refine exists_section_of_equiv_subgroup ψ C Z' (B := B)
    ((QuotientGroup.congr Z' Z κ.symm ?_).trans φ)
  ext x
  simp [Z']

theorem exists_section_of_equiv_of_le {T : Type} [Group T] {A : Type} [Group A] (G : Subgroup A)
    (ψ : T ≃* G) (C : Subgroup A) (hC : C ≤ G) (Z : Subgroup C) [Z.Normal] {B : Type} [Group B]
    (φ : (C ⧸ Z) ≃* B) :
    ∃ (A' : Subgroup T) (N : Subgroup A') (_ : N.Normal), Nonempty ((A' ⧸ N) ≃* B) :=
  exists_section_of_equiv_subgroup_of_iso ψ (C.subgroupOf G)
    (Subgroup.subgroupOfEquivOfLe hC).symm Z φ

end CFSG.RankThree.PartOne
