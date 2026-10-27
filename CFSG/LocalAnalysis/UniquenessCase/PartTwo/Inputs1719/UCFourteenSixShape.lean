module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASShapeOdd
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20i
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Sec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem cfShape_sup_of_barInf {H T : Subgroup G} {P : ∀ (X : Type) [Group X], Prop}
    (hP : IsoInvPred P) (hTH : T ≤ normalizer (H : Set G)) (hT : IsPGroup 2 T)
    (hs : IsSimpleGroup (UC22.BarInf H)) (hPH : P (UC22.BarInf H)) :
    CFShape ↥(H ⊔ T) P := by
  intro L _ hcf hnab
  have hHn : (H.subgroupOf (H ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : H ≤ H ⊔ T)).2
      (sup_le Subgroup.le_normalizer hTH)
  rcases isCompositionFactor_of_normal (H.subgroupOf (H ⊔ T)) hcf with h1 | h2
  · have hHcf : E1.IsCompositionFactor ↥H L :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ T))).mp h1
    rcases isCompositionFactor_of_normal (CFSG.solvableRadical ↥H) hHcf with h3 | h4
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (UC22.uc22p20a_abelian_of_compositionFactor
        (CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := ↥H))
        h3 a b) hab
    · obtain ⟨e⟩ := isCompositionFactor_mulEquiv_of_isSimpleGroup h4
      exact hP _ _ ⟨e⟩ hPH
  · have : Group.IsSolvable (↥(H ⊔ T) ⧸ H.subgroupOf (H ⊔ T)) :=
      UC22.uc22p20i_isSolvable_quotient_sup H T hTH hT
    obtain ⟨a, b, hab⟩ := hnab
    exact absurd (UC22.uc22p20a_abelian_of_compositionFactor inferInstance h2 a b) hab

theorem inE_one_sup_of_shape
    {H T : Subgroup G} (hTH : T ≤ normalizer (H : Set G)) (hT : IsPGroup 2 T)
    (hcase : Group.IsSolvable ↥H ∨
      (IsSimpleGroup (UC22.BarInf H) ∧
        ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧ F6.IsL2 p e (UC22.BarInf H)) ∨
          ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
            (LieModel (UC22.BarInf H) .PSL 3 p f ∨ LieModel (UC22.BarInf H) .PSU 3 p f)))) :
    E1.InE 1 (H ⊔ T) := by
  obtain ⟨S, hSyl⟩ := E1.exists_isSylowIn_two (⊤ : Subgroup ↥(H ⊔ T))
  have hHn : (H.subgroupOf (H ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : H ≤ H ⊔ T)).2
      (sup_le Subgroup.le_normalizer hTH)
  rcases hcase with hsolv | ⟨hsimple, hcases⟩
  · have := hsolv
    have : Group.IsSolvable ↥(H.subgroupOf (H ⊔ T)) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ T)).symm
    have : Group.IsSolvable (↥(H ⊔ T) ⧸ H.subgroupOf (H ⊔ T)) :=
      UC22.uc22p20i_isSolvable_quotient_sup H T hTH hT
    have : Group.IsSolvable ↥(H ⊔ T) :=
      Group.isSolvable_of_subgroup_quotient (H.subgroupOf (H ⊔ T))
    have hshape : ShapeInEAS 1 (fun X _ => False) := by
      intro L₀ _ _ _ _ hP
      exact hP.elim
    exact (E1.inE_subgroupOf 1 (H ⊔ T)).mpr
      (inE_of_cfShape le_rfl hSyl (cfShape_of_isSolvable (fun X _ => False)) hshape)
  · rcases hcases with ⟨p, e, hp, hp2, h5, hPL2⟩ | ⟨p, f, hp, hp2, hPL3⟩
    · have hCF : CFShape ↥(H ⊔ T) (fun X _ => F6.IsL2 p e X) :=
        cfShape_sup_of_barInf (isoInvPred_f6IsL2 p e) hTH hT hsimple hPL2
      exact (E1.inE_subgroupOf 1 (H ⊔ T)).mpr
        (inE_of_cfShape le_rfl hSyl hCF (shapeInEAS_l2 hp hp2 h5))
    · have hCF : CFShape ↥(H ⊔ T)
          (fun X _ => LieModel X .PSL 3 p f ∨ LieModel X .PSU 3 p f) :=
        cfShape_sup_of_barInf
          (isoInvPred_or (isoInvPred_lieModel .PSL 3 p f) (isoInvPred_lieModel .PSU 3 p f))
          hTH hT hsimple hPL3
      exact (E1.inE_subgroupOf 1 (H ⊔ T)).mpr
        (inE_of_cfShape le_rfl hSyl hCF (shapeInEAS_l3u3_odd hp hp2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
