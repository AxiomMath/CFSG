module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixAut
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem gffa2_fixSub_eq {R : Type} [Group R] (x : MulAut R) :
    ggFixSub x = ggAutFixedSubgroup x :=
  Subgroup.ext fun _ => Iff.rfl

theorem gffa2_fixedEquiv {X R : Type} [Group X] [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (hZ : Subgroup.center X = ⊥) (ψ : MulAut X)
    (f u : MulAut R) (hind : LargeEvenInduces θ (fun k k' => k' = ψ k) (u * f * u⁻¹)) :
    Nonempty (↥(ggAutFixedSubgroup ψ) ≃* ↥(ggAutFixedSubgroup f)) := by
  refine gff_nonempty_equiv_fixed (gffIsoOfCenterBot θ hZ) ψ u f (fun x => ?_)
    (MulEquiv.refl ↥(ggAutFixedSubgroup f))
  simpa only [gffIsoOfCenterBot_apply] using hind x (ψ x) rfl

theorem gffa2_fixedEquiv_of_congr {R' R : Type} [Group R'] [Group R] (ε : R' ≃* R)
    (g : MulAut R') (f : MulAut R) (h : ∀ x, f (ε x) = ε (g x)) :
    Nonempty (↥(ggAutFixedSubgroup f) ≃* ↥(ggAutFixedSubgroup g)) := by
  exact ⟨(MulEquiv.subgroupCongr (gff_map_fixed ε g f h)).symm.trans
    (Subgroup.equivMapOfInjective (ggAutFixedSubgroup g) ε.toMonoidHom ε.injective).symm⟩

theorem gffa2_commutator_equiv {G H : Type} [Group G] [Group H] {A : Subgroup G} {B : Subgroup H}
    (e : ↥A ≃* ↥B) : Nonempty (↥⁅A, A⁆ ≃* ↥⁅B, B⁆) := by
  exact ⟨(ggCommutatorEquiv A).trans ((ggCommutatorCongr e).trans (ggCommutatorEquiv B).symm)⟩

theorem gffa2_component_equiv {X R₀ : Type} [Group X] [Group R₀] {C : Subgroup X}
    (T : ↥⁅C, C⁆ ≃* R₀) (hs : IsSimpleGroup R₀) {Q : Subgroup X} (hQ : IsComponentOf Q C) :
    Nonempty (↥Q ≃* R₀) := by
  haveI := hs
  have hQ' : Q = ⁅C, C⁆ := ggComponent_eq_commutator hQ T.isSimpleGroup
  exact ⟨(MulEquiv.subgroupCongr hQ').trans T⟩

theorem gffa2_false_of_solvable {X : Type} [Group X] {C Q : Subgroup X}
    (hC : Group.IsSolvable ↥C) (hQ : IsComponentOf Q C) : False := by
  haveI : Group.IsSolvable ↥C := hC
  have hsol : Group.IsSolvable ↥Q :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hQ.1)
      (Subgroup.inclusion_injective hQ.1)
  haveI : Group.IsSolvable ↥Q := hsol
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr (ggComponent_ne_bot hQ)
  have hcomm : commutator ↥Q = ⊤ := by
    rw [← ggCommutator_subgroupOf Q, ggComponent_perfect hQ, Subgroup.subgroupOf_self]
  have hlt : commutator ↥Q < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Q
  rw [hcomm] at hlt
  exact lt_irrefl _ hlt

end CFSG.StandardType
