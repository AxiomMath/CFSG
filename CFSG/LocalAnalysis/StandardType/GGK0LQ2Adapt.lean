module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]

noncomputable def coreFactor_equiv_rationalComponent
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (A : K0LangMark Omega lab p R I phi) (c : KernelComponent (rootCharHom A.a)) :
    coreFactor A.setup A.iota A.a c ≃*
      rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) c := by
  have hspan : rationalSpan A.setup.ρ A.setup.Γ (rootCharHom A.a) c ≤ A.setup.Γ :=
    inf_le_right
  have hleΓ : rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) c ≤ A.setup.Γ :=
    Subgroup.commutator_le_of_le hspan hspan
  have hle : rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) c ≤ A.iota.range := by
    rw [A.iota_range]
    exact hleΓ
  refine (Subgroup.equivMapOfInjective
    (coreFactor A.setup A.iota A.a c) A.iota A.iota_inj).trans ?_
  refine MulEquiv.subgroupCongr ?_
  rw [coreFactor, Subgroup.map_comap_eq]
  exact inf_eq_right.mpr hle

theorem coreFactor_label_of_rationalComponent_label
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    {ell : LargeEvenLabel}
    (A : K0LangMark Omega lab p R I phi) (c : KernelComponent (rootCharHom A.a))
    (h : GGHasLabel ell
      (rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) c ⧸
        Subgroup.center (rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) c))) :
    GGHasLabel ell
      (coreFactor A.setup A.iota A.a c ⧸
        Subgroup.center (coreFactor A.setup A.iota A.a c)) :=
  largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨f⟩ =>
      ⟨(QuotientGroup.congr
        (Subgroup.center ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) c))
        (Subgroup.center ↥(coreFactor A.setup A.iota A.a c))
        (coreFactor_equiv_rationalComponent A c).symm
        (Subgroup.map_center_eq (coreFactor_equiv_rationalComponent A c).symm)).symm.trans f⟩)
    h

end CFSG.StandardType.GGK0MarkedKacIface1587

end
