module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] noncomputable def fixedDerivedImage (hx : OddOrderIsometry Q p x)
    (F : Subgroup (V ≃ₗ[K] V)) :
    Subgroup ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
  (F.subgroupOf (supportedFixedDerived Q x)).map (supportedFixedDerivedEquiv hx).toMonoidHom

theorem nonempty_fixedDerivedImage_equiv (hx : OddOrderIsometry Q p x)
    {F : Subgroup (V ≃ₗ[K] V)} (hFle : F ≤ supportedFixedDerived Q x) :
    Nonempty (↥F ≃* ↥(fixedDerivedImage hx F)) :=
  ⟨(Subgroup.subgroupOfEquivOfLe hFle).symm.trans
    ((F.subgroupOf (supportedFixedDerived Q x)).equivMapOfInjective
      (supportedFixedDerivedEquiv hx).toMonoidHom (supportedFixedDerivedEquiv hx).injective)⟩

theorem isQuasisimple_fixedDerivedImage (hx : OddOrderIsometry Q p x)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x) :
    CFSG.IsQuasisimple ↥(fixedDerivedImage hx F) := by
  obtain ⟨e⟩ := nonempty_fixedDerivedImage_equiv hx hFle
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hFq

theorem normal_fixedDerivedImage (hx : OddOrderIsometry Q p x)
    {F : Subgroup (V ≃ₗ[K] V)}
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal) :
    (fixedDerivedImage hx F).Normal := by
  have hsurj : Function.Surjective (supportedFixedDerivedEquiv hx).toMonoidHom :=
    (supportedFixedDerivedEquiv hx).surjective
  have h := hFn.map (supportedFixedDerivedEquiv hx).toMonoidHom hsurj
  simpa only [fixedDerivedImage] using h

end CFSG.RankThree.PartOne.KCOrthogonal

end
