module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

theorem signalizerMcBrideHypothesisA_of_isSectionOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    {H : Subgroup G} (hH : signalizerMcBrideHypothesisB p H) {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] (hX : IsSectionOf X H) (hnc : ∃ x y : X, x * y ≠ y * x) :
    signalizerMcBrideHypothesisA p X := by
  obtain ⟨K', f, hf⟩ := hX
  let ι : K' →* G := H.subtype.comp K'.subtype
  have hι : Function.Injective ι := H.subtype_injective.comp K'.subtype_injective
  let e₁ : K' ≃* ι.range := MonoidHom.ofInjective hι
  let q : ι.range →* X := f.comp e₁.symm.toMonoidHom
  have hq : Function.Surjective q := hf.comp e₁.symm.surjective
  let L₀ : Subgroup G := q.ker.map ι.range.subtype
  have hKH : ι.range ≤ H := by
    rintro _ ⟨k, rfl⟩
    exact (k : H).2
  have hLK : L₀ ≤ ι.range := Subgroup.map_subtype_le _
  have hker : L₀.subgroupOf ι.range = q.ker :=
    Subgroup.comap_map_eq_self_of_injective ι.range.subtype_injective q.ker
  have : (L₀.subgroupOf ι.range).Normal := by
    rw [hker]
    exact MonoidHom.normal_ker q
  let E : ι.range ⧸ L₀.subgroupOf ι.range ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hsimple : IsSimpleGroup (ι.range ⧸ L₀.subgroupOf ι.range) := E.isSimpleGroup
  have hA := hH.2.2 ι.range L₀ hKH hLK hsimple
    (by
      obtain ⟨x, y, hxy⟩ := hnc
      exact ⟨E.symm x, E.symm y, fun hc => hxy (by simpa using congrArg E hc)⟩)
  exact signalizerMcBrideHypothesisA_of_mulEquiv E hA

end CFSG.SignalizerFunctorTheorem
