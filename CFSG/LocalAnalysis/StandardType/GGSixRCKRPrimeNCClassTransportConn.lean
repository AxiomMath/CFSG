module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassicalSpecs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

theorem rckCT_mem_pair_iff
    {τ τK : Tag} {a b : Fin τ.rank → GGLˣ} {aK : Fin τK.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {ι : (Fin τ.rank → ℤ) → (Fin τK.rank → ℤ)}
    (hbij : Set.BijOn ι (componentRoots (rootCharHom a) i) {γ' | IsRoot τK γ'})
    (hchar : ∀ γ ∈ componentRoots (rootCharHom a) i,
      rootCharHom aK (Multiplicative.ofAdd (ι γ)) = rootCharHom b (Multiplicative.ofAdd γ))
    {δ : Fin τ.rank → ℤ} (hδ : δ ∈ componentRoots (rootCharHom a) i) :
    δ ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b)) ↔
      ι δ ∈ kernelRoots (rootCharHom aK) := by
  obtain ⟨hδk, hδeq⟩ := hδ
  have hδc : δ ∈ componentRoots (rootCharHom a) i := ⟨hδk, hδeq⟩
  constructor
  · intro hP
    refine ⟨hbij.mapsTo hδc, ?_⟩
    have hb : rootCharHom b (Multiplicative.ofAdd δ) = 1 := by
      have h2 := hP.2
      rw [MonoidHom.prod_apply, Prod.mk_eq_one] at h2
      exact h2.2
    rw [hchar δ hδc, hb]
  · intro hK
    refine ⟨hδk.1, ?_⟩
    rw [MonoidHom.prod_apply, Prod.mk_eq_one]
    exact ⟨hδk.2, by rw [← hchar δ hδc]; exact hK.2⟩

private theorem rckCT_eqvGen
    {τ τK : Tag} {a b : Fin τ.rank → GGLˣ} {aK : Fin τK.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {ι : (Fin τ.rank → ℤ) → (Fin τK.rank → ℤ)}
    (hbij : Set.BijOn ι (componentRoots (rootCharHom a) i) {γ' | IsRoot τK γ'})
    (hform : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      CFSG.LieType.Steinberg.Adjoint.iform (ι γ) (ι δ) =
        CFSG.LieType.Steinberg.Adjoint.iform γ δ)
    (hchar : ∀ γ ∈ componentRoots (rootCharHom a) i,
      rootCharHom aK (Multiplicative.ofAdd (ι γ)) = rootCharHom b (Multiplicative.ofAdd γ))
    (u v : kernelRoots (rootCharHom aK))
    (huv : Relation.EqvGen (fun α β : kernelRoots (rootCharHom aK) =>
      (α : Fin τK.rank → ℤ) ⬝ᵥ (Matrix.mulVec τK.symmetrizedCartan
        (β : Fin τK.rank → ℤ)) ≠ 0) u v) :
    ∀ (x y : Fin τ.rank → ℤ), x ∈ componentRoots (rootCharHom a) i →
      y ∈ componentRoots (rootCharHom a) i →
      ι x = (u : Fin τK.rank → ℤ) → ι y = (v : Fin τK.rank → ℤ) →
      ∀ (hxP : x ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b)))
        (hyP : y ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b))),
      Relation.EqvGen (fun α β : kernelRoots ((rootCharHom a).prod (rootCharHom b)) =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (Matrix.mulVec τ.symmetrizedCartan
          (β : Fin τ.rank → ℤ)) ≠ 0) ⟨x, hxP⟩ ⟨y, hyP⟩ := by
  induction huv with
  | rel u v huv =>
      intro x y hx hy hix hiy hxP hyP
      refine Relation.EqvGen.rel _ _ ?_
      rw [dotProduct_mulVec_eq_iform]
      have huv' : CFSG.LieType.Steinberg.Adjoint.iform (u : Fin τK.rank → ℤ) v ≠ 0 := by
        rwa [dotProduct_mulVec_eq_iform] at huv
      have hxy : CFSG.LieType.Steinberg.Adjoint.iform (ι x) (ι y) ≠ 0 := by
        rw [hix, hiy]
        exact huv'
      rw [← hform x hx y hy]
      exact hxy
  | refl u =>
      intro x y hx hy hix hiy hxP hyP
      have hxy : x = y := hbij.injOn hx hy (hix.trans hiy.symm)
      have hst : (⟨x, hxP⟩ : kernelRoots ((rootCharHom a).prod (rootCharHom b))) =
          ⟨y, hyP⟩ := Subtype.ext hxy
      rw [hst]
      exact Relation.EqvGen.refl _
  | symm u v huv ih =>
      intro x y hx hy hix hiy hxP hyP
      exact Relation.EqvGen.symm _ _ (ih y x hy hx hiy hix hyP hxP)
  | trans u v w huv hvw ihuv ihvw =>
      intro x y hx hy hix hiy hxP hyP
      obtain ⟨z, hz, hiz⟩ := hbij.surjOn v.2.1
      have hzP : z ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b)) :=
        (rckCT_mem_pair_iff hbij hchar hz).2 (by rw [hiz]; exact v.2)
      exact Relation.EqvGen.trans _ _ _
        (ihuv x z hx hz hix hiz hxP hzP) (ihvw z y hz hy hiz hiy hzP hyP)

theorem rckCT_connected
    {τ τK : Tag} {a b : Fin τ.rank → GGLˣ} {aK : Fin τK.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {ι : (Fin τ.rank → ℤ) → (Fin τK.rank → ℤ)}
    (hbij : Set.BijOn ι (componentRoots (rootCharHom a) i) {γ' | IsRoot τK γ'})
    (hform : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      CFSG.LieType.Steinberg.Adjoint.iform (ι γ) (ι δ) = CFSG.LieType.Steinberg.Adjoint.iform γ δ)
    (hchar : ∀ γ ∈ componentRoots (rootCharHom a) i,
      rootCharHom aK (Multiplicative.ofAdd (ι γ)) = rootCharHom b (Multiplicative.ofAdd γ))
    {j : KernelComponent (rootCharHom aK)} {γ δ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) (hδ : δ ∈ componentRoots (rootCharHom a) i)
    (hγj : ι γ ∈ componentRoots (rootCharHom aK) j)
    (hδj : ι δ ∈ componentRoots (rootCharHom aK) j)
    (hγP : γ ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b)))
    (hδP : δ ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b))) :
    (⟦⟨γ, hγP⟩⟧ : KernelComponent ((rootCharHom a).prod (rootCharHom b))) = ⟦⟨δ, hδP⟩⟧ := by
  obtain ⟨hγk, hγjeq⟩ := hγj
  obtain ⟨hδk, hδjeq⟩ := hδj
  have huv : Relation.EqvGen (fun α β : kernelRoots (rootCharHom aK) =>
      (α : Fin τK.rank → ℤ) ⬝ᵥ (Matrix.mulVec τK.symmetrizedCartan
        (β : Fin τK.rank → ℤ)) ≠ 0) ⟨ι γ, hγk⟩ ⟨ι δ, hδk⟩ :=
    Quotient.exact (hγjeq.trans hδjeq.symm)
  exact Quotient.sound (rckCT_eqvGen hbij hform hchar ⟨ι γ, hγk⟩ ⟨ι δ, hδk⟩ huv
    γ δ hγ hδ rfl rfl hγP hδP)

end CFSG.StandardType.RCKRP

end
