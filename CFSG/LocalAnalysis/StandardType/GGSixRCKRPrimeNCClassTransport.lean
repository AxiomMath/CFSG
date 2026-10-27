module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassicalSpecs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCClassTransportConn

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore
open scoped Matrix
open CFSG.Open (StatedLieTag)

private theorem rckCT_iform_comm (τ : Tag) (x y : Fin τ.rank → ℤ) :
    CFSG.LieType.Steinberg.Adjoint.iform x y = CFSG.LieType.Steinberg.Adjoint.iform y x := by
  simp only [CFSG.LieType.Steinberg.Adjoint.iform]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [(symmetrizedCartan_isSymm τ).apply i j]
  ring

private theorem rckCT_closed
    {τ τK : Tag} {a b : Fin τ.rank → GGLˣ} {aK : Fin τK.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} {ι : (Fin τ.rank → ℤ) → (Fin τK.rank → ℤ)}
    (hbij : Set.BijOn ι (componentRoots (rootCharHom a) i) {γ' | IsRoot τK γ'})
    (hform : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      CFSG.LieType.Steinberg.Adjoint.iform (ι γ) (ι δ) = CFSG.LieType.Steinberg.Adjoint.iform γ δ)
    (hchar : ∀ γ ∈ componentRoots (rootCharHom a) i,
      rootCharHom aK (Multiplicative.ofAdd (ι γ)) = rootCharHom b (Multiplicative.ofAdd γ))
    {j : KernelComponent (rootCharHom aK)} {δ ε : Fin τ.rank → ℤ}
    (hδ : δ ∈ componentRoots (rootCharHom a) i) (hδj : ι δ ∈ componentRoots (rootCharHom aK) j)
    (hεP : ε ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b)))
    (hne : CFSG.LieType.Steinberg.Adjoint.iform δ ε ≠ 0) :
    ε ∈ componentRoots (rootCharHom a) i ∧ ι ε ∈ componentRoots (rootCharHom aK) j := by
  obtain ⟨hδk, hδki⟩ := hδ
  have hεk : ε ∈ kernelRoots (rootCharHom a) := by
    refine ⟨hεP.1, ?_⟩
    have h1 := hεP.2
    rw [MonoidHom.prod_apply, Prod.mk_eq_one] at h1
    exact h1.1
  have hεΨ : ε ∈ componentRoots (rootCharHom a) i := by
    refine ⟨hεk, ?_⟩
    rw [← hδki]
    exact (mk_eq_of_iform_ne_zero (α := ⟨δ, hδk⟩) (β := ⟨ε, hεk⟩) hne).symm
  have hιεk : ι ε ∈ kernelRoots (rootCharHom aK) :=
    (rckCT_mem_pair_iff hbij hchar hεΨ).1 hεP
  have hne' : CFSG.LieType.Steinberg.Adjoint.iform (ι δ) (ι ε) ≠ 0 := by
    rw [hform δ ⟨hδk, hδki⟩ ε hεΨ]
    exact hne
  obtain ⟨hιδk, hιδj⟩ := hδj
  refine ⟨hεΨ, ?_⟩
  refine ⟨hιεk, ?_⟩
  rw [← hιδj]
  exact (mk_eq_of_iform_ne_zero (α := ⟨ι δ, hιδk⟩) (β := ⟨ι ε, hιεk⟩) hne').symm

theorem rckClassTransport_holds : RCKClassTransport := by
  intro τ τK a b aK i ι hbij hform hchar j
  induction j using Quotient.inductionOn with
  | _ u =>
    obtain ⟨γ, hγ, hιγ⟩ := hbij.surjOn u.2.1
    have hιγk : ι γ ∈ kernelRoots (rootCharHom aK) := by rw [hιγ]; exact u.2
    have hγP : γ ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b)) :=
      (rckCT_mem_pair_iff hbij hchar hγ).2 hιγk
    have hγj : ι γ ∈ componentRoots (rootCharHom aK)
        (⟦u⟧ : KernelComponent (rootCharHom aK)) := by
      refine ⟨hιγk, ?_⟩
      rw [show (⟨ι γ, hιγk⟩ : kernelRoots (rootCharHom aK)) = u from Subtype.ext hιγ]
    refine ⟨(⟦⟨γ, hγP⟩⟧ : KernelComponent ((rootCharHom a).prod (rootCharHom b))), ?_⟩
    ext δ
    constructor
    · intro hδ
      obtain ⟨hδP, hδeq⟩ := hδ
      have hEqv : Relation.EqvGen
          (fun α β : kernelRoots ((rootCharHom a).prod (rootCharHom b)) =>
            (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
          ⟨δ, hδP⟩ ⟨γ, hγP⟩ := Quotient.exact hδeq
      have hiff : ∀ x y : kernelRoots ((rootCharHom a).prod (rootCharHom b)),
          Relation.EqvGen
            (fun α β : kernelRoots ((rootCharHom a).prod (rootCharHom b)) =>
              (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y →
          ((x.1 ∈ componentRoots (rootCharHom a) i ∧
              ι x.1 ∈ componentRoots (rootCharHom aK) (⟦u⟧ : KernelComponent (rootCharHom aK))) ↔
            (y.1 ∈ componentRoots (rootCharHom a) i ∧
              ι y.1 ∈ componentRoots (rootCharHom aK)
                (⟦u⟧ : KernelComponent (rootCharHom aK)))) := by
        intro x y hxy
        induction hxy with
        | rel x y hr =>
          have hr' : CFSG.LieType.Steinberg.Adjoint.iform x.1 y.1 ≠ 0 := by
            rw [← dotProduct_mulVec_eq_iform x.1 y.1]
            exact hr
          have hr'' : CFSG.LieType.Steinberg.Adjoint.iform y.1 x.1 ≠ 0 := by
            rw [rckCT_iform_comm τ y.1 x.1]
            exact hr'
          exact ⟨fun hx => rckCT_closed hbij hform hchar hx.1 hx.2 y.2 hr',
            fun hy => rckCT_closed hbij hform hchar hy.1 hy.2 x.2 hr''⟩
        | refl x => exact Iff.rfl
        | symm x y _ ih => exact ih.symm
        | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
      have hγT : γ ∈ componentRoots (rootCharHom a) i ∧
          ι γ ∈ componentRoots (rootCharHom aK) (⟦u⟧ : KernelComponent (rootCharHom aK)) :=
        ⟨hγ, hγj⟩
      exact (hiff ⟨δ, hδP⟩ ⟨γ, hγP⟩ hEqv).2 hγT
    · intro hδ
      obtain ⟨hδΨ, hδj⟩ := hδ
      obtain ⟨hιδk, hιδjmem⟩ := hδj
      have hδP : δ ∈ kernelRoots ((rootCharHom a).prod (rootCharHom b)) :=
        (rckCT_mem_pair_iff hbij hchar hδΨ).2 hιδk
      refine ⟨hδP, ?_⟩
      exact (rckCT_connected hbij hform hchar hγ hδΨ hγj ⟨hιδk, hιδjmem⟩ hγP hδP).symm

end CFSG.StandardType.RCKRP

end
