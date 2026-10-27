module

public import CFSG.Quasithin.Background.SmithD37Lin
import CFSG.Quasithin.Background.SmithD37Sub
import CFSG.LinearAlgebra.PiTensorFinrank

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.QuasithinUnique.Setup.Offender
open scoped TensorProduct

variable {U : Type} [CommGroup U] [Finite U]

theorem exists_tensor_card (hU : ∀ u : U, u ^ 2 = 1) [Nontrivial U]
    {L₁ L₂ : Subgroup (MulAut U)} (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hirr : ∀ J : Subgroup U, (∀ g ∈ L₁ ⊔ L₂, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (V₀ V₁ : Type) (_ : AddCommGroup V₀) (_ : AddCommGroup V₁)
      (_ : Module F V₀) (_ : Module F V₁) (_ : FiniteDimensional F V₀)
      (_ : FiniteDimensional F V₁) (ρ₀ : ↥L₁ →* (V₀ ≃ₗ[F] V₀)) (ρ₁ : ↥L₂ →* (V₁ ≃ₗ[F] V₁)),
      Nontrivial V₀ ∧ Nontrivial V₁ ∧ Function.Injective ρ₀ ∧ Function.Injective ρ₁ ∧
      (∀ P : Submodule F V₀, (∀ g : ↥L₁, ∀ v ∈ P, ρ₀ g v ∈ P) → P = ⊥ ∨ P = ⊤) ∧
      (∀ P : Submodule F V₁, (∀ g : ↥L₂, ∀ v ∈ P, ρ₁ g v ∈ P) → P = ⊥ ∨ P = ⊤) ∧
      Nat.card U = Nat.card F ^ (Module.finrank F V₀ * Module.finrank F V₁) := by
  classical
  obtain ⟨F, hF, hFin, hAlg, V, hVg, hVm, ρ, e, hnt, hfin, hact, hspan, -⟩ :=
    exists_tensor_decomp (U := U) hU hcomm hirr
  let : Field F := hF
  let : Finite F := hFin
  let : Algebra (ZMod 2) F := hAlg
  let : ∀ i, AddCommGroup (V i) := hVg
  let : ∀ i, Module F (V i) := hVm
  let : ∀ i, Finite (V i) := hfin
  have : ∀ i, Module.Finite F (V i) := fun i => Module.Finite.of_finite
  have hchar : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hinj : ∀ i, Function.Injective (ρ i) := by
    intro i
    rw [injective_iff_map_eq_one]
    intro g hg
    refine Subtype.ext (MulEquiv.ext fun u => ?_)
    have h2 : factorEnd i ((1 : V i ≃ₗ[F] V i) : Module.End F (V i)) = 1 := by
      rw [LinearEquiv.coe_toLinearMap_one]
      exact factorEnd_one i
    have h := hact i g u
    rw [hg, h2, Module.End.one_apply] at h
    exact Additive.ofMul.injective (e.injective h)
  have hirrV : ∀ i, ∀ P : Submodule F (V i),
      (∀ g : ↥(pair L₁ L₂ i), ∀ v ∈ P, ρ i g v ∈ P) → P = ⊥ ∨ P = ⊤ := by
    intro i P hP
    by_cases hbot : P = ⊥
    · exact Or.inl hbot
    · exact Or.inr (SubForm.eq_top_of_forall_end_mem hbot
        (SubForm.forall_end_mem_of_span_eq_top (hspan i) (fun g v hv => hP g v hv)))
  have hcard : Nat.card U = Nat.card F ^ (Module.finrank F (V 0) * Module.finrank F (V 1)) := by
    have h1 : Nat.card U = Nat.card (Additive U) := (Nat.card_congr Additive.toMul).symm
    have h2 : Nat.card (Additive U) = Nat.card (⨂[F] i, V i) := Nat.card_congr e.toEquiv
    have h3 : Nat.card (⨂[F] i, V i) = Nat.card F ^ Module.finrank F (⨂[F] i, V i) :=
      Module.natCard_eq_pow_finrank (K := F)
    rw [h1, h2, h3, CFSG.LinearAlgebra.finrank_piTensorProduct, Fin.prod_univ_two]
  exact ⟨F, hF, hFin, hchar, V 0, V 1, hVg 0, hVg 1, hVm 0, hVm 1, inferInstance, inferInstance,
    ρ 0, ρ 1, hnt 0, hnt 1, hinj 0, hinj 1, hirrV 0, hirrV 1, hcard⟩

end CFSG.Quasithin.SmithD37
