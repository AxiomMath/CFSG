module

public import CFSG.Quasithin.Background.E11Stmt

public section

namespace CFSG.Quasithin

namespace G11

@[expose] def G119E11Use : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H : Subgroup (GLV V)) (I : Submodule (ZMod 2) V),
    Homogeneous H → IrrPlus H I → fixedSpace H = ⊥ →
    sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤ →
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (U : Type) (_ : AddCommGroup U)
      (_ : Module F U) (_ : Module.Finite F U)
      (ψ : {J : Submodule (ZMod 2) V // IrrPlus H J} ≃ Projectivization F U),
      Module.finrank F U * Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) V ∧
      (∀ g ∈ Subgroup.normalizer (H : Set (GLV V)),
        ∃ (τ : F →+* F) (σ : U →ₛₗ[τ] U) (hσ : Function.Injective σ),
          ∀ (J : Submodule (ZMod 2) V) (hJ : IrrPlus H J) (hgJ : IrrPlus H (conjSub g J)),
            ψ ⟨conjSub g J, hgJ⟩ = Projectivization.map σ hσ (ψ ⟨J, hJ⟩)) ∧
      (∀ M : Submodule (ZMod 2) V, Invariant H M →
        ∃ S : Submodule F U, (∀ (J : Submodule (ZMod 2) V) (hJ : IrrPlus H J),
          J ≤ M ↔ (ψ ⟨J, hJ⟩).submodule ≤ S) ∧
          Module.finrank F S * Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) M)

theorem g119_e11Use_of_e11Stmt (hE : E11Stmt) : G119E11Use := by
  intro V _ _ _ H I hhom hI hfix hsSup
  obtain ⟨D⟩ := hE V H I hhom hI hfix hsSup
  refine ⟨D.F, inferInstance, inferInstance, ?_, D.U, inferInstance, inferInstance, ?_, D.ψ,
    D.finrank_mul, ?_, D.exists_subspace⟩
  · exact charP_of_injective_algebraMap (algebraMap (ZMod 2) D.F).injective 2
  · exact Module.Finite.of_finite
  · intro g hg
    obtain ⟨τ, σ, hσ, hact, -⟩ := D.semilinear g hg
    refine ⟨τ, σ, hσ.1, fun J hJ hgJ => ?_⟩
    obtain ⟨hJ', h⟩ := hact J hJ
    exact h

end G11

end CFSG.Quasithin
