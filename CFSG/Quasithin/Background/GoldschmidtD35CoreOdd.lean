module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreGeom

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 Equiv
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {L : Subgroup (V ≃ₗ[F] V)} {pt : Fin 6 → ℙ F V}

theorem pointAct_eq_of_smul (n : gammaL F V) {p q : ℙ F V} {c : F} (h : n.1 p.rep = c • q.rep) :
    pointAct n p = q := by
  have h1 : pointAct n p = Projectivization.mk F (n.1 p.rep)
      (gammaL_ne_zero n.2 p.rep_nonzero) := by
    conv_lhs => rw [← Projectivization.mk_rep p]
    exact pointAct_mk n p.rep_nonzero
  rw [h1]
  conv_rhs => rw [← Projectivization.mk_rep q]
  exact (Projectivization.mk_eq_mk_iff' F _ _ _ q.rep_nonzero).2 ⟨c, h.symm⟩

theorem IsSixOrbit.indep_smul [FiniteDimensional F V] (hV : Module.finrank F V = 3)
    (hO : IsSixOrbit L pt)
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {i j k : Fin 6} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {c₁ c₂ c₃ : F} (h₁ : c₁ ≠ 0)
    (h₂ : c₂ ≠ 0) (h₃ : c₃ ≠ 0) :
    LinearIndependent F ![c₁ • (pt i).rep, c₂ • (pt j).rep, c₃ • (pt k).rep] := by
  have := (hO.linearIndependent_three hV hirr hij hik hjk).units_smul
    ![Units.mk0 c₁ h₁, Units.mk0 c₂ h₂, Units.mk0 c₃ h₃]
  convert this using 1
  funext a
  fin_cases a <;> simp [Units.smul_def]

theorem IsSixOrbit.not_smul_of_ne (hO : IsSixOrbit L pt) {i j : Fin 6} (hij : i ≠ j) (c : F) :
    (pt j).rep ≠ c • (pt i).rep := by
  intro h
  apply hij
  apply hO.inj
  symm
  rw [← Projectivization.mk_rep (pt j), ← Projectivization.mk_rep (pt i)]
  exact (Projectivization.mk_eq_mk_iff' F _ _ _ (pt i).rep_nonzero).2 ⟨c, h.symm⟩

end CFSG.Quasithin.D35Core
