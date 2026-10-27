module

public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusPolar
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.G11 Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {K : Type} [Field K] [Algebra (ZMod 2) K]

@[expose] noncomputable def omegaTraceForm (b : K) (ψ : V ≃ₗ[ZMod 2] (QIdx → K)) :
    LinearMap.BilinForm (ZMod 2) V :=
  LinearMap.mk₂ (ZMod 2) (fun x y => Algebra.trace (ZMod 2) K (omegaBil b (ψ x) (ψ y)))
    (fun x x' y => by
      rw [map_add, omegaBil_add_left, map_add])
    (fun c x y => by
      have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hc c with rfl | rfl
      · simp [omegaBil_zero_left]
      · simp)
    (fun x y y' => by
      rw [map_add, omegaBil_add_right, map_add])
    (fun c x y => by
      have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hc c with rfl | rfl
      · simp [omegaBil_comm _ _ 0, omegaBil_zero_left]
      · simp)

theorem omegaTraceForm_apply (b : K) (ψ : V ≃ₗ[ZMod 2] (QIdx → K)) (x y : V) :
    omegaTraceForm b ψ x y = Algebra.trace (ZMod 2) K (omegaBil b (ψ x) (ψ y)) := rfl

theorem omegaTraceForm_separatingLeft [Finite K] (b : K) (hb : b ≠ 0) (ψ : V ≃ₗ[ZMod 2] (QIdx → K)) :
    (omegaTraceForm b ψ).SeparatingLeft := by
  intro x hx
  have hw : ∀ w : QIdx → K, omegaBil b (ψ x) w = 0 := by
    intro w
    refine (traceForm_nondegenerate (ZMod 2) K).1 _ fun k => ?_
    rw [Algebra.traceForm_apply]
    have := hx (ψ.symm (k • w))
    rw [omegaTraceForm_apply, LinearEquiv.apply_symm_apply, omegaBil_smul_right] at this
    rw [mul_comm]
    exact this
  exact ψ.injective (by simpa using eq_zero_of_omegaBil_eq_zero hb hw)

theorem omegaTraceForm_comm (b : K) (ψ : V ≃ₗ[ZMod 2] (QIdx → K)) (x y : V) :
    omegaTraceForm b ψ x y = omegaTraceForm b ψ y x := by
  rw [omegaTraceForm_apply, omegaTraceForm_apply, omegaBil_comm]

theorem selfDual_of_omegaNatural [Finite K] {L : Subgroup (GLV V)} {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ψ : V ≃ₗ[ZMod 2] (QIdx → K))
    (A : ↥L → Matrix QIdx QIdx K)
    (hψ : ∀ (l : ↥L) (v : V), ψ ((l : GLV V) v) = A l *ᵥ ψ v)
    (hQ : ∀ (l : ↥L) (v : QIdx → K),
      StatedQuadMinus 2 K b c (A l *ᵥ v) = StatedQuadMinus 2 K b c v) :
    SelfDual L ⊤ := by
  have hchar : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hb := ne_zero_of_nonsplit h2 hbc
  let f := (omegaTraceForm b ψ).compl₁₂ (Submodule.topEquiv (R := ZMod 2) (M := V)).toLinearMap
    (Submodule.topEquiv (R := ZMod 2) (M := V)).toLinearMap
  have hf : ∀ i j : (⊤ : Submodule (ZMod 2) V), f i j = omegaTraceForm b ψ i j := fun i j => rfl
  refine ⟨f, ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩
  · have := omegaTraceForm_separatingLeft b hb ψ (x : V) fun y => hx ⟨y, trivial⟩
    exact Subtype.ext this
  · have := omegaTraceForm_separatingLeft b hb ψ (y : V) fun x => by
      rw [omegaTraceForm_comm]
      exact hy ⟨x, trivial⟩
    exact Subtype.ext this
  · intro k hk i j i' j' hi hj
    rw [hf, hf]
    have hi' : (i' : V) = (k : GLV V) i := hi.symm
    have hj' : (j' : V) = (k : GLV V) j := hj.symm
    rw [hi', hj', omegaTraceForm_apply, omegaTraceForm_apply]
    have := hψ ⟨k, hk⟩
    simp only at this
    rw [this, this, omegaBil_mulVec h2 b c _ (hQ ⟨k, hk⟩)]

end CFSG.Quasithin.G11.Harris.L2
