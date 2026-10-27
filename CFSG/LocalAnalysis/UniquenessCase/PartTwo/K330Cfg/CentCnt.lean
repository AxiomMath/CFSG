module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

theorem card_modEq_inf_ker {F : Type*} [Field F] [Finite F] {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (g : V ≃ₗ[F] V) {ℓ : ℕ} (hℓ : ℓ.Prime) (hg : g ^ ℓ = 1)
    (W : Submodule F V) (hW : ∀ w ∈ W, g w ∈ W) :
    Nat.card ↥W ≡ Nat.card ↥(W ⊓ LinearMap.ker ((g : V →ₗ[F] V) - 1)) [MOD ℓ] := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype ↥W := Fintype.ofFinite ↥W
  let e : ↥W → ↥W := fun w => ⟨g w, hW w w.2⟩
  have he : Function.Injective e := by
    intro w₁ w₂ h
    exact Subtype.ext (g.injective (Subtype.ext_iff.mp h))
  let σ : Equiv.Perm ↥W := Equiv.ofBijective e (Finite.injective_iff_bijective.1 he)
  have hσ : ∀ w : ↥W, (σ w : V) = g w := fun _ => rfl
  have hpow : ∀ k : ℕ, ∀ w : ↥W, ((σ ^ k) w : V) = (g ^ k) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
        intro w
        rw [pow_succ, Equiv.Perm.mul_apply, ih (σ w), hσ w, pow_succ, LinearEquiv.mul_apply]
  have hσpow : σ ^ ℓ = 1 := by
    ext w
    have h := hpow ℓ w
    rw [hg] at h
    simpa using h
  have hmem_ker : ∀ v : V, v ∈ LinearMap.ker ((g : V →ₗ[F] V) - 1) ↔ g v = v := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rfl
  have hmem_supp : ∀ w : ↥W, w ∈ σ.supportᶜ ↔ σ w = w := by
    intro w
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
  have hfixed : Nat.card ↥(σ.supportᶜ)
      = Nat.card ↥(W ⊓ LinearMap.ker ((g : V →ₗ[F] V) - 1)) := by
    apply Nat.card_congr
    refine
      { toFun := fun w => ⟨w.1.1, w.1.2, (hmem_ker w.1.1).mpr ?_⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, ?_⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
    · have hw := (hmem_supp w.1).mp w.2
      have h := congrArg (fun x : ↥W => (x : V)) hw
      simpa [hσ] using h
    · exact (hmem_supp ⟨v.1, v.2.1⟩).mpr (by
        apply Subtype.ext
        show g v.1 = v.1
        exact (hmem_ker v.1).mp v.2.2)
  have hsupp_nat : σ.supportᶜ.card = Nat.card ↥(σ.supportᶜ) := (Nat.card_eq_finsetCard _).symm
  have hkey := Equiv.Perm.card_compl_support_modEq (σ := σ) (p := ℓ) (n := 1)
    (by rw [pow_one]; exact hσpow)
  rw [Fintype.card_eq_nat_card] at hkey
  rw [hsupp_nat, hfixed] at hkey
  exact hkey.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
