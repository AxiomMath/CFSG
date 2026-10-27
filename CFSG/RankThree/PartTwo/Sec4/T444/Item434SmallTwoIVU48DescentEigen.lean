module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48.Descent

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_orderOf_eq_three {F : Type*} [Field F] (hF : Nat.card F = 4) :
    ∃ ζ : Fˣ, orderOf ζ = 3 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_prime_orderOf_dvd_card' 3 hdvd

theorem exists_orthonormal_eigenvectors {F : Type} [Field F] (h₀ : UnitaryFieldData 2 1 F)
    {W : Type*} [AddCommGroup W] [Module F W] [Module.Finite F W] (hdim : Module.finrank F W = 4)
    {B : W →ₛₗ[h₀.bar] W →ₗ[F] F} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {P : Module.End F W} (hP3 : ∀ x, P (P (P x)) = x) (hPiso : ∀ x y, B (P x) (P y) = B x y) :
    ∃ (u : Fin 4 → W) (μ : Fin 4 → F), (∀ i j, B (u i) (u j) = if i = j then 1 else 0) ∧
      (∀ j, P (u j) = μ j • u j) ∧ ∀ j, μ j ^ 3 = 1 := by
  have hP3' : P ^ 3 = 1 := LinearMap.ext fun x => by
    simpa [pow_succ, Module.End.mul_apply] using hP3 x
  obtain ⟨z, hz⟩ := exists_orderOf_eq_three (F := F) (by rw [h₀.card]; norm_num)
  have hζ : IsPrimitiveRoot (z : F) 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr (by simpa [hz] using IsPrimitiveRoot.orderOf z)
  obtain ⟨u, μ, hu, hon⟩ :=
    CFSG.RankThree.PartOne.KCUnitaryPlane.exists_orthonormal_common_eigenbasis h₀ hζ
      (by norm_num : 3 ∣ 2 ^ 1 + 1) hB hBl (ι := Unit) (fun _ => P)
      (fun _ _ => Commute.refl _) (fun _ => hP3') (fun _ => hPiso)
  let e : Fin 4 ≃ Fin (Module.finrank F W) := finCongr hdim.symm
  refine ⟨fun j => u (e j), fun j => μ () (e j), fun i j => ?_, fun j => hu () (e j), fun j => ?_⟩
  · rw [hon]
    by_cases h : i = j
    · subst h
      simp
    · have : e i ≠ e j := fun h' => h (e.injective h')
      simp [h, this]
  · have hev : Module.End.HasEigenvector P (μ () (e j)) (u (e j)) :=
      ⟨Module.End.mem_eigenspace_iff.mpr (hu () (e j)), u.ne_zero (e j)⟩
    have h1 := hev.pow_apply 3
    rw [hP3', Module.End.one_apply] at h1
    have h2 : (μ () (e j) ^ 3 - 1) • (u (e j)) = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right (u.ne_zero (e j)))

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48.Descent
