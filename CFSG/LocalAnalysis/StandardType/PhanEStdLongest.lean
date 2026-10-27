module

public import CFSG.Monster.B.Geometry.Coxeter
public import CFSG.LieType.RootSystem.Form

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.RootSystem CFSG.Monster.B.Geometry

section Generic

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A)

@[expose] def reflFn (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (v : Fin n → ℤ) : Fin n → ℤ :=
  v - (∑ j, A i j * v j) • Pi.single i 1

theorem reflection_eq_reflFn (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (v : Fin n → ℤ) :
    reflection A i v = reflFn A i v :=
  reflection_apply A i v

theorem weylAction_wordProd (ω : List (Fin n)) (v : Fin n → ℤ) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd ω) v =
      ω.foldr (fun i w => reflFn A i w) v := by
  induction ω with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, Module.End.mul_apply, ih, weylAction_simple,
      reflection_eq_reflFn]
    rfl

end Generic

section Table

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A)
  {w₀ : (coxeterMatrix hA).Group} {ρ : Fin n → Fin n}
  (htab : ∀ i, weylAction hA w₀ (Pi.single i 1) = -Pi.single (ρ i) 1)
  (hρ : ∀ i, ρ (ρ i) = i)

include htab hρ

theorem mul_self_of_table : w₀ * w₀ = 1 := by
  apply weylAction_injective hA
  rw [map_mul, map_one]
  refine (Pi.basisFun ℤ (Fin n)).ext fun i => ?_
  rw [Pi.basisFun_apply, Module.End.mul_apply, htab, map_neg, htab, hρ, neg_neg,
    Module.End.one_apply]

theorem isLongest_of_table :
    IsLongest (coxeterMatrix hA).toCoxeterSystem Set.univ w₀ := by
  haveI : Finite (coxeterMatrix hA).Group := finite_group hA
  haveI : Finite ((coxeterMatrix hA).toCoxeterSystem.parabolic (Set.univ : Set (Fin n))) := by
    rw [CoxeterSystem.parabolic_univ]
    infer_instance
  have hinv : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right (mul_self_of_table hA htab hρ)
  refine isLongest_of_forall_isLeftDescent (by
    rw [CoxeterSystem.parabolic_univ]; exact Subgroup.mem_top w₀) fun i _ => ?_
  have h : (coxeterMatrix hA).toCoxeterSystem.IsLeftDescent w₀⁻¹ i := by
    rw [(coxeterMatrix hA).toCoxeterSystem.isLeftDescent_inv_iff, isRightDescent_iff, htab]
    intro j
    simp [Pi.single_apply]
    split_ifs <;> simp
  rwa [hinv] at h

variable (hAρ : ∀ i j, A (ρ i) (ρ j) = A i j)

include hAρ

theorem hop_of_table (i : Fin n) :
    w₀ * (coxeterMatrix hA).toCoxeterSystem.simple i * w₀ =
      (coxeterMatrix hA).toCoxeterSystem.simple (ρ i) := by
  apply weylAction_injective hA
  rw [map_mul, map_mul, weylAction_simple, weylAction_simple]
  refine (Pi.basisFun ℤ (Fin n)).ext fun k => ?_
  rw [Pi.basisFun_apply, Module.End.mul_apply, Module.End.mul_apply, htab,
    reflection_apply, reflection_apply]
  have hk : A i (ρ k) = A (ρ i) k := by
    rw [← hAρ i (ρ k), hρ]
  simp only [map_sub, map_neg, map_smul, htab, hρ, Pi.neg_apply, Pi.single_apply,
    mul_neg, Finset.sum_neg_distrib, neg_neg, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, smul_neg, sub_neg_eq_add, hk]
  rw [neg_smul, sub_eq_add_neg]

end Table

section Explicit

@[expose] def wordE6 : List (Fin 6) := [
  0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
  5, 4, 3, 2, 0]

@[expose] def wordE7 : List (Fin 7) := [
  0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
  5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5,
  6]

@[expose] def wordE8 : List (Fin 8) := [
  0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
  5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5,
  6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6,
  5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]

@[expose] def rhoE6 : Fin 6 → Fin 6 := ![5, 1, 4, 3, 2, 0]

theorem tableE6 : ∀ i : Fin 6, wordE6.foldr (fun j w => reflFn (CartanMatrix.E 6) j w)
    (Pi.single i 1) = -Pi.single (rhoE6 i) 1 := by
  decide +kernel

theorem tableE7 : ∀ i : Fin 7, wordE7.foldr (fun j w => reflFn (CartanMatrix.E 7) j w)
    (Pi.single i 1) = -Pi.single i 1 := by
  decide +kernel

theorem tableE8 : ∀ i : Fin 8, wordE8.foldr (fun j w => reflFn (CartanMatrix.E 8) j w)
    (Pi.single i 1) = -Pi.single i 1 := by
  decide +kernel

theorem rhoE6_involutive : ∀ i : Fin 6, rhoE6 (rhoE6 i) = i := by decide

theorem cartanE6_rho : ∀ p : Fin 6 × Fin 6,
    CartanMatrix.E 6 (rhoE6 p.1) (rhoE6 p.2) = CartanMatrix.E 6 p.1 p.2 := by
  decide +kernel

theorem exists_longest_E6 {A : Matrix (Fin 6) (Fin 6) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAE : A = CartanMatrix.E 6) :
    ∃ w₀ : (coxeterMatrix hA).Group,
      IsLongest (coxeterMatrix hA).toCoxeterSystem Set.univ w₀ ∧
        (∀ i, weylAction hA w₀ (Pi.single i 1) = -Pi.single (rhoE6 i) 1) ∧
        ∀ i, w₀ * (coxeterMatrix hA).toCoxeterSystem.simple i * w₀ =
          (coxeterMatrix hA).toCoxeterSystem.simple (rhoE6 i) := by
  subst hAE
  have htab : ∀ i, weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd wordE6)
      (Pi.single i 1) = -Pi.single (rhoE6 i) 1 := fun i => by
    rw [weylAction_wordProd]
    exact tableE6 i
  exact ⟨_, isLongest_of_table hA htab rhoE6_involutive, htab,
    hop_of_table hA htab rhoE6_involutive fun i j => cartanE6_rho (i, j)⟩

theorem exists_longest_E7 {A : Matrix (Fin 7) (Fin 7) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAE : A = CartanMatrix.E 7) :
    ∃ w₀ : (coxeterMatrix hA).Group,
      IsLongest (coxeterMatrix hA).toCoxeterSystem Set.univ w₀ ∧
        (∀ i, weylAction hA w₀ (Pi.single i 1) = -Pi.single (id i) 1) ∧
        ∀ i, w₀ * (coxeterMatrix hA).toCoxeterSystem.simple i * w₀ =
          (coxeterMatrix hA).toCoxeterSystem.simple i := by
  subst hAE
  have htab : ∀ i, weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd wordE7)
      (Pi.single i 1) = -Pi.single (id i) 1 := fun i => by
    rw [weylAction_wordProd]
    exact tableE7 i
  exact ⟨_, isLongest_of_table hA htab fun _ => rfl, htab,
    hop_of_table hA htab (fun _ => rfl) fun _ _ => rfl⟩

theorem exists_longest_E8 {A : Matrix (Fin 8) (Fin 8) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAE : A = CartanMatrix.E 8) :
    ∃ w₀ : (coxeterMatrix hA).Group,
      IsLongest (coxeterMatrix hA).toCoxeterSystem Set.univ w₀ ∧
        (∀ i, weylAction hA w₀ (Pi.single i 1) = -Pi.single (id i) 1) ∧
        ∀ i, w₀ * (coxeterMatrix hA).toCoxeterSystem.simple i * w₀ =
          (coxeterMatrix hA).toCoxeterSystem.simple i := by
  subst hAE
  have htab : ∀ i, weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd wordE8)
      (Pi.single i 1) = -Pi.single (id i) 1 := fun i => by
    rw [weylAction_wordProd]
    exact tableE8 i
  exact ⟨_, isLongest_of_table hA htab fun _ => rfl, htab,
    hop_of_table hA htab (fun _ => rfl) fun _ _ => rfl⟩

end Explicit

end CFSG.ClassicalInvolution.Phan.PhanE
