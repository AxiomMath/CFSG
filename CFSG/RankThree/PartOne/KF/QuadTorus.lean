module

public import CFSG.RankThree.PartOne.KF.QuadExt

public section

namespace CFSG.RankThree.PartOne.KFQ

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type}

abbrev QV (K : Type) [Field K] [Finite K] [CharP K 2] (ι : Type) : Type := ι → Qext K

@[expose] noncomputable def torusEquiv (x : ι → (Qext K)ˣ) : QV K ι ≃ₗ[K] QV K ι :=
  LinearEquiv.piCongrRight fun i => DistribMulAction.toModuleAut K (Qext K) (x i)

theorem torusEquiv_apply (x : ι → (Qext K)ˣ) (v : QV K ι) (i : ι) :
    torusEquiv x v i = (x i : Qext K) * v i := rfl

theorem torusEquiv_one : torusEquiv (1 : ι → (Qext K)ˣ) = (1 : QV K ι ≃ₗ[K] QV K ι) := by
  ext v i
  simp [torusEquiv_apply]

theorem torusEquiv_mul (x y : ι → (Qext K)ˣ) :
    torusEquiv (x * y) = torusEquiv x * torusEquiv y := by
  ext v i
  simp [torusEquiv_apply, mul_assoc]

@[expose] noncomputable def torusHom : (ι → (Qext K)ˣ) →* (QV K ι ≃ₗ[K] QV K ι) where
  toFun := torusEquiv
  map_one' := torusEquiv_one
  map_mul' := torusEquiv_mul

theorem torusHom_apply (x : ι → (Qext K)ˣ) : torusHom x = torusEquiv x := rfl

theorem torusEquiv_toLinearMap (x : ι → (Qext K)ˣ) :
    (torusEquiv x).toLinearMap = mulAlg K (fun i => (x i : Qext K)) := by
  ext v i
  simp [torusEquiv_apply, mulAlg_apply]

theorem conjAlgEquiv_torusEquiv (g : QV K ι ≃ₗ[K] QV K ι) (x : ι → (Qext K)ˣ) :
    LinearEquiv.conjAlgEquiv K g (mulAlg K (fun i => (x i : Qext K))) =
      (g * torusEquiv x * g⁻¹).toLinearMap := by
  have hm : ∀ w, mulAlg K (fun i => (x i : Qext K)) w = torusEquiv x w := fun w =>
    funext fun j => by simp [mulAlg_apply, torusEquiv_apply]
  refine LinearMap.ext fun v => ?_
  simp [LinearEquiv.conjAlgEquiv_apply, hm]

variable [Fintype ι] [DecidableEq ι]

theorem normalizer_torus_units {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (g : QV K ι ≃ₗ[K] QV K ι)
    (hg : ∀ x : ι → (Qext K)ˣ, (∀ i, x i ^ p = 1) →
      ∃ y : ι → (Qext K)ˣ, g * torusEquiv x * g⁻¹ = torusEquiv y) :
    ∃ (π : Equiv.Perm ι) (ε : ι → Bool), ∀ x y : ι → (Qext K)ˣ, (∀ i, x i ^ p = 1) →
      g * torusEquiv x * g⁻¹ = torusEquiv y →
        ∀ i, y (π i) = if ε i then (x i)⁻¹ else x i := by
  classical
  obtain ⟨m, hmp, hm1, -⟩ := exists_root_not_mem hp hp2 hpq
  have hμ1 : (1 : Qext K) ∈ {z : Qext K | z ^ p = 1} := by simp
  have hspan : Submodule.span K {z : Qext K | z ^ p = 1} = ⊤ := span_roots_eq_top hp hp2 hpq
  have hne : ∃ z ∈ {z : Qext K | z ^ p = 1}, z ≠ 1 := ⟨m, hmp, hm1⟩
  have hmem : ∀ (x : ι → (Qext K)ˣ), (∀ i, x i ^ p = 1) →
      ∀ i, ((x i : (Qext K)ˣ) : Qext K) ∈ {z : Qext K | z ^ p = 1} := fun x hx i => by
    simp only [Set.mem_ofPred_eq]
    rw [← Units.val_pow_eq_pow_val, hx i, Units.val_one]
  have hg' : ∀ x : ι → Qext K, (∀ i, x i ∈ {z : Qext K | z ^ p = 1}) →
      ∃ y : ι → Qext K, LinearEquiv.conjAlgEquiv K g (mulAlg K x) = mulAlg K y := by
    intro x hx
    have hx0 : ∀ i, x i ≠ 0 := fun i h => by
      have := hx i
      simp only [Set.mem_ofPred_eq, h] at this
      rw [zero_pow hp.ne_zero] at this
      exact zero_ne_one this
    let xu : ι → (Qext K)ˣ := fun i => Units.mk0 (x i) (hx0 i)
    have hxu : ∀ i, xu i ^ p = 1 := fun i => Units.ext (by
      have := hx i
      simpa [xu] using this)
    obtain ⟨yu, hyu⟩ := hg xu hxu
    refine ⟨fun i => (yu i : Qext K), ?_⟩
    have hx' : x = fun i => ((xu i : (Qext K)ˣ) : Qext K) := funext fun i => (Units.val_mk0 _).symm
    rw [hx', conjAlgEquiv_torusEquiv, hyu, torusEquiv_toLinearMap]
  obtain ⟨π, τ, hπτ⟩ := normalizer_torus hμ1 hspan hne g hg'
  refine ⟨π, fun i => if τ i = 1 then false else true, fun x y hx hxy i => ?_⟩
  have h1 : (y (π i) : Qext K) = τ i (x i : Qext K) := by
    refine hπτ (fun i => (x i : Qext K)) (fun i => (y i : Qext K)) ?_ i
    rw [conjAlgEquiv_torusEquiv, hxy, torusEquiv_toLinearMap]
  by_cases hτ : τ i = 1
  · simp only [hτ, ite_true, Bool.false_eq_true, ite_false]
    apply Units.ext
    rw [h1, hτ]
    rfl
  · simp only [hτ, ite_false, ite_true]
    rcases gal_cases (τ i) with h | h
    · exact absurd h hτ
    · apply Units.ext
      rw [h1, h, Units.val_inv_eq_inv_val]
      refine frobQ_eq_inv ?_
      have hpq' : (x i : Qext K) ^ (Nat.card K + 1) = 1 := by
        obtain ⟨c, hc⟩ := hpq
        rw [hc, pow_mul, ← Units.val_pow_eq_pow_val, hx i, Units.val_one, one_pow]
      exact hpq'

end Torus

end CFSG.RankThree.PartOne.KFQ
