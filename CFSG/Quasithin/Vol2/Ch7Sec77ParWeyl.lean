module

public import CFSG.Quasithin.EmptyFaithful.S153QPA1

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace SL3W

variable {F : Type} [Field F]

@[expose] noncomputable def torus01 : Fˣ →* SpecialLinearGroup (Fin 3) F where
  toFun a := ⟨Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F), 1], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp⟩
  map_one' := by
    apply Subtype.ext
    show Matrix.diagonal _ = (1 : Matrix (Fin 3) (Fin 3) F)
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show Matrix.diagonal ![((a * b : Fˣ) : F), (((a * b)⁻¹ : Fˣ) : F), 1] = Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F), 1] * Matrix.diagonal ![(b : F), ((b⁻¹ : Fˣ) : F), 1]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

@[expose] noncomputable def torus12 : Fˣ →* SpecialLinearGroup (Fin 3) F where
  toFun a := ⟨Matrix.diagonal ![1, (a : F), ((a⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp⟩
  map_one' := by
    apply Subtype.ext
    show Matrix.diagonal _ = (1 : Matrix (Fin 3) (Fin 3) F)
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Subtype.ext
    show Matrix.diagonal ![1, ((a * b : Fˣ) : F), (((a * b)⁻¹ : Fˣ) : F)] = Matrix.diagonal ![1, (a : F), ((a⁻¹ : Fˣ) : F)] * Matrix.diagonal ![1, (b : F), ((b⁻¹ : Fˣ) : F)]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

theorem torus01_injective : Function.Injective (torus01 (F := F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) ha
  simp [torus01] at h1
  exact (Subgroup.mem_bot).2 (Units.ext h1)

theorem torus12_injective : Function.Injective (torus12 (F := F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 1) ha
  simp [torus12] at h1
  exact (Subgroup.mem_bot).2 (Units.ext h1)

theorem torus01_mem (a : Fˣ) : torus01 a ∈ upperTriangular 3 F := by
  intro i j hij
  change Matrix.diagonal _ i j = 0
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

theorem torus12_mem (a : Fˣ) : torus12 a ∈ upperTriangular 3 F := by
  intro i j hij
  change Matrix.diagonal _ i j = 0
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

variable (h2 : (2 : F) = 0)
include h2

theorem neg_one_eq_one : (-1 : F) = 1 := by linear_combination -h2

@[expose] noncomputable def swap01 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp [neg_one_eq_one h2]⟩

@[expose] noncomputable def swap12 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by
    rw [Matrix.det_fin_three]
    simp [neg_one_eq_one h2]⟩

theorem swap01_mul_self : swap01 h2 * swap01 h2 = 1 := by
  apply Subtype.ext
  show !![(0 : F), 1, 0; 1, 0, 0; 0, 0, 1] * !![(0 : F), 1, 0; 1, 0, 0; 0, 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_mul_self : swap12 h2 * swap12 h2 = 1 := by
  apply Subtype.ext
  show !![(1 : F), 0, 0; 0, 0, 1; 0, 1, 0] * !![(1 : F), 0, 0; 0, 0, 1; 0, 1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swap01_conj (a : Fˣ) : swap01 h2 * torus01 a * (swap01 h2)⁻¹ = (torus01 a)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right (swap01_mul_self h2), ← map_inv]
  apply Subtype.ext
  show !![(0 : F), 1, 0; 1, 0, 0; 0, 0, 1] * Matrix.diagonal ![(a : F), ((a⁻¹ : Fˣ) : F), 1] *
    !![(0 : F), 1, 0; 1, 0, 0; 0, 0, 1] =
      Matrix.diagonal ![((a⁻¹ : Fˣ) : F), (((a⁻¹)⁻¹ : Fˣ) : F), 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.vecHead, Matrix.vecTail,
      Matrix.vecMul_diagonal]

theorem swap12_conj (a : Fˣ) : swap12 h2 * torus12 a * (swap12 h2)⁻¹ = (torus12 a)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right (swap12_mul_self h2), ← map_inv]
  apply Subtype.ext
  show !![(1 : F), 0, 0; 0, 0, 1; 0, 1, 0] * Matrix.diagonal ![1, (a : F), ((a⁻¹ : Fˣ) : F)] *
    !![(1 : F), 0, 0; 0, 0, 1; 0, 1, 0] =
      Matrix.diagonal ![1, ((a⁻¹ : Fˣ) : F), (((a⁻¹)⁻¹ : Fˣ) : F)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.vecHead, Matrix.vecTail,
      Matrix.vecMul_diagonal]

theorem swap01_not_mem : swap01 h2 ∉ stabilizer (flagSpace 3 F 1) := by
  intro h
  set v : Fin 3 → F := Pi.single 0 1 with hv
  have hvF : v ∈ flagSpace 3 F 1 := by
    rw [mem_flagSpace]
    intro j hj
    have hj0 : j ≠ 0 := fun h => by rw [h] at hj; exact absurd hj (by decide)
    simp [hv, hj0]
  have h1 : (swap01 h2 : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ flagSpace 3 F 1 := by
    rw [← (mem_stabilizer.mp h)]
    exact ⟨v, hvF, rfl⟩
  rw [mem_flagSpace] at h1
  have h3 := h1 1 (by decide)
  simp [swap01, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h3

theorem swap12_not_mem : swap12 h2 ∉ stabilizer (flagSpace 3 F 2) := by
  intro h
  set v : Fin 3 → F := Pi.single 1 1 with hv
  have hvF : v ∈ flagSpace 3 F 2 := by
    rw [mem_flagSpace]
    intro j hj
    have hj1 : j ≠ 1 := fun h => by rw [h] at hj; exact absurd hj (by decide)
    simp [hv, hj1]
  have h1 : (swap12 h2 : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ flagSpace 3 F 2 := by
    rw [← (mem_stabilizer.mp h)]
    exact ⟨v, hvF, rfl⟩
  rw [mem_flagSpace] at h1
  have h3 := h1 2 (by decide)
  simp [swap12, hv, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h3

end SL3W

open SL3W in
theorem sl3ParabolicWeylFact_holds :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X P : Subgroup Γ) (F : Type) [Field F] [Fintype F] (n : ℕ),
      Fintype.card F = 2 ^ n → 2 ≤ n →
        Nonempty (↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) → IsMaxParabolic2 X P →
          ∃ y ∈ P, ∃ w ∈ X, orderOf y = 2 ^ n - 1 ∧ w ∉ P ∧ w * y * w⁻¹ ∈ Subgroup.zpowers y := by
  intro Γ _ _ X P F _ _ n hFc hn ⟨e⟩ hP
  classical
  have h2F : (2 : F) = 0 := by
    obtain ⟨p, hpc, m, hprime, hm⟩ := FiniteField.card' F
    have hdvd : p ∣ 2 ^ n := by
      rw [← hFc, hm]
      exact dvd_pow_self p m.pos.ne'
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hdvd)
    subst hp2
    have := hpc
    exact_mod_cast CharP.cast_eq_zero F 2
  have : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2F
  set e' : ↥X ≃* SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm with he'
  obtain ⟨g, d, hd1, hd3, hPg⟩ := QP.exists_conj_stabilizer_of_mulEquiv (F := F) (by norm_num) hP e'
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hoa : orderOf a = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_eq_fintype_card, Fintype.card_units,
      hFc]
  obtain ⟨y₀, w₀, hy₀, hw₀, hconj, hord⟩ : ∃ y₀ w₀ : SpecialLinearGroup (Fin 3) F,
      y₀ ∈ stabilizer (flagSpace 3 F d) ∧ w₀ ∉ stabilizer (flagSpace 3 F d) ∧
      w₀ * y₀ * w₀⁻¹ = y₀⁻¹ ∧ orderOf y₀ = 2 ^ n - 1 := by
    rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
    · exact ⟨torus01 a, swap01 h2F, upperTriangular_le_stabilizer_flagSpace 1 (torus01_mem a),
        swap01_not_mem h2F, swap01_conj h2F a, by rw [orderOf_injective _ torus01_injective, hoa]⟩
    · exact ⟨torus12 a, swap12 h2F, upperTriangular_le_stabilizer_flagSpace 2 (torus12_mem a),
        swap12_not_mem h2F, swap12_conj h2F a, by rw [orderOf_injective _ torus12_injective, hoa]⟩
  have hy' : (MulAut.conj g) y₀ ∈ (P.subgroupOf X).map e'.toMonoidHom := by
    rw [hPg]
    exact ⟨y₀, hy₀, rfl⟩
  obtain ⟨p, hp, hpy⟩ := hy'
  set w : ↥X := e'.symm ((MulAut.conj g) w₀) with hw
  refine ⟨(p : Γ), Subgroup.mem_subgroupOf.mp hp, (w : Γ), w.2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e' p]
    change orderOf (e'.toMonoidHom p) = _
    rw [hpy, MulEquiv.orderOf_eq, hord]
  · intro hwP
    apply hw₀
    have h1 : e'.toMonoidHom w ∈ (P.subgroupOf X).map e'.toMonoidHom :=
      ⟨w, Subgroup.mem_subgroupOf.mpr hwP, rfl⟩
    rw [hPg] at h1
    obtain ⟨w₁, hw₁, hw₁e⟩ := h1
    have h2 : (MulAut.conj g) w₁ = (MulAut.conj g) w₀ := by
      rw [show (MulAut.conj g : SpecialLinearGroup (Fin 3) F →* _) w₁ = (MulAut.conj g) w₁ from
        rfl] at hw₁e
      rw [hw₁e, hw]
      exact e'.apply_symm_apply _
    rw [← (MulAut.conj g).injective h2]
    exact hw₁
  · have hkey : w * p * w⁻¹ = p⁻¹ := by
      apply e'.injective
      rw [map_mul, map_mul, map_inv, map_inv, hw, e'.apply_symm_apply]
      change (MulAut.conj g) w₀ * e'.toMonoidHom p * ((MulAut.conj g) w₀)⁻¹ = (e'.toMonoidHom p)⁻¹
      rw [hpy, ← map_inv, ← map_mul, ← map_mul, hconj, map_inv]
    have h1 := congrArg (fun x : ↥X => (x : Γ)) hkey
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [h1]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

end CFSG.Quasithin.H13
