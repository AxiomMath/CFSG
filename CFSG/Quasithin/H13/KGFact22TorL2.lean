module

public import CFSG.Quasithin.H13.KGFact22TorL3

public section

namespace CFSG.Quasithin.H13.KG22

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique

variable {K : Type} [Field K]

local notation "SL₂" => SpecialLinearGroup (Fin 2) K

@[expose] def diag2 (x y : K) (h : x * y = 1) : SL₂ :=
  ⟨Matrix.diagonal ![x, y], by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simpa using h⟩

theorem coe_diag2 (x y : K) (h : x * y = 1) :
    ((diag2 x y h : SL₂) : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![x, y] :=
  rfl

theorem diag2_mul (x y : K) (h : x * y = 1) (x' y' : K) (h' : x' * y' = 1) :
    diag2 x y h * diag2 x' y' h' = diag2 (x * x') (y * y') (by
      calc x * x' * (y * y') = (x * y) * (x' * y') := by ring
        _ = 1 := by rw [h, h', one_mul]) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diag2, coe_diag2, coe_diag2, diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

theorem diag2_eq_one (h : (1 : K) * 1 = 1) : diag2 (1 : K) 1 h = 1 := by
  ext i j
  rw [coe_diag2, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem diag2_congr {x y x' y' : K} (h : x * y = 1) (hx : x = x') (hy : y = y') :
    diag2 x y h = diag2 x' y' (hx ▸ hy ▸ h) := by
  subst hx hy
  rfl

@[expose] noncomputable def tT : Kˣ →* SL₂ where
  toFun a := diag2 (a : K) ((a⁻¹ : Kˣ) : K) (by simp)
  map_one' := by
    rw [← diag2_eq_one (K := K) (by simp)]
    apply diag2_congr <;> simp
  map_mul' a b := by
    rw [diag2_mul]
    apply diag2_congr <;> simp [mul_comm]

theorem tT_apply (a : Kˣ) : tT a = diag2 (a : K) ((a⁻¹ : Kˣ) : K) (by simp) :=
  rfl

theorem tT_mem_upperTriangular (a : Kˣ) : tT a ∈ upperTriangular 2 K := fun i j hij => by
  rw [tT_apply, coe_diag2, diagonal_apply_ne _ (ne_of_gt hij)]

theorem tT_injective : Function.Injective (tT : Kˣ →* SL₂) := by
  intro a b h
  have := congrFun (congrFun (congrArg (fun g : SL₂ => (g : Matrix (Fin 2) (Fin 2) K)) h) 0) 0
  simp only [tT_apply, coe_diag2, diagonal_apply_eq, Matrix.cons_val_zero] at this
  exact Units.ext this

variable [CharP K 2]

theorem tT_proj_eq_one {y : SL₂} (hy : y ∈ tT.range) (h : proj 2 K y = 1) : y = 1 := by
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨c, hc2, hc⟩ := proj_eq_one_iff.1 h
  have h00 := congrFun (congrFun hc 0) 0
  simp only [tT_apply, coe_diag2, diagonal_apply_eq, scalar_apply, Matrix.cons_val_zero] at h00
  have hca : (c : K) * c = 1 := by
    have : ((c : K)) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc2, Units.val_one]
    rwa [sq] at this
  have hc1 : (c : K) = 1 := by
    have h2 : ((c : K) + 1) * ((c : K) + 1) = 0 := by
      have : ((c : K) + 1) * ((c : K) + 1) = (c : K) * c + 1 + 2 * (c : K) := by ring
      rw [this, hca, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
    have h3 : (c : K) + 1 = 0 := mul_self_eq_zero.1 h2
    rw [← CharTwo.neg_eq (1 : K)]
    exact eq_neg_of_add_eq_zero_left h3
  have ha1 : a = 1 := Units.ext (by rw [h00, hc1, Units.val_one])
  rw [ha1, map_one]

@[expose] def w2 : SL₂ :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem coe_w2 : ((w2 : SL₂) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

theorem w2_mul_self : (w2 : SL₂) * w2 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_w2, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w2_inv : (w2 : SL₂)⁻¹ = w2 :=
  inv_eq_of_mul_eq_one_right w2_mul_self

theorem w2_conj_diag2 (x y : K) (h : x * y = 1) :
    (w2 : SL₂) * diag2 x y h * w2⁻¹ = diag2 y x (by rw [← h]; ring) := by
  rw [w2_inv]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_w2, coe_diag2,
    coe_diag2]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp

theorem w2_conj_tT (a : Kˣ) : (w2 : SL₂) * tT a * w2⁻¹ = (tT a)⁻¹ := by
  rw [← map_inv, tT_apply, tT_apply, w2_conj_diag2]
  apply diag2_congr <;> simp

theorem w2_not_mem_upperTriangular : (w2 : SL₂) ∉ upperTriangular 2 K := by
  intro h
  have := h 1 0 (by decide)
  rw [coe_w2] at this
  simp at this

omit [CharP K 2] in
theorem upperTriangular_le_two :
    upperTriangular 2 K ≤ tT.range ⊔ ⊥ ⊔ unitriangular 2 K := by
  intro b hb
  have hbU : (b : Matrix (Fin 2) (Fin 2) K).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.1 hb
  have hdet : (b : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have h1 := Matrix.det_of_isUpperTriangular hbU
    rw [b.2, Fin.prod_univ_two] at h1
    exact h1.symm
  set x := (b : Matrix (Fin 2) (Fin 2) K) 0 0 with hx
  set y := (b : Matrix (Fin 2) (Fin 2) K) 1 1 with hy
  have hx0 : x ≠ 0 := fun h => by rw [h, zero_mul] at hdet; exact zero_ne_one hdet
  have hy0 : y ≠ 0 := fun h => by rw [h, mul_zero] at hdet; exact zero_ne_one hdet
  set a : Kˣ := Units.mk0 x hx0 with ha
  have ht : tT a = diag2 x y hdet := by
    rw [tT_apply]
    apply diag2_congr
    · simp [ha]
    · simp only [ha, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact (eq_inv_of_mul_eq_one_right hdet).symm
  set ti := diag2 x⁻¹ y⁻¹ (by rw [← mul_inv, hdet, inv_one]) with hti
  have htti : diag2 x y hdet * ti = 1 := by
    rw [hti, diag2_mul, ← diag2_eq_one (K := K) (by simp)]
    apply diag2_congr <;> simp [hx0, hy0]
  have hu : ti * b ∈ unitriangular 2 K := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, hti, coe_diag2, Matrix.diagonal_mul, hbU hij,
        mul_zero]
    · rw [Matrix.SpecialLinearGroup.coe_mul, hti, coe_diag2, Matrix.diagonal_mul]
      fin_cases i <;> simp [hx0, hy0, ← hx, ← hy]
  have hb : b = tT a * (ti * b) := by
    rw [ht, ← mul_assoc, htti, one_mul]
  rw [hb]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨a, rfl⟩))
    (Subgroup.mem_sup_right hu)

theorem torusOut_projectiveSL2 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    TorusOut (projUnitriangular 2 K) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBN : upperTriangular 2 K ≤ Subgroup.normalizer (unitriangular 2 K : Set SL₂) := by
    rw [normalizer_unitriangular]
  refine torusOut_of_hom (proj 2 K) (U := unitriangular 2 K) (B := upperTriangular 2 K)
    (Y₀ := tT.range) (Y₀' := ⊥) (w₀ := w2) ?_ bot_le ?_ upperTriangular_le_two
    (isCyclic_of_surjective tT.rangeRestrict tT.rangeRestrict_surjective) inferInstance
    (fun y hy h => tT_proj_eq_one hy h) ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact hBN (tT_mem_upperTriangular a)
  · show Subgroup.normalizer (projUnitriangular 2 K : Set (projectiveSL 2 K)) ≤ _
    rw [normalizer_projUnitriangular 2]
    rfl
  · rw [← Nat.card_congr (MonoidHom.ofInjective tT_injective).toEquiv, Nat.card_units, hK]
  · intro a _ b hb
    rw [Subgroup.mem_bot] at hb
    rw [hb, mul_one, one_mul]
  · intro h
    have h1 : w2 ∈ ((upperTriangular 2 K).map (proj 2 K)).comap (proj 2 K) := h
    rw [Subgroup.comap_map_eq, ker_proj, sup_eq_left.2 (scalars_le_upperTriangular 2 K)] at h1
    exact w2_not_mem_upperTriangular h1
  · rintro _ ⟨a, rfl⟩
    exact w2_conj_tT a
  · intro y hy
    rw [Subgroup.mem_bot] at hy
    rw [hy, mul_one, mul_inv_cancel]

theorem torusOut_of_isPSL2 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : IsPSL 2 2 n X) {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) : TorusOut S n := by
  obtain ⟨-, K', _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K' 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have e' : X ≃* projectiveSL 2 K' := e.trans (Id2519.projectiveSLEquivStatedProj 2 K').symm
  refine torusOut_of_equiv e' (fun S' hS' => ?_) hS
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K') 2 (n := 2) (by norm_num)
  exact torusOut_of_sylow P (hP ▸ torusOut_projectiveSL2 hK) hS'

end CFSG.Quasithin.H13.KG22
