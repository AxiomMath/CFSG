module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34

public section

namespace CFSG.Quasithin.H13.KGL34A

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Unitriangular

variable {K : Type*} [Field K]

theorem unitri_diag {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K) (i : Fin 3) :
    (u : Matrix (Fin 3) (Fin 3) K) i i = 1 :=
  (mem_unitriangular.1 hu).2 i

theorem unitri_lower {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    {i j : Fin 3} (h : j < i) : (u : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
  (mem_unitriangular.1 hu).1 i j h

theorem mul_apply_zero_two {u v : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (hv : v ∈ unitriangular 3 K) :
    ((u * v : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 =
      (v : Matrix (Fin 3) (Fin 3) K) 0 2 +
        (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (v : Matrix (Fin 3) (Fin 3) K) 1 2 +
          (u : Matrix (Fin 3) (Fin 3) K) 0 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, unitri_diag hu 0,
    unitri_diag hv 2]
  ring

theorem comm_entries {u v : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (hv : v ∈ unitriangular 3 K) (h : u * v = v * u) :
    (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (v : Matrix (Fin 3) (Fin 3) K) 1 2 =
      (v : Matrix (Fin 3) (Fin 3) K) 0 1 * (u : Matrix (Fin 3) (Fin 3) K) 1 2 := by
  have e : ((u * v : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 =
      ((v * u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 := by rw [h]
  rw [mul_apply_zero_two hu hv, mul_apply_zero_two hv hu] at e
  linear_combination e

theorem sq_entries [CharP K 2] {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (h : u * u = 1) :
    (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
  have e : ((u * u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 =
      ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 := by rw [h]
  rw [mul_apply_zero_two hu hu, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_ne (by decide)] at e
  have h2 : (u : Matrix (Fin 3) (Fin 3) K) 0 2 + (u : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination e - h2

theorem row_or_col [CharP K 2] {F : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hFU : F ≤ unitriangular 3 K) (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hs : ∀ x ∈ F, x * x = 1) :
    (∀ u ∈ F, (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) ∨
      ∀ u ∈ F, (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
  by_cases h : ∃ x ∈ F, (x : Matrix (Fin 3) (Fin 3) K) 0 1 ≠ 0
  · obtain ⟨x, hx, hx0⟩ := h
    left
    intro u hu
    have hx12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 :=
      (mul_eq_zero.1 (sq_entries (hFU hx) (hs x hx))).resolve_left hx0
    have h2 := comm_entries (hFU hx) (hFU hu) (hc x hx u hu)
    rw [hx12, mul_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_left hx0
  · right
    intro u hu
    by_contra hu0
    exact h ⟨u, hu, hu0⟩

theorem eq_of_row {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (h12 : (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :
    (u : Matrix (Fin 3) (Fin 3) K) = !![1, (u : Matrix (Fin 3) (Fin 3) K) 0 1,
      (u : Matrix (Fin 3) (Fin 3) K) 0 2; 0, 1, 0; 0, 0, 1] := by
  conv_lhs => rw [Matrix.eta_fin_three (u : Matrix (Fin 3) (Fin 3) K)]
  rw [unitri_diag hu 0, unitri_diag hu 1, unitri_diag hu 2, unitri_lower hu (show (0 : Fin 3) < 1 by
    decide), unitri_lower hu (show (0 : Fin 3) < 2 by decide),
    unitri_lower hu (show (1 : Fin 3) < 2 by decide), h12]

theorem eq_of_col {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (h01 : (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) :
    (u : Matrix (Fin 3) (Fin 3) K) = !![1, 0, (u : Matrix (Fin 3) (Fin 3) K) 0 2;
      0, 1, (u : Matrix (Fin 3) (Fin 3) K) 1 2; 0, 0, 1] := by
  conv_lhs => rw [Matrix.eta_fin_three (u : Matrix (Fin 3) (Fin 3) K)]
  rw [unitri_diag hu 0, unitri_diag hu 1, unitri_diag hu 2, unitri_lower hu (show (0 : Fin 3) < 1 by
    decide), unitri_lower hu (show (0 : Fin 3) < 2 by decide),
    unitri_lower hu (show (1 : Fin 3) < 2 by decide), h01]

theorem injective_row {F : Subgroup (SpecialLinearGroup (Fin 3) K)} (hFU : F ≤ unitriangular 3 K)
    (hR : ∀ u ∈ F, (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :
    Function.Injective fun u : ↥F =>
      (((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1,
        ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) := by
  intro u v huv
  simp only [Prod.mk.injEq] at huv
  apply Subtype.ext
  apply Subtype.ext
  rw [eq_of_row (hFU u.2) (hR _ u.2), eq_of_row (hFU v.2) (hR _ v.2), huv.1, huv.2]

theorem injective_col {F : Subgroup (SpecialLinearGroup (Fin 3) K)} (hFU : F ≤ unitriangular 3 K)
    (hC : ∀ u ∈ F, (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) :
    Function.Injective fun u : ↥F =>
      (((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2,
        ((u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) := by
  intro u v huv
  simp only [Prod.mk.injEq] at huv
  apply Subtype.ext
  apply Subtype.ext
  rw [eq_of_col (hFU u.2) (hC _ u.2), eq_of_col (hFU v.2) (hC _ v.2), huv.1, huv.2]

theorem exists_conj_unitriangular [Finite K] [CharP K 2]
    {F : Subgroup (SpecialLinearGroup (Fin 3) K)} (hs : ∀ x ∈ F, x * x = 1) :
    ∃ g : SpecialLinearGroup (Fin 3) K, ∀ y ∈ F, g⁻¹ * y * g ∈ unitriangular 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : IsPGroup 2 F := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, sq]
    exact hs x x.2)⟩
  obtain ⟨S, hFS⟩ := hF.exists_le_sylow
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) K) P₀ S
  refine ⟨g, fun y hy => ?_⟩
  have hyS : y ∈ (S : Subgroup (SpecialLinearGroup (Fin 3) K)) := hFS hy
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hyS
  obtain ⟨u, hu, hyu⟩ := hyS
  have hy' : y = g * u * g⁻¹ := hyu.symm
  rw [hy', show g⁻¹ * (g * u * g⁻¹) * g = u by group, ← hP₀]
  exact hu

theorem card_le_of_elemAb [Finite K] [CharP K 2] {F : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hs : ∀ x ∈ F, x * x = 1) :
    Nat.card F ≤ Nat.card K ^ 2 := by
  obtain ⟨g, hg⟩ := exists_conj_unitriangular hs
  set F' := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hmem : ∀ u ∈ F', ∃ y ∈ F, u = g⁻¹ * y * g := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩
  have hF'U : F' ≤ unitriangular 3 K := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := hmem u hu
    exact hg y hy
  have hc' : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := hmem x hx
    obtain ⟨y', hy', rfl⟩ := hmem y hy
    have := hc x' hx' y' hy'
    calc g⁻¹ * x' * g * (g⁻¹ * y' * g) = g⁻¹ * (x' * y') * g := by group
      _ = g⁻¹ * (y' * x') * g := by rw [this]
      _ = g⁻¹ * y' * g * (g⁻¹ * x' * g) := by group
  have hs' : ∀ x ∈ F', x * x = 1 := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hmem x hx
    have := hs x' hx'
    calc g⁻¹ * x' * g * (g⁻¹ * x' * g) = g⁻¹ * (x' * x') * g := by group
      _ = 1 := by rw [this]; group
  have hcard : Nat.card F' = Nat.card F := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  rw [← hcard, sq, ← Nat.card_prod]
  rcases row_or_col hF'U hc' hs' with h | h
  · exact Nat.card_le_card_of_injective _ (injective_row hF'U h)
  · exact Nat.card_le_card_of_injective _ (injective_col hF'U h)

theorem det_eq_zero_of_row {N : Matrix (Fin 3) (Fin 3) K}
    (h₁ : (single 0 1 1 : Matrix (Fin 3) (Fin 3) K)ᵀ * N = N * single 0 1 1)
    (h₂ : (single 0 2 1 : Matrix (Fin 3) (Fin 3) K)ᵀ * N = N * single 0 2 1) : N.det = 0 := by
  have e₁ := congrFun (congrFun h₁ 1) 0
  have e₂ := congrFun (congrFun h₁ 1) 2
  have e₃ := congrFun (congrFun h₂ 2) 1
  simp [Matrix.mul_apply, Matrix.single_apply] at e₁ e₂ e₃
  rw [Matrix.det_fin_three, e₁, e₂, e₃]
  ring

theorem det_eq_zero_of_col {N : Matrix (Fin 3) (Fin 3) K}
    (h₁ : (single 1 2 1 : Matrix (Fin 3) (Fin 3) K)ᵀ * N = N * single 1 2 1)
    (h₂ : (single 0 2 1 : Matrix (Fin 3) (Fin 3) K)ᵀ * N = N * single 0 2 1) : N.det = 0 := by
  have e₁ := congrFun (congrFun h₁ 2) 0
  have e₂ := congrFun (congrFun h₁ 2) 1
  have e₃ := congrFun (congrFun h₂ 2) 0
  have e₄ := congrFun (congrFun h₂ 2) 1
  simp [Matrix.mul_apply, Matrix.single_apply] at e₁ e₂ e₃ e₄
  rw [Matrix.det_fin_three, e₁, e₂, e₃, e₄]
  ring

theorem single_comm_of_comm {N E : Matrix (Fin 3) (Fin 3) K}
    (h : (1 + E)ᵀ * N = N * (1 + E)) : Eᵀ * N = N * E := by
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one] at h
  exact add_left_cancel h

theorem card_ne_of_twisted [Finite K] [CharP K 2] (τ : K ≃+* K)
    {F : Subgroup (SpecialLinearGroup (Fin 3) K)} (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x)
    (hs : ∀ x ∈ F, x * x = 1)
    (hτ : ∀ y ∈ F, ((y : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ = y) :
    Nat.card F ≠ Nat.card K ^ 2 := by
  intro hcard
  obtain ⟨g, hg⟩ := exists_conj_unitriangular hs
  set F' := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
  have hmem : ∀ u ∈ F', ∃ y ∈ F, u = g⁻¹ * y * g := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩
  have hmem' : ∀ y ∈ F, g⁻¹ * y * g ∈ F' := fun y hy => ⟨y, hy, by simp⟩
  have hF'U : F' ≤ unitriangular 3 K := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := hmem u hu
    exact hg y hy
  have hc' : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := hmem x hx
    obtain ⟨y', hy', rfl⟩ := hmem y hy
    have := hc x' hx' y' hy'
    calc g⁻¹ * x' * g * (g⁻¹ * y' * g) = g⁻¹ * (x' * y') * g := by group
      _ = g⁻¹ * (y' * x') * g := by rw [this]
      _ = g⁻¹ * y' * g * (g⁻¹ * x' * g) := by group
  have hs' : ∀ x ∈ F', x * x = 1 := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hmem x hx
    have := hs x' hx'
    calc g⁻¹ * x' * g * (g⁻¹ * x' * g) = g⁻¹ * (x' * x') * g := by group
      _ = 1 := by rw [this]; group
  have hcard' : Nat.card ↥F' = Nat.card (K × K) := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard, Nat.card_prod,
      sq]
  set N : Matrix (Fin 3) (Fin 3) K :=
    ((g : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ * (g : Matrix (Fin 3) (Fin 3) K) with hN
  have hNdet : N.det ≠ 0 := by
    have h1 : ((g : Matrix (Fin 3) (Fin 3) K).map τ).det = τ (g : Matrix (Fin 3) (Fin 3) K).det :=
      (RingHom.map_det τ.toRingHom (g : Matrix (Fin 3) (Fin 3) K)).symm
    rw [hN, Matrix.det_mul, Matrix.det_transpose, h1, Matrix.SpecialLinearGroup.det_coe, map_one,
      one_mul]
    exact one_ne_zero
  have key : ∀ u ∈ F', (u : Matrix (Fin 3) (Fin 3) K).map τ = u →
      (u : Matrix (Fin 3) (Fin 3) K)ᵀ * N = N * u := by
    intro u hu hτu
    obtain ⟨y, hy, rfl⟩ := hmem u hu
    have hy' : (y : Matrix (Fin 3) (Fin 3) K) = (g : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ * y * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    set u := g⁻¹ * y * g
    have h1 := hτ y hy
    rw [hy', Matrix.map_mul, Matrix.map_mul, hτu, Matrix.transpose_mul, Matrix.transpose_mul] at h1
    have hgi : (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ *
        ((g : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero τ)
        (map_one τ), Matrix.transpose_one]
    have hgi' : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc (u : Matrix (Fin 3) (Fin 3) K)ᵀ * N
        = (((g : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ *
            (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ) *
              (u : Matrix (Fin 3) (Fin 3) K)ᵀ * ((g : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ *
                (g : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul,
            inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
            Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one, Matrix.one_mul,
            hN, Matrix.mul_assoc]
      _ = ((g : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ *
            ((((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ *
              ((u : Matrix (Fin 3) (Fin 3) K)ᵀ * ((g : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ)) *
                (g : Matrix (Fin 3) (Fin 3) K) := by
          simp only [Matrix.mul_assoc]
      _ = ((g : Matrix (Fin 3) (Fin 3) K).map τ)ᵀ * ((g : Matrix (Fin 3) (Fin 3) K) *
            (u : Matrix (Fin 3) (Fin 3) K) *
              ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
                (g : Matrix (Fin 3) (Fin 3) K) := by rw [h1]
      _ = N * u := by
          rw [hN]
          simp only [Matrix.mul_assoc]
          rw [hgi', Matrix.mul_one]
  have hτ01 : ∀ x : K, x = 0 ∨ x = 1 → τ x = x := by
    rintro x (rfl | rfl)
    · exact map_zero τ
    · exact map_one τ
  rcases row_or_col hF'U hc' hs' with hR | hC
  · have hbij := (injective_row hF'U hR).bijective_of_nat_card_le hcard'.ge
    obtain ⟨u₁, hu₁⟩ := hbij.2 (1, 0)
    obtain ⟨u₂, hu₂⟩ := hbij.2 (0, 1)
    simp only [Prod.mk.injEq] at hu₁ hu₂
    have hm₁ := eq_of_row (hF'U u₁.2) (hR _ u₁.2)
    have hm₂ := eq_of_row (hF'U u₂.2) (hR _ u₂.2)
    rw [hu₁.1, hu₁.2] at hm₁
    rw [hu₂.1, hu₂.2] at hm₂
    have e₁ : ((u₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 + single 0 1 1 := by
      rw [hm₁]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e₂ : ((u₂ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 + single 0 2 1 := by
      rw [hm₂]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hτ₁ : ((u₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ = u₁ := by
      rw [e₁]
      ext i j
      exact hτ01 _ (by fin_cases i <;> fin_cases j <;> simp)
    have hτ₂ : ((u₂ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ = u₂ := by
      rw [e₂]
      ext i j
      exact hτ01 _ (by fin_cases i <;> fin_cases j <;> simp)
    have k₁ := key _ u₁.2 hτ₁
    have k₂ := key _ u₂.2 hτ₂
    rw [e₁] at k₁
    rw [e₂] at k₂
    exact hNdet (det_eq_zero_of_row (single_comm_of_comm k₁) (single_comm_of_comm k₂))
  · have hbij := (injective_col hF'U hC).bijective_of_nat_card_le hcard'.ge
    obtain ⟨u₁, hu₁⟩ := hbij.2 (1, 0)
    obtain ⟨u₂, hu₂⟩ := hbij.2 (0, 1)
    simp only [Prod.mk.injEq] at hu₁ hu₂
    have hm₁ := eq_of_col (hF'U u₁.2) (hC _ u₁.2)
    have hm₂ := eq_of_col (hF'U u₂.2) (hC _ u₂.2)
    rw [hu₁.1, hu₁.2] at hm₁
    rw [hu₂.1, hu₂.2] at hm₂
    have e₁ : ((u₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 + single 1 2 1 := by
      rw [hm₁]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e₂ : ((u₂ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 + single 0 2 1 := by
      rw [hm₂]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hτ₁ : ((u₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ = u₁ := by
      rw [e₁]
      ext i j
      exact hτ01 _ (by fin_cases i <;> fin_cases j <;> simp)
    have hτ₂ : ((u₂ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ = u₂ := by
      rw [e₂]
      ext i j
      exact hτ01 _ (by fin_cases i <;> fin_cases j <;> simp)
    have k₁ := key _ u₁.2 hτ₁
    have k₂ := key _ u₂.2 hτ₂
    rw [e₁] at k₁
    rw [e₂] at k₂
    exact hNdet (det_eq_zero_of_col (single_comm_of_comm k₁) (single_comm_of_comm k₂))

end Unitriangular

section Lift

variable {k : Type} [Field k] [Finite k]

theorem scalar_pow_three (hk : Nat.card k = 4) {μ : SpecialLinearGroup (Fin 3) k}
    (hμ : μ ∈ scalars 3 k) : μ ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥(scalars 3 k)) (x := ⟨μ, hμ⟩)
  rw [card_scalars_three hk] at h
  simpa using congrArg Subtype.val h

omit [Finite k] in
theorem scalar_comm {μ : SpecialLinearGroup (Fin 3) k} (hμ : μ ∈ scalars 3 k)
    (z : SpecialLinearGroup (Fin 3) k) : μ * z = z * μ := by
  rw [scalars_eq_center] at hμ
  exact (Subgroup.mem_center_iff.1 hμ z).symm

theorem scalar_eq_one (hk : Nat.card k = 4) {μ : SpecialLinearGroup (Fin 3) k}
    (hμ : μ ∈ scalars 3 k) (h2 : μ * μ = 1) : μ = 1 := by
  have h3 := scalar_pow_three hk hμ
  calc μ = μ ^ 3 * (μ * μ)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem eq_of_proj_eq (hk : Nat.card k = 4) {y z : SpecialLinearGroup (Fin 3) k}
    (hy : y * y = 1) (hz : z * z = 1) (h : proj 3 k y = proj 3 k z) : y = z := by
  have hμ : y⁻¹ * z ∈ scalars 3 k := proj_eq_proj_iff.1 h
  have hc := scalar_comm hμ y⁻¹
  have h2 : (y⁻¹ * z) * (y⁻¹ * z) = 1 := by
    calc (y⁻¹ * z) * (y⁻¹ * z) = ((y⁻¹ * z) * y⁻¹) * z := by group
      _ = (y⁻¹ * (y⁻¹ * z)) * z := by rw [hc]
      _ = (y * y)⁻¹ * (z * z) := by group
      _ = 1 := by rw [hy, hz]; group
  have h1 := scalar_eq_one hk hμ h2
  calc y = y * (y⁻¹ * z) := by rw [h1, mul_one]
    _ = z := by group

theorem exists_lift (hk : Nat.card k = 4) {x : projectiveSL 3 k} (hx : x * x = 1) :
    ∃ y : SpecialLinearGroup (Fin 3) k, proj 3 k y = x ∧ y * y = 1 := by
  obtain ⟨y₀, rfl⟩ := proj_surjective 3 k x
  have hμ : y₀ * y₀ ∈ scalars 3 k := by
    rw [← proj_eq_one_iff, map_mul, hx]
  refine ⟨y₀ * (y₀ * y₀), ?_, ?_⟩
  · rw [map_mul, proj_eq_one_iff.2 hμ, mul_one]
  · have h3 := scalar_pow_three hk hμ
    calc y₀ * (y₀ * y₀) * (y₀ * (y₀ * y₀)) = (y₀ * y₀) ^ 3 := by
          rw [pow_three]
          simp only [mul_assoc]
      _ = 1 := h3

theorem commute_of_proj (hk : Nat.card k = 4) {y z : SpecialLinearGroup (Fin 3) k}
    (hz : z * z = 1)
    (h : proj 3 k y * proj 3 k z = proj 3 k z * proj 3 k y) : y * z = z * y := by
  set μ := y * z * y⁻¹ * z⁻¹ with hμdef
  have hμ : μ ∈ scalars 3 k := by
    rw [← proj_eq_one_iff, hμdef, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hc := scalar_comm hμ z
  have h1 : y * z * y⁻¹ = μ * z := by rw [hμdef]; group
  have e1 : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
    calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hz]; group
  rw [h1] at e1
  have h2 : μ * μ = 1 := by
    calc μ * μ = μ * μ * (z * z) := by rw [hz, mul_one]
      _ = μ * (μ * z) * z := by group
      _ = μ * (z * μ) * z := by rw [hc]
      _ = μ * z * (μ * z) := by group
      _ = 1 := e1
  have h3 : y * z * y⁻¹ * z⁻¹ = 1 := scalar_eq_one hk hμ h2
  calc y * z = (y * z * y⁻¹ * z⁻¹) * z * y := by group
    _ = z * y := by rw [h3, one_mul]

@[expose] def liftSub (hk : Nat.card k = 4) (E : Subgroup (projectiveSL 3 k))
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := {y | proj 3 k y ∈ E ∧ y * y = 1}
  one_mem' := ⟨by rw [map_one]; exact E.one_mem, mul_one 1⟩
  mul_mem' := by
    rintro y z ⟨hyE, hy⟩ ⟨hzE, hz⟩
    have hyz := commute_of_proj hk hz (hc _ hyE _ hzE)
    refine ⟨by rw [map_mul]; exact E.mul_mem hyE hzE, ?_⟩
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [hyz]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hy, hz, mul_one]
  inv_mem' := by
    rintro y ⟨hyE, hy⟩
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    show proj 3 k y⁻¹ ∈ E ∧ y⁻¹ * y⁻¹ = 1
    rw [hyi]
    exact ⟨hyE, hy⟩

theorem mem_liftSub {hk : Nat.card k = 4} {E : Subgroup (projectiveSL 3 k)}
    {hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x} {y : SpecialLinearGroup (Fin 3) k} :
    y ∈ liftSub hk E hc ↔ proj 3 k y ∈ E ∧ y * y = 1 :=
  Iff.rfl

theorem liftSub_comm {hk : Nat.card k = 4} {E : Subgroup (projectiveSL 3 k)}
    {hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x} :
    ∀ x ∈ liftSub hk E hc, ∀ y ∈ liftSub hk E hc, x * y = y * x :=
  fun _ hx _ hy => commute_of_proj hk hy.2 (hc _ hx.1 _ hy.1)

theorem card_liftSub (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) :
    Nat.card (liftSub hk E hc) = Nat.card E := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun y : liftSub hk E hc => (⟨proj 3 k y, y.2.1⟩ : E)) ⟨fun y z hyz => ?_, fun x => ?_⟩)
  · exact Subtype.ext (eq_of_proj_eq hk y.2.2 z.2.2 (congrArg Subtype.val hyz))
  · obtain ⟨y, hy, hy2⟩ := exists_lift hk (hs x x.2)
    exact ⟨⟨y, by rw [mem_liftSub, hy]; exact ⟨x.2, hy2⟩⟩, Subtype.ext hy⟩

theorem card_le_sixteen (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 16 := by
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  rw [← card_liftSub hk hc hs]
  have h := card_le_of_elemAb (F := liftSub hk E hc) liftSub_comm fun _ hx => hx.2
  rw [hk] at h
  exact h

end Lift

end CFSG.Quasithin.H13.KGL34A
