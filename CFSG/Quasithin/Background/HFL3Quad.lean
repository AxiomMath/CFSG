module

public import CFSG.Quasithin.Background.HFL3Tw
public import CFSG.Quasithin.Background.HFL3Alpha
public import CFSG.Quasithin.Background.SmithB45SL3Row
public import CFSG.Quasithin.Background.HFL3Q

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.H.SU3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem eq_smul_of_quad_entries (hK : Nat.card K = (2 ^ n) ^ 2) {a₀ b₀ a b : K}
    (h0 : a₀ ≠ 0 ∨ b₀ ≠ 0) (h1 : a₀ * bar n a + a * bar n a₀ = 0)
    (h2 : b₀ * bar n b + b * bar n b₀ = 0) (h3 : a₀ * bar n b + a * bar n b₀ = 0) :
    ∃ μ : K, bar n μ = μ ∧ a = μ * a₀ ∧ b = μ * b₀ := by
  have hneg : ∀ x y : K, x + y = 0 → x = y := fun x y h => by
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq, h]
  have main : a₀ ≠ 0 → ∃ μ : K, bar n μ = μ ∧ a = μ * a₀ ∧ b = μ * b₀ := by
    intro ha₀
    have hba : bar n a₀ ≠ 0 := (map_ne_zero (bar n)).mpr ha₀
    have hμ : bar n (a / a₀) = a / a₀ := by
      rw [map_div₀, div_eq_div_iff hba ha₀]
      linear_combination hneg _ _ h1
    refine ⟨a / a₀, hμ, by field_simp, ?_⟩
    have hb : bar n b = a / a₀ * bar n b₀ := by
      field_simp
      linear_combination hneg _ _ h3
    have := congrArg (bar n) hb
    rwa [map_mul, bar_bar hK, bar_bar hK, hμ] at this
  rcases h0 with ha₀ | hb₀
  · exact main ha₀
  · by_cases ha₀ : a₀ = 0
    · subst ha₀
      have hbb : bar n b₀ ≠ 0 := (map_ne_zero (bar n)).mpr hb₀
      have ha : a = 0 := by
        have : a * bar n b₀ = 0 := by linear_combination h3
        exact (mul_eq_zero.mp this).resolve_right hbb
      refine ⟨b / b₀, ?_, by rw [ha, mul_zero], by field_simp⟩
      rw [map_div₀, div_eq_div_iff hbb hb₀]
      linear_combination hneg _ _ h2
    · exact main ha₀

theorem rk1_quad (hK : Nat.card K = (2 ^ n) ^ 2) {x x₀ : SpecialLinearGroup (Fin 3) K}
    (hq : ∀ X : HMod n K, rho hK x (rho hK x₀ X * X⁻¹) = rho hK x₀ X * X⁻¹) (v : Fin 3 → K) :
    rk1 n ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ ((x₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) -
        rk1 n ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      rk1 n ((x₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) - rk1 n v := by
  have hρ : ∀ (y : SpecialLinearGroup (Fin 3) K) (w : Fin 3 → K),
      rho hK y (pt hK w) = pt hK ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := fun y w =>
    rhoT_pt hK (SpecialLinearGroup.toGL y) w
  have h := congrArg mat (hq (pt hK v))
  rw [map_mul, map_inv, hρ, hρ, hρ] at h
  simp only [mat_mul, mat_inv, mat_pt] at h
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h

theorem quad_entries_Q1 (hK : Nat.card K = (2 ^ n) ^ 2) {x x₀ : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ unitriangular 3 K) (hx₀ : x₀ ∈ unitriangular 3 K)
    (hx₀12 : (x₀ : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (hq : ∀ X : HMod n K, rho hK x (rho hK x₀ X * X⁻¹) = rho hK x₀ X * X⁻¹) {l : K}
    (hl : bar n l ≠ l) :
    (x₀ : Matrix (Fin 3) (Fin 3) K) 0 1 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 1) +
        (x : Matrix (Fin 3) (Fin 3) K) 0 1 * bar n ((x₀ : Matrix (Fin 3) (Fin 3) K) 0 1) = 0 ∧
      (x₀ : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 2) +
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n ((x₀ : Matrix (Fin 3) (Fin 3) K) 0 2) = 0 ∧
      (x₀ : Matrix (Fin 3) (Fin 3) K) 0 1 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 2) +
        (x : Matrix (Fin 3) (Fin 3) K) 0 1 * bar n ((x₀ : Matrix (Fin 3) (Fin 3) K) 0 2) = 0 := by
  obtain ⟨x00, -, -, -, -, -⟩ := uni3_entries hx
  obtain ⟨y00, y11, y22, -, -, y21⟩ := uni3_entries hx₀
  obtain ⟨a₀, ha₀⟩ : ∃ t, (x₀ : Matrix (Fin 3) (Fin 3) K) 0 1 = t := ⟨_, rfl⟩
  obtain ⟨b₀, hb₀⟩ : ∃ t, (x₀ : Matrix (Fin 3) (Fin 3) K) 0 2 = t := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ t, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = t := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ t, (x : Matrix (Fin 3) (Fin 3) K) 0 2 = t := ⟨_, rfl⟩
  rw [ha₀, hb₀, ha, hb]
  have key : ∀ c : K, (a₀ + c * b₀) * (bar n a + bar n c * bar n b) +
      (a + c * b) * (bar n a₀ + bar n c * bar n b₀) = 0 := by
    intro c
    have h := congrFun (congrFun (rk1_quad hK hq ![0, 1, c]) 0) 0
    simp only [rk1_apply, Matrix.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, x00, y00, y11, y21, y22, hx₀12, ha₀, hb₀, ha, hb, map_add, map_mul,
      map_zero, mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at h
    linear_combination h
  have h1 : a₀ * bar n a + a * bar n a₀ = 0 := by
    have := key 0
    simp only [map_zero, zero_mul, add_zero] at this
    exact this
  have h2 : b₀ * bar n b + b * bar n b₀ = 0 := by
    have h := congrFun (congrFun (rk1_quad hK hq ![0, 0, 1]) 0) 0
    simp only [rk1_apply, Matrix.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, x00, y00, y22, hx₀12, ha₀, hb₀, ha, hb, map_add, map_zero, mul_zero,
      mul_one, one_mul, add_zero, zero_add] at h
    linear_combination h
  have hc1 := key 1
  have hcl := key l
  rw [map_one] at hc1
  have hwb : bar n (a₀ * bar n b + a * bar n b₀) = bar n a₀ * b + bar n a * b₀ := by
    rw [map_add, map_mul, map_mul, bar_bar hK, bar_bar hK]
  have hw1 : (a₀ * bar n b + a * bar n b₀) + bar n (a₀ * bar n b + a * bar n b₀) = 0 := by
    rw [hwb]
    linear_combination hc1 - h1 - h2
  have hwl : bar n l * (a₀ * bar n b + a * bar n b₀) +
      l * bar n (a₀ * bar n b + a * bar n b₀) = 0 := by
    rw [hwb]
    linear_combination hcl - h1 - (l * bar n l) * h2
  set w := a₀ * bar n b + a * bar n b₀ with hw
  have e1 : bar n w = w := by
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
    linear_combination hw1
  rw [e1] at hwl
  have e2 : (bar n l + l) * w = 0 := by linear_combination hwl
  have hl' : bar n l + l ≠ 0 := by
    intro h0
    apply hl
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
    exact h0
  exact ⟨h1, h2, (mul_eq_zero.mp e2).resolve_left hl'⟩

theorem quad_entries_Q2 (hK : Nat.card K = (2 ^ n) ^ 2) {x x₀ : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ unitriangular 3 K) (hx₀ : x₀ ∈ unitriangular 3 K)
    (hx01 : (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (hx₀01 : (x₀ : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (hq : ∀ X : HMod n K, rho hK x (rho hK x₀ X * X⁻¹) = rho hK x₀ X * X⁻¹) :
    (x₀ : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 2) +
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n ((x₀ : Matrix (Fin 3) (Fin 3) K) 0 2) = 0 ∧
      (x₀ : Matrix (Fin 3) (Fin 3) K) 1 2 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 1 2) +
        (x : Matrix (Fin 3) (Fin 3) K) 1 2 * bar n ((x₀ : Matrix (Fin 3) (Fin 3) K) 1 2) = 0 ∧
      (x₀ : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 1 2) +
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n ((x₀ : Matrix (Fin 3) (Fin 3) K) 1 2) = 0 := by
  obtain ⟨x00, x11, -, x10, -, -⟩ := uni3_entries hx
  obtain ⟨y00, y11, y22, y10, -, -⟩ := uni3_entries hx₀
  have h := rk1_quad hK hq ![0, 0, 1]
  have e00 := congrFun (congrFun h 0) 0
  have e11 := congrFun (congrFun h 1) 1
  have e01 := congrFun (congrFun h 0) 1
  simp only [rk1_apply, Matrix.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, x00, x10, x11, hx01, y00, y10, y11, y22, hx₀01, map_add, map_zero,
    mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at e00 e11 e01
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e00
  · linear_combination e11
  · linear_combination e01

theorem quad_map_congrHom {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    {A : Subgroup (MulAut V)} (hq : ∀ a ∈ A, ∀ b ∈ A, ∀ v : V, b (a v * v⁻¹) = a v * v⁻¹) :
    ∀ a ∈ A.map (congrHom e), ∀ b ∈ A.map (congrHom e), ∀ w : W, b (a w * w⁻¹) = a w * w⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
  show e (b (e.symm (e (a (e.symm w)) * w⁻¹))) = e (a (e.symm w)) * w⁻¹
  calc e (b (e.symm (e (a (e.symm w)) * w⁻¹))) = e (b (a (e.symm w) * (e.symm w)⁻¹)) := by
        rw [map_mul, map_inv, e.symm_apply_apply]
    _ = e (a (e.symm w) * (e.symm w)⁻¹) := by rw [hq a ha b hb]
    _ = e (a (e.symm w)) * w⁻¹ := by rw [map_mul, map_inv, e.apply_symm_apply]

omit [Finite K] [CharP K 2] in
theorem eq_of_Q1 {x y : SpecialLinearGroup (Fin 3) K} (hx : x ∈ unitriangular 3 K)
    (hy : y ∈ unitriangular 3 K) (hx12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (hy12 : (y : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (h01 : (x : Matrix (Fin 3) (Fin 3) K) 0 1 = (y : Matrix (Fin 3) (Fin 3) K) 0 1)
    (h02 : (x : Matrix (Fin 3) (Fin 3) K) 0 2 = (y : Matrix (Fin 3) (Fin 3) K) 0 2) : x = y := by
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx
  obtain ⟨y00, y11, y22, y10, y20, y21⟩ := uni3_entries hy
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [x00, x11, x22, x10, x20, x21, y00, y11, y22, y10, y20,
    y21, hx12, hy12, h01, h02]

omit [Finite K] [CharP K 2] in
theorem eq_of_Q2 {x y : SpecialLinearGroup (Fin 3) K} (hx : x ∈ unitriangular 3 K)
    (hy : y ∈ unitriangular 3 K) (hx01 : (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (hy01 : (y : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (h02 : (x : Matrix (Fin 3) (Fin 3) K) 0 2 = (y : Matrix (Fin 3) (Fin 3) K) 0 2)
    (h12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = (y : Matrix (Fin 3) (Fin 3) K) 1 2) : x = y := by
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx
  obtain ⟨y00, y11, y22, y10, y20, y21⟩ := uni3_entries hy
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [x00, x11, x22, x10, x20, x21, y00, y11, y22, y10, y20,
    y21, hx01, hy01, h02, h12]

theorem card_le_of_quadratic_uni3 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hPU : P ≤ unitriangular 3 K)
    (hPQ : (∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) ∨
      ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (hq : ∀ x ∈ P, ∀ x₀ ∈ P, ∀ X : HMod n K, rho hK x (rho hK x₀ X * X⁻¹) = rho hK x₀ X * X⁻¹) :
    Nat.card P ≤ 2 ^ n := by
  classical
  by_cases hPb : P = ⊥
  · rw [hPb, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  obtain ⟨⟨x₀, hx₀⟩, hx₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hPb
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (Subtype.ext h)
  obtain ⟨l, hl'⟩ := exists_bar_ne hn hK
  rcases hPQ with hQ | hQ
  · have h0 : (x₀ : Matrix (Fin 3) (Fin 3) K) 0 1 ≠ 0 ∨
        (x₀ : Matrix (Fin 3) (Fin 3) K) 0 2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx₀1 (eq_of_Q1 (hPU hx₀) (one_mem _) (hQ x₀ hx₀) (by simp) (by simp [h.1])
        (by simp [h.2]))
    have hμ : ∀ x : ↥P, ∃ μ : K, bar n μ = μ ∧
        (x : Matrix (Fin 3) (Fin 3) K) 0 1 = μ * (x₀ : Matrix (Fin 3) (Fin 3) K) 0 1 ∧
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 = μ * (x₀ : Matrix (Fin 3) (Fin 3) K) 0 2 := by
      intro x
      obtain ⟨e1, e2, e3⟩ := quad_entries_Q1 hK (hPU x.2) (hPU hx₀) (hQ x₀ hx₀)
        (hq x x.2 x₀ hx₀) hl'
      exact eq_smul_of_quad_entries hK h0 e1 e2 e3
    choose μ hμfix hμ1 hμ2 using hμ
    let f : ↥P → {c : K // bar n c = c} := fun x => ⟨μ x, hμfix x⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h := congrArg Subtype.val hxy
      change μ x = μ y at h
      exact Subtype.ext (eq_of_Q1 (hPU x.2) (hPU y.2) (hQ x x.2) (hQ y y.2)
        (by rw [hμ1, hμ1, h]) (by rw [hμ2, hμ2, h]))
    have := Nat.card_le_card_of_injective f hf
    rwa [card_fixed hn hK] at this
  · have h0 : (x₀ : Matrix (Fin 3) (Fin 3) K) 0 2 ≠ 0 ∨
        (x₀ : Matrix (Fin 3) (Fin 3) K) 1 2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx₀1 (eq_of_Q2 (hPU hx₀) (one_mem _) (hQ x₀ hx₀) (by simp) (by simp [h.1])
        (by simp [h.2]))
    have hμ : ∀ x : ↥P, ∃ μ : K, bar n μ = μ ∧
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 = μ * (x₀ : Matrix (Fin 3) (Fin 3) K) 0 2 ∧
        (x : Matrix (Fin 3) (Fin 3) K) 1 2 = μ * (x₀ : Matrix (Fin 3) (Fin 3) K) 1 2 := by
      intro x
      obtain ⟨e1, e2, e3⟩ := quad_entries_Q2 hK (hPU x.2) (hPU hx₀) (hQ x x.2) (hQ x₀ hx₀)
        (hq x x.2 x₀ hx₀)
      exact eq_smul_of_quad_entries hK h0 e1 e2 e3
    choose μ hμfix hμ1 hμ2 using hμ
    let f : ↥P → {c : K // bar n c = c} := fun x => ⟨μ x, hμfix x⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h := congrArg Subtype.val hxy
      change μ x = μ y at h
      exact Subtype.ext (eq_of_Q2 (hPU x.2) (hPU y.2) (hQ x x.2) (hQ y y.2)
        (by rw [hμ1, hμ1, h]) (by rw [hμ2, hμ2, h]))
    have := Nat.card_le_card_of_injective f hf
    rwa [card_fixed hn hK] at this

theorem card_le_of_quadratic_img (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ img hK) (hAe : IsElemAbelian2 A)
    (hq : ∀ a ∈ A, ∀ b ∈ A, ∀ X : HMod n K, b (a X * X⁻¹) = a X * X⁻¹) :
    Nat.card A ≤ 2 ^ n := by
  obtain ⟨g, P, hPU, -, hinj, hmap⟩ :=
    exists_conj_uni3 hK (hA.trans (img_le_linImg hK)) (IsElemAbelian2.isPGroup hAe)
  set c := rho hK g with hc
  rw [conj_eq_congrHom] at hmap
  have hqA := quad_map_congrHom c hq
  have hAe' := (isElemAbelian2_map_congrHom c).2 hAe
  have hmem : ∀ x ∈ P, rho hK x ∈ A.map (congrHom c) := fun x hx => hmap ▸ ⟨x, hx, rfl⟩
  have hc' : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have h1 : rho hK (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hAe'.1 _ (hmem x hx) _ (hmem y hy), mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj _ (P.mul_mem (P.mul_mem hx hy) (P.inv_mem (P.mul_mem hy hx))) h1)
  have hs : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    refine hinj _ (P.mul_mem hx hx) ?_
    rw [map_mul, ← sq]
    exact hAe'.2 _ (hmem x hx)
  have hPQ := uni3_cases hPU hc' hs
  have hle := card_le_of_quadratic_uni3 hn hK hPU hPQ fun x hx x₀ hx₀ X =>
    hqA _ (hmem x₀ hx₀) _ (hmem x hx) X
  rw [← card_map_rho_of_inj hK hinj, hmap, card_map_congrHom] at hle
  exact hle

theorem two_mul_rk_lt_of_quadratic (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ norm hK) (hAe : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) (hq : ∀ a ∈ A, ∀ b ∈ A, ∀ X : HMod n K, b (a X * X⁻¹) = a X * X⁻¹) :
    2 * rk ↥A < rkIdx (fixV A) := by
  have : Finite (HMod n K) := Finite.of_injective _ (mat_injective (n := n) (K := K))
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hrk : ∀ U : Subgroup (HMod n K), Nat.card U = 2 ^ rk ↥U := card_eq_two_pow sq_eq_one_HMod
  have hrkV : ∀ U : Subgroup (HMod n K), rk ↥U + rkIdx U = 9 * n := by
    intro U
    have h1 := rk_add_rkIdx U
    have h2 : rk (HMod n K) = 9 * n := by
      have := card_eq_two_pow_of_isPGroup
        (isPGroup_two_of_sq_eq_one (sq_eq_one_HMod (n := n) (K := K)))
      rw [card_HMod hn hK] at this
      exact (Nat.pow_right_injective (le_refl 2) this).symm
    omega
  have hcA : Nat.card A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup (IsElemAbelian2.isPGroup hAe)
  have hfixle : ∀ t ∈ A, fixV A ≤ fixV (Subgroup.zpowers t) := fun t ht =>
    fixV_anti (Subgroup.zpowers_le.mpr ht)
  by_cases hAL : A ⊓ img hK = ⊥
  ·
    have hc2 := card_le_two_of_inf_img_eq_bot hn hK hA hAe hAL
    rw [hcA] at hc2
    have hrkA : rk ↥A ≤ 1 := by
      by_contra h
      have : 2 ^ 2 ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨⟨t, htA⟩, ht1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
    have ht2 : t * t = 1 := by rw [← sq]; exact hAe.2 t htA
    have h6 := (Subgroup.card_le_of_le (hfixle t htA)).trans
      (card_fixV_le_of_involution hn hK (hA htA) ht2 ht1)
    rw [hrk] at h6
    have h6' : rk ↥(fixV A) ≤ 6 * n := (Nat.pow_le_pow_iff_right (by norm_num)).mp h6
    have := hrkV (fixV A)
    omega
  ·
    obtain ⟨⟨s, hsA, hsL⟩, hs1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAL
    have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
    have hs2 : IsPGroup 2 ↥(Subgroup.zpowers s) :=
      (IsElemAbelian2.isPGroup hAe).to_le (Subgroup.zpowers_le.mpr hsA)
    obtain ⟨P, -, hPs, hinj⟩ := exists_lift hK
      ((Subgroup.zpowers_le.mpr hsL).trans (img_le_linImg hK)) hs2
    obtain ⟨s', hs'P, hs's⟩ : ∃ s' ∈ P, rho hK s' = s := by
      have : s ∈ P.map (rho hK) := hPs ▸ Subgroup.mem_zpowers s
      exact this
    have hs'2 : s' * s' = 1 := hinj _ (P.mul_mem hs'P hs'P) (by
      rw [map_mul, hs's, ← sq]
      exact hAe.2 s hsA)
    have hs'1 : s' ≠ 1 := fun h => hs1 (by rw [← hs's, h, map_one])
    have hAimg : A ≤ img hK := fun a ha =>
      B45SL3.mem_img_of_quadratic hn hK hs'1 hs'2 (hA ha) (by rw [← sq]; exact hAe.2 a ha)
        fun X => by rw [hs's]; exact hq s hsA a ha X
    have hcle := card_le_of_quadratic_img hn hK hAimg hAe hq
    rw [hcA] at hcle
    have hrkA : rk ↥A ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hcle
    have hs5 : Nat.card ↥(fixV (Subgroup.zpowers s)) ≤ 2 ^ (5 * n) := by
      have h := card_fixV_rhoT_le hn hK (A := SpecialLinearGroup.toGL s')
        (by rw [show rhoT hK (SpecialLinearGroup.toGL s') = rho hK s' from rfl, hs's]; exact hs1)
      rwa [show rhoT hK (SpecialLinearGroup.toGL s') = rho hK s' from rfl, hs's] at h
    have h5 := (Subgroup.card_le_of_le (hfixle s hsA)).trans hs5
    rw [hrk] at h5
    have h5' : rk ↥(fixV A) ≤ 5 * n := (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
    have := hrkV (fixV A)
    omega

end CFSG.Quasithin.H.L3Nine
