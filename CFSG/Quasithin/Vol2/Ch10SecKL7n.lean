module

public import CFSG.Quasithin.Vol2.Ch10SecKL7a
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] def uM (a b c : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, a, b; 0, 1, c; 0, 0, 1]

@[expose] def qM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

theorem uM_det_spec : ∀ a b c : ZMod 2,
    (uM a b c 0 0 * uM a b c 1 1 * uM a b c 2 2 - uM a b c 0 0 * uM a b c 1 2 * uM a b c 2 1 -
      uM a b c 0 1 * uM a b c 1 0 * uM a b c 2 2 + uM a b c 0 1 * uM a b c 1 2 * uM a b c 2 0 +
      uM a b c 0 2 * uM a b c 1 0 * uM a b c 2 1 - uM a b c 0 2 * uM a b c 1 1 * uM a b c 2 0) ≠
      0 := by
  decide

theorem det_uM (a b c : ZMod 2) : (uM a b c).det ≠ 0 := by
  rw [Matrix.det_fin_three]
  exact uM_det_spec a b c

theorem det_qM : qM.det ≠ 0 := by rw [Matrix.det_fin_three]; decide

theorem uM_mul : ∀ a b c a' b' c' : ZMod 2,
    uM a b c * uM a' b' c' = uM (a + a') (b + b' + a * c') (c + c') := by
  decide

theorem uM_zero : uM 0 0 0 = 1 := by decide

theorem uM_inv : ∀ a b c : ZMod 2, uM a b c * uM a (b + a * c) c = 1 := by decide

theorem uM_pow_four : ∀ a b c : ZMod 2, uM a b c * uM a b c * (uM a b c * uM a b c) = 1 := by
  decide

theorem qM_cube : qM * qM * qM = 1 := by decide

theorem qM_ne_one : qM ≠ 1 := by decide

theorem qM_uM : ∀ a b : ZMod 2, qM * uM a b 0 = uM (a + b) a 0 * qM := by decide

theorem uM_conj_E : ∀ a b c a' b' : ZMod 2, ∃ a'' b'' : ZMod 2,
    uM a b c * uM a' b' 0 = uM a'' b'' 0 * uM a b c := by
  decide

theorem uM_qM : ∀ a b c : ZMod 2,
    (∃ a' b' : ZMod 2, uM a b c * qM = uM a' b' 0 * qM * uM a b c) ∨
      (∃ a' b' : ZMod 2, uM a b c * qM = uM a' b' 0 * (qM * qM) * uM a b c) := by
  decide

@[expose] def U3 : Subgroup SL32 where
  carrier := {γ | ∃ a b c, mat γ = uM a b c}
  one_mem' := ⟨0, 0, 0, by rw [mat_one, uM_zero]⟩
  mul_mem' := by
    rintro x y ⟨a, b, c, hx⟩ ⟨a', b', c', hy⟩
    exact ⟨_, _, _, by rw [mat_mul, hx, hy, uM_mul]⟩
  inv_mem' := by
    rintro x ⟨a, b, c, hx⟩
    refine ⟨a, b + a * c, c, ?_⟩
    have h1 : x * mkSL (uM a (b + a * c) c) (det_uM _ _ _) = 1 :=
      ext_mat (by rw [mat_mul, hx, mat_mkSL, uM_inv, mat_one])
    rw [inv_eq_of_mul_eq_one_right h1, mat_mkSL]

@[expose] def EE : Subgroup SL32 where
  carrier := {γ | ∃ a b, mat γ = uM a b 0}
  one_mem' := ⟨0, 0, by rw [mat_one, uM_zero]⟩
  mul_mem' := by
    rintro x y ⟨a, b, hx⟩ ⟨a', b', hy⟩
    exact ⟨_, _, by rw [mat_mul, hx, hy, uM_mul, mul_zero, add_zero, add_zero]⟩
  inv_mem' := by
    rintro x ⟨a, b, hx⟩
    refine ⟨a, b, ?_⟩
    have h1 : x * mkSL (uM a b 0) (det_uM _ _ _) = 1 := ext_mat (by
      rw [mat_mul, hx, mat_mkSL, mat_one]
      have := uM_inv a b 0
      rwa [mul_zero, add_zero] at this)
    rw [inv_eq_of_mul_eq_one_right h1, mat_mkSL]

@[expose] noncomputable def gq : SL32 := mkSL qM det_qM

theorem EE_le_U3 : EE ≤ U3 := by
  rintro x ⟨a, b, hx⟩
  exact ⟨a, b, 0, hx⟩

theorem isPGroup_U3 : IsPGroup 2 U3 := by
  rintro ⟨x, a, b, c, hx⟩
  refine ⟨2, Subtype.ext (ext_mat ?_)⟩
  rw [Subgroup.coe_pow, show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, pow_two, pow_two, mat_mul,
    mat_mul, hx, uM_pow_four]
  rfl

theorem card_U3 : Nat.card U3 = 8 := by
  have hc : Nat.card (ZMod 2 × ZMod 2 × ZMod 2) = 8 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  rw [← hc]
  let e : (ZMod 2 × ZMod 2 × ZMod 2) ≃ ↥U3 :=
    { toFun := fun p => ⟨mkSL (uM p.1 p.2.1 p.2.2) (det_uM _ _ _), ⟨p.1, p.2.1, p.2.2, rfl⟩⟩
      invFun := fun x => (mat x 0 1, mat x 0 2, mat x 1 2)
      left_inv := fun p => by
        obtain ⟨a, b, c⟩ := p
        rfl
      right_inv := fun x => by
        obtain ⟨x, a, b, c, hx⟩ := x
        apply Subtype.ext
        apply ext_mat
        simp only [mat_mkSL]
        rw [hx]
        simp [uM] }
  exact (Nat.card_congr e).symm

theorem gq_pow_three : gq ^ 3 = 1 :=
  ext_mat (by rw [pow_three, mat_mul, mat_mul, mat_one, ← mul_assoc]; exact qM_cube)

theorem gq_ne_one : gq ≠ 1 := fun h => qM_ne_one (by
  have := congrArg mat h
  rwa [mat_one] at this)

theorem gq_conj_EE {e : SL32} (he : e ∈ EE) : gq * e * gq⁻¹ ∈ EE := by
  obtain ⟨a, b, he⟩ := he
  refine ⟨a + b, a, ?_⟩
  have h1 : gq * e = mkSL (uM (a + b) a 0) (det_uM _ _ _) * gq :=
    ext_mat (by rw [mat_mul, mat_mul, he, mat_mkSL]; exact qM_uM a b)
  rw [h1, mul_inv_cancel_right, mat_mkSL]

theorem U3_conj_EE {u e : SL32} (hu : u ∈ U3) (he : e ∈ EE) : u * e * u⁻¹ ∈ EE := by
  obtain ⟨a, b, c, hu⟩ := hu
  obtain ⟨a', b', he⟩ := he
  obtain ⟨a'', b'', h⟩ := uM_conj_E a b c a' b'
  refine ⟨a'', b'', ?_⟩
  have h1 : u * e = mkSL (uM a'' b'' 0) (det_uM _ _ _) * u :=
    ext_mat (by rw [mat_mul, mat_mul, hu, he, mat_mkSL]; exact h)
  rw [h1, mul_inv_cancel_right, mat_mkSL]

theorem U3_conj_gq {u : SL32} (hu : u ∈ U3) : u * gq * u⁻¹ ∈ EE ⊔ Subgroup.zpowers gq := by
  obtain ⟨a, b, c, hu⟩ := hu
  rcases uM_qM a b c with ⟨a', b', h⟩ | ⟨a', b', h⟩
  · have h1 : u * gq = mkSL (uM a' b' 0) (det_uM _ _ _) * gq * u :=
      ext_mat (by rw [mat_mul, mat_mul, mat_mul, hu, mat_mkSL]; exact h)
    rw [h1, mul_inv_cancel_right]
    exact mul_mem (Subgroup.mem_sup_left ⟨a', b', rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers gq))
  · have h1 : u * gq = mkSL (uM a' b' 0) (det_uM _ _ _) * (gq * gq) * u :=
      ext_mat (by rw [mat_mul, mat_mul, mat_mul, mat_mul, hu, mat_mkSL]; exact h)
    rw [h1, mul_inv_cancel_right]
    exact mul_mem (Subgroup.mem_sup_left ⟨a', b', rfl⟩)
      (Subgroup.mem_sup_right (mul_mem (Subgroup.mem_zpowers gq) (Subgroup.mem_zpowers gq)))

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
