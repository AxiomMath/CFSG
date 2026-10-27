module

public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n : ℕ}

theorem zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h
  decide

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem add_self_vec (x : Fin n → ZMod 2) : x + x = 0 := by
  ext i
  exact zmod2_add_self (x i)

theorem eq_of_add_eq_zero_vec {x y : Fin n → ZMod 2} (h : x + y = 0) : x = y := by
  calc x = x + y + y := by rw [add_assoc, add_self_vec, add_zero]
    _ = y := by rw [h, zero_add]

theorem single_dot (j : Fin n) (x : Fin n → ZMod 2) : Pi.single j (1 : ZMod 2) ⬝ᵥ x = x j := by
  rw [single_dotProduct, one_mul]

theorem exists_dot_zero_one {x y : Fin n → ZMod 2} (hy : y ≠ 0) (hxy : y ≠ x) :
    ∃ u : Fin n → ZMod 2, u ⬝ᵥ x = 0 ∧ u ⬝ᵥ y = 1 := by
  by_cases h : ∃ j, y j = 1 ∧ x j = 0
  · obtain ⟨j, hj1, hj0⟩ := h
    exact ⟨Pi.single j 1, by rw [single_dot, hj0], by rw [single_dot, hj1]⟩
  have h' : ∀ j, y j = 1 → x j = 1 := fun j hj =>
    zmod2_eq_one_of_ne_zero fun h0 => h ⟨j, hj, h0⟩
  obtain ⟨k, hk⟩ : ∃ k, y k ≠ x k := by
    by_contra hc
    exact hxy (funext fun k => by
      by_contra hk
      exact hc ⟨k, hk⟩)
  have hyk : y k = 0 := by
    rcases zmod2_cases (y k) with h0 | h1
    · exact h0
    · exact absurd (h1.trans (h' k h1).symm) hk
  have hxk : x k = 1 := by
    rcases zmod2_cases (x k) with h0 | h1
    · exact absurd (hyk.trans h0.symm) hk
    · exact h1
  obtain ⟨j, hj⟩ : ∃ j, y j = 1 := by
    by_contra hc
    exact hy (funext fun i => (zmod2_cases (y i)).resolve_right fun h1 => hc ⟨i, h1⟩)
  have hxj : x j = 1 := h' j hj
  refine ⟨Pi.single j 1 + Pi.single k 1, ?_, ?_⟩
  · rw [add_dotProduct, single_dot, single_dot, hxj, hxk]
    rfl
  · rw [add_dotProduct, single_dot, single_dot, hj, hyk, add_zero]

theorem exists_sep_pair {a b c : Fin n → ZMod 2} (ha : a ≠ 0) (hc0 : c ≠ 0) (hca : c ≠ a)
    (hcb : c ≠ b) (hcab : c ≠ a + b) :
    ∃ u : Fin n → ZMod 2, u ⬝ᵥ a = 0 ∧ u ⬝ᵥ b = 0 ∧ u ⬝ᵥ c = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, a i = 1 := by
    by_contra hc
    exact ha (funext fun j => (zmod2_cases (a j)).resolve_right fun h1 => hc ⟨j, h1⟩)
  have hc' : c + c i • a ≠ 0 := by
    intro h
    have h' := eq_of_add_eq_zero_vec h
    rcases zmod2_cases (c i) with h0 | h1
    · rw [h0, zero_smul] at h'
      exact hc0 h'
    · rw [h1, one_smul] at h'
      exact hca h'
  have hcb' : c + c i • a ≠ b + b i • a := by
    intro h
    have h' : c = b + (b i + c i) • a := by
      calc c = c + c i • a + c i • a := by rw [add_assoc, add_self_vec, add_zero]
        _ = b + (b i + c i) • a := by rw [h, add_smul, add_assoc]
    rcases zmod2_cases (b i + c i) with h0 | h1
    · rw [h0, zero_smul, add_zero] at h'
      exact hcb h'
    · rw [h1, one_smul, add_comm] at h'
      exact hcab h'
  obtain ⟨u', hu'0, hu'1⟩ := exists_dot_zero_one hc' hcb'
  refine ⟨u' + (u' ⬝ᵥ a) • Pi.single i 1, ?_, ?_, ?_⟩
  · rw [add_dotProduct, smul_dotProduct, single_dot, hi, smul_eq_mul, mul_one, zmod2_add_self]
  · rw [add_dotProduct, smul_dotProduct, single_dot, smul_eq_mul, ← hu'0, dotProduct_add,
      dotProduct_smul, smul_eq_mul, mul_comm]
  · rw [add_dotProduct, smul_dotProduct, single_dot, smul_eq_mul, ← hu'1, dotProduct_add,
      dotProduct_smul, smul_eq_mul, mul_comm]

@[expose] def trv (u w : Fin n → ZMod 2) (h : u ⬝ᵥ w = 0) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  ⟨1 + vecMulVec w u, by
    rw [vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

theorem trv_mulVec (u w : Fin n → ZMod 2) (h : u ⬝ᵥ w = 0) (x : Fin n → ZMod 2) :
    ((trv u w h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      x = x + (u ⬝ᵥ x) • w := by
  simp only [trv, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext i
  simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem exists_mulVec_eq {v w : Fin n → ZMod 2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = w := by
  by_cases hvw : v = w
  · exact ⟨1, by rw [hvw, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]⟩
  have hne : v ≠ v + w := by
    intro h
    apply hw
    calc w = v + v + w := by rw [add_self_vec, zero_add]
      _ = 0 := by rw [add_assoc, ← h, add_self_vec]
  obtain ⟨u, hu0, hu1⟩ := exists_dot_zero_one hv hne
  refine ⟨trv u (v + w) hu0, ?_⟩
  rw [trv_mulVec, hu1, one_smul, ← add_assoc, add_self_vec, zero_add]

theorem exists_fix_fix_move {a b c : Fin n → ZMod 2} (ha : a ≠ 0) (hc0 : c ≠ 0) (hca : c ≠ a)
    (hcb : c ≠ b) (hcab : c ≠ a + b) :
    ∃ h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a = a ∧
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b = b ∧
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ c ≠ c := by
  obtain ⟨u, hua, hub, hu1⟩ := exists_sep_pair ha hc0 hca hcb hcab
  refine ⟨trv u a hua, ?_, ?_, ?_⟩
  · rw [trv_mulVec, hua, zero_smul, add_zero]
  · rw [trv_mulVec, hub, zero_smul, add_zero]
  · rw [trv_mulVec, hu1, one_smul]
    intro h
    apply ha
    calc a = c + a + c := by rw [add_comm c a, add_assoc, add_self_vec, add_zero]
      _ = 0 := by rw [h, add_self_vec]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
