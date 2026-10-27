module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcQ
public import Certificates.Data.OPlusFourTwo
import all CFSG.Fischer.F4

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Fischer CFSG.OPlusFourTwo

@[expose] def f4re (c : F4) : ZMod 2 := if c = 0 ∨ c = F4.ω then 0 else 1

@[expose] def f4im (c : F4) : ZMod 2 := if c = 0 ∨ c = 1 then 0 else 1

@[expose] def f4lift (k : ZMod 2) : F4 := if k = 0 then 0 else 1

theorem f4re_zero : f4re 0 = 0 := by decide

theorem f4re_add (a b : F4) : f4re (a + b) = f4re a + f4re b := by
  obtain ⟨i⟩ := a
  obtain ⟨j⟩ := b
  revert i j
  decide

theorem f4im_add (a b : F4) : f4im (a + b) = f4im a + f4im b := by
  obtain ⟨i⟩ := a
  obtain ⟨j⟩ := b
  revert i j
  decide

theorem f4im_sq (c : F4) : f4im (c ^ 2) = f4im c := by
  obtain ⟨i⟩ := c
  revert i
  decide

theorem f4im_mul_F2 {a b : F4} (ha : a ^ 2 = a) (hb : b ^ 2 = b) : f4im (a * b) = 0 := by
  revert ha hb
  obtain ⟨i⟩ := a
  obtain ⟨j⟩ := b
  revert i j
  decide

theorem eq_zero_of_f4re {a : F4} (ha : a ^ 2 = a) (h : f4re a = 0) : a = 0 := by
  revert ha h
  obtain ⟨i⟩ := a
  revert i
  decide

theorem f4im_eq_zero_iff (c : F4) : f4im c = 0 ↔ c = 0 ∨ c = 1 := by
  obtain ⟨i⟩ := c
  revert i
  decide

theorem f4_mul_cases {a b : F4} (ha : a ^ 2 = a) (hb : b ^ 2 = b) :
    (f4re a * f4re b = 1 → a * b = 1) ∧ (f4re a * f4re b ≠ 1 → a * b = 0) := by
  revert ha hb
  obtain ⟨i⟩ := a
  obtain ⟨j⟩ := b
  revert i j
  decide

theorem f4_sq_cases {a b : F4} (ha : a ^ 2 = a) (hb : b ^ 2 = b) (c : F4) :
    (f4re a * f4re b + f4im c = 1 → c + c ^ 2 + a * b = 1) ∧
      (f4re a * f4re b + f4im c ≠ 1 → c + c ^ 2 + a * b = 0) := by
  revert ha hb
  obtain ⟨i⟩ := a
  obtain ⟨j⟩ := b
  obtain ⟨k⟩ := c
  revert i j k
  decide

theorem f4lift_sq (k : ZMod 2) : f4lift k ^ 2 = f4lift k := by
  revert k
  decide

theorem f4re_lift (k : ZMod 2) : f4re (f4lift k) = k := by
  revert k
  decide

theorem f4im_lift_mul (k : ZMod 2) : f4im (f4lift k * F4.ω) = k := by
  revert k
  decide

theorem f4_cases (c : F4) : c = 0 ∨ c = 1 ∨ c = F4.ω ∨ c = F4.ω + 1 := by
  obtain ⟨i⟩ := c
  revert i
  decide

namespace ExcNF

variable {G : Type} [Group G] {T S V₁ V₂ Z : Subgroup G} (N : ExcNF T S V₁ V₂ Z)

theorem eq_of_coord {p q : F4 × F4 × F4} {e f : Bool}
    (h : N.Φ p * (if e then N.x else 1) = N.Φ q * (if f then N.x else 1)) : p = q ∧ e = f := by
  cases e <;> cases f <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h
  · exact ⟨N.inj h, rfl⟩
  · exact absurd h (N.Φ_ne_Φx p q)
  · exact absurd h.symm (N.Φ_ne_Φx q p)
  · exact ⟨N.inj (mul_right_cancel h), rfl⟩

@[expose] noncomputable def tcoord (g : G) : (F4 × F4 × F4) × Bool :=
  Classical.epsilon fun q : (F4 × F4 × F4) × Bool => g = N.Φ q.1 * (if q.2 then N.x else 1)

theorem tcoord_spec (p : F4 × F4 × F4) (e : Bool) :
    N.tcoord (N.Φ p * (if e then N.x else 1)) = (p, e) := by
  have hex : ∃ q : (F4 × F4 × F4) × Bool,
      N.Φ p * (if e then N.x else 1) = N.Φ q.1 * (if q.2 then N.x else 1) := ⟨(p, e), rfl⟩
  have h := Classical.epsilon_spec hex
  obtain ⟨h1, h2⟩ := N.eq_of_coord h.symm
  exact Prod.ext h1 h2

@[expose] noncomputable def δ (g : G) : Fin 4 → ZMod 2 :=
  ![f4re (N.tcoord g).1.2.1, f4re (N.tcoord g).1.2.2, f4im (N.tcoord g).1.1,
    if (N.tcoord g).2 then 1 else 0]

theorem δ_Φ (c a b : F4) : N.δ (N.Φ (c, a, b)) = ![f4re a, f4re b, f4im c, 0] := by
  have h := N.tcoord_spec (c, a, b) false
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h
  simp only [δ, h, Bool.false_eq_true, ↓reduceIte]

theorem δ_Φx (c a b : F4) : N.δ (N.Φ (c, a, b) * N.x) = ![f4re a, f4re b, f4im c, 1] := by
  have h := N.tcoord_spec (c, a, b) true
  simp only [↓reduceIte] at h
  simp only [δ, h, ↓reduceIte]

theorem δ_mul {y y' : G} (hy : y ∈ N.Q) (hy' : y' ∈ N.Q) : N.δ (y * y') = N.δ y + N.δ y' := by
  obtain ⟨c, a, b, ha, hb, rfl | rfl⟩ := hy <;>
    obtain ⟨c', a', b', ha', hb', rfl | rfl⟩ := hy'
  · rw [N.mul, N.δ_Φ, N.δ_Φ, N.δ_Φ]
    funext i
    fin_cases i <;> simp [f4re_add, f4im_add, f4im_mul_F2 ha' hb]
  · rw [← mul_assoc, N.mul, N.δ_Φx, N.δ_Φ, N.δ_Φx]
    funext i
    fin_cases i <;> simp [f4re_add, f4im_add, f4im_mul_F2 ha' hb]
  · rw [mul_assoc, N.x_mul_Φ, ← mul_assoc, N.mul, N.δ_Φx, N.δ_Φx, N.δ_Φ, ha', hb']
    funext i
    fin_cases i <;> simp [f4re_add, f4im_add, f4im_sq, f4im_mul_F2 ha' hb]
  · have e : N.Φ (c, a, b) * N.x * (N.Φ (c', a', b') * N.x) =
        N.Φ (c, a, b) * (N.x * N.Φ (c', a', b')) * N.x := by group
    rw [e, N.x_mul_Φ, ← mul_assoc, mul_assoc _ N.x N.x, N.x_mul_self, mul_one, N.mul, N.δ_Φ,
      N.δ_Φx, N.δ_Φx, ha', hb']
    funext i
    fin_cases i <;> simp [f4re_add, f4im_add, f4im_sq, f4im_mul_F2 ha' hb]
    decide

theorem δ_one : N.δ 1 = 0 := by
  rw [← N.Φ_zero, N.δ_Φ]
  funext i
  fin_cases i <;> decide

theorem δ_inv {y : G} (hy : y ∈ N.Q) : N.δ y⁻¹ = N.δ y := by
  have h := N.δ_mul (N.Q.inv_mem hy) hy
  rw [inv_mul_cancel, N.δ_one] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.zero_apply, Pi.add_apply] at hi
  have h2 : ∀ u w : ZMod 2, 0 = u + w → u = w := by decide
  exact h2 _ _ hi

theorem δ_eq_zero_iff {y : G} (hy : y ∈ N.Q) :
    N.δ y = 0 ↔ y ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) := by
  obtain ⟨c, a, b, ha, hb, rfl | rfl⟩ := hy
  · rw [N.δ_Φ, N.Φ_mem_zpowers_iff]
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Pi.zero_apply] at h0 h1 h2
      exact ⟨(f4im_eq_zero_iff c).mp h2, eq_zero_of_f4re ha h0, eq_zero_of_f4re hb h1⟩
    · rintro ⟨hc, rfl, rfl⟩
      rcases hc with rfl | rfl <;> (funext i; fin_cases i <;> decide)
  · constructor
    · intro h
      have h3 := congrFun h 3
      rw [N.δ_Φx] at h3
      simp at h3
    · intro h
      exact absurd h (N.Φx_not_mem_zpowers _)

@[expose] noncomputable def sec (v : Fin 4 → ZMod 2) : G :=
  N.Φ (f4lift (v 2) * F4.ω, f4lift (v 0), f4lift (v 1)) * (if v 3 = 1 then N.x else 1)

theorem sec_mem (v : Fin 4 → ZMod 2) : N.sec v ∈ N.Q := by
  refine ⟨f4lift (v 2) * F4.ω, f4lift (v 0), f4lift (v 1), f4lift_sq _, f4lift_sq _, ?_⟩
  unfold sec
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl (mul_one _)

theorem δ_sec (v : Fin 4 → ZMod 2) : N.δ (N.sec v) = v := by
  unfold sec
  have h3 : v 3 = 0 ∨ v 3 = 1 := by
    have : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide
    exact this _
  rcases h3 with h3 | h3
  · have h31 : ¬ v 3 = 1 := by rw [h3]; decide
    rw [ite_eq_right_iff.mpr (fun h => absurd h h31), mul_one, N.δ_Φ]
    funext i
    fin_cases i <;> simp [f4re_lift, f4im_lift_mul, h3]
  · rw [ite_eq_left_iff.mpr (fun h => absurd h3 h), N.δ_Φx]
    funext i
    fin_cases i <;> simp [f4re_lift, f4im_lift_mul, h3]

theorem mul_self_eq {y : G} (hy : y ∈ N.Q) :
    y * y = if q0 (N.δ y) = 1 then N.Φ (1, 0, 0) else 1 := by
  obtain ⟨c, a, b, ha, hb, rfl | rfl⟩ := hy
  · rw [N.sq_Φ, N.δ_Φ]
    have hq : q0 ![f4re a, f4re b, f4im c, 0] = f4re a * f4re b := by
      simp [q0]
    rw [hq]
    obtain ⟨h1, h0⟩ := f4_mul_cases ha hb
    split_ifs with h
    · rw [h1 h]
    · rw [h0 h, N.Φ_zero]
  · rw [N.sq_Φx, N.δ_Φx]
    have hq : q0 ![f4re a, f4re b, f4im c, 1] = f4re a * f4re b + f4im c := by
      simp [q0]
    rw [hq]
    obtain ⟨h1, h0⟩ := f4_sq_cases ha hb c
    have e2 : a + a ^ 2 = 0 := by rw [ha]; linear_combination a * F4.two_eq_zero
    have e3 : b + b ^ 2 = 0 := by rw [hb]; linear_combination b * F4.two_eq_zero
    rw [e2, e3, ha]
    split_ifs with h
    · rw [h1 h]
    · rw [h0 h, N.Φ_zero]

theorem mem_V₁_of_δ {y : G} (hy : y ∈ N.Q) (h1 : N.δ y 1 = 0) (h3 : N.δ y 3 = 0) : y ∈ V₁ := by
  obtain ⟨c, a, b, ha, hb, rfl | rfl⟩ := hy
  · rw [N.δ_Φ] at h1
    simp only [Matrix.cons_val_one] at h1
    rw [eq_zero_of_f4re hb h1, N.mem_V₁]
    exact ⟨c, a, rfl⟩
  · rw [N.δ_Φx] at h3
    simp at h3

theorem δ_conj_ω (hST : S ≤ T) {t : G} (ht : t ∈ T) :
    N.δ (t * N.Φ (F4.ω, 0, 0) * t⁻¹) = N.δ (N.Φ (F4.ω, 0, 0)) := by
  obtain ⟨c, a, b, rfl | rfl⟩ := (N.mem_T_iff hST).mp ht
  · rw [N.Φ_conj, N.δ_Φ, N.δ_Φ]
    funext i
    fin_cases i <;> simp
  · have e : N.Φ (c, a, b) * N.x * N.Φ (F4.ω, 0, 0) * (N.Φ (c, a, b) * N.x)⁻¹ =
        N.Φ (c, a, b) * (N.x * N.Φ (F4.ω, 0, 0) * N.x⁻¹) * (N.Φ (c, a, b))⁻¹ := by group
    rw [e, N.x_act, N.Φ_conj, N.δ_Φ, N.δ_Φ]
    funext i
    fin_cases i <;> simp [f4im_sq]

theorem Z_cases (c : F4) : N.Φ (c, 0, 0) ∈ Subgroup.zpowers (N.Φ (1, 0, 0)) ∨
    ∃ w ∈ Subgroup.zpowers (N.Φ (1, 0, 0)), N.Φ (c, 0, 0) = N.Φ (F4.ω, 0, 0) * w := by
  rcases f4_cases c with rfl | rfl | rfl | rfl
  · exact Or.inl ((N.Φ_mem_zpowers_iff).mpr ⟨Or.inl rfl, rfl, rfl⟩)
  · exact Or.inl ((N.Φ_mem_zpowers_iff).mpr ⟨Or.inr rfl, rfl, rfl⟩)
  · exact Or.inr ⟨1, Subgroup.one_mem _, (mul_one _).symm⟩
  · refine Or.inr ⟨N.Φ (1, 0, 0), Subgroup.mem_zpowers _, ?_⟩
    rw [N.mul]
    exact N.Φ_eq (by ring) (by ring) (by ring)

end ExcNF

end CFSG.Quasithin.H13.Sec53L3
