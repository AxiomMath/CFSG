module

public import CFSG.Quasithin.H13.A6S13828a
public import CFSG.Quasithin.H13.A6S13828c

public section

namespace CFSG.Quasithin.H13.A6

open Matrix

@[expose] def pl (a b : Fin 4 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun p => a (wedgePair p).1 * b (wedgePair p).2 + a (wedgePair p).2 * b (wedgePair p).1

theorem wedge2_mulVec_pl (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (a b : Fin 4 → ZMod 2) :
    (wedge2 A).mulVec (pl a b) = pl (A.mulVec a) (A.mulVec b) := by
  funext p
  fin_cases p <;>
  · simp [wedge2, pl, wedgePair, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring_nf
    reduce_mod_char

theorem pl_self (a : Fin 4 → ZMod 2) : pl a a = 0 := by
  funext p
  simp only [pl, Pi.zero_apply]
  rw [mul_comm (a (wedgePair p).2) (a (wedgePair p).1)]
  exact (by decide : ∀ s : ZMod 2, s + s = 0) _

theorem pl_comm (a b : Fin 4 → ZMod 2) : pl a b = pl b a := by
  funext p
  simp only [pl]
  ring

theorem pl_add_right (a b c : Fin 4 → ZMod 2) : pl a (b + c) = pl a b + pl a c := by
  funext p
  simp only [pl, Pi.add_apply]
  ring

theorem pl_add_left (a b c : Fin 4 → ZMod 2) : pl (a + b) c = pl a c + pl b c := by
  funext p
  simp only [pl, Pi.add_apply]
  ring

theorem pl_zero_left (b : Fin 4 → ZMod 2) : pl 0 b = 0 := by
  funext p
  simp [pl]

theorem pl_zero_right (a : Fin 4 → ZMod 2) : pl a 0 = 0 := by
  funext p
  simp [pl]

theorem pl_single : ∀ p : Fin 6,
    pl (Pi.single (wedgePair p).1 1) (Pi.single (wedgePair p).2 1) = Pi.single p 1 := by
  decide

@[expose] def tvm (k l : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => if i = j then 1 else if i = k ∧ j = l then 1 else 0

theorem tvm_sq : ∀ k l : Fin 4, k ≠ l → tvm k l * tvm k l = 1 := by
  decide

@[expose] def tvU (k l : Fin 4) (hkl : k ≠ l) : GL (Fin 4) (ZMod 2) :=
  ⟨tvm k l, tvm k l, tvm_sq k l hkl, tvm_sq k l hkl⟩

@[expose] def rowv (l : Fin 4) (x : Fin 6 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![![0, x 0, x 1, x 2], ![x 0, 0, x 3, x 4], ![x 1, x 3, 0, x 5], ![x 2, x 4, x 5, 0]] l

theorem tv_wedge2 : ∀ k l : Fin 4, k ≠ l → ∀ x : Fin 6 → ZMod 2,
    (wedge2 (tvm k l)).mulVec x + x = pl (Pi.single k 1) (rowv l x) := by
  decide

theorem exists_tv_ne : ∀ x : Fin 6 → ZMod 2, x ≠ 0 →
    ∃ k l : Fin 4, k ≠ l ∧ pl (Pi.single k 1) (rowv l x) ≠ 0 := by
  decide

theorem exists_not_mem_list (s : List (Fin 4 → ZMod 2)) (hs : s.length < 16) :
    ∃ v : Fin 4 → ZMod 2, v ∉ s := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin 4 → ZMod 2)) ⊆ s.toFinset :=
    fun x _ => List.mem_toFinset.2 (h x)
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le s
  rw [Finset.card_univ, card_vec4] at h1
  omega

theorem exists_basis_of_pair {a b : Fin 4 → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ c d : Fin 4 → ZMod 2, ∀ x : Fin 4 → ZMod 2,
      x 0 • a + x 1 • b + x 2 • c + x 3 • d = 0 → x = 0 := by
  obtain ⟨c, hc⟩ := exists_not_mem_list [0, a, b, a + b] (by simp)
  obtain ⟨d, hd⟩ := exists_not_mem_list [0, a, b, a + b, c, a + c, b + c, a + b + c] (by simp)
  have key3 : ∀ s₀ s₁ s₂ : ZMod 2,
      s₀ • a + s₁ • b + s₂ • c ∈ [0, a, b, a + b, c, a + c, b + c, a + b + c] := by
    intro s₀ s₁ s₂
    rcases zmodTwo_cases s₀ with rfl | rfl <;> rcases zmodTwo_cases s₁ with rfl | rfl <;>
      rcases zmodTwo_cases s₂ with rfl | rfl <;> simp
  have key2 : ∀ s₀ s₁ : ZMod 2, s₀ • a + s₁ • b ∈ [0, a, b, a + b] := by
    intro s₀ s₁
    rcases zmodTwo_cases s₀ with rfl | rfl <;> rcases zmodTwo_cases s₁ with rfl | rfl <;> simp
  refine ⟨c, d, fun x hx => ?_⟩
  have h3 : x 3 = 0 := by
    rcases zmodTwo_cases (x 3) with h | h
    · exact h
    exfalso
    rw [h, one_smul] at hx
    have hd' : d = x 0 • a + x 1 • b + x 2 • c := (eq_of_add_eq_zero_vec4 hx).symm
    exact hd (hd' ▸ key3 _ _ _)
  rw [h3, zero_smul, add_zero] at hx
  have h2 : x 2 = 0 := by
    rcases zmodTwo_cases (x 2) with h | h
    · exact h
    exfalso
    rw [h, one_smul] at hx
    have hc' : c = x 0 • a + x 1 • b := (eq_of_add_eq_zero_vec4 hx).symm
    exact hc (hc' ▸ key2 _ _)
  rw [h2, zero_smul, add_zero] at hx
  have h01 := pair_indep4 ha hb hab hx
  funext i
  fin_cases i
  · exact h01.1
  · exact h01.2
  · exact h2
  · exact h3

@[expose] def perm4 (p : Fin 6) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![cols4 (Pi.single 0 1) (Pi.single 1 1) (Pi.single 2 1) (Pi.single 3 1),
    cols4 (Pi.single 0 1) (Pi.single 2 1) (Pi.single 1 1) (Pi.single 3 1),
    cols4 (Pi.single 0 1) (Pi.single 3 1) (Pi.single 1 1) (Pi.single 2 1),
    cols4 (Pi.single 1 1) (Pi.single 2 1) (Pi.single 0 1) (Pi.single 3 1),
    cols4 (Pi.single 1 1) (Pi.single 3 1) (Pi.single 0 1) (Pi.single 2 1),
    cols4 (Pi.single 2 1) (Pi.single 3 1) (Pi.single 0 1) (Pi.single 1 1)] p

theorem perm4_facts : ∀ p : Fin 6, perm4 p * (perm4 p).transpose = 1 ∧
    (perm4 p).transpose * perm4 p = 1 ∧
    (wedge2 (perm4 p)).mulVec (Pi.single 0 1) = Pi.single p 1 := by
  decide

@[expose] def permU (p : Fin 6) : GL (Fin 4) (ZMod 2) :=
  ⟨perm4 p, (perm4 p).transpose, (perm4_facts p).1, (perm4_facts p).2.1⟩

theorem wedge2_irred (X : AddSubgroup (Fin 6 → ZMod 2))
    (hX : ∀ g : GL (Fin 4) (ZMod 2), ∀ x ∈ X,
      (wedge2 (g : Matrix (Fin 4) (Fin 4) (ZMod 2))).mulVec x ∈ X)
    {x : Fin 6 → ZMod 2} (hx : x ∈ X) (hx0 : x ≠ 0) : X = ⊤ := by
  obtain ⟨k, l, hkl, hne⟩ := exists_tv_ne x hx0
  have hdec : pl (Pi.single k 1) (rowv l x) ∈ X := by
    rw [← tv_wedge2 k l hkl x]
    exact X.add_mem (hX (tvU k l hkl) x hx) hx
  have ha : (Pi.single k 1 : Fin 4 → ZMod 2) ≠ 0 := fun h => hne (by rw [h, pl_zero_left])
  have hb : rowv l x ≠ 0 := fun h => hne (by rw [h, pl_zero_right])
  have hab : (Pi.single k 1 : Fin 4 → ZMod 2) ≠ rowv l x := fun h => hne (by rw [h, pl_self])
  obtain ⟨c, d, hind⟩ := exists_basis_of_pair ha hb hab
  have hP := isUnit_cols4 hind
  have key : ∀ v : Fin 4 → ZMod 2, ((hP.unit⁻¹ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec ((cols4 (Pi.single k 1) (rowv l x) c d).mulVec v) =
        v := by
    intro v
    rw [Matrix.mulVec_mulVec, IsUnit.val_inv_mul hP, Matrix.one_mulVec]
  have h01 : (Pi.single 0 1 : Fin 6 → ZMod 2) ∈ X := by
    have h1 := hX hP.unit⁻¹ _ hdec
    rw [wedge2_mulVec_pl] at h1
    have e0 := key (Pi.single 0 1)
    have e1 := key (Pi.single 1 1)
    have c0 : (cols4 (Pi.single k 1) (rowv l x) c d).mulVec (Pi.single 0 1) = Pi.single k 1 := by
      rw [cols4_mulVec]
      simp
    have c1 : (cols4 (Pi.single k 1) (rowv l x) c d).mulVec (Pi.single 1 1) = rowv l x := by
      rw [cols4_mulVec]
      simp
    rw [c0] at e0
    rw [c1] at e1
    rw [e0, e1] at h1
    have h2 := pl_single 0
    simp only [wedgePair, Matrix.cons_val_zero] at h2
    rwa [h2] at h1
  have hall : ∀ p, (Pi.single p 1 : Fin 6 → ZMod 2) ∈ X := fun p => by
    have h1 := hX (permU p) _ h01
    have h2 := (perm4_facts p).2.2
    rwa [show ((permU p : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = perm4 p from
      rfl, h2] at h1
  rw [eq_top_iff]
  intro y _
  rw [← Finset.univ_sum_single y]
  refine X.sum_mem fun p _ => ?_
  rcases zmodTwo_cases (y p) with h | h
  · rw [h, Pi.single_zero]
    exact X.zero_mem
  · rw [h]
    exact hall p

@[expose] def lam3 (x : Fin 4 → ZMod 2) (ω : Fin 6 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![x 0 * ω 3 + x 1 * ω 1 + x 2 * ω 0, x 0 * ω 4 + x 1 * ω 2 + x 3 * ω 0,
    x 0 * ω 5 + x 2 * ω 2 + x 3 * ω 1, x 1 * ω 5 + x 2 * ω 4 + x 3 * ω 3]

theorem lam3_pl : ∀ a b x : Fin 4 → ZMod 2, pl a b ≠ 0 →
    (lam3 x (pl a b) = 0 ↔ x = 0 ∨ x = a ∨ x = b ∨ x = a + b) := by
  decide

theorem mem_span_of_pl_eq {a b x y : Fin 4 → ZMod 2} (h : pl x y = pl a b) (h0 : pl a b ≠ 0) :
    x = 0 ∨ x = a ∨ x = b ∨ x = a + b := by
  refine (lam3_pl a b x h0).1 ?_
  rw [← h]
  exact (lam3_pl x y x (h ▸ h0)).2 (Or.inr (Or.inl rfl))

theorem pl_ne_zero_iff : ∀ a b : Fin 4 → ZMod 2, pl a b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  decide

theorem exists_basis_of_triple {a b c : Fin 4 → ZMod 2}
    (h : ∀ s₀ s₁ s₂ : ZMod 2, s₀ • a + s₁ • b + s₂ • c = 0 → s₀ = 0 ∧ s₁ = 0 ∧ s₂ = 0) :
    ∃ d : Fin 4 → ZMod 2, ∀ x : Fin 4 → ZMod 2,
      x 0 • a + x 1 • b + x 2 • c + x 3 • d = 0 → x = 0 := by
  obtain ⟨d, hd⟩ := exists_not_mem_list [0, a, b, a + b, c, a + c, b + c, a + b + c] (by simp)
  have key3 : ∀ s₀ s₁ s₂ : ZMod 2,
      s₀ • a + s₁ • b + s₂ • c ∈ [0, a, b, a + b, c, a + c, b + c, a + b + c] := by
    intro s₀ s₁ s₂
    rcases zmodTwo_cases s₀ with rfl | rfl <;> rcases zmodTwo_cases s₁ with rfl | rfl <;>
      rcases zmodTwo_cases s₂ with rfl | rfl <;> simp
  refine ⟨d, fun x hx => ?_⟩
  have h3 : x 3 = 0 := by
    rcases zmodTwo_cases (x 3) with h' | h'
    · exact h'
    exfalso
    rw [h', one_smul] at hx
    have hd' : d = x 0 • a + x 1 • b + x 2 • c := (eq_of_add_eq_zero_vec4 hx).symm
    exact hd (hd' ▸ key3 _ _ _)
  rw [h3, zero_smul, add_zero] at hx
  obtain ⟨h0, h1, h2⟩ := h _ _ _ hx
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

section Bilin

variable {M : Type*} [AddCommGroup M]

theorem vec4_decomp (x : Fin 4 → ZMod 2) :
    x = x 0 • Pi.single 0 1 + x 1 • Pi.single 1 1 + x 2 • Pi.single 2 1 + x 3 • Pi.single 3 1 := by
  funext i
  fin_cases i <;> simp

theorem additive_eq_zero (f : (Fin 4 → ZMod 2) → M) (hadd : ∀ a b, f (a + b) = f a + f b)
    (hb : ∀ i, f (Pi.single i 1) = 0) : ∀ a, f a = 0 := by
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    simpa using this
  have hs : ∀ (s : ZMod 2) i, f (s • Pi.single i 1) = 0 := by
    intro s i
    rcases zmodTwo_cases s with rfl | rfl
    · rw [zero_smul, h0]
    · rw [one_smul, hb]
  intro a
  rw [vec4_decomp a, hadd, hadd, hadd, hs, hs, hs, hs]
  simp

theorem biadditive_eq_zero (F : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → M)
    (h₁ : ∀ a b c, F (a + b) c = F a c + F b c) (h₂ : ∀ a b c, F a (b + c) = F a b + F a c)
    (hb : ∀ i j, F (Pi.single i 1) (Pi.single j 1) = 0) : ∀ a b, F a b = 0 := by
  intro a b
  refine additive_eq_zero (fun x => F a x) (h₂ a) (fun j => ?_) b
  exact additive_eq_zero (fun x => F x (Pi.single j 1)) (fun x y => h₁ x y _) (fun i => hb i j) a

end Bilin

theorem cols4_mulVec_single (a b c d : Fin 4 → ZMod 2) :
    (cols4 a b c d).mulVec (Pi.single 0 1) = a ∧ (cols4 a b c d).mulVec (Pi.single 1 1) = b ∧
      (cols4 a b c d).mulVec (Pi.single 2 1) = c ∧ (cols4 a b c d).mulVec (Pi.single 3 1) = d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [cols4_mulVec] <;> simp

theorem exists_GL_map4 {a b c d a' b' c' d' : Fin 4 → ZMod 2}
    (h : ∀ x : Fin 4 → ZMod 2, x 0 • a + x 1 • b + x 2 • c + x 3 • d = 0 → x = 0)
    (h' : ∀ x : Fin 4 → ZMod 2, x 0 • a' + x 1 • b' + x 2 • c' + x 3 • d' = 0 → x = 0) :
    ∃ g : GL (Fin 4) (ZMod 2), (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec a = a' ∧
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec b = b' ∧
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec c = c' ∧
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec d = d' := by
  have hP := isUnit_cols4 h
  have hP' := isUnit_cols4 h'
  have key : ∀ v : Fin 4 → ZMod 2, ((hP.unit⁻¹ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec ((cols4 a b c d).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, IsUnit.val_inv_mul hP, Matrix.one_mulVec]
  obtain ⟨e0, e1, e2, e3⟩ := cols4_mulVec_single a b c d
  obtain ⟨f0, f1, f2, f3⟩ := cols4_mulVec_single a' b' c' d'
  have k0 := key (Pi.single 0 1)
  have k1 := key (Pi.single 1 1)
  have k2 := key (Pi.single 2 1)
  have k3 := key (Pi.single 3 1)
  rw [e0] at k0
  rw [e1] at k1
  rw [e2] at k2
  rw [e3] at k3
  refine ⟨hP'.unit * hP.unit⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, k0, IsUnit.unit_spec, f0]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, k1, IsUnit.unit_spec, f1]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, k2, IsUnit.unit_spec, f2]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, k3, IsUnit.unit_spec, f3]

end CFSG.Quasithin.H13.A6
