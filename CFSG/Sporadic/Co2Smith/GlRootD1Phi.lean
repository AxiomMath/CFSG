module

public import CFSG.Sporadic.Co2Smith.GlRootD1Spec
public import CFSG.Sporadic.Co2Smith.GlSteinConc

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type*} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

@[expose] noncomputable def phiK (s q : K) : K :=
  [q, s, q, q, q, s, α3K, s, q, s, q, q, q, α3K, α3K].prod

theorem list_prod_rows (xs : List K) (Rs : List (Array ℕ))
    (h : List.Forall₂ (fun x R => x.val.val = rowsMatrix 22 R) xs Rs) :
    xs.prod.val.val = rowsMatrix 22 (Native.d1Prod Rs) := by
  rw [List.prod_eq_foldl, Native.d1Prod]
  exact rows_foldl xs (idRows 22) Rs (by rw [rowsMatrix_idRows]; rfl) h

theorem phiK_val {s q : K} {S Q : Array ℕ} (hs : s.val.val = rowsMatrix 22 S)
    (hq : q.val.val = rowsMatrix 22 Q) : (phiK s q).val.val = rowsMatrix 22 (Native.d1Phi S Q) :=
  list_prod_rows _ _ (.cons hq (.cons hs (.cons hq (.cons hq (.cons hq (.cons hs (.cons α3K_val
    (.cons hs (.cons hq (.cons hs (.cons hq (.cons hq (.cons hq (.cons α3K_val
      (.cons α3K_val .nil)))))))))))))))

theorem mem_of_mem_phiList {S : Subgroup K} {a b c x : K} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hx : x ∈ [a, b, a, a, a, b, c, b, a, b, a, a, a, c, c]) : x ∈ S := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    assumption

theorem chartT_list_prod
    {α : Cz} (hm : SmithC0Marking φ α ρ) (hφz : φ (zC z) = zCz) :
    ∀ xs : List K, (∀ x ∈ xs, x ∈ Ax25) → chartT φ ρ xs.prod = (xs.map (chartT φ ρ)).prod
  | [], _ => chartT_one hm hφz
  | x :: xs, h => by
    rw [List.prod_cons, chartT_mul hm hφz (h x List.mem_cons_self)
      (Ax25.list_prod_mem fun y hy => h y (List.mem_cons_of_mem _ hy)), List.map_cons,
      List.prod_cons, chartT_list_prod hm hφz xs fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem chartT_phiK
    (hm : SmithC0Marking φ α3c ρ) (hφz : φ (zC z) = zCz) {s q : K} (hs : s ∈ Ax25)
    (hTs : chartT φ ρ s = s) (hq : q ∈ Ax25) : chartT φ ρ (phiK s q) = phiK s (chartT φ ρ q) := by
  rw [phiK, chartT_list_prod hm hφz _ fun x hx => mem_of_mem_phiList hq hs α3K_mem_Ax25 hx]
  simp only [List.map_cons, List.map_nil, hTs, chartT_α3K hm hφz]
  rfl

theorem d1Phi_spec :
    (∀ e ∈ Native.d1QD, Native.d1InX 1 (Native.d1Phi Native.glX34 (Native.glQRows e)) = true ∧
      Native.d1InX 2 (Native.d1Phi Native.glX43 (Native.glQRows e)) = true ∧
      Native.d1InX 4 (Native.d1Phi Native.glX34 (Native.d1FR e)) = true ∧
      Native.d1InX 5 (Native.d1Phi Native.glX43 (Native.d1FR e)) = true) ∧
    ∀ t ∈ [1, 2, 3],
      (∃ e ∈ Native.d1QD, Native.d1Phi Native.glX34 (Native.glQRows e) = Native.glRootRows 1 t) ∧
      (∃ e ∈ Native.d1QD, Native.d1Phi Native.glX43 (Native.glQRows e) = Native.glRootRows 2 t) ∧
      (∃ e ∈ Native.d1QD, Native.d1Phi Native.glX34 (Native.d1FR e) = Native.glRootRows 4 t) ∧
      ∃ e ∈ Native.d1QD, Native.d1Phi Native.glX43 (Native.d1FR e) = Native.glRootRows 5 t := by
  have h := d1_parts.2.2.2.2.2.2.1
  rw [Native.d1PhiOK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨fun e he => ?_, fun t ht => ?_⟩
  · have := h.1 e he
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · have := h.2 t ht
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem d1InX_spec {r : ℕ} {R : Array ℕ} (h : Native.d1InX r R = true) :
    ∃ t < 4, R = Native.glRootRows r t := by
  simp only [Native.d1InX, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem phiK_eq_root {s q : K} {S Q : Array ℕ} (hs : s.val.val = rowsMatrix 22 S)
    (hq : q.val.val = rowsMatrix 22 Q) {r : ℕ} (h : Native.d1InX r (Native.d1Phi S Q) = true) :
    ∃ t < 4, phiK s q = xRootK r t := by
  obtain ⟨t, ht, hR⟩ := d1InX_spec h
  exact ⟨t, ht, eq_of_val_rows (phiK_val hs hq) (xRootK_val r t) hR⟩


theorem phiK_x34_Qx25 {q : K} (hq : q ∈ Qx25) : ∃ t < 4, phiK x34K q = xRootK 1 t := by
  obtain ⟨e, he, rfl⟩ := exists_qElt (mem_Qx25.1 hq).1
  exact phiK_eq_root x34K_val (glQRows_val he) (d1Phi_spec.1 e ((qElt_mem_Qx25_iff he).1 hq)).1

theorem phiK_x43_Qx25 {q : K} (hq : q ∈ Qx25) : ∃ t < 4, phiK x43K q = xRootK 2 t := by
  obtain ⟨e, he, rfl⟩ := exists_qElt (mem_Qx25.1 hq).1
  exact phiK_eq_root x43K_val (glQRows_val he)
    (d1Phi_spec.1 e ((qElt_mem_Qx25_iff he).1 hq)).2.1

theorem phiK_x34_F0c {f : K} (hf : f ∈ F0c 1) : ∃ t < 4, phiK x34K f = xRootK 4 t := by
  obtain ⟨e, he, rfl⟩ := mem_F0c_one_iff.1 hf
  exact phiK_eq_root x34K_val (d1FR_val (lt_of_mem_d1QD he)) (d1Phi_spec.1 e he).2.2.1

theorem phiK_x43_F0c {f : K} (hf : f ∈ F0c 1) : ∃ t < 4, phiK x43K f = xRootK 5 t := by
  obtain ⟨e, he, rfl⟩ := mem_F0c_one_iff.1 hf
  exact phiK_eq_root x43K_val (d1FR_val (lt_of_mem_d1QD he)) (d1Phi_spec.1 e he).2.2.2

theorem phiK_wit {t : ℕ} (ht : t ∈ [1, 2, 3]) :
    (∃ q ∈ Qx25, phiK x34K q = xRootK 1 t) ∧ (∃ q ∈ Qx25, phiK x43K q = xRootK 2 t) ∧
      (∃ f ∈ F0c 1, phiK x34K f = xRootK 4 t) ∧ ∃ f ∈ F0c 1, phiK x43K f = xRootK 5 t := by
  obtain ⟨⟨e1, he1, h1⟩, ⟨e2, he2, h2⟩, ⟨e4, he4, h4⟩, ⟨e5, he5, h5⟩⟩ := d1Phi_spec.2 t ht
  refine ⟨⟨qElt e1, (qElt_mem_Qx25_iff (lt_of_mem_d1QD he1)).2 he1,
      eq_of_val_rows (phiK_val x34K_val (glQRows_val (lt_of_mem_d1QD he1))) (xRootK_val 1 t) h1⟩,
    ⟨qElt e2, (qElt_mem_Qx25_iff (lt_of_mem_d1QD he2)).2 he2,
      eq_of_val_rows (phiK_val x43K_val (glQRows_val (lt_of_mem_d1QD he2))) (xRootK_val 2 t) h2⟩,
    ⟨_, mem_F0c_one_iff.2 ⟨e4, he4, rfl⟩,
      eq_of_val_rows (phiK_val x34K_val (d1FR_val (lt_of_mem_d1QD he4))) (xRootK_val 4 t) h4⟩,
    ⟨_, mem_F0c_one_iff.2 ⟨e5, he5, rfl⟩,
      eq_of_val_rows (phiK_val x43K_val (d1FR_val (lt_of_mem_d1QD he5))) (xRootK_val 5 t) h5⟩⟩

end CFSG.Sporadic.Co2Smith
