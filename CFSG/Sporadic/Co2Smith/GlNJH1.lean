module

public import CFSG.Sporadic.Co2Smith.GlNJKCompl

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section H1


theorem glNJT_lt {k : ℕ} (hk : k < 3) (x : ℕ) : Native.glNJT k x < 1024 := by
  have htab := glWTab_spec (glNJGen_spec.2.2.2.2 k hk).1
  have key : ∀ l : List ℕ, (∀ i ∈ l, i < 10) →
      l.foldr (fun i acc => if x.testBit i then (Native.glNJTab[k]!)[i]! ^^^ acc else acc) 0 <
        2 ^ 10 := by
    intro l
    induction l with
    | nil => intro _; norm_num
    | cons i l ih =>
      intro hl
      rw [List.foldr_cons]
      have ih' := ih fun j hj => hl j (List.mem_cons_of_mem _ hj)
      split_ifs
      · exact Nat.xor_lt_two_pow (htab i (hl i List.mem_cons_self)).1 ih'
      · exact ih'
  exact key _ fun _ hi => List.mem_range.1 hi

@[expose] noncomputable def liftK (c₁ c₂ : ℕ) (k : ℕ) : K :=
  jcElt (if k = 0 then c₁ else c₂) * qK k

theorem glNJF_lt {c₁ c₂ : ℕ} (h₁ : c₁ < 1024) (h₂ : c₂ < 1024) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 2) → Native.glNJF c₁ c₂ w < 1024
  | [], _ => by rw [Native.glNJF]; norm_num
  | k :: w, hw => by
    rw [Native.glNJF]
    have hk := hw k List.mem_cons_self
    refine Nat.xor_lt_two_pow (n := 10) ?_ (glNJT_lt (by omega) _)
    split_ifs
    · exact h₁
    · exact h₂

theorem prod_lift (c₁ c₂ : ℕ) :
    ∀ w : List ℕ, (∀ k ∈ w, k < 2) →
      (w.map (liftK c₁ c₂)).prod = jcElt (Native.glNJF c₁ c₂ w) * (w.map qK).prod
  | [], _ => by simp [Native.glNJF, jcElt_zero]
  | k :: w, hw => by
    have hk := hw k List.mem_cons_self
    have ih := prod_lift c₁ c₂ w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, Native.glNJF,
      jcElt_xor, liftK]
    have e := qK_conj (show k < 3 by omega) (Native.glNJF c₁ c₂ w)
    calc jcElt (if k = 0 then c₁ else c₂) * qK k * (jcElt (Native.glNJF c₁ c₂ w) *
          (w.map qK).prod) =
        jcElt (if k = 0 then c₁ else c₂) * (qK k * jcElt (Native.glNJF c₁ c₂ w) * (qK k)⁻¹) *
          (qK k * (w.map qK).prod) := by group
      _ = _ := by rw [e, mul_assoc]

theorem prod_qK_val :
    ∀ w : List ℕ, (∀ k ∈ w, k < 3) →
      ((w.map qK).prod).val.val = rowsMatrix 22 (Native.glNJWord Native.glNJG w)
  | [], _ => by
    rw [List.map_nil, List.prod_nil, val_val_one, Native.glNJWord, List.foldr_nil,
      rowsMatrix_idRows]
  | k :: w, hw => by
    have ih := prod_qK_val w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [List.map_cons, List.prod_cons, val_val_mul, qK_val (hw k List.mem_cons_self), ih,
      ← rowsMatrix_mulRows]
    rfl


theorem prod_qK_rel {r : List ℕ} (hr : r ∈ Native.glNJRels) : (r.map qK).prod = 1 :=
  eq_of_rows (prod_qK_val r fun k hk => by have := (glNJH1_spec.1 r hr).1 k hk; omega)
    val_one_rows (glNJH1_spec.1 r hr).2

end H1

section Class


theorem conj_lift {n c : ℕ} {k : ℕ} (hk : k < 3) :
    jcElt n * (jcElt c * qK k) * (jcElt n)⁻¹ = jcElt (c ^^^ n ^^^ Native.glNJT k n) * qK k := by
  have e := qK_conj hk n
  rw [jcElt_inv]
  calc jcElt n * (jcElt c * qK k) * jcElt n =
      jcElt n * jcElt c * (qK k * jcElt n * (qK k)⁻¹) * qK k := by group
    _ = jcElt (c ^^^ n ^^^ Native.glNJT k n) * qK k := by
      rw [e, jcElt_xor, jcElt_xor, jcElt_comm n c]

theorem exists_conj_QKs {C : Subgroup K} (hCN : C ≤ normalizer (Jc : Set K)) (hCz : C ≤ Cz)
    (hCJ : ∀ x ∈ C, x ∈ Jc → x = 1)
    (hCQ : ∀ q ∈ normalizer (Jc : Set K), q ∈ Cz → ∃ j ∈ Jc, j * q ∈ C) :
    ∃ n < 1024, ∃ s, (s = 0 ∨ s = 18 ∨ s = 76 ∨ s = 94) ∧
      C.map (MulAut.conj (jcElt n)).toMonoidHom = QKs s := by
  obtain ⟨j₁, hj₁, hC₁⟩ := hCQ (qK 0) (qK_mem_N (by norm_num)) (qK_mem_Cz (by norm_num))
  obtain ⟨j₂, hj₂, hC₂⟩ := hCQ (qK 1) (qK_mem_N (by norm_num)) (qK_mem_Cz (by norm_num))
  obtain ⟨c₁, hc₁, rfl⟩ := exists_coord hj₁
  obtain ⟨c₂, hc₂, rfl⟩ := exists_coord hj₂
  obtain ⟨hn, hnrm⟩ := glNJH1_spec.2.1 c₁ hc₁
  set n := Native.glNJNrm[c₁]!
  set C' := C.map (MulAut.conj (jcElt n)).toMonoidHom
  set d₁ := c₁ ^^^ n ^^^ Native.glNJT 0 n
  set d₂ := c₂ ^^^ n ^^^ Native.glNJT 1 n
  have hd₁ : d₁ < 1024 := Nat.xor_lt_two_pow (n := 10)
    (Nat.xor_lt_two_pow (n := 10) hc₁ hn) (glNJT_lt (by norm_num) n)
  have hd₂ : d₂ < 1024 := Nat.xor_lt_two_pow (n := 10)
    (Nat.xor_lt_two_pow (n := 10) hc₂ hn) (glNJT_lt (by norm_num) n)
  have hmem : ∀ x ∈ C, (MulAut.conj (jcElt n)).toMonoidHom x ∈ C' := fun x hx => ⟨x, hx, rfl⟩
  have hg₁ : liftK d₁ d₂ 0 ∈ C' := by
    have := hmem _ hC₁
    rwa [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      conj_lift (by norm_num)] at this
  have hg₂ : liftK d₁ d₂ 1 ∈ C' := by
    have := hmem _ hC₂
    rwa [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      conj_lift (by norm_num)] at this
  have hC'J : ∀ x ∈ C', x ∈ Jc → x = 1 := by
    rintro _ ⟨y, hy, rfl⟩ hJ
    rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at hJ ⊢
    have hyJ : y ∈ Jc := by
      have e : y = (jcElt n)⁻¹ * (jcElt n * y * (jcElt n)⁻¹) * jcElt n := by group
      rw [e]
      exact Jc.mul_mem (Jc.mul_mem (Jc.inv_mem (jcElt_mem n)) hJ) (jcElt_mem n)
    rw [hCJ y hy hyJ, mul_one, mul_inv_cancel]
  have hrel : ∀ r ∈ Native.glNJRels, Native.glNJF d₁ d₂ r = 0 := by
    intro r hr
    have hlt := (glNJH1_spec.1 r hr).1
    have hprod := prod_lift d₁ d₂ r hlt
    rw [prod_qK_rel hr, mul_one] at hprod
    have hin : (r.map (liftK d₁ d₂)).prod ∈ C' := by
      refine list_prod_mem fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      rcases Nat.lt_succ_iff_lt_or_eq.1 (hlt k hk) with h0 | rfl
      · rw [Nat.lt_one_iff.1 h0]
        exact hg₁
      · exact hg₂
    rw [hprod] at hin
    have h1 := hC'J _ hin (jcElt_mem _)
    rw [← jcElt_zero] at h1
    exact jcElt_inj (glNJF_lt hd₁ hd₂ r hlt) (by norm_num) h1
  have hd₁' : d₁ = 0 ∨ d₁ = 64 := hnrm
  obtain ⟨h0, hs⟩ := glNJH1_spec.2.2 d₁ hd₁' d₂ hd₂ hrel
  refine ⟨n, hn, d₂, hs, le_antisymm ?_ ?_⟩
  ·
    have hQC : QKs d₂ ≤ C' := by
      rw [QKs, closure_le]
      rintro _ (rfl | rfl)
      · have e : liftK d₁ d₂ 0 = qK 0 := by
          rw [liftK, ite_eq_left rfl, h0, jcElt_zero, one_mul]
        rw [← e]
        exact hg₁
      · exact hg₂
    intro x hx
    have hxN : x ∈ normalizer (Jc : Set K) := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact mul_mem (mul_mem (le_normalizer (jcElt_mem n)) (hCN hy))
        (inv_mem (le_normalizer (jcElt_mem n)))
    have hxz : x ∈ Cz := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact mul_mem (mul_mem (Jc_le_Cz (jcElt_mem n)) (hCz hy)) (inv_mem (Jc_le_Cz (jcElt_mem n)))
    obtain ⟨y, hy, e⟩ := exists_QKs_piK d₂ (σ := piK ⟨x, hxN⟩)
      ⟨piK_mem_njAut _, (piK_zero_iff ⟨x, hxN⟩).2 hxz⟩
    have := piK_inj_of_inf hC'J (hQC hy) hx e
    rw [← show (y : K) = x from congrArg Subtype.val this]
    exact hy
  · rw [QKs, closure_le]
    rintro _ (rfl | rfl)
    · have e : liftK d₁ d₂ 0 = qK 0 := by
        rw [liftK, ite_eq_left rfl, h0, jcElt_zero, one_mul]
      rw [← e]
      exact hg₁
    · exact hg₂

end Class

end CFSG.Sporadic.Co2Smith
