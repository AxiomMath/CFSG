module

public import Certificates.Certificate7196
public import CFSG.Quasithin.H13.L32N1447Model
public import CFSG.Quasithin.H13.L32A1410b

public section

namespace CFSG.Quasithin.H13.Q1447A

open Mat8Cert L1442M S7Cert S8Cert G5Cert G5ACert Q1447Cert

theorem q1447aCheck_eq : q1447aCheck = true :=
  Certificates.certificate7196

theorem q1447aCheck_parts :
    a5InvB = true ∧ a5PB = true ∧ a5ZB = true ∧ a5KB = true := by
  have h := q1447aCheck_eq
  simp only [q1447aCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

@[expose] def b5AV (v w : Fin 8 → ZMod 2) : ZMod 2 :=
  quadOf q5a (v + w) + quadOf q5a v + quadOf q5a w

theorem q5ac_eq : dec8 q5ac = q5a := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem quadA_spec (v : ℕ) : b2z (quadA v) = quadOf q5a (vec8 v) := by
  rw [quadA, dotN_spec, ← dec8_mulVec, q5ac_eq]
  rfl

theorem b5A_spec (v w : ℕ) : b2z (b5A v w) = b5AV (vec8 v) (vec8 w) := by
  simp only [b5A, b2z_xor, quadA_spec, vec8_xor, b5AV]

theorem a5_vec (b : Bool)
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ g5 b false) (hx1 : x ≠ 1) (hxx : x * x = 1) :
    ∃ w : Fin 8 → ZMod 2, b5AV w (vec8 vA) = 0 ∧
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w + w ≠ 0 ∧
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w + w ≠ vec8 vA := by
  have h := q1447aCheck_parts.1
  simp only [a5InvB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  have hvlt : vA < 256 := by decide
  rcases h b (mem_tf b) _ ((mem_gA5_iff b x).mp hx) with h' | ⟨n, hn, ⟨hb, h0⟩, ha⟩
  · rw [invol8_of hx1 hxx] at h'
    exact absurd h' (by decide)
  · have hnlt : n < 256 := List.mem_range.mp hn
    refine ⟨vec8 n, ?_, fun h0' => h0 ?_, fun ha' => ha ?_⟩
    · rw [← b5A_spec, hb]
      rfl
    · apply vec8_inj (O3Cert.xor_lt_256 (mv8_lt (valid8_colsOf _) n) hnlt) (by norm_num)
      rw [vec8_xor, ← mulVec_vec8, h0', vec8_zero]
    · apply vec8_inj (O3Cert.xor_lt_256 (mv8_lt (valid8_colsOf _) n) hnlt) hvlt
      rw [vec8_xor, ← mulVec_vec8, ha']

theorem a5P_big (b : Bool)
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ PA5 b) (hx1 : x ≠ 1) (hxx : x * x = 1) :
    4 < (Finset.univ.image fun v : Fin 8 → ZMod 2 =>
      (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v).card ∨
    ∀ v, (x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v ≠ vec8 vA := by
  have h := q1447aCheck_parts.2.1
  simp only [a5PB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  have hvlt : vA < 256 := by decide
  rcases h b (mem_tf b) _ ((mem_PA5_iff b x).mp hx) with (h' | h') | h'
  · rw [invol8_of hx1 hxx] at h'
    exact absurd h' (by decide)
  · exact Or.inl (bigImg8_spec h')
  · refine Or.inr fun v hv => ?_
    rw [List.any_eq_false] at h'
    apply h' (code8 v) (List.mem_range.mpr (code8_lt v))
    rw [beq_iff_eq]
    apply vec8_inj (O3Cert.xor_lt_256 (mv8_lt (valid8_colsOf _) _) (code8_lt v)) hvlt
    rw [vec8_xor, ← mulVec_vec8, vec8_code8, hv]

theorem zA_spec :
    (∀ b : Bool, ∀ z ∈ zA b, z ∈ pEA b ∧ ∀ p ∈ pEA b, mul8 z p = mul8 p z) ∧
      ncA.1 ∈ pEA true ∧ ncA.2 ∈ pEA true ∧ mul8 ncA.1 ncA.2 ≠ mul8 ncA.2 ncA.1 := by
  have h := q1447aCheck_parts.2.2.1
  simp only [a5ZB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun b z hz => h1 b (mem_tf b) z hz, h2, h3, h4⟩

theorem exists_mem_PA5 (b : Bool) {c : List ℕ} (hc : c ∈ pEA b) :
    ∃ u ∈ PA5 b, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  exact exists_evalW _ (subB_spec (pA_spec b).1).2.2.2.2 (unit_of_gEA b (pA_spec b).2.2.1) w

theorem zA_mem (b : Bool)
    {z : GL (Fin 8) (ZMod 2)} (hz : colsOf (z : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ zA b) :
    z ∈ PA5 b :=
  (mem_PA5_iff b z).mpr (zA_spec.1 b _ hz).1

theorem zA_central (b : Bool)
    {z : GL (Fin 8) (ZMod 2)} (hz : colsOf (z : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ zA b)
    {p : GL (Fin 8) (ZMod 2)} (hp : p ∈ PA5 b) : z * p = p * z := by
  apply eq_of_colsOf_eq
  rw [Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul]
  exact (zA_spec.1 b _ hz).2 _ ((mem_PA5_iff b p).mp hp)

theorem not_comm_PA5 :
    ∃ p ∈ PA5 true, ∃ p' ∈ PA5 true, p * p' ≠ p' * p := by
  have hval := (subB_spec (pA_spec true).1).1
  obtain ⟨-, h1, h2, h3⟩ := zA_spec
  obtain ⟨u, hu, hu'⟩ := exists_mem_PA5 true h1
  obtain ⟨u', hv, hv'⟩ := exists_mem_PA5 true h2
  refine ⟨u, hu, u', hv, fun h => h3 ?_⟩
  have hc := congrArg (fun y : GL (Fin 8) (ZMod 2) => colsOf (y : Matrix (Fin 8) (Fin 8) (ZMod 2)))
    h
  simp only [Units.val_mul, colsOf_mul, hu', hv'] at hc
  rwa [colsOf_dec8 (hval _ h1), colsOf_dec8 (hval _ h2)] at hc

theorem a5_oTwoUpper_le (b : Bool) :
    oTwoUpper (g5 b false) ≤ Subgroup.closure {y | ∃ k ∈ g5 b false, ∃ z : GL (Fin 8) (ZMod 2),
      colsOf (z : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ zA b ∧ y = k * z * k⁻¹} := by
  have hval := (subB_spec (pA_spec b).1).1
  have hYv : ∀ c ∈ zA b, Valid8 c := fun c hc => hval c (zA_spec.1 b c hc).1
  have hYex : ∀ c ∈ zA b, ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c :=
    fun c hc => let ⟨u, _, hu⟩ := exists_mem_PA5 b (zA_spec.1 b c hc).1; ⟨u, hu⟩
  have hcard : Nat.card (g5 b false) = 2 ^ (if b then 4 else 3) * 45 := by
    rw [card_gA5]
    cases b <;> rfl
  have hKB := q1447aCheck_parts.2.2.2
  simp only [a5KB, List.all_eq_true] at hKB
  exact oTwoUpper_le_of_pow hcard fun x hx hxm =>
    conjB_spec (hKB b (mem_tf b)) (mem_gA5_iff b) (fun c hc => valid8_of_gEA b hc)
      (fun c hc => let ⟨u, _, hu⟩ := exists_mem_gA5 b hc; ⟨u, hu⟩) hYv hYex hx hxm

end CFSG.Quasithin.H13.Q1447A
