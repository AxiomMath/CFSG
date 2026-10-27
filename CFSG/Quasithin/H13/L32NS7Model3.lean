module

public import CFSG.Quasithin.H13.L32NS7Model2
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.S7Cert

open Mat8Cert CFSG.Quasithin.H13.L1442M CFSG.Quasithin

theorem colsOf_pow3 (u : GL (Fin 8) (ZMod 2)) :
    colsOf ((u ^ 3 : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      mul8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))
        (mul8 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))
          (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))) := by
  rw [show u ^ 3 = u * (u * u) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
    Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul]

theorem colsOf_pow4 (u : GL (Fin 8) (ZMod 2)) :
    colsOf ((u ^ 4 : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      pow4 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
  rw [show u ^ 4 = (u * u) * (u * u) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
    Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul, pow4]

theorem colsOf_pow16 (u : GL (Fin 8) (ZMod 2)) :
    colsOf ((u ^ 16 : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      pow4 (pow4 (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))) := by
  rw [show u ^ 16 = (u ^ 4) ^ 4 by rw [← pow_mul], colsOf_pow4, colsOf_pow4]

theorem card_of_cols {S : Subgroup (GL (Fin 8) (ZMod 2))} {L : List (List ℕ)}
    (hS : ∀ u, u ∈ S ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ L) (hL : L.Nodup)
    (hval : ∀ x ∈ L, Valid8 x)
    (hex : ∀ x ∈ L, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 x) :
    Nat.card S = L.length := by
  let f : S → {x // x ∈ L} := fun u =>
    ⟨colsOf ((u : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)), (hS u).mp u.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun u v h => ?_, fun ⟨x, hx⟩ => ?_⟩
    · exact Subtype.ext (eq_of_colsOf_eq (congrArg Subtype.val h))
    · obtain ⟨v, hv⟩ := hex x hx
      have hvx : colsOf (v : Matrix (Fin 8) (Fin 8) (ZMod 2)) = x := by
        rw [hv, colsOf_dec8 (hval x hx)]
      exact ⟨⟨v, (hS v).mpr (hvx ▸ hx)⟩, Subtype.ext hvx⟩
  rw [Nat.card_eq_of_bijective f hf,
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := L) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hL]

theorem oB_spec :
    (∀ y ∈ mE 0, mv8 y vStar = vStar) ∧
    ∀ i ∈ [1, 2], (oWs.getD i (0, 0)).1 ≠ 0 ∧ (oWs.getD i (0, 0)).2 ≠ 0 ∧
      (oWs.getD i (0, 0)).1 ≠ (oWs.getD i (0, 0)).2 ∧
      (∀ y ∈ oE i, mv8 y vStar ^^^ vStar ∈ [0, (oWs.getD i (0, 0)).1, (oWs.getD i (0, 0)).2,
        (oWs.getD i (0, 0)).1 ^^^ (oWs.getD i (0, 0)).2]) ∧
      (∃ y ∈ oE i, mv8 y vStar ^^^ vStar = (oWs.getD i (0, 0)).1) ∧
      (∃ y ∈ oE i, mv8 y vStar ^^^ vStar = (oWs.getD i (0, 0)).2) ∧
      (∀ w ∈ [(oWs.getD i (0, 0)).1, (oWs.getD i (0, 0)).2,
        (oWs.getD i (0, 0)).1 ^^^ (oWs.getD i (0, 0)).2], w ∈ eSpan) ∧
      (∃ y ∈ oE i, ∃ v ∈ List.range 256, b4N (mv8 y v ^^^ v) (oWs.getD i (0, 0)).1 = true) ∧
      subB (oddOf (mE i)) (oE i) = true ∧ (twoOf (oE i)).Nodup ∧
      (oE i).length = 3 * (twoOf (oE i)).length ∧
      (∀ a ∈ twoOf (oE i), ∀ b ∈ twoOf (oE i), mul8 a b ∈ twoOf (oE i)) ∧
      ∀ o ∈ oE i, pow4 (pow4 o) = one8 → pow4 o = one8 := by
  have h := s7Check_parts.2.2.2.2.2.1
  simp only [oB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨h0, h12⟩ := h
  refine ⟨h0, fun i hi => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, k⟩, l⟩, m⟩, n⟩, o⟩, p⟩ := h12 i hi
  refine ⟨by simpa using a, by simpa using b, by simpa using c, fun y hy => ?_, ?_, ?_,
    fun w hw => ?_, ?_, l, nodup_of_nodupB m, n, fun x hx y hy => ?_, fun y hy hy4 => ?_⟩
  · simpa [List.contains_iff_mem] using d y hy
  · simpa [List.any_eq_true] using e
  · simpa [List.any_eq_true] using f
  · simpa [List.contains_iff_mem] using g w hw
  · simpa [List.any_eq_true] using k
  · simpa [Std.HashSet.contains_ofList, List.contains_iff_mem] using o x hx y hy
  · have := p y hy
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq] at this
    exact this.resolve_left (not_not.mpr hy4)

theorem M7_zero_fix {y : GL (Fin 8) (ZMod 2)} (hy : y ∈ M7 0) :
    (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) = vec8 vStar := by
  rw [mulVec_vec8, oB_spec.1 _ ((mem_M7_iff (by norm_num) y).mp hy)]

@[expose] def O7 (i : ℕ) : Subgroup (GL (Fin 8) (ZMod 2)) := genSub (oddOf (mE i))

theorem oddOf_sub {M : List (List ℕ)} : ∀ x ∈ oddOf M, x ∈ M := fun _ hx =>
  (List.mem_filter.mp hx).1

theorem mem_one_two {i : ℕ} (hi : i = 1 ∨ i = 2) : i ∈ [1, 2] := by
  rcases hi with rfl | rfl <;> simp

theorem O7_le_M7 {i : ℕ} (hi : i < 3) : O7 i ≤ M7 i := by
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  exact (mem_M7_iff hi u).mpr (oddOf_sub _ hu)

theorem O7_gens_mem {i : ℕ} (hi : i < 3) :
    ∀ g ∈ oddOf (mE i), g ∈ s7E := by
  intro g hg
  have hgM := oddOf_sub g hg
  obtain ⟨w, rfl⟩ := mem_elemsOf hgM
  obtain ⟨u, hu, hu'⟩ := exists_evalW (pG ++ [mReps.getD i one8])
    (subB_spec (mE_spec hi).2).2.2.2.2 (unit_of_s7E (M7_gens_mem hi)) w
  rw [← colsOf_dec8 (valid8_evalW _ (subB_spec (mE_spec hi).2).2.2.2.2 w), ← hu']
  exact colsOf_mem_s7E (M7_le_s7 hi hu)

theorem mem_O7_iff {i : ℕ} (hi : i = 1 ∨ i = 2)
    (u : GL (Fin 8) (ZMod 2)) :
    u ∈ O7 i ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ oE i :=
  mem_genSub_iff_of (oB_spec.2 i (mem_one_two hi)).2.2.2.2.2.2.2.2.1
    (unit_of_s7E (O7_gens_mem (by omega))) u

theorem odd_orderOf_iff {M : Subgroup (GL (Fin 8) (ZMod 2))} (hM : Nat.card M = 48)
    {x : GL (Fin 8) (ZMod 2)} (hx : x ∈ M) : Odd (orderOf x) ↔ x ^ 3 = 1 := by
  have hd : orderOf x ∣ 48 := by
    rw [← hM, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  constructor
  · intro ho
    have hc : Nat.Coprime (orderOf x) 16 := by
      have := Nat.Coprime.pow_right 4 (Nat.coprime_two_right.mpr ho)
      simpa using this
    exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left (by simpa using hd))
  · intro h3
    rcases (Nat.dvd_prime (by norm_num)).mp (orderOf_dvd_of_pow_eq_one h3) with h | h <;>
      rw [h] <;> decide

theorem oTwoUpper_M7 {i : ℕ} (hi : i < 3) :
    oTwoUpper (M7 i) = O7 i := by
  unfold oTwoUpper O7 genSub
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine List.mem_filter.mpr ⟨(mem_M7_iff hi u).mp h1, ?_⟩
    rw [beq_iff_eq, ← colsOf_pow3, (odd_orderOf_iff (card_M7 hi) h1).mp h2, Units.val_one,
      colsOf_one]
  · intro h
    obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    have hu : u ∈ M7 i := (mem_M7_iff hi u).mpr h1
    refine ⟨hu, (odd_orderOf_iff (card_M7 hi) hu).mpr ?_⟩
    rw [beq_iff_eq, ← colsOf_pow3, ← colsOf_one, ← Units.val_one] at h2
    exact eq_of_colsOf_eq h2

theorem O7_vec {i : ℕ} (hi : i = 1 ∨ i = 2)
    {y : GL (Fin 8) (ZMod 2)} (hy : y ∈ O7 i) :
    (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) + vec8 vStar ∈
      ({0, vec8 (oWs.getD i (0, 0)).1, vec8 (oWs.getD i (0, 0)).2,
        vec8 (oWs.getD i (0, 0)).1 + vec8 (oWs.getD i (0, 0)).2} : Set (Fin 8 → ZMod 2)) := by
  have hmem := (oB_spec.2 i (mem_one_two hi)).2.2.2.1 _ ((mem_O7_iff hi y).mp hy)
  rw [mulVec_vec8, ← vec8_xor (mv8 _ vStar) vStar]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h <;> rw [h]
  · exact Or.inl vec8_zero
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (vec8_xor _ _)))

theorem exists_O7_of {i : ℕ} (hi : i = 1 ∨ i = 2) {c : List ℕ}
    (hc : c ∈ oE i) : ∃ u ∈ O7 i, (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  have hsub := (oB_spec.2 i (mem_one_two hi)).2.2.2.2.2.2.2.2.1
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  exact exists_evalW _ (subB_spec hsub).2.2.2.2 (unit_of_s7E (O7_gens_mem (by omega))) w

theorem O7_vec_eq {i : ℕ} (hi : i = 1 ∨ i = 2) :
    (∃ y ∈ O7 i, (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) + vec8 vStar =
      vec8 (oWs.getD i (0, 0)).1) ∧
    ∃ y ∈ O7 i, (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) + vec8 vStar =
      vec8 (oWs.getD i (0, 0)).2 := by
  have h := oB_spec.2 i (mem_one_two hi)
  constructor
  · obtain ⟨c, hc, hcw⟩ := h.2.2.2.2.1
    obtain ⟨u, hu, hu'⟩ := exists_O7_of hi hc
    exact ⟨u, hu, by rw [hu', dec8_mulVec, ← vec8_xor, hcw]⟩
  · obtain ⟨c, hc, hcw⟩ := h.2.2.2.2.2.1
    obtain ⟨u, hu, hu'⟩ := exists_O7_of hi hc
    exact ⟨u, hu, by rw [hu', dec8_mulVec, ← vec8_xor, hcw]⟩

theorem oWs_ne {i : ℕ} (hi : i = 1 ∨ i = 2) :
    vec8 (oWs.getD i (0, 0)).1 ≠ 0 ∧ vec8 (oWs.getD i (0, 0)).2 ≠ 0 ∧
      vec8 (oWs.getD i (0, 0)).1 ≠ vec8 (oWs.getD i (0, 0)).2 := by
  rcases hi with rfl | rfl <;> decide

theorem oWs_mem {i : ℕ} (hi : i = 1 ∨ i = 2)
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (hW : ∀ p ∈ eW, vec8 (mv8 p.1 p.2 ^^^ p.2) ∈ W) :
    vec8 (oWs.getD i (0, 0)).1 ∈ W ∧ vec8 (oWs.getD i (0, 0)).2 ∈ W := by
  have h := (oB_spec.2 i (mem_one_two hi)).2.2.2.2.2.2.1
  exact ⟨eSpan_mem W hW _ (h _ (by simp)), eSpan_mem W hW _ (h _ (by simp))⟩

theorem O7_b4 {i : ℕ} (hi : i = 1 ∨ i = 2) :
    ∃ y ∈ O7 i, ∃ v : ℕ, b4V ((y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 v) + vec8 v)
      (vec8 (oWs.getD i (0, 0)).1) = 1 := by
  obtain ⟨c, hc, v, -, hv⟩ := (oB_spec.2 i (mem_one_two hi)).2.2.2.2.2.2.2.1
  obtain ⟨u, hu, hu'⟩ := exists_O7_of hi hc
  refine ⟨u, hu, v, ?_⟩
  rw [hu', dec8_mulVec, ← vec8_xor, ← b4N_spec, hv]
  rfl

theorem O7_ne : O7 1 ≠ O7 2 := by
  intro h
  obtain ⟨y, hy, hyw⟩ := (O7_vec_eq (Or.inl rfl)).1
  have := O7_vec (Or.inr rfl) (h ▸ hy)
  rw [hyw] at this
  revert this
  decide

@[expose] def R7 (i : ℕ) (hi : i = 1 ∨ i = 2) :
    Subgroup (GL (Fin 8) (ZMod 2)) where
  carrier := {u | colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oE i)}
  one_mem' := by
    show colsOf ((1 : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oE i)
    rw [Units.val_one, colsOf_one]
    exact List.mem_filter.mpr
      ⟨(subB_spec (oB_spec.2 i (mem_one_two hi)).2.2.2.2.2.2.2.2.1).2.2.2.1, by decide⟩
  mul_mem' := fun {a b} ha hb => by
    show colsOf ((a * b : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oE i)
    rw [Units.val_mul, colsOf_mul]
    exact (oB_spec.2 i (mem_one_two hi)).2.2.2.2.2.2.2.2.2.2.2.1 _ ha _ hb
  inv_mem' := fun {a} ha => by
    show colsOf ((a⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oE i)
    have h4 : a ^ 4 = 1 := by
      have := (List.mem_filter.mp ha).2
      rw [beq_iff_eq, ← colsOf_pow4, ← colsOf_one, ← Units.val_one] at this
      exact eq_of_colsOf_eq this
    have hinv : a⁻¹ = a * (a * a) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv,
        show a * (a * a) * a = a ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc], h4]
    rw [hinv, Units.val_mul, Units.val_mul, colsOf_mul, colsOf_mul]
    have hc := (oB_spec.2 i (mem_one_two hi)).2.2.2.2.2.2.2.2.2.2.2.1
    exact hc _ ha _ (hc _ ha _ ha)

theorem mem_R7_iff {i : ℕ} (hi : i = 1 ∨ i = 2)
    (u : GL (Fin 8) (ZMod 2)) :
    u ∈ R7 i hi ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ twoOf (oE i) := Iff.rfl

theorem R7_le_O7 {i : ℕ} (hi : i = 1 ∨ i = 2) :
    R7 i hi ≤ O7 i :=
  fun u hu => (mem_O7_iff hi u).mpr (List.mem_filter.mp hu).1

theorem pow_four_of_R7 {i : ℕ} (hi : i = 1 ∨ i = 2)
    {u : GL (Fin 8) (ZMod 2)} (hu : u ∈ R7 i hi) : u ^ 4 = 1 := by
  have := (List.mem_filter.mp hu).2
  rw [beq_iff_eq, ← colsOf_pow4, ← colsOf_one, ← Units.val_one] at this
  exact eq_of_colsOf_eq this

theorem card_O7_eq {i : ℕ} (hi : i = 1 ∨ i = 2) :
    Nat.card (O7 i) = 3 * Nat.card (R7 i hi) := by
  have h := oB_spec.2 i (mem_one_two hi)
  have hsub := subB_spec h.2.2.2.2.2.2.2.2.1
  have hO : Nat.card (O7 i) = (oE i).length :=
    card_genSub_of h.2.2.2.2.2.2.2.2.1 (unit_of_s7E (O7_gens_mem (by omega)))
  have hR : Nat.card (R7 i hi) = (twoOf (oE i)).length := by
    refine card_of_cols (mem_R7_iff hi) h.2.2.2.2.2.2.2.2.2.1
      (fun x hx => hsub.1 x (List.mem_filter.mp hx).1) fun x hx => ?_
    obtain ⟨u, -, hu⟩ := exists_O7_of hi (List.mem_filter.mp hx).1
    exact ⟨u, hu⟩
  rw [hO, hR]
  exact h.2.2.2.2.2.2.2.2.2.2.1

theorem R7_normal {i : ℕ} (hi : i = 1 ∨ i = 2) :
    ((R7 i hi).subgroupOf (O7 i)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hgn : ((g * n * g⁻¹ : ↥(O7 i)) : GL (Fin 8) (ZMod 2)) ∈ O7 i := (g * n * g⁻¹).2
  have h4 : ((g * n * g⁻¹ : ↥(O7 i)) : GL (Fin 8) (ZMod 2)) ^ 4 = 1 := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, pow_four_of_R7 hi hn, mul_one, mul_inv_cancel]
  refine List.mem_filter.mpr ⟨(mem_O7_iff hi _).mp hgn, ?_⟩
  rw [beq_iff_eq, ← colsOf_pow4, h4, Units.val_one, colsOf_one]

theorem R7_isPGroup {i : ℕ} (hi : i = 1 ∨ i = 2) :
    IsPGroup 2 ↥((R7 i hi).subgroupOf (O7 i)) := by
  rintro ⟨⟨u, huO⟩, hu⟩
  refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
  simpa using pow_four_of_R7 hi (Subgroup.mem_subgroupOf.mp hu)

theorem pCore_O7 {i : ℕ} (hi : i = 1 ∨ i = 2) :
    CFSG.Open.pCore 2 ↥(O7 i) = (R7 i hi).subgroupOf (O7 i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun x hx => ?_)
    (CFSG.LieType.BorelTits.le_pCore 2 (R7_normal hi) (R7_isPGroup hi))
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(O7 i)) (r := 2)) ⟨x, hx⟩
  have hxn : (x : GL (Fin 8) (ZMod 2)) ^ 2 ^ n = 1 := by
    have := congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥(O7 i)) => ((y : ↥(O7 i)) :
      GL (Fin 8) (ZMod 2))) hn
    simpa using this
  have hxM : (x : GL (Fin 8) (ZMod 2)) ∈ M7 i := O7_le_M7 (by omega) x.2
  have h48 : orderOf (x : GL (Fin 8) (ZMod 2)) ∣ 48 := by
    rw [← card_M7 (i := i) (by omega), ← Subgroup.orderOf_mk _ hxM]
    exact orderOf_dvd_natCard _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxn)
  have h16 : orderOf (x : GL (Fin 8) (ZMod 2)) ∣ 16 := by
    rw [hk] at h48 ⊢
    have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    exact hc.dvd_of_dvd_mul_right (by simpa using h48)
  have hx16 : (x : GL (Fin 8) (ZMod 2)) ^ 16 = 1 := orderOf_dvd_iff_pow_eq_one.mp h16
  rw [Subgroup.mem_subgroupOf]
  have hc := (mem_O7_iff hi _).mp x.2
  refine List.mem_filter.mpr ⟨hc, ?_⟩
  rw [beq_iff_eq]
  refine (oB_spec.2 i (mem_one_two hi)).2.2.2.2.2.2.2.2.2.2.2.2 _ hc ?_
  rw [← colsOf_pow16, hx16, Units.val_one, colsOf_one]

theorem index_pCore_O7 {i : ℕ} (hi : i = 1 ∨ i = 2) :
    (CFSG.Open.pCore 2 ↥(O7 i)).index = 3 := by
  rw [pCore_O7 hi]
  have h := Subgroup.relIndex_mul_card (R7 i hi) (O7 i)
  rw [inf_eq_left.mpr (R7_le_O7 hi), card_O7_eq hi] at h
  have hpos : 0 < Nat.card (R7 i hi) := Nat.card_pos
  unfold Subgroup.relIndex at h
  nlinarith

theorem O7_sup_P7 {i : ℕ} (hi : i = 1 ∨ i = 2) :
    O7 i ⊔ P7 = M7 i := by
  have hi3 : i < 3 := by omega
  have hle : O7 i ⊔ P7 ≤ M7 i := sup_le (O7_le_M7 hi3) (P7_le_M7 i)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_M7 hi3]
  have h3 : 3 ∣ Nat.card ↥(O7 i ⊔ P7) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : O7 i ≤ O7 i ⊔ P7)
    rw [card_O7_eq hi] at this
    exact (Dvd.intro _ rfl).trans this
  have h16 : 16 ∣ Nat.card ↥(O7 i ⊔ P7) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : P7 ≤ O7 i ⊔ P7)
    rwa [card_P7] at this
  have h48 : 48 ∣ Nat.card ↥(O7 i ⊔ P7) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 16) h3 h16
  exact Nat.le_of_dvd Nat.card_pos h48

@[expose] def M12 : Subgroup (GL (Fin 8) (ZMod 2)) :=
  genSub (pG ++ [mReps.getD 1 one8, mReps.getD 2 one8])

theorem m12B_spec :
    subB (pG ++ [mReps.getD 1 one8, mReps.getD 2 one8]) m12E = true ∧
    (∀ x ∈ m12E, blkPerm blkA x ∈ perm3L ∧ blkPerm blkB x ∈ perm3L) ∧
    (∀ x ∈ m12E, ∀ y ∈ m12E,
      blkPerm blkA (mul8 x y) = compL (blkPerm blkA x) (blkPerm blkA y) ∧
        blkPerm blkB (mul8 x y) = compL (blkPerm blkB x) (blkPerm blkB y)) ∧
    (∀ l ∈ perm3L, ∀ l' ∈ perm3L, ∃ x ∈ m12E, blkPerm blkA x = l ∧ blkPerm blkB x = l') ∧
    ∀ x ∈ m12E, blkPerm blkA x = [0, 1, 2] → blkPerm blkB x = [0, 1, 2] → mul8 x x = one8 := by
  have h := s7Check_parts.2.2.2.2.2.2
  simp only [m12B, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
  refine ⟨a, fun x hx => ?_, c, fun l hl l' hl' => ?_, fun x hx h1 h2 => ?_⟩
  · simpa [List.contains_iff_mem] using b x hx
  · simpa [List.any_eq_true] using d l hl l' hl'
  · have := e x hx
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      beq_iff_eq] at this
    rcases this with (h | h) | h
    · exact absurd h1 h
    · exact absurd h2 h
    · exact h

theorem M12_gens_mem :
    ∀ g ∈ pG ++ [mReps.getD 1 one8, mReps.getD 2 one8], g ∈ s7E := by
  intro g hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl | rfl
  · exact pB_spec.2.2.1 g hg
  · exact mRep_mem (by norm_num)
  · exact mRep_mem (by norm_num)

theorem mem_M12_iff (u : GL (Fin 8) (ZMod 2)) :
    u ∈ M12 ↔ colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ m12E :=
  mem_genSub_iff_of m12B_spec.1 (unit_of_s7E M12_gens_mem) u

theorem sup_M7 : M7 1 ⊔ M7 2 = M12 := by
  apply le_antisymm
  · refine sup_le (Subgroup.closure_mono fun u hu => ?_) (Subgroup.closure_mono fun u hu => ?_)
    · simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hu ⊢
      tauto
    · simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hu ⊢
      tauto
  · refine (Subgroup.closure_le _).mpr fun u hu => ?_
    simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hu
    rcases hu with hu | hu | hu
    · exact Subgroup.mem_sup_left (P7_le_M7 1 (Subgroup.subset_closure hu))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp [hu]))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [hu]))

@[expose] def toPerm3 (l : List ℕ) : Equiv.Perm (Fin 3) :=
  if l = [1, 0, 2] then Equiv.swap 0 1 else if l = [0, 2, 1] then Equiv.swap 1 2
  else if l = [2, 1, 0] then Equiv.swap 0 2 else if l = [1, 2, 0] then finRotate 3
  else if l = [2, 0, 1] then (finRotate 3)⁻¹ else 1

theorem toPerm3_mul :
    ∀ l ∈ perm3L, ∀ l' ∈ perm3L, toPerm3 (compL l l') = toPerm3 l * toPerm3 l' := by
  decide

theorem toPerm3_surj : ∀ σ : Equiv.Perm (Fin 3), ∃ l ∈ perm3L, toPerm3 l = σ := by
  decide

theorem toPerm3_eq_one : ∀ l ∈ perm3L, toPerm3 l = 1 → l = [0, 1, 2] := by
  decide

theorem blkPerm_one : blkPerm blkA one8 = [0, 1, 2] ∧ blkPerm blkB one8 = [0, 1, 2] := by
  decide

@[expose] noncomputable def chi :
    ↥M12 →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) where
  toFun x := (toPerm3 (blkPerm blkA (colsOf ((x : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)))),
    toPerm3 (blkPerm blkB (colsOf ((x : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)))))
  map_one' := by
    simp only [OneMemClass.coe_one, Units.val_one, colsOf_one, blkPerm_one.1, blkPerm_one.2]
    rfl
  map_mul' x y := by
    have hx := (mem_M12_iff _).mp x.2
    have hy := (mem_M12_iff _).mp y.2
    simp only [Subgroup.coe_mul, Units.val_mul, colsOf_mul, (m12B_spec.2.2.1 _ hx _ hy).1,
      (m12B_spec.2.2.1 _ hx _ hy).2,
      toPerm3_mul _ (m12B_spec.2.1 _ hx).1 _ (m12B_spec.2.1 _ hy).1,
      toPerm3_mul _ (m12B_spec.2.1 _ hx).2 _ (m12B_spec.2.1 _ hy).2, Prod.mk_mul_mk]

theorem chi_surjective : Function.Surjective chi := by
  rintro ⟨σ, τ⟩
  obtain ⟨l, hl, rfl⟩ := toPerm3_surj σ
  obtain ⟨l', hl', rfl⟩ := toPerm3_surj τ
  obtain ⟨c, hc, hca, hcb⟩ := m12B_spec.2.2.2.1 l hl l' hl'
  obtain ⟨w, rfl⟩ := mem_elemsOf hc
  obtain ⟨u, hu, hu'⟩ := exists_evalW (pG ++ [mReps.getD 1 one8, mReps.getD 2 one8])
    (subB_spec m12B_spec.1).2.2.2.2 (unit_of_s7E M12_gens_mem) w
  have hcu : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      evalW (pG ++ [mReps.getD 1 one8, mReps.getD 2 one8]) w := by
    rw [hu', colsOf_dec8 (valid8_evalW (pG ++ [mReps.getD 1 one8, mReps.getD 2 one8])
      (subB_spec m12B_spec.1).2.2.2.2 w)]
  refine ⟨⟨u, hu⟩, ?_⟩
  show (toPerm3 (blkPerm blkA (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)))),
    toPerm3 (blkPerm blkB (colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))))) = _
  rw [hcu, hca, hcb]

theorem sq_eq_one_of_chi {x : ↥M12} (h : chi x = 1) :
    (x : GL (Fin 8) (ZMod 2)) * x = 1 := by
  have hx := (mem_M12_iff _).mp x.2
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change toPerm3 (blkPerm blkA (colsOf ((x : GL (Fin 8) (ZMod 2)) :
    Matrix (Fin 8) (Fin 8) (ZMod 2)))) = 1 at h1
  change toPerm3 (blkPerm blkB (colsOf ((x : GL (Fin 8) (ZMod 2)) :
    Matrix (Fin 8) (Fin 8) (ZMod 2)))) = 1 at h2
  have hsq := m12B_spec.2.2.2.2 _ hx (toPerm3_eq_one _ (m12B_spec.2.1 _ hx).1 h1)
    (toPerm3_eq_one _ (m12B_spec.2.1 _ hx).2 h2)
  apply eq_of_colsOf_eq
  rw [Units.val_mul, colsOf_mul, hsq, Units.val_one, colsOf_one]

end CFSG.Quasithin.H13.S7Cert
