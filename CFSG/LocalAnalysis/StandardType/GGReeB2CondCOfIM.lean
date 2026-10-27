module

public import CFSG.LocalAnalysis.StandardType.GGReeB2LamArith

public section

namespace CFSG.StandardType.ReeB2Fixed

private theorem two_pow_e_eq_one (e : ℕ) : (2 : ZMod (2 ^ e - 1)) ^ e = 1 := by
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  rw [show (2 : ZMod (2 ^ e - 1)) = ((2 : ℕ) : ZMod (2 ^ e - 1)) by norm_num]
  rw [← Nat.cast_pow, ← Nat.sub_add_cancel h1, Nat.cast_add, ZMod.natCast_self,
    zero_add, Nat.cast_one]

private theorem pow_eq_pow_mod_zmod (e k : ℕ) :
    (2 : ZMod (2 ^ e - 1)) ^ k = 2 ^ (k % e) :=
  pow_eq_pow_mod k (two_pow_e_eq_one e)

private theorem two_pow_succσ (e : ℕ) (p : Fin e) :
    (2 : ZMod (2 ^ e - 1)) ^ (succσ e p : ℕ) =
      2 ^ (p : ℕ) * 2 ^ ((e + 1) / 2) := by
  have hval : (succσ e p : ℕ) = ((p : ℕ) + (e + 1) / 2) % e := rfl
  rw [hval, ← pow_eq_pow_mod_zmod e ((p : ℕ) + (e + 1) / 2), pow_add]

private theorem r_mul_theta (e : ℕ) (he : Odd e) :
    (2 : ZMod (2 ^ e - 1)) ^ ((e + 1) / 2) * 2 ^ ((e - 1) / 2) = 1 := by
  obtain ⟨m, rfl⟩ := he
  rw [← pow_add,
    show (2 * m + 1 + 1) / 2 + (2 * m + 1 - 1) / 2 = 2 * m + 1 by omega,
    two_pow_e_eq_one]

private theorem two_pow_eq_succσ_mul (e : ℕ) (he : Odd e) (p : Fin e) :
    (2 : ZMod (2 ^ e - 1)) ^ (p : ℕ) =
      2 ^ (succσ e p : ℕ) * 2 ^ ((e - 1) / 2) := by
  rw [two_pow_succσ e p, mul_assoc, r_mul_theta e he, mul_one]

private theorem succσ_injective (e : ℕ) : Function.Injective (succσ e) := by
  intro p q hpq
  have hv : ((p : ℕ) + (e + 1) / 2) % e = ((q : ℕ) + (e + 1) / 2) % e := by
    have := congrArg Fin.val hpq
    simpa [succσ] using this
  have hmod : ((p : ℕ) + (e + 1) / 2) ≡ ((q : ℕ) + (e + 1) / 2) [MOD e] := hv
  have hmod' : (p : ℕ) ≡ (q : ℕ) [MOD e] := Nat.ModEq.add_right_cancel' _ hmod
  exact Fin.ext (hmod'.eq_of_lt_of_lt p.isLt q.isLt)

private theorem S_digits (e : ℕ) (he : 0 < e) (x : ZMod (2 ^ e - 1)) :
    S e (digits e x) = x := by
  haveI : NeZero (2 ^ e - 1) := ⟨by
    have h1 : 1 < 2 ^ e := by
      calc
        1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega⟩
  dsimp only [S, digits]
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if x.val.testBit j then (2 : ZMod (2 ^ e - 1)) ^ j else 0)]
  have hbits : x.val.bitIndices.toFinset ⊆ Finset.range e := by
    intro i hi
    rw [Finset.mem_range]
    by_contra hge
    push Not at hge
    have hmem : i ∈ x.val.bitIndices := by simpa using hi
    have hle : 2 ^ i ≤ x.val := Nat.two_pow_le_of_mem_bitIndices hmem
    have hlt : x.val < 2 ^ e := lt_of_lt_of_le (ZMod.val_lt x) (Nat.sub_le _ _)
    have hpow : 2 ^ e ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hge
    omega
  have hT : (∑ j ∈ Finset.range e, (if x.val.testBit j then (2 : ℕ) ^ j else 0)) = x.val := by
    calc
      (∑ j ∈ Finset.range e, (if x.val.testBit j then (2 : ℕ) ^ j else 0))
          = ∑ j ∈ Finset.range e,
              (if j ∈ x.val.bitIndices.toFinset then (2 : ℕ) ^ j else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            have hb : x.val.testBit j ↔ j ∈ x.val.bitIndices.toFinset := by
              rw [← Nat.mem_bitIndices, List.mem_toFinset]
            simp only [hb]
      _ = ∑ j ∈ x.val.bitIndices.toFinset,
              (if j ∈ x.val.bitIndices.toFinset then (2 : ℕ) ^ j else 0) :=
            (Finset.sum_subset hbits (fun j _ hj' => by simp [hj'])).symm
      _ = ∑ j ∈ x.val.bitIndices.toFinset, (2 : ℕ) ^ j := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [hj]
      _ = x.val := Finset.sum_toFinset_bitIndices_two_pow x.val
  have hcast :
      (∑ j ∈ Finset.range e,
          (if x.val.testBit j then (2 : ZMod (2 ^ e - 1)) ^ j else 0))
        = ((∑ j ∈ Finset.range e,
              (if x.val.testBit j then (2 : ℕ) ^ j else 0) : ℕ) : ZMod (2 ^ e - 1)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hp : x.val.testBit j
    · rw [if_pos hp, if_pos hp]
      norm_cast
    · rw [if_neg hp, if_neg hp]
      simp
  rw [hcast, hT]
  exact ZMod.natCast_zmod_val x

private theorem exists_indep_subset (e : ℕ) (he : Odd e) (A : Finset (Fin e)) :
    ∃ A' ⊆ A, IndepSigma e A' ∧ Lam e A' ⊆ Lam e A := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hI : IndepSigma e A
    · exact ⟨A, fun x hx => hx, hI, fun x hx => hx⟩
    · rw [IndepSigma] at hI
      push Not at hI
      obtain ⟨p, hp, hq⟩ := hI
      obtain ⟨A', hA'sub, hI', hLam'⟩ := ih (A.erase (succσ e p)) (Finset.erase_ssubset hq)
      refine ⟨A', hA'sub.trans (Finset.erase_subset _ _), hI', hLam'.trans ?_⟩
      exact lam_erase_succ_subset e he A p hp hq

private theorem neg_term_true (e : ℕ) (he : Odd e) (p : Fin e) :
    -(term e true p) = (2 ^ ((e - 1) / 2) - 1) * 2 ^ (succσ e p : ℕ) := by
  have h : (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) * 2 ^ ((e + 1) / 2) = 1 := by
    rw [mul_comm, r_mul_theta e he]
  simp only [term, if_true, R, two_pow_succσ e p]
  calc
    -(2 ^ (p : ℕ) * (2 ^ ((e + 1) / 2) - 1))
        = 2 ^ (p : ℕ) - 2 ^ (p : ℕ) * 2 ^ ((e + 1) / 2) := by ring
    _ = ((2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) - 1)
          * (2 ^ (p : ℕ) * 2 ^ ((e + 1) / 2))
        + (1 - (2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2)
            * 2 ^ ((e + 1) / 2)) * 2 ^ (p : ℕ) := by ring
    _ = ((2 : ZMod (2 ^ e - 1)) ^ ((e - 1) / 2) - 1)
          * (2 ^ (p : ℕ) * 2 ^ ((e + 1) / 2)) := by rw [h]; ring

private theorem neg_term_false (e : ℕ) (p : Fin e) :
    -(term e false p) = (-1) * 2 ^ (p : ℕ) := by
  simp only [term, Bool.false_eq_true, if_false]
  ring

private theorem neg_term_false_not_mem (e : ℕ) (he : Odd e) (p : Fin e) :
    -(term e false p) = (-(2 ^ ((e - 1) / 2))) * 2 ^ (succσ e p : ℕ) := by
  simp only [term, Bool.false_eq_true, if_false]
  rw [two_pow_eq_succσ_mul e he p]
  ring

private theorem neg_sum_mem_delta (e : ℕ) (he : Odd e) (A' : Finset (Fin e))
    (t : Fin e → Bool) (U : Finset (Fin e)) (hI : IndepSigma e A')
    (hSlots : Slots e A' t U) :
    -(∑ p ∈ A', term e (t p) p) ∈ Delta e U := by
  classical
  let slot : Fin e → Fin e := fun p =>
    if t p then succσ e p else if p ∈ U then p else succσ e p
  let dd : Fin e → ZMod (2 ^ e - 1) := fun p =>
    if t p then 2 ^ ((e - 1) / 2) - 1 else if p ∈ U then -1 else -2 ^ ((e - 1) / 2)
  let d : Fin e → ZMod (2 ^ e - 1) := fun j =>
    if h : ∃ p ∈ A', slot p = j then dd (Classical.choose h) else 0
  have hslot_mem : ∀ p ∈ A', slot p ∈ U := by
    intro p hp
    have hs := hSlots p hp
    dsimp only [slot]
    by_cases ht : t p = true
    · rw [if_pos ht] at hs ⊢
      exact hs
    · rw [if_neg ht] at hs ⊢
      by_cases hpu : p ∈ U
      · rw [if_pos hpu]
        exact hpu
      · rw [if_neg hpu]
        exact hs.resolve_left hpu
  have hslot_inj : Set.InjOn slot A' := by
    intro p hp p' hp' heq
    by_cases hpp' : p = p'
    · exact hpp'
    · have hsp : slot p = p ∨ slot p = succσ e p := by
        dsimp only [slot]
        by_cases ht : t p = true
        · rw [if_pos ht]; exact Or.inr rfl
        · rw [if_neg ht]
          by_cases hpu : p ∈ U
          · rw [if_pos hpu]; exact Or.inl rfl
          · rw [if_neg hpu]; exact Or.inr rfl
      have hsp' : slot p' = p' ∨ slot p' = succσ e p' := by
        dsimp only [slot]
        by_cases ht : t p' = true
        · rw [if_pos ht]; exact Or.inr rfl
        · rw [if_neg ht]
          by_cases hpu : p' ∈ U
          · rw [if_pos hpu]; exact Or.inl rfl
          · rw [if_neg hpu]; exact Or.inr rfl
      rcases hsp with h | h <;> rcases hsp' with h' | h' <;> rw [h, h'] at heq
      · exact absurd heq hpp'
      · exact absurd (heq ▸ hp) (hI p' hp')
      · exact absurd (heq.symm ▸ hp') (hI p hp)
      · exact absurd (succσ_injective e heq) hpp'
  have hd_slot : ∀ p ∈ A', d (slot p) = dd p := by
    intro p hp
    have hex : ∃ q ∈ A', slot q = slot p := ⟨p, hp, rfl⟩
    dsimp only [d]
    rw [dif_pos hex]
    have hq := Classical.choose_spec hex
    have hchoose : Classical.choose hex = p := hslot_inj hq.1 hp hq.2
    rw [hchoose]
  have hdd_mem : ∀ p ∈ A', dd p ∈
      ({0, -1, 2 ^ ((e - 1) / 2) - 1, -2 ^ ((e - 1) / 2)} :
        Finset (ZMod (2 ^ e - 1))) := by
    intro p _
    dsimp only [dd]
    by_cases ht : t p = true
    · rw [if_pos ht]
      simp
    · rw [if_neg ht]
      by_cases hpu : p ∈ U
      · rw [if_pos hpu]
        simp
      · rw [if_neg hpu]
        simp
  have hd_mem : ∀ j ∈ U, d j ∈
      ({0, -1, 2 ^ ((e - 1) / 2) - 1, -2 ^ ((e - 1) / 2)} :
        Finset (ZMod (2 ^ e - 1))) := by
    intro j _
    by_cases hex : ∃ p ∈ A', slot p = j
    · dsimp only [d]
      rw [dif_pos hex]
      exact hdd_mem (Classical.choose hex) (Classical.choose_spec hex).1
    · dsimp only [d]
      rw [dif_neg hex]
      simp
  have hterm : ∀ p ∈ A', -(term e (t p) p) = dd p * 2 ^ (slot p : ℕ) := by
    intro p _
    dsimp only [slot, dd]
    by_cases ht : t p = true
    · rw [if_pos ht, if_pos ht, ht]
      exact neg_term_true e he p
    · have htf : t p = false := Bool.eq_false_of_not_eq_true ht
      rw [if_neg ht, if_neg ht, htf]
      by_cases hpu : p ∈ U
      · simp only [if_pos hpu]
        rw [neg_term_false]
      · simp only [if_neg hpu]
        exact neg_term_false_not_mem e he p
  have hsum : -(∑ p ∈ A', term e (t p) p) = ∑ j ∈ U, d j * 2 ^ (j : ℕ) := by
    rw [← Finset.sum_neg_distrib]
    calc
      ∑ p ∈ A', -(term e (t p) p) = ∑ p ∈ A', dd p * 2 ^ (slot p : ℕ) :=
        Finset.sum_congr rfl hterm
      _ = ∑ j ∈ A'.image slot, d j * 2 ^ (j : ℕ) := by
        rw [Finset.sum_image hslot_inj]
        exact Finset.sum_congr rfl (fun p hp => by rw [hd_slot p hp])
      _ = ∑ j ∈ U, d j * 2 ^ (j : ℕ) := by
        refine Finset.sum_subset ?_ ?_
        · intro j hj
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
          exact hslot_mem p hp
        · intro j _ hjnot
          have hdj : d j = 0 := by
            dsimp only [d]
            rw [dif_neg]
            rintro ⟨p, hp, hps⟩
            exact hjnot (Finset.mem_image.mpr ⟨p, hp, hps⟩)
          rw [hdj, zero_mul]
  rw [Delta]
  exact ⟨d, hd_mem, hsum⟩

theorem condC_of_IM (e : ℕ) (he : Odd e) (h3 : 3 ≤ e) (h : IM e) : CondC e := by
  classical
  intro A B hAB
  obtain ⟨hGoodA, hGoodB, hDisjAB⟩ := hAB
  obtain ⟨A', hA'sub, hI, hLam_sub⟩ := exists_indep_subset e he A
  have hepos : 0 < e := by
    obtain ⟨m, hm⟩ := he
    omega
  have hGoodA' : Good e A' := fun h0 => hGoodA (hLam_sub h0)
  have hDisjA' : Disjoint (Lam e A') (Lam e B) :=
    Set.disjoint_of_subset_left hLam_sub hDisjAB
  have hAB' : Admissible e A' B := ⟨hGoodA', hGoodB, hDisjA'⟩
  obtain ⟨t, hSlots⟩ := h A' B hI hAB'
  set s : ZMod (2 ^ e - 1) := ∑ p ∈ A', term e (t p) p with hs
  have hkappaA' : -s ∈ Lam e A' := by
    refine ⟨fun p => -(if t p then R e else 1), ?_, ?_⟩
    · intro p _
      dsimp only
      by_cases ht : t p = true
      · rw [if_pos ht]
        simp [units]
      · rw [if_neg ht]
        simp [units]
    · rw [hs, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p _
      dsimp only
      by_cases ht : t p = true
      · rw [if_pos ht, ht]
        rw [term]
        simp only [if_true]
        ring
      · have htf : t p = false := Bool.eq_false_of_not_eq_true ht
        rw [if_neg ht, htf]
        rw [term]
        simp only [Bool.false_eq_true, if_false]
        ring
  refine ⟨-s, hLam_sub hkappaA', ?_⟩
  set U : Finset (Fin e) := digits e (S e B + s) with hU
  set V : Finset (Fin e) := digits e (S e B - s) with hV
  have harg1 : digits e (S e B - -s) = U := by
    rw [sub_neg_eq_add, ← hU]
  have harg2 : digits e (S e B + -s) = V := by
    rw [← sub_eq_add_neg, ← hV]
  rw [harg1, harg2]
  intro hUV
  obtain ⟨_, _, hDisjUV⟩ := hUV
  have hyV : (S e B - s) ∈ Lam e V := by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro j _
      simp [units]
    · have hSV : S e V = S e B - s := by rw [hV, S_digits e hepos]
      rw [← hSV]
      simp only [S, one_mul]
  have hyU : (S e B - s) ∈ Lam e U := by
    rw [lam_eq_S_add_two_delta e he U]
    refine ⟨-s, ?_, ?_⟩
    · exact neg_sum_mem_delta e he A' t U hI hSlots
    · have hSU : S e U = S e B + s := by rw [hU, S_digits e hepos]
      rw [hSU]
      ring
  exact (Set.disjoint_left.mp hDisjUV) hyU hyV

end CFSG.StandardType.ReeB2Fixed
