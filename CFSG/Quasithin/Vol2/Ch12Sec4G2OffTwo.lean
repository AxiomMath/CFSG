module

public import CFSG.Quasithin.Vol2.Ch12Sec4G2OffCodes

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Orbit

section Sub

variable {B : Subgroup ↥(quasithinG2 (ZMod 2))}

theorem sEltG_zero : sEltG 0 = 1 := Subtype.ext sElt_zero

theorem zero_mem_idx : 0 ∈ idx B :=
  mem_idx.2 ⟨by norm_num, by rw [sEltG_zero]; exact one_mem B⟩

theorem matCode_mul_sElt {i j : ℕ} (hi : i < 64) (hj : j < 64) :
    matCode ⇑(sElt i * sElt j) = mmul (sM i) (sM j) := by
  rw [matCode_mul, matCode_sElt hi, matCode_sElt hj]

theorem idx_inv (hB2 : ∀ b ∈ B, b ^ 2 = 1) {i : ℕ} (hi : i ∈ idx B) (h0 : i ≠ 0) : i ∈ sInv := by
  have hi64 := (mem_idx.1 hi).1
  refine (sInv_spec i hi64).1 ⟨?_, h0⟩
  have h : sElt i * sElt i = 1 := by
    have := congrArg Subtype.val (hB2 _ (mem_idx.1 hi).2)
    rw [pow_two] at this
    exact this
  rw [← matCode_mul_sElt hi64 hi64, h, matCode_one]

theorem idx_comm (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {i j : ℕ} (hi : i ∈ idx B)
    (hj : j ∈ idx B) : mmul (sM i) (sM j) = mmul (sM j) (sM i) := by
  have h : sElt i * sElt j = sElt j * sElt i :=
    congrArg Subtype.val (hBc _ (mem_idx.1 hi).2 _ (mem_idx.1 hj).2)
  rw [← matCode_mul_sElt (mem_idx.1 hi).1 (mem_idx.1 hj).1, h,
    matCode_mul_sElt (mem_idx.1 hj).1 (mem_idx.1 hi).1]

theorem sCommB_of (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {i l : ℕ}
    (hi : i ∈ idx B) (hi0 : i ≠ 0) (hl : l ∈ idx B) : sCommB i l = true := by
  have hiInv := idx_inv hB2 hi hi0
  rw [sComm_spec i hiInv l (mem_idx.1 hl).1]
  have h1 : (l == 0 || decide (l ∈ sInv)) = true := by
    by_cases hl0 : l = 0
    · simp [hl0]
    · simp [idx_inv hB2 hl hl0]
  rw [h1, Bool.true_and, beq_iff_eq]
  exact idx_comm hBc hl hi

theorem idx_mul (hB : B ≤ sSubG) {i j : ℕ} (hi : i ∈ idx B) (hj : j ∈ idx B) :
    ∃ p ∈ idx B, sM p = mmul (sM i) (sM j) := by
  have hm : sEltG i * sEltG j ∈ B := mul_mem (mem_idx.1 hi).2 (mem_idx.1 hj).2
  obtain ⟨p, hp, hpe⟩ := mem_sSubG.1 (hB hm)
  refine ⟨p, mem_idx.2 ⟨hp, by rw [hpe]; exact hm⟩, ?_⟩
  have hpe' : sElt p = sElt i * sElt j := congrArg Subtype.val hpe
  rw [← matCode_sElt hp, ← matCode_mul_sElt (mem_idx.1 hi).1 (mem_idx.1 hj).1, hpe']

theorem card_idx_pow (hB : B ≤ sSubG) (hB2 : ∀ b ∈ B, b ^ 2 = 1) : ∃ n, (idx B).card = 2 ^ n := by
  have hp : IsPGroup 2 ↥B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB2 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  exact ⟨n, (card_eq_idx hB).symm.trans hn⟩

theorem pow_two_cases {m : ℕ} (h : ∃ n, m = 2 ^ n) : m = 1 ∨ m = 2 ∨ m = 4 ∨ 8 ≤ m := by
  obtain ⟨n, rfl⟩ := h
  rcases n with _ | _ | _ | n
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr ?_))
    exact le_trans (by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (show 3 ≤ n + 1 + 1 + 1 by omega))

theorem idx_eq_sE8 (hB : B ≤ sSubG) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h8 : 8 ≤ (idx B).card) :
    ∃ e < 8, ∀ l, l ∈ idx B ↔ l ∈ sE8.getD e [] := by
  classical
  obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton]; omega)
  obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, i} : Finset ℕ)) (t := idx B)
    (by have := Finset.card_le_two (a := 0) (b := i); omega)
  obtain ⟨p, hp, hpe⟩ := idx_mul hB hi hj
  obtain ⟨k, hk, hk0⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, i, j, p} : Finset ℕ)) (t := idx B)
    (by have := Finset.card_le_four (a := 0) (b := i) (c := j) (d := p); omega)
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0 hk0
  have hiI := idx_inv hB2 hi hi0
  have hjI := idx_inv hB2 hj hj0.1
  have hkI := idx_inv hB2 hk hk0.1
  have hkp : sM k ≠ mmul (sM i) (sM j) := by
    rw [← hpe]
    intro h
    exact hk0.2.2.2 (sMats_inj k (mem_idx.1 hk).1 p (mem_idx.1 hp).1 h)
  obtain ⟨e, he, hee⟩ := sTriple i hiI j hjI k hkI (sCommB_of hB2 hBc hi hi0 hj)
    (sCommB_of hB2 hBc hi hi0 hk) (sCommB_of hB2 hBc hj hj0.1 hk) (Ne.symm hj0.2)
    (Ne.symm hk0.2.1) (Ne.symm hk0.2.2.1) hkp
  have hsub : ∀ l ∈ idx B, l ∈ sE8.getD e [] := by
    intro l hl
    have h1 := sCommB_of hB2 hBc hi hi0 hl
    have h2 := sCommB_of hB2 hBc hj hj0.1 hl
    have h3 := sCommB_of hB2 hBc hk hk0.1 hl
    have h := sE8_spec e he l (mem_idx.1 hl).1
    rw [← hee, Nat.testBit_land, Nat.testBit_land] at h
    unfold sCommB at h1 h2 h3
    rw [h1, h2, h3] at h
    simpa using h.symm
  obtain ⟨hlen, hnd, -⟩ := sE8_len e he
  have hcard : (sE8.getD e []).toFinset.card = 8 := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have hsub' : idx B ⊆ (sE8.getD e []).toFinset := fun l hl => List.mem_toFinset.2 (hsub l hl)
  have heq : idx B = (sE8.getD e []).toFinset :=
    Finset.eq_of_subset_of_card_le hsub' (by rw [hcard]; exact h8)
  refine ⟨e, he, fun l => ?_⟩
  rw [heq, List.mem_toFinset]

theorem card_idx_le_8 (hB : B ≤ sSubG) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (h8 : 8 ≤ (idx B).card) : (idx B).card = 8 := by
  classical
  obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
  obtain ⟨hlen, hnd, -⟩ := sE8_len e he
  have heq : idx B = (sE8.getD e []).toFinset := by
    ext l
    rw [hiff, List.mem_toFinset]
  rw [heq, List.toFinset_card_of_nodup hnd, hlen]

end Sub

theorem mact_idMat : ∀ c < 256, mact idMat c = c := by
  decide +kernel

theorem mem_idx_bot {i : ℕ} : i ∈ idx (⊥ : Subgroup ↥(quasithinG2 (ZMod 2))) ↔ i = 0 := by
  rw [mem_idx, Subgroup.mem_bot]
  constructor
  · rintro ⟨hi, h⟩
    exact sEltG_injective hi (by norm_num) (h.trans sEltG_zero.symm)
  · rintro rfl
    exact ⟨by norm_num, sEltG_zero⟩

theorem card_ModO : Nat.card ModO = 128 := by
  have h := card_fixV_O (B := ⊥) bot_le (fun _ => true) fun c =>
    ⟨fun _ i hi => by
      rw [mem_idx_bot.1 hi, sM_zero]
      simp [fixOB, mact_idMat c.1 (mem_o0Codes.1 c.2).1], fun _ => rfl⟩
  rw [Subgroup.map_bot, B1.fixV_bot, Subgroup.card_top] at h
  rw [h]
  decide +kernel

theorem card_ModQ : Nat.card ModQ = 64 := by
  have h := card_fixV_Q (B := ⊥) bot_le (fun _ => true) fun c =>
    ⟨fun _ i hi => by
      rw [mem_idx_bot.1 hi, sM_zero]
      simp [fixQB, mact_idMat c.1 (mem_o0Codes.1 c.2).1], fun _ => rfl⟩
  rw [Subgroup.map_bot, B1.fixV_bot, Subgroup.card_top] at h
  rw [h]
  decide +kernel

section Sylow

variable {B : Subgroup ↥(quasithinG2 (ZMod 2))}

theorem length_filter_le {P Q : ℕ → Bool} (h : ∀ c, P c = true → Q c = true) :
    (o0Codes.filter P).length ≤ (o0Codes.filter Q).length :=
  (List.monotone_filter_right o0Codes h).length_le

theorem offender_sylow_O (hB : B ≤ sSubG) (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hff : 128 ≤ (idx B).card * Nat.card (fixV (B.map (g2OAct (ZMod 2))))) :
    commV (B.map (g2OAct (ZMod 2))) = fixV (B.map (g2OAct (ZMod 2))) := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixOB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixOB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_O hB P hP
  have hCi : ∀ i ∈ idx B, Nat.card (fixV (B.map (g2OAct (ZMod 2)))) ≤
      (o0Codes.filter (fixOB (sM i))).length := fun i hi => by
    rw [hC]
    exact length_filter_le fun c hc => by simp only [P, decide_eq_true_eq] at hc; exact hc i hi
  have hCij : ∀ i ∈ idx B, ∀ j ∈ idx B, Nat.card (fixV (B.map (g2OAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => fixOB (sM i) c && fixOB (sM j) c).length := fun i hi j hj => by
    rw [hC]
    refine length_filter_le fun c hc => ?_
    simp only [P, decide_eq_true_eq] at hc
    simp [hc i hi, hc j hj]
  have hsingle : ∀ i ∈ idx B, i ≠ 0 → (o0Codes.filter (fixOB (sM i))).length ≤ 32 := by
    intro i hi hi0
    rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
    · rw [(sInner_fix i h).1]
    · rw [(sOuter_fix i h).1]
      norm_num
  rcases pow_two_cases (card_idx_pow hB hB2) with hn | hn | hn | h8
  · exfalso
    exact hB1 (Subgroup.eq_bot_of_card_eq B (by rw [card_eq_idx hB, hn]))
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    rw [Finset.mem_singleton] at hi0
    have h1 := (hCi i hi).trans (hsingle i hi hi0)
    rw [hn] at hff
    omega
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, i} : Finset ℕ)) (t := idx B)
      (by have := Finset.card_le_two (a := 0) (b := i); rw [hn]; omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0
    rw [hn] at hff
    have hbound : Nat.card (fixV (B.map (g2OAct (ZMod 2)))) < 32 := by
      rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
      · rcases List.mem_append.1 (idx_inv hB2 hj hj0.1) with h' | h'
        · exact (hCij i hi j hj).trans_lt
            (sInner_pair i h j h' (Ne.symm hj0.2) (idx_comm hBc hi hj)).1
        · have := (hCi j hj).trans_eq (sOuter_fix j h').1
          omega
      · have := (hCi i hi).trans_eq (sOuter_fix i h).1
        omega
    omega
  · have hcard8 := card_idx_le_8 hB hB2 hBc h8
    obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
    have hfilter : (o0Codes.filter P) = sFixO.getD e [] := by
      rw [sFixO_spec e he]
      refine List.filter_congr fun c _ => ?_
      simp only [P]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
      exact forall_congr' fun i => imp_congr (hiff i) Iff.rfl
    have h16 : 16 ≤ (sFixO.getD e []).length := by
      rw [← hfilter, ← hC]
      rw [hcard8] at hff
      omega
    rcases sClaimO e he with hlt | ⟨hc1, hc2⟩
    · omega
    · refine commV_eq_fixV_O hB hiff (F := sFixO.getD e []) (fun c => ?_) hc1 fun f hf => ?_
      · rw [sFixO_spec e he, List.mem_filter, List.all_eq_true]
        simp only [c.2, true_and]
      · obtain ⟨w, -, hw⟩ := hc2 f hf
        exact ⟨w, hw⟩

theorem offender_sylow_Q (hB : B ≤ sSubG) (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hff : 64 ≤ (idx B).card * Nat.card (fixV (B.map (g2QAct (ZMod 2))))) :
    commV (B.map (g2QAct (ZMod 2))) = fixV (B.map (g2QAct (ZMod 2))) := by
  classical
  let P : ℕ → Bool := fun c => decide (∀ i ∈ idx B, fixQB (sM i) c = true)
  have hP : ∀ c : O0C, P c.1 = true ↔ ∀ i ∈ idx B, fixQB (sM i) c.1 = true := fun c => by
    simp [P]
  have hC := card_fixV_Q hB P hP
  have hCi : ∀ i ∈ idx B, Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length := fun i hi => by
    rw [hC]
    refine length_filter_le fun c hc => ?_
    simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [Bool.and_eq_true]
    exact ⟨hc.1, hc.2 i hi⟩
  have hCij : ∀ i ∈ idx B, ∀ j ∈ idx B, Nat.card (fixV (B.map (g2QAct (ZMod 2)))) ≤
      (o0Codes.filter fun c => !c.testBit 0 && (fixQB (sM i) c && fixQB (sM j) c)).length :=
    fun i hi j hj => by
      rw [hC]
      refine length_filter_le fun c hc => ?_
      simp only [P, Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨hc.1, hc.2 i hi, hc.2 j hj⟩
  have hsingle : ∀ i ∈ idx B, i ≠ 0 →
      (o0Codes.filter fun c => !c.testBit 0 && fixQB (sM i) c).length ≤ 16 := by
    intro i hi hi0
    rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
    · rw [(sInner_fix i h).2]
    · rw [(sOuter_fix i h).2]
      norm_num
  rcases pow_two_cases (card_idx_pow hB hB2) with hn | hn | hn | h8
  · exfalso
    exact hB1 (Subgroup.eq_bot_of_card_eq B (by rw [card_eq_idx hB, hn]))
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    rw [Finset.mem_singleton] at hi0
    have h1 := (hCi i hi).trans (hsingle i hi hi0)
    rw [hn] at hff
    omega
  · exfalso
    obtain ⟨i, hi, hi0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0} : Finset ℕ)) (t := idx B) (by rw [Finset.card_singleton, hn]; norm_num)
    obtain ⟨j, hj, hj0⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, i} : Finset ℕ)) (t := idx B)
      (by have := Finset.card_le_two (a := 0) (b := i); rw [hn]; omega)
    simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hi0 hj0
    rw [hn] at hff
    have hbound : Nat.card (fixV (B.map (g2QAct (ZMod 2)))) < 16 := by
      rcases List.mem_append.1 (idx_inv hB2 hi hi0) with h | h
      · rcases List.mem_append.1 (idx_inv hB2 hj hj0.1) with h' | h'
        · exact (hCij i hi j hj).trans_lt
            (sInner_pair i h j h' (Ne.symm hj0.2) (idx_comm hBc hi hj)).2
        · have := (hCi j hj).trans_eq (sOuter_fix j h').2
          omega
      · have := (hCi i hi).trans_eq (sOuter_fix i h).2
        omega
    omega
  · have hcard8 := card_idx_le_8 hB hB2 hBc h8
    obtain ⟨e, he, hiff⟩ := idx_eq_sE8 hB hB2 hBc h8
    have hfilter : (o0Codes.filter fun c => !c.testBit 0 && P c) =
        o0Codes.filter fun c => !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c := by
      refine List.filter_congr fun c _ => ?_
      congr 1
      simp only [P]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true]
      exact forall_congr' fun i => imp_congr (hiff i) Iff.rfl
    have h8' : 8 ≤ (o0Codes.filter fun c =>
        !c.testBit 0 && (sE8.getD e []).all fun i => fixQB (sM i) c).length := by
      rw [← hfilter, ← hC]
      rw [hcard8] at hff
      omega
    rcases sClaimQ e he with hlt | ⟨hc1, hc2⟩
    · omega
    · refine commV_eq_fixV_Q hB hiff (F := sFixQ.getD e []) (fun c => ?_) hc1 fun f hf => ?_
      · rw [sFixQ_spec e he, List.mem_filter, List.all_eq_true]
        simp only [c.2, true_and]
      · obtain ⟨w, -, hw⟩ := hc2 f hf
        exact ⟨w, hw⟩

end Sylow

theorem decodeZ_one_eq_mul : decodeZ 1 = quasithinZornMul (decodeZ 2) (decodeZ 16) := by
  decide

theorem decodeZ_128 : decodeZ 128 = decodeZ 129 + decodeZ 1 := by
  decide

theorem norm_xor_129 : ∀ c ∈ o0Codes, zornNorm (decodeZ (c ^^^ 129)) ≠ zornNorm (decodeZ c) := by
  decide +kernel

theorem eq_one_of_fix_o0 {g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)}
    (hg : g ∈ quasithinG2 (ZMod 2)) (hfix : ∀ c ∈ o0Codes, g (decodeZ c) = decodeZ c) : g = 1 := by
  have hz := mem_quasithinG2_isZornAuto hg
  have h1 : g (decodeZ 1) = decodeZ 1 := by
    rw [decodeZ_one_eq_mul, hz, hfix 2 (by decide), hfix 16 (by decide)]
  have h128 : g (decodeZ 128) = decodeZ 128 := by
    rw [decodeZ_128, map_add, hfix 129 (by decide), h1]
  apply linearEquiv_eq_of_matCode
  rw [matCode_one]
  unfold matCode
  have hk : ∀ k ∈ List.range 8, encodeZ (g (decodeZ (2 ^ k))) = 2 ^ k := by
    intro k hk
    rw [List.mem_range] at hk
    have hfix' : g (decodeZ (2 ^ k)) = decodeZ (2 ^ k) := by
      interval_cases k
      · exact h1
      · exact hfix _ (by decide)
      · exact hfix _ (by decide)
      · exact hfix _ (by decide)
      · exact hfix _ (by decide)
      · exact hfix _ (by decide)
      · exact hfix _ (by decide)
      · exact h128
    rw [hfix', encodeZ_decodeZ _ (by
      have : 2 ^ k < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hk
      simpa using this)]
  rw [List.map_congr_left hk]
  decide

theorem g2OAct_injective : Function.Injective (g2OAct (ZMod 2)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine eq_one_of_fix_o0 g.2 fun c hc => ?_
  have h := congrArg (fun x : MulAut ModO => x (codeO ⟨c, hc⟩)) hg
  simp only [MulAut.one_apply] at h
  rw [g2OAct_codeO] at h
  have h2 := congrArg Subtype.val (codeO_injective h)
  change mact (matCode g.1) c = c at h2
  rw [← decodeZ_mact' g.1 (mem_o0Codes.1 hc).1, h2]

theorem g2QAct_injective : Function.Injective (g2QAct (ZMod 2)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine eq_one_of_fix_o0 g.2 fun c hc => ?_
  have h := congrArg (fun x : MulAut ModQ => x (codeQ ⟨c, hc⟩)) hg
  simp only [MulAut.one_apply] at h
  rw [g2QAct_codeQ, codeQ_eq_iff] at h
  have hn := quasithinG2_norm g.2 (decodeZ c)
  rw [← decodeZ_mact' g.1 (mem_o0Codes.1 hc).1]
  rcases h with h | h
  · change c = mact (matCode g.1) c at h
    rw [← h]
  · exfalso
    change c = mact (matCode g.1) c ^^^ 129 at h
    have hm : mact (matCode g.1) c = c ^^^ 129 := by
      conv_rhs => rw [h]
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [← decodeZ_mact' g.1 (mem_o0Codes.1 hc).1, hm] at hn
    exact norm_xor_129 c hc hn

end CFSG.Quasithin.H13
