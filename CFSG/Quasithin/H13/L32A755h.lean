module

public import CFSG.Quasithin.H13.L32A755g

public section

namespace CFSG.Quasithin.H13.L32A.M755

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 Orbit

@[expose] def qCodes : List ℕ := (List.range 64).map (2 * ·)

@[expose] def u0Codes : List ℕ := [0, 8, 16, 24, 32, 40, 48, 56]

@[expose] def w0Codes : List ℕ := (List.range 32).map (2 * ·)

@[expose] def lineB (b : ℕ) : List ℕ :=
  if b = 2 then [0, 8, 16, 24] else if b = 4 then [0, 8, 32, 40] else [0, 8, 48, 56]

@[expose] def actC (g c : ℕ) : ℕ := if g = 64 then nq (mact z1Mat c) else nq (mact (sM g) c)

@[expose] def spanL : List ℕ → List ℕ
  | [] => [0]
  | g :: l => spanL l ++ (spanL l).map (· ^^^ g)

@[expose] def invG1 : List ℕ := [0, 64, 1, 1, 0, 64, 1, 1, 0, 64, 1, 1, 0, 64, 1, 1, 0, 64, 1, 1,
  0, 64, 1, 1, 0, 64, 1, 1, 0, 64, 1, 1, 24, 24, 1, 1, 24, 24, 1, 1, 24, 24, 1, 1, 24, 24, 1, 1,
  24, 24, 1, 1, 24, 24, 1, 1, 24, 24, 1, 1, 24, 24, 1, 1]

@[expose] def invG2 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 40, 24, 24, 40, 40, 24, 24, 40, 40, 24, 24, 40, 40, 24, 24, 40,
  40, 24, 24, 40, 40, 24, 24, 40, 40, 24, 24, 40, 40, 24, 24]

theorem qCodes_mem : ∀ c ∈ qCodes, c ∈ o0Codes ∧ (c = 0 ∨ c ∈ ptsQ) := by
  decide +kernel

theorem qCodes_xor : ∀ c ∈ qCodes, ∀ d ∈ qCodes, (c ^^^ d) ∈ qCodes := by
  decide +kernel

theorem actC_mem : ∀ g ∈ [0, 1, 2, 4, 6, 8, 10, 12, 14, 24, 40, 64], ∀ c ∈ qCodes,
    actC g c ∈ qCodes := by
  decide +kernel

theorem facts_B0 : ∀ b ∈ [2, 4, 6], ∀ c ∈ qCodes,
    (actC b c ^^^ c) ∈ lineB b ∧ (c ∈ w0Codes → (actC b c ^^^ c) ∈ [0, 8]) := by
  decide +kernel

theorem facts_B0_onto : ∀ b ∈ [2, 4, 6], ∀ d ∈ lineB b, ∃ c ∈ qCodes, actC b c ^^^ c = d := by
  decide +kernel

theorem facts_A0_onto : ∀ a ∈ [8, 10, 12, 14], ∀ d ∈ u0Codes, ∃ c ∈ qCodes, actC a c ^^^ c = d := by
  decide +kernel

theorem facts_CB0 : ∀ c ∈ qCodes,
    ((actC 2 c = c ∧ actC 4 c = c ∧ actC 6 c = c) ↔ c ∈ u0Codes) := by
  decide +kernel

theorem facts_wA0 : ∀ c ∈ w0Codes, c ∉ u0Codes → ∃ b ∈ [2, 4, 6],
    (∀ a ∈ [0, 2, 4, 6, 8, 10, 12, 14], (actC a c ^^^ c) ∈ lineB b) ∧
    ∀ d ∈ lineB b, ∃ a ∈ [0, 2, 4, 6, 8, 10, 12, 14], actC a c ^^^ c = d := by
  decide +kernel

theorem facts_inv : ∀ k < 64, (2 * k) ∉ u0Codes → ∀ d ∈ (if k < 32 then w0Codes else qCodes),
    d ∈ spanL [8, 16, 32, 2 * k, actC (invG1.getD k 0) (2 * k), actC (invG2.getD k 0) (2 * k)] := by
  decide +kernel

theorem ptsQ_qCodes : ∀ c ∈ ptsQ, c ∈ qCodes := by
  decide +kernel

theorem invG_mem : ∀ k < 64, invG1.getD k 0 ∈ [0, 1, 24, 40, 64] ∧
    invG2.getD k 0 ∈ [0, 1, 24, 40, 64] := by
  decide +kernel

theorem actC_zero : ∀ c ∈ qCodes, actC 0 c = c := by
  decide +kernel

theorem ptQ_zero : ptQ 0 = 1 := by
  rw [ptQ_eq_codeQ zero_mem_o0Codes, ← codeQ_zero]
  rfl

theorem exists_code (q : ModQ) : ∃ c ∈ qCodes, ptQ c = q := by
  by_cases hq : q = 1
  · exact ⟨0, by decide, hq ▸ ptQ_zero⟩
  · obtain ⟨c, hc, rfl⟩ := exists_ptQ hq
    exact ⟨c, ptsQ_qCodes c hc, rfl⟩

theorem ptQ_inj {c d : ℕ} (hc : c ∈ qCodes) (hd : d ∈ qCodes) (h : ptQ c = ptQ d) : c = d := by
  rcases (qCodes_mem c hc).2 with rfl | hc'
  · rcases (qCodes_mem d hd).2 with rfl | hd'
    · rfl
    · exact absurd (h.symm.trans ptQ_zero) (ptQ_ne_one hd')
  · rcases (qCodes_mem d hd).2 with rfl | hd'
    · exact absurd (h.trans ptQ_zero) (ptQ_ne_one hc')
    · exact ptQ_injective hc' hd' h

theorem ptQ_xor {c d : ℕ} (hc : c ∈ qCodes) (hd : d ∈ qCodes) :
    ptQ (c ^^^ d) = ptQ c * ptQ d :=
  (ptQ_mul (qCodes_mem c hc).1 (qCodes_mem d hd).1).symm

theorem g2QAct_sEltG_code {i : ℕ} (hi : i < 64) {c : ℕ} (hc : c ∈ qCodes) :
    g2QAct (ZMod 2) (sEltG i) (ptQ c) = ptQ (actC i c) := by
  have hc0 := (qCodes_mem c hc).1
  have hi64 : i ≠ 64 := by omega
  rw [g2QAct_ptQ _ hc0, actC, ite_eq_right hi64, matCode_sEltG hi,
    ptQ_nq (mact_mem_o0Codes (sEltG i).2 hc0 |> fun h => by rwa [matCode_sEltG hi] at h)]

theorem g2QAct_z1_code {c : ℕ} (hc : c ∈ qCodes) :
    g2QAct (ZMod 2) z1 (ptQ c) = ptQ (actC 64 c) := by
  have hc0 := (qCodes_mem c hc).1
  rw [g2QAct_ptQ _ hc0, actC, ite_eq_left rfl, matCode_z1,
    ptQ_nq (mact_mem_o0Codes z1.2 hc0 |> fun h => by rwa [matCode_z1] at h)]

@[expose] def InU0 (q : ModQ) : Prop := ∃ c ∈ u0Codes, ptQ c = q

@[expose] def InW0 (q : ModQ) : Prop := ∃ c ∈ w0Codes, ptQ c = q

theorem mem_of_spanL {Y : Subgroup ModQ} :
    ∀ L : List ℕ, (∀ g ∈ L, g ∈ qCodes ∧ ptQ g ∈ Y) → ∀ d ∈ spanL L, d ∈ qCodes ∧ ptQ d ∈ Y
  | [], _, d, hd => by
    simp only [spanL, List.mem_singleton] at hd
    subst hd
    exact ⟨by decide, ptQ_zero ▸ Y.one_mem⟩
  | g :: l, hL, d, hd => by
    have ih := mem_of_spanL l fun g' hg' => hL g' (List.mem_cons_of_mem _ hg')
    rw [spanL, List.mem_append, List.mem_map] at hd
    rcases hd with hd | ⟨d', hd', rfl⟩
    · exact ih d hd
    · obtain ⟨h1, h2⟩ := ih d' hd'
      obtain ⟨hg1, hg2⟩ := hL g List.mem_cons_self
      exact ⟨qCodes_xor _ h1 _ hg1, by rw [ptQ_xor h1 hg1]; exact Y.mul_mem h2 hg2⟩

theorem inv_cases {Y : Subgroup ModQ} (hU : ∀ c ∈ u0Codes, ptQ c ∈ Y)
    (hs : ∀ i ∈ [1, 24, 40], ∀ y ∈ Y, g2QAct (ZMod 2) (sEltG i) y ∈ Y)
    (hz : ∀ y ∈ Y, g2QAct (ZMod 2) z1 y ∈ Y) :
    (∀ y ∈ Y, InU0 y) ∨ (∀ y, y ∈ Y ↔ InW0 y) ∨ Y = ⊤ := by
  have hact : ∀ g ∈ [0, 1, 24, 40, 64], ∀ c ∈ qCodes, ptQ c ∈ Y → ptQ (actC g c) ∈ Y := by
    intro g hg c hc hcY
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · rw [actC_zero c hc]; exact hcY
    · rw [← g2QAct_sEltG_code (by norm_num) hc]; exact hs 1 (by simp) _ hcY
    · rw [← g2QAct_sEltG_code (by norm_num) hc]; exact hs 24 (by simp) _ hcY
    · rw [← g2QAct_sEltG_code (by norm_num) hc]; exact hs 40 (by simp) _ hcY
    · rw [← g2QAct_z1_code hc]; exact hz _ hcY
  have hspan : ∀ k < 64, (2 * k) ∉ u0Codes → ptQ (2 * k) ∈ Y →
      ∀ d ∈ (if k < 32 then w0Codes else qCodes), ptQ d ∈ Y := by
    intro k hk hku hkY d hd
    have h2k : 2 * k ∈ qCodes := List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩
    obtain ⟨hg1, hg2⟩ := invG_mem k hk
    refine (mem_of_spanL _ (fun g hg => ?_) d (facts_inv k hk hku d hd)).2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, hU 8 (by decide)⟩
    · exact ⟨by decide, hU 16 (by decide)⟩
    · exact ⟨by decide, hU 32 (by decide)⟩
    · exact ⟨h2k, hkY⟩
    · exact ⟨actC_mem _ (by simp only [List.mem_cons] at hg1 ⊢; tauto) _ h2k,
        hact _ hg1 _ h2k hkY⟩
    · exact ⟨actC_mem _ (by simp only [List.mem_cons] at hg2 ⊢; tauto) _ h2k,
        hact _ hg2 _ h2k hkY⟩
  have hcode : ∀ c ∈ qCodes, ∃ k < 64, c = 2 * k := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
    exact ⟨k, List.mem_range.1 hk, rfl⟩
  have htop : ∀ c ∈ qCodes, c ∉ w0Codes → ptQ c ∈ Y → Y = ⊤ := by
    intro c hc hcw hcY
    obtain ⟨k, hk, rfl⟩ := hcode c hc
    have hk32 : ¬ k < 32 := fun h => hcw (List.mem_map.2 ⟨k, List.mem_range.2 h, rfl⟩)
    have hku : 2 * k ∉ u0Codes := fun h => hcw (by
      simp only [u0Codes, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h <;> omega)
    rw [eq_top_iff]
    intro q _
    obtain ⟨d, hd, rfl⟩ := exists_code q
    have := hspan k hk hku hcY d
    rw [ite_eq_right hk32] at this
    exact this hd
  by_cases h1 : ∀ y ∈ Y, InU0 y
  · exact Or.inl h1
  push Not at h1
  obtain ⟨y, hyY, hyU⟩ := h1
  obtain ⟨c, hc, rfl⟩ := exists_code y
  have hcu : c ∉ u0Codes := fun h => hyU ⟨c, h, rfl⟩
  by_cases hcw : c ∈ w0Codes
  ·
    obtain ⟨k, hk, rfl⟩ := hcode c hc
    have hk32 : k < 32 := by
      obtain ⟨k', hk', hk'e⟩ := List.mem_map.1 hcw
      have := List.mem_range.1 hk'
      omega
    have hW : ∀ d ∈ w0Codes, ptQ d ∈ Y := fun d hd => by
      have := hspan k hk hcu hyY d
      rw [ite_eq_left hk32] at this
      exact this hd
    by_cases h2 : ∀ y ∈ Y, InW0 y
    · refine Or.inr (Or.inl fun y => ⟨h2 y, ?_⟩)
      rintro ⟨d, hd, rfl⟩
      exact hW d hd
    · push Not at h2
      obtain ⟨y', hy'Y, hy'W⟩ := h2
      obtain ⟨c', hc', rfl⟩ := exists_code y'
      exact Or.inr (Or.inr (htop c' hc' (fun h => hy'W ⟨c', h, rfl⟩) hy'Y))
  · exact Or.inr (Or.inr (htop c hc hcw hyY))

@[expose] def yW (b : ℕ) : List ℕ :=
  if b = 2 then [1, 1, 2, 1] else if b = 4 then [2] else [1, 2, 1, 1]

@[expose] noncomputable def yB (b : ℕ) : ↥(quasithinG2 (ZMod 2)) := wordGG (yW b)

@[expose] def wMatC (w : List ℕ) : List ℕ := (List.range 8).map fun k => applyG w (2 ^ k)

theorem matCode_wordGG' {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) :
    matCode (wordGG w).1 = wMatC w := by
  change matCode ⇑(wordG (R := ZMod 2) w) = _
  unfold matCode wMatC
  refine List.map_congr_left fun k hk => ?_
  have hk8 : 2 ^ k < 256 := by
    have h8 : k < 8 := List.mem_range.1 hk
    calc 2 ^ k < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) h8
      _ = 256 := by norm_num
  obtain ⟨h1, h2⟩ := decodeZ_applyG hw hk8
  rw [← h1, encodeZ_decodeZ _ h2]

theorem yW_tok : ∀ b ∈ [2, 4, 6], ∀ t ∈ yW b, t = 1 ∨ t = 2 := by
  decide

theorem facts_yB : ∀ b ∈ [2, 4, 6],
    mmul (wMatC (yW b)) (sM b) = mmul (sM b) (wMatC (yW b)) ∧
      ∀ c ∈ lineB b, c ≠ 0 → nq (mact (wMatC (yW b)) c) ∈ lineB b ∧
        nq (mact (wMatC (yW b)) c) ≠ c := by
  decide +kernel

theorem yB_mem (b : ℕ) : yB b ∈ g2Derived (ZMod 2) := wordGG_mem_derived _

theorem yB_comm {b : ℕ} (hb : b ∈ [2, 4, 6]) : yB b * sEltG b = sEltG b * yB b := by
  have hb64 : b < 64 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; omega
  apply Subtype.ext
  apply linearEquiv_eq_of_matCode
  rw [Subgroup.coe_mul, Subgroup.coe_mul, matCode_mul, matCode_mul, yB,
    matCode_wordGG' (yW_tok b hb), matCode_sEltG hb64]
  exact (facts_yB b hb).1

theorem yB_act {b : ℕ} (hb : b ∈ [2, 4, 6]) {c : ℕ} (hc : c ∈ lineB b) (hc0 : c ≠ 0) :
    ∃ d ∈ lineB b, d ≠ 0 ∧ d ≠ c ∧ g2QAct (ZMod 2) (yB b) (ptQ c) = ptQ d := by
  have hcq : c ∈ o0Codes := by
    have : ∀ b ∈ [2, 4, 6], ∀ c ∈ lineB b, c ∈ o0Codes := by decide
    exact this b hb c hc
  obtain ⟨h1, h2⟩ := (facts_yB b hb).2 c hc hc0
  refine ⟨_, h1, fun h => ?_, h2, ?_⟩
  · have : ∀ b ∈ [2, 4, 6], ∀ c ∈ lineB b, c ≠ 0 →
        nq (mact (wMatC (yW b)) c) ≠ 0 := by decide +kernel
    exact this b hb c hc hc0 h
  · rw [g2QAct_ptQ _ hcq, yB, matCode_wordGG' (yW_tok b hb),
      ptQ_nq (by rw [← matCode_wordGG' (yW_tok b hb)]; exact mact_mem_o0Codes (yB b).2 hcq)]

@[expose] def fixAll (e c : ℕ) : Bool := (sE8.getD e []).all fun i => actC i c == c

@[expose] def centerE (e : ℕ) : ℕ := if e = 1 then 32 else if e = 2 then 8 else 40

theorem center_spec : ∀ e ∈ [1, 2, 6], ∀ c ∈ qCodes,
    (c ≠ 0 ∧ fixAll e c = true ∧ ∀ d ∈ qCodes, fixAll e d = true → d = 0 ∨ d = c ∨
      collT c d = true) ↔ c = centerE e := by
  decide +kernel

end CFSG.Quasithin.H13.L32A.M755
