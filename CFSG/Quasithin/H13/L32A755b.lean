module

public import CFSG.Quasithin.H13.L32A755a
public import CFSG.Quasithin.Vol2.Ch12Sec4G2OffCodes

public section

namespace CFSG.Quasithin.H13.L32A.M755

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 Orbit

theorem ptsQ_mem : ∀ c ∈ ptsQ, c ∈ o0Codes ∧ (c ^^^ 129) ∈ o0Codes ∧ c.testBit 0 = false := by
  decide +kernel

theorem sqL_spec : ∀ c ∈ ptsQ, sqL c ∈ o0Codes ∧ nq (sqL c) = c ∧
    encodeZ (quasithinZornMul (decodeZ (sqL c)) (decodeZ (sqL c))) = 0 := by
  decide +kernel

theorem sqL_nq : ∀ e ∈ o0Codes, encodeZ (quasithinZornMul (decodeZ e) (decodeZ e)) = 0 →
    e ≠ 0 → nq e ∈ ptsQ ∧ sqL (nq e) = e := by
  decide +kernel

theorem nq_mem_ptsQ : ∀ e ∈ o0Codes, e ≠ 0 → e ≠ 129 → nq e ∈ ptsQ := by
  decide +kernel

@[expose] def o0c (c : ℕ) : O0C := if h : c ∈ o0Codes then ⟨c, h⟩ else o0Zero

@[expose] noncomputable def ptQ (c : ℕ) : ModQ := codeQ (o0c c)

theorem ptQ_eq_codeQ {c : ℕ} (hc : c ∈ o0Codes) : ptQ c = codeQ ⟨c, hc⟩ := by
  simp [ptQ, o0c, hc]

theorem ptQ_injective {c d : ℕ} (hc : c ∈ ptsQ) (hd : d ∈ ptsQ) (h : ptQ c = ptQ d) : c = d := by
  obtain ⟨hc0, -, hc1⟩ := ptsQ_mem c hc
  obtain ⟨hd0, -, hd1⟩ := ptsQ_mem d hd
  rw [ptQ_eq_codeQ hc0, ptQ_eq_codeQ hd0, codeQ_eq_iff] at h
  rcases h with h | h
  · exact h.symm
  · exfalso
    have := congrArg (fun x => x.testBit 0) h
    simp only at this
    rw [testBit_xor_129, hc1, hd1] at this
    exact absurd this (by decide)

theorem ptQ_ne_one {c : ℕ} (hc : c ∈ ptsQ) : ptQ c ≠ 1 := by
  intro h
  obtain ⟨hc0, -, -⟩ := ptsQ_mem c hc
  rw [ptQ_eq_codeQ hc0, ← codeQ_zero, codeQ_eq_iff] at h
  have h0 : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    exact absurd hc (by decide)
  have h129 : c ≠ 129 := by
    intro h1
    rw [h1] at hc
    exact absurd hc (by decide)
  rcases h with h | h
  · exact h0 (by simpa [o0Zero] using h.symm)
  · apply h129
    have h' : c ^^^ 129 = 0 := by simpa [o0Zero] using h.symm
    rw [xor_eq_iff', Nat.xor_zero] at h'
    exact h'

theorem ptQ_mul {c d : ℕ} (hc : c ∈ o0Codes) (hd : d ∈ o0Codes) :
    ptQ c * ptQ d = ptQ (c ^^^ d) := by
  rw [ptQ_eq_codeQ hc, ptQ_eq_codeQ hd, ptQ_eq_codeQ (xor_mem_o0Codes hc hd), ← codeQ_xor]
  rfl

theorem ptQ_nq {e : ℕ} (he : e ∈ o0Codes) : ptQ (nq e) = ptQ e := by
  have h129 : (129 : ℕ) ∈ o0Codes := by decide
  unfold nq
  split_ifs
  · rw [← ptQ_mul he h129]
    have h1 : ptQ 129 = 1 := by
      rw [ptQ_eq_codeQ h129, ← codeQ_zero, codeQ_eq_iff]
      right
      simp [o0Zero]
    rw [h1, mul_one]
  · rfl

theorem exists_ptQ {p : ModQ} (hp : p ≠ 1) : ∃ c ∈ ptsQ, ptQ c = p := by
  obtain ⟨⟨e, he⟩, rfl⟩ := codeQ_surjective p
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hp codeQ_zero
  have he1 : e ≠ 129 := by
    rintro rfl
    apply hp
    rw [← codeQ_zero, codeQ_eq_iff]
    right
    simp [o0Zero]
  refine ⟨nq e, nq_mem_ptsQ e he he0 he1, ?_⟩
  rw [ptQ_nq he, ptQ_eq_codeQ he]

theorem g2QAct_ptQ (g : ↥(quasithinG2 (ZMod 2))) {c : ℕ} (hc : c ∈ o0Codes) :
    g2QAct (ZMod 2) g (ptQ c) = ptQ (mact (matCode g.1) c) := by
  rw [ptQ_eq_codeQ hc, g2QAct_codeQ, ptQ_eq_codeQ (mact_mem_o0Codes g.2 hc)]
  rfl

@[expose] def CollQ (p q : ModQ) : Prop :=
  ∃ c ∈ ptsQ, ∃ d ∈ ptsQ, ptQ c = p ∧ ptQ d = q ∧ collT c d = true

theorem collQ_ptQ {c d : ℕ} (hc : c ∈ ptsQ) (hd : d ∈ ptsQ) :
    CollQ (ptQ c) (ptQ d) ↔ collT c d = true := by
  constructor
  · rintro ⟨c', hc', d', hd', h1, h2, h3⟩
    rwa [ptQ_injective hc' hc h1, ptQ_injective hd' hd h2] at h3
  · exact fun h => ⟨c, hc, d, hd, rfl, rfl, h⟩

theorem collQ_ne {p q : ModQ} (h : CollQ p q) : p ≠ q ∧ p ≠ 1 ∧ q ≠ 1 := by
  obtain ⟨c, hc, d, hd, rfl, rfl, h⟩ := h
  refine ⟨fun e => ?_, ptQ_ne_one hc, ptQ_ne_one hd⟩
  rw [ptQ_injective hc hd e] at h
  rw [← collTabQ_spec d hd d hd] at h
  simp [collC] at h

theorem collQ_symm {p q : ModQ} (h : CollQ p q) : CollQ q p := by
  obtain ⟨c, hc, d, hd, rfl, rfl, h⟩ := h
  exact ⟨d, hd, c, hc, rfl, rfl, (collT_symm c hc d hd) ▸ h⟩

theorem collQ_mul {p q : ModQ} (h : CollQ p q) : CollQ p (p * q) ∧ CollQ q (p * q) := by
  obtain ⟨c, hc, d, hd, rfl, rfl, h⟩ := h
  obtain ⟨hx, h1, h2⟩ := collT_xor c hc d hd h
  rw [ptQ_mul (ptsQ_mem c hc).1 (ptsQ_mem d hd).1]
  exact ⟨⟨c, hc, _, hx, rfl, rfl, h1⟩, ⟨d, hd, _, hx, rfl, rfl, h2⟩⟩

theorem eq_of_length_filter_le_one {l : List ℕ} {P : ℕ → Bool} (h : (l.filter P).length ≤ 1)
    {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hPa : P a = true) (hPb : P b = true) : a = b := by
  have ha' : a ∈ l.filter P := List.mem_filter.2 ⟨ha, hPa⟩
  have hb' : b ∈ l.filter P := List.mem_filter.2 ⟨hb, hPb⟩
  generalize l.filter P = L at h ha' hb'
  match L, h with
  | [], _ => simp at ha'
  | [x], _ =>
    rw [List.mem_singleton] at ha' hb'
    rw [ha', hb']

theorem collQ_common {p q r r' : ModQ} (hpq : p ≠ q) (h1 : CollQ p r) (h2 : CollQ q r)
    (h3 : CollQ p r') (h4 : CollQ q r') : r = r' := by
  obtain ⟨c, hc, e, he, rfl, rfl, h1⟩ := h1
  obtain ⟨d, hd, e₂, he₂, rfl, h5, h2⟩ := h2
  rw [ptQ_injective he₂ he h5] at h2
  obtain ⟨c₃, hc₃, e', he', h6, rfl, h3⟩ := h3
  rw [ptQ_injective hc₃ hc h6] at h3
  obtain ⟨d₄, hd₄, e'₄, he'₄, h7, h8, h4⟩ := h4
  rw [ptQ_injective hd₄ hd h7, ptQ_injective he'₄ he' h8] at h4
  have hcd : c ≠ d := fun e => hpq (by rw [e])
  rw [eq_of_length_filter_le_one (collT_common c hc d hd hcd) he he' (by simp [h1, h2])
    (by simp [h3, h4])]

theorem encodeZ_zero : encodeZ (0 : quasithinZorn (ZMod 2)) = 0 := by
  rw [← decodeZ_zero, encodeZ_decodeZ 0 (by norm_num)]

theorem mul_eq_zero_of_encodeZ {x y : quasithinZorn (ZMod 2)}
    (h : encodeZ (quasithinZornMul x y) = 0) : quasithinZornMul x y = 0 := by
  rw [← decodeZ_encodeZ (quasithinZornMul x y), h, decodeZ_zero]

theorem collQ_act_of (g : ↥(quasithinG2 (ZMod 2))) {p q : ModQ} (h : CollQ p q) :
    CollQ (g2QAct (ZMod 2) g p) (g2QAct (ZMod 2) g q) := by
  have hA := mem_quasithinG2_isZornAuto g.2
  obtain ⟨c, hc, d, hd, rfl, rfl, hcd⟩ := h
  have hcd' := hcd
  rw [← collTabQ_spec c hc d hd] at hcd'
  simp only [collC, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hcd'
  obtain ⟨hne, hprod⟩ := hcd'
  obtain ⟨ha, hna, ha2⟩ := sqL_spec c hc
  obtain ⟨hb, hnb, hb2⟩ := sqL_spec d hd
  set a := sqL c
  set b := sqL d
  set a' := mact (matCode g.1) a
  set b' := mact (matCode g.1) b
  have ha' : a' ∈ o0Codes := mact_mem_o0Codes g.2 ha
  have hb' : b' ∈ o0Codes := mact_mem_o0Codes g.2 hb
  have hda : decodeZ a' = g.1 (decodeZ a) := decodeZ_mact' g.1 (mem_o0Codes.1 ha).1
  have hdb : decodeZ b' = g.1 (decodeZ b) := decodeZ_mact' g.1 (mem_o0Codes.1 hb).1
  have hsq : ∀ {x : ℕ}, encodeZ (quasithinZornMul (decodeZ x) (decodeZ x)) = 0 →
      encodeZ (quasithinZornMul (g.1 (decodeZ x)) (g.1 (decodeZ x))) = 0 := fun hx => by
    rw [← hA, mul_eq_zero_of_encodeZ hx, map_zero, encodeZ_zero]
  have ha'2 : encodeZ (quasithinZornMul (decodeZ a') (decodeZ a')) = 0 := hda ▸ hsq ha2
  have hb'2 : encodeZ (quasithinZornMul (decodeZ b') (decodeZ b')) = 0 := hdb ▸ hsq hb2
  have hpa : g2QAct (ZMod 2) g (ptQ c) = ptQ a' := by
    rw [← hna, ptQ_nq ha, g2QAct_ptQ g ha]
  have hpb : g2QAct (ZMod 2) g (ptQ d) = ptQ b' := by
    rw [← hnb, ptQ_nq hb, g2QAct_ptQ g hb]
  have ha'0 : a' ≠ 0 := by
    intro h0
    apply ptQ_ne_one hc
    apply (g2QAct (ZMod 2) g).injective
    rw [hpa, h0, map_one]
    rw [ptQ_eq_codeQ (by decide : (0 : ℕ) ∈ o0Codes)]
    exact codeQ_zero
  have hb'0 : b' ≠ 0 := by
    intro h0
    apply ptQ_ne_one hd
    apply (g2QAct (ZMod 2) g).injective
    rw [hpb, h0, map_one]
    rw [ptQ_eq_codeQ (by decide : (0 : ℕ) ∈ o0Codes)]
    exact codeQ_zero
  obtain ⟨hc', hsa⟩ := sqL_nq a' ha' ha'2 ha'0
  obtain ⟨hd', hsb⟩ := sqL_nq b' hb' hb'2 hb'0
  refine ⟨nq a', hc', nq b', hd', by rw [ptQ_nq ha', hpa], by rw [ptQ_nq hb', hpb], ?_⟩
  rw [← collTabQ_spec _ hc' _ hd']
  simp only [collC, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨fun e => hne ?_, ?_⟩
  · have h1 : ptQ a' = ptQ b' := by rw [← ptQ_nq ha', e, ptQ_nq hb']
    rw [← hpa, ← hpb] at h1
    exact ptQ_injective hc hd ((g2QAct (ZMod 2) g).injective h1)
  · rw [hsa, hsb, hda, hdb, ← hA, mul_eq_zero_of_encodeZ hprod, map_zero, encodeZ_zero]

theorem collQ_act (g : ↥(quasithinG2 (ZMod 2))) {p q : ModQ} :
    CollQ (g2QAct (ZMod 2) g p) (g2QAct (ZMod 2) g q) ↔ CollQ p q := by
  refine ⟨fun h => ?_, collQ_act_of g⟩
  have := collQ_act_of g⁻¹ h
  simpa [← MulAut.mul_apply, ← map_mul] using this

end CFSG.Quasithin.H13.L32A.M755
