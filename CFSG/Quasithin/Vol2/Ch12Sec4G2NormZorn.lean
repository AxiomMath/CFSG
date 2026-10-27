module

public import CFSG.Quasithin.Vol2.Ch12Sec4G2OffProof
public import CFSG.Quasithin.H13.VolIAltCoverG2
public import CFSG.Quasithin.Background.P3G2Aut
public import CFSG.Quasithin.Background.P3G2Iso

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Orbit

instance g2Derived_normal (K : Type) [Field K] : (g2Derived K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.commutator_le_self _)).2
    (Subgroup.normalizer_commutator_ge_left _ _)

section Two

@[expose] def wordGG (w : List ℕ) : ↥(quasithinG2 (ZMod 2)) :=
  ⟨wordG w, Subgroup.commutator_le_self _ (wordG_mem w)⟩

theorem wordGG_mem_derived (w : List ℕ) : wordGG w ∈ g2Derived (ZMod 2) :=
  Subgroup.mem_subgroupOf.2 (wordG_mem w)

theorem o0Act_wordGG {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) (c : O0C) :
    (o0Act (wordGG w) c).1 = applyG w c.1 := by
  obtain ⟨h1, h2⟩ := decodeZ_applyG hw (mem_o0Codes.1 c.2).1
  change mact (matCode (wordG w : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] _)) c.1 = _
  apply decodeZ_injective (mact_lt' _ c.1) h2
  rw [decodeZ_mact' _ (mem_o0Codes.1 c.2).1, h1]

@[expose] def stabW1 : List ℕ := [1, 2, 1, 2, 2, 1, 1]

@[expose] def stabW2 : List ℕ := [2, 1, 2, 1, 2, 1, 2, 2]

theorem stab_words : (∀ t ∈ stabW1, t = 1 ∨ t = 2) ∧ (∀ t ∈ stabW2, t = 1 ∨ t = 2) ∧
    applyG stabW1 2 = 2 ∧ applyG stabW2 2 = 2 := by
  decide +kernel

@[expose] def fixQW (w : List ℕ) (c : ℕ) : Bool := (applyG w c ^^^ c) ||| 129 == 129

theorem stab_fixQ : ∀ c ∈ o0Codes, fixQW stabW1 c = true → fixQW stabW2 c = true →
    c = 0 ∨ c = 2 ∨ c = 129 ∨ c = 131 := by
  decide +kernel

theorem stab_fixO : ∀ c ∈ o0Codes, applyG stabW1 c = c → applyG stabW2 c = c →
    c = 0 ∨ c = 2 ∨ c = 129 ∨ c = 131 := by
  decide +kernel

theorem cent_fixO : ∀ c ∈ o0Codes, applyG [1] c = c → applyG [2] c = c → c = 0 ∨ c = 129 := by
  decide +kernel

theorem singular_or : ∀ c ∈ o0Codes, c ≠ 0 → c ≠ 129 →
    (zornNorm (decodeZ c) = 0 ∧ decodeZ c ≠ 0 ∧ decodeZ c ≠ zornOne) ∨
      (zornNorm (decodeZ (c ^^^ 129)) = 0 ∧ decodeZ (c ^^^ 129) ≠ 0 ∧
        decodeZ (c ^^^ 129) ≠ zornOne) := by
  decide +kernel

theorem trace_decodeZ_of_mem {c : ℕ} (hc : c ∈ o0Codes) : (decodeZ c).1 + (decodeZ c).2.2.2 = 0 :=
  (trace_decodeZ_iff c (mem_o0Codes.1 hc).1).2 (mem_o0Codes.1 hc).2

theorem singular_word {c : ℕ} (hc : c ∈ o0Codes) (hn : zornNorm (decodeZ c) = 0)
    (h0 : decodeZ c ≠ 0) (h1 : decodeZ c ≠ zornOne) :
    applyG (g2Words.getD c []) 2 = c ∧ ∀ t ∈ g2Words.getD c [], t = 1 ∨ t = 2 := by
  have h := g2_cert c (mem_o0Codes.1 hc).1 (trace_decodeZ_of_mem hc) h0 h1
  rw [ite_eq_left hn] at h
  exact ⟨h, g2_words c (mem_o0Codes.1 hc).1⟩

theorem fixQW_of {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) (c : O0C)
    (h : g2QAct (ZMod 2) (wordGG w) (codeQ c) = codeQ c) : fixQW w c.1 = true := by
  rw [g2QAct_codeQ, codeQ_eq_iff, o0Act_wordGG hw] at h
  unfold fixQW
  rcases h with h | h
  · rw [← h, Nat.xor_self]
    rfl
  · have h' : applyG w c.1 ^^^ c.1 = 129 := xor_eq_iff.2 h
    rw [h']
    rfl

theorem fixOW_of {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) (c : O0C)
    (h : g2OAct (ZMod 2) (wordGG w) (codeO c) = codeO c) : applyG w c.1 = c.1 := by
  rw [g2OAct_codeO] at h
  rw [← o0Act_wordGG hw]
  exact congrArg Subtype.val (codeO_injective h)

theorem codeQ_word_e {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) {c : ℕ} (hc : c ∈ o0Codes)
    (h2 : (2 : ℕ) ∈ o0Codes) (hwc : applyG w 2 = c) :
    g2QAct (ZMod 2) (wordGG w) (codeQ ⟨2, h2⟩) = codeQ ⟨c, hc⟩ := by
  rw [g2QAct_codeQ]
  congr 1
  exact Subtype.ext ((o0Act_wordGG hw _).trans hwc)

theorem codeO_word_e {w : List ℕ} (hw : ∀ t ∈ w, t = 1 ∨ t = 2) {c : ℕ} (hc : c ∈ o0Codes)
    (h2 : (2 : ℕ) ∈ o0Codes) (hwc : applyG w 2 = c) :
    g2OAct (ZMod 2) (wordGG w) (codeO ⟨2, h2⟩) = codeO ⟨c, hc⟩ := by
  rw [g2OAct_codeO]
  congr 1
  exact Subtype.ext ((o0Act_wordGG hw _).trans hwc)

theorem codeQ_eq_one_iff (c : O0C) : codeQ c = 1 ↔ c.1 = 0 ∨ c.1 = 129 := by
  rw [← codeQ_zero, codeQ_eq_iff]
  change 0 = c.1 ∨ 0 = c.1 ^^^ 129 ↔ _
  rw [eq_comm (a := 0), eq_comm (a := 0), xor_eq_iff', Nat.xor_zero]

theorem codeO_eq_one_iff (c : O0C) : codeO c = 1 ↔ c.1 = 0 := by
  rw [← codeO_zero]
  constructor
  · intro h
    exact congrArg Subtype.val (codeO_injective h)
  · intro h
    exact congrArg codeO (Subtype.ext h)

theorem schur_Q (y : MulAut ModQ)
    (hy : ∀ h ∈ (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)), y * h = h * y) : y = 1 := by
  have hcomm : ∀ (w : List ℕ) (v : ModQ),
      y (g2QAct (ZMod 2) (wordGG w) v) = g2QAct (ZMod 2) (wordGG w) (y v) := fun w v =>
    congrArg (fun f : MulAut ModQ => f v) (hy _ ⟨_, wordGG_mem_derived w, rfl⟩)
  obtain ⟨hw1, hw2, hs1, hs2⟩ := stab_words
  have h2mem : (2 : ℕ) ∈ o0Codes := by decide
  have hv0 : y (codeQ ⟨2, h2mem⟩) = codeQ ⟨2, h2mem⟩ := by
    obtain ⟨c, hc⟩ := codeQ_surjective (y (codeQ ⟨2, h2mem⟩))
    have hf : ∀ w, (∀ t ∈ w, t = 1 ∨ t = 2) → applyG w 2 = 2 → fixQW w c.1 = true := by
      intro w hw hw2
      refine fixQW_of hw c ?_
      rw [hc, ← hcomm, codeQ_word_e hw h2mem h2mem hw2]
    have hne1 : y (codeQ ⟨2, h2mem⟩) ≠ 1 := by
      intro h
      have h' := (codeQ_eq_one_iff _).1 (y.injective (h.trans (map_one y).symm))
      simp at h'
    rcases stab_fixQ c.1 c.2 (hf _ hw1 hs1) (hf _ hw2 hs2) with h | h | h | h
    · exact absurd (hc.symm.trans ((codeQ_eq_one_iff c).2 (Or.inl h))) hne1
    · rw [← hc]
      exact congrArg codeQ (Subtype.ext h)
    · exact absurd (hc.symm.trans ((codeQ_eq_one_iff c).2 (Or.inr h))) hne1
    · rw [← hc, codeQ_eq_iff]
      right
      change 2 = c.1 ^^^ 129
      rw [h]
      rfl
  ext v
  obtain ⟨c, rfl⟩ := codeQ_surjective v
  change y (codeQ c) = codeQ c
  by_cases h0 : c.1 = 0 ∨ c.1 = 129
  · rw [(codeQ_eq_one_iff c).2 h0, map_one]
  rw [not_or] at h0
  obtain ⟨c', hc'mem, hcc', hn, hd0, hd1⟩ : ∃ c' : ℕ, ∃ h : c' ∈ o0Codes,
      codeQ c = codeQ ⟨c', h⟩ ∧ zornNorm (decodeZ c') = 0 ∧ decodeZ c' ≠ 0 ∧
        decodeZ c' ≠ zornOne := by
    rcases singular_or c.1 c.2 h0.1 h0.2 with ⟨hn, hd0, hd1⟩ | ⟨hn, hd0, hd1⟩
    · exact ⟨c.1, c.2, rfl, hn, hd0, hd1⟩
    · refine ⟨c.1 ^^^ 129, xor_mem_o0Codes c.2 (by decide), ?_, hn, hd0, hd1⟩
      rw [codeQ_eq_iff]
      exact Or.inr rfl
  obtain ⟨hwc, hwl⟩ := singular_word hc'mem hn hd0 hd1
  rw [hcc', ← codeQ_word_e hwl hc'mem h2mem hwc, hcomm, hv0]

theorem o0Act_one (g : ↥(quasithinG2 (ZMod 2))) (h129 : (129 : ℕ) ∈ o0Codes) :
    o0Act g ⟨129, h129⟩ = ⟨129, h129⟩ := by
  apply Subtype.ext
  change mact (matCode g.1) 129 = 129
  apply decodeZ_injective (mact_lt' _ _) (by norm_num)
  rw [decodeZ_mact' g.1 (by norm_num)]
  have h1 : decodeZ 129 = zornOne := by decide
  rw [h1]
  exact quasithinG2_one g.2

theorem schur_O (y : MulAut ModO)
    (hy : ∀ h ∈ (g2Derived (ZMod 2)).map (g2OAct (ZMod 2)), y * h = h * y) : y = 1 := by
  have hcomm : ∀ (w : List ℕ) (v : ModO),
      y (g2OAct (ZMod 2) (wordGG w) v) = g2OAct (ZMod 2) (wordGG w) (y v) := fun w v =>
    congrArg (fun f : MulAut ModO => f v) (hy _ ⟨_, wordGG_mem_derived w, rfl⟩)
  obtain ⟨hw1, hw2, hs1, hs2⟩ := stab_words
  have h2mem : (2 : ℕ) ∈ o0Codes := by decide
  have h129 : (129 : ℕ) ∈ o0Codes := by decide
  set e2 : O0C := ⟨2, h2mem⟩ with he2
  set e1 : O0C := ⟨129, h129⟩ with he1
  have hρ1 : ∀ g, g2OAct (ZMod 2) g (codeO e1) = codeO e1 := fun g => by
    rw [g2OAct_codeO, o0Act_one]
  have hne : codeO e1 ≠ 1 := fun h => by
    have := (codeO_eq_one_iff e1).1 h
    simp [he1] at this
  have hone : y (codeO e1) = codeO e1 := by
    obtain ⟨c, hc⟩ := codeO_surjective (y (codeO e1))
    have hf : ∀ w, (∀ t ∈ w, t = 1 ∨ t = 2) → applyG w c.1 = c.1 := by
      intro w hw
      refine fixOW_of hw c ?_
      rw [hc, ← hcomm, hρ1]
    rcases cent_fixO c.1 c.2 (hf [1] (by simp)) (hf [2] (by simp)) with h | h
    · exfalso
      have h1 : y (codeO e1) = 1 := by rw [← hc]; exact (codeO_eq_one_iff c).2 h
      exact hne (y.injective (h1.trans (map_one y).symm))
    · rw [← hc]
      exact congrArg codeO (Subtype.ext h)
  have hv0 : y (codeO e2) = codeO e2 ∨ y (codeO e2) = codeO e2 * codeO e1 := by
    obtain ⟨c, hc⟩ := codeO_surjective (y (codeO e2))
    have hf : ∀ w, (∀ t ∈ w, t = 1 ∨ t = 2) → applyG w 2 = 2 → applyG w c.1 = c.1 := by
      intro w hw hw2
      refine fixOW_of hw c ?_
      rw [hc, ← hcomm, codeO_word_e hw h2mem h2mem hw2]
    rcases stab_fixO c.1 c.2 (hf _ hw1 hs1) (hf _ hw2 hs2) with h | h | h | h
    · exfalso
      have h1 : y (codeO e2) = 1 := by rw [← hc]; exact (codeO_eq_one_iff c).2 h
      have h2 := y.injective (h1.trans (map_one y).symm)
      have := (codeO_eq_one_iff e2).1 h2
      simp [he2] at this
    · left
      rw [← hc]
      exact congrArg codeO (Subtype.ext h)
    · exfalso
      have h1 : y (codeO e2) = y (codeO e1) := by
        rw [← hc, hone]
        exact congrArg codeO (Subtype.ext h)
      have h2 := congrArg Subtype.val (codeO_injective (y.injective h1))
      simp [he1, he2] at h2
    · right
      rw [← hc, ← codeO_xor]
      exact congrArg codeO (Subtype.ext (h.trans (by
        change (131 : ℕ) = 2 ^^^ 129
        decide +kernel)))
  have hsing : ∀ (c : ℕ) (hc : c ∈ o0Codes), zornNorm (decodeZ c) = 0 → decodeZ c ≠ 0 →
      decodeZ c ≠ zornOne → ∃ w : List ℕ, codeO ⟨c, hc⟩ =
        g2OAct (ZMod 2) (wordGG w) (codeO e2) ∧
          y (codeO ⟨c, hc⟩) = g2OAct (ZMod 2) (wordGG w) (y (codeO e2)) := by
    intro c hc hn hd0 hd1
    obtain ⟨hwc, hwl⟩ := singular_word hc hn hd0 hd1
    have he := (codeO_word_e hwl hc h2mem hwc).symm
    exact ⟨_, he, by rw [he, hcomm]⟩
  rcases hv0 with hv0 | hv0
  ·
    have hfix : ∀ (d : ℕ) (hd : d ∈ o0Codes), zornNorm (decodeZ d) = 0 → decodeZ d ≠ 0 →
        decodeZ d ≠ zornOne → y (codeO ⟨d, hd⟩) = codeO ⟨d, hd⟩ := by
      intro d hd hn hd0 hd1
      obtain ⟨w, hw, hyw⟩ := hsing d hd hn hd0 hd1
      rw [hyw, hv0, ← hw]
    ext v
    obtain ⟨c, rfl⟩ := codeO_surjective v
    change y (codeO c) = codeO c
    by_cases h0 : c.1 = 0
    · rw [(codeO_eq_one_iff c).2 h0, map_one]
    by_cases h1 : c.1 = 129
    · have : c = e1 := Subtype.ext h1
      rw [this, hone]
    rcases singular_or c.1 c.2 h0 h1 with ⟨hn, hd0, hd1⟩ | ⟨hn, hd0, hd1⟩
    · exact hfix c.1 c.2 hn hd0 hd1
    · have hc' : c = o0Xor ⟨c.1 ^^^ 129, xor_mem_o0Codes c.2 h129⟩ e1 := by
        apply Subtype.ext
        change c.1 = c.1 ^^^ 129 ^^^ 129
        rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hc', codeO_xor, map_mul, hfix _ _ hn hd0 hd1, hone]
  ·
    exfalso
    have hshift : ∀ (d : ℕ) (hd : d ∈ o0Codes), zornNorm (decodeZ d) = 0 → decodeZ d ≠ 0 →
        decodeZ d ≠ zornOne → y (codeO ⟨d, hd⟩) = codeO ⟨d, hd⟩ * codeO e1 := by
      intro d hd hn hd0 hd1
      obtain ⟨w, hw, hyw⟩ := hsing d hd hn hd0 hd1
      rw [hyw, hv0, map_mul, hρ1, ← hw]
    have h4 : (4 : ℕ) ∈ o0Codes := by decide
    have h6 : (6 : ℕ) ∈ o0Codes := by decide
    have hy4 := hshift 4 h4 (by decide) (by decide) (by decide)
    have hy6 := hshift 6 h6 (by decide) (by decide) (by decide)
    have h246 : codeO ⟨6, h6⟩ = codeO e2 * codeO ⟨4, h4⟩ := by
      rw [← codeO_xor]
      exact congrArg codeO (Subtype.ext (show (6 : ℕ) = 2 ^^^ 4 by decide +kernel))
    have he11 : codeO e1 * codeO e1 = 1 := by
      rw [← codeO_xor, o0Xor_self, codeO_zero]
    have key : codeO ⟨6, h6⟩ * codeO e1 = codeO ⟨6, h6⟩ := by
      rw [← hy6, h246, map_mul, hv0, hy4]
      calc codeO e2 * codeO e1 * (codeO ⟨4, h4⟩ * codeO e1)
          = codeO e2 * codeO ⟨4, h4⟩ * (codeO e1 * codeO e1) := by
            rw [mul_mul_mul_comm]
        _ = codeO e2 * codeO ⟨4, h4⟩ := by rw [he11, mul_one]
    exact hne (mul_eq_left.1 key)

theorem card_mulAut_g2Derived :
    Nat.card (MulAut ↥(g2Derived (ZMod 2))) = 12096 :=
  G11.P3G2.card_mulAut_of_equiv
    (((Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self _)).trans VolI.g2TwoEquiv).trans
      G11.P3G2.subG2EquivSU)

theorem normalizer_two {M : Type} [CommGroup M] (ρ : ↥(quasithinG2 (ZMod 2)) →* MulAut M)
    (hρ : Function.Injective ρ)
    (hschur : ∀ y : MulAut M, (∀ h ∈ (g2Derived (ZMod 2)).map ρ, y * h = h * y) → y = 1)
    (hcardAut : Nat.card (MulAut ↥(g2Derived (ZMod 2))) = 12096) (x : MulAut M)
    (hx : ∀ h, h ∈ (g2Derived (ZMod 2)).map ρ ↔ x * h * x⁻¹ ∈ (g2Derived (ZMod 2)).map ρ) :
    x ∈ ρ.range := by
  have : Finite (MulAut ↥(g2Derived (ZMod 2))) := Finite.of_injective _ DFunLike.coe_injective
  have hc_inj : Function.Injective
      (MulAut.conjNormal : ↥(quasithinG2 (ZMod 2)) →* MulAut ↥(g2Derived (ZMod 2))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply hρ
    rw [map_one]
    apply hschur
    rintro _ ⟨d, hd, rfl⟩
    have h1 : g * d * g⁻¹ = d := by
      have := congrArg (fun f : MulAut ↥(g2Derived (ZMod 2)) =>
        ((f ⟨d, hd⟩ : ↥(g2Derived (ZMod 2))) : ↥(quasithinG2 (ZMod 2)))) hg
      simpa [MulAut.conjNormal_apply] using this
    rw [← map_mul, ← map_mul]
    congr 1
    calc g * d = g * d * g⁻¹ * g := by group
      _ = d * g := by rw [h1]
  have hc_bij : Function.Bijective
      (MulAut.conjNormal : ↥(quasithinG2 (ZMod 2)) →* MulAut ↥(g2Derived (ZMod 2))) :=
    hc_inj.bijective_of_nat_card_le (le_of_eq (by rw [hcardAut, card_g2Two]))
  let ρD : ↥(g2Derived (ZMod 2)) ≃* ↥((g2Derived (ZMod 2)).map ρ) :=
    (g2Derived (ZMod 2)).equivMapOfInjective ρ hρ
  have hxm : ∀ h ∈ (g2Derived (ZMod 2)).map ρ, x * h * x⁻¹ ∈ (g2Derived (ZMod 2)).map ρ :=
    fun h hh => (hx h).1 hh
  have hxm' : ∀ h ∈ (g2Derived (ZMod 2)).map ρ, x⁻¹ * h * x ∈ (g2Derived (ZMod 2)).map ρ :=
    fun h hh => by
    refine (hx _).2 ?_
    rw [show x * (x⁻¹ * h * x) * x⁻¹ = h by group]
    exact hh
  let cx : ↥((g2Derived (ZMod 2)).map ρ) ≃* ↥((g2Derived (ZMod 2)).map ρ) :=
    { toFun := fun h => ⟨x * h * x⁻¹, hxm h h.2⟩
      invFun := fun h => ⟨x⁻¹ * h * x, hxm' h h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun h k => Subtype.ext (by simp [mul_assoc]) }
  let α : MulAut ↥(g2Derived (ZMod 2)) := ρD.trans (cx.trans ρD.symm)
  obtain ⟨g, hg⟩ := hc_bij.2 α
  have key : ∀ d ∈ g2Derived (ZMod 2), ρ g * ρ d * (ρ g)⁻¹ = x * ρ d * x⁻¹ := by
    intro d hd
    have h1 := congrArg (fun f : MulAut ↥(g2Derived (ZMod 2)) =>
      ((f ⟨d, hd⟩ : ↥(g2Derived (ZMod 2))) : ↥(quasithinG2 (ZMod 2)))) hg
    simp only [MulAut.conjNormal_apply] at h1
    have h2 : ρ (g * d * g⁻¹) = x * ρ d * x⁻¹ := by
      rw [h1]
      have h3 : ρD (α ⟨d, hd⟩) = cx (ρD ⟨d, hd⟩) := by
        simp [α]
      have h4 := congrArg Subtype.val h3
      exact h4
    rw [← h2, map_mul, map_mul, map_inv]
  have hy := hschur ((ρ g)⁻¹ * x) (by
    rintro _ ⟨d, hd, rfl⟩
    have := key d hd
    calc (ρ g)⁻¹ * x * ρ d = (ρ g)⁻¹ * (x * ρ d * x⁻¹) * x := by group
      _ = (ρ g)⁻¹ * (ρ g * ρ d * (ρ g)⁻¹) * x := by rw [← this]
      _ = ρ d * ((ρ g)⁻¹ * x) := by group)
  exact ⟨g, (inv_mul_eq_one.1 hy)⟩

theorem normalizer_two_Q
    (x : MulAut ModQ)
    (hx : ∀ h, h ∈ (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ↔
      x * h * x⁻¹ ∈ (g2Derived (ZMod 2)).map (g2QAct (ZMod 2))) :
    x ∈ (g2QAct (ZMod 2)).range :=
  normalizer_two _ g2QAct_injective schur_Q card_mulAut_g2Derived x hx

theorem normalizer_two_O
    (x : MulAut ModO)
    (hx : ∀ h, h ∈ (g2Derived (ZMod 2)).map (g2OAct (ZMod 2)) ↔
      x * h * x⁻¹ ∈ (g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) :
    x ∈ (g2OAct (ZMod 2)).range :=
  normalizer_two _ g2OAct_injective schur_O card_mulAut_g2Derived x hx

end Two

section Field

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

omit [Finite K] [CharP K 2] in
theorem zornEquivK_smul (s : ZMod 2) (x : quasithinZorn (ZMod 2)) :
    zornEquivK hK (s • x) = twoEquiv hK s • zornEquivK hK x := by
  rw [zornEquivK_apply, zornEquivK_apply]
  apply zorn_ext <;> (try intro i) <;> simp [zornMap]

@[expose] noncomputable def conjK (g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :
    quasithinZorn K ≃ₗ[K] quasithinZorn K where
  toFun x := zornEquivK hK (g ((zornEquivK hK).symm x))
  invFun x := zornEquivK hK (g.symm ((zornEquivK hK).symm x))
  map_add' x y := by simp
  map_smul' t x := by
    obtain ⟨s, rfl⟩ := (twoEquiv hK).surjective t
    have h1 : (zornEquivK hK).symm (twoEquiv hK s • x) = s • (zornEquivK hK).symm x := by
      apply (zornEquivK hK).injective
      rw [zornEquivK_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    simp only [RingHom.id_apply]
    rw [h1, map_smul, zornEquivK_smul]
  left_inv x := by simp
  right_inv x := by simp

omit [Finite K] [CharP K 2] in
theorem conjK_mem {g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)}
    (hg : g ∈ quasithinG2 (ZMod 2)) : conjK hK g ∈ quasithinG2 K := by
  have hz := mem_quasithinG2_isZornAuto hg
  refine mem_quasithinG2 fun x y => ?_
  change zornEquivK hK (g ((zornEquivK hK).symm (quasithinZornMul x y))) =
    quasithinZornMul (zornEquivK hK (g ((zornEquivK hK).symm x)))
      (zornEquivK hK (g ((zornEquivK hK).symm y)))
  rw [zornEquivK_symm_mul, hz, zornEquivK_mul]

omit [Finite K] [CharP K 2] in
theorem conjF2_conjK (g : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) :
    conjF2 hK (conjK hK g) = g := by
  refine LinearEquiv.ext fun x => ?_
  change (zornEquivK hK).symm (zornEquivK hK (g ((zornEquivK hK).symm (zornEquivK hK x)))) = g x
  simp

@[expose] noncomputable def conjF2Hom : ↥(quasithinG2 K) →* ↥(quasithinG2 (ZMod 2)) where
  toFun g := ⟨conjF2 hK g.1, conjF2_mem hK g.2⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun x => by simp [conjF2_apply])
  map_mul' g h := Subtype.ext (LinearEquiv.ext fun x => by simp [conjF2_apply])

omit [Finite K] [CharP K 2] in
theorem conjF2Hom_apply (g : ↥(quasithinG2 K)) :
    conjF2Hom hK g = ⟨conjF2 hK g.1, conjF2_mem hK g.2⟩ := rfl

omit [Finite K] [CharP K 2] in
theorem conjF2Hom_surjective : Function.Surjective (conjF2Hom hK) := fun g =>
  ⟨⟨conjK hK g.1, conjK_mem hK g.2⟩, Subtype.ext (conjF2_conjK hK g.1)⟩

theorem g2Derived_eq_commutator (F : Type) [Field F] :
    g2Derived F = ⁅(⊤ : Subgroup ↥(quasithinG2 F)), ⊤⁆ := by
  apply Subgroup.map_injective (quasithinG2 F).subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, g2Derived,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (Subgroup.commutator_le_self _)]

omit [Finite K] [CharP K 2] in
theorem map_g2Derived_conjF2Hom : (g2Derived K).map (conjF2Hom hK) = g2Derived (ZMod 2) := by
  rw [g2Derived_eq_commutator, g2Derived_eq_commutator, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ (conjF2Hom_surjective hK)]

omit [Finite K] [CharP K 2] in
theorem normalizer_transport {M₂ MK : Type} [CommGroup M₂] [CommGroup MK] (e : M₂ ≃* MK)
    (ρ₂ : ↥(quasithinG2 (ZMod 2)) →* MulAut M₂) (ρK : ↥(quasithinG2 K) →* MulAut MK)
    (hρ : ∀ g, MulAut.congr e.symm (ρK g) = ρ₂ (conjF2Hom hK g))
    (h₂ : ∀ x : MulAut M₂, (∀ h, h ∈ (g2Derived (ZMod 2)).map ρ₂ ↔
      x * h * x⁻¹ ∈ (g2Derived (ZMod 2)).map ρ₂) → x ∈ ρ₂.range)
    (x : MulAut MK) (hx : ∀ h, h ∈ (g2Derived K).map ρK ↔ x * h * x⁻¹ ∈ (g2Derived K).map ρK) :
    x ∈ ρK.range := by
  set φ := MulAut.congr e.symm with hφdef
  have hH : ((g2Derived K).map ρK).map φ.toMonoidHom = (g2Derived (ZMod 2)).map ρ₂ := by
    rw [Subgroup.map_map, ← map_g2Derived_conjF2Hom hK, Subgroup.map_map]
    congr 1
    ext g : 1
    exact hρ g
  have hx' : ∀ h, h ∈ (g2Derived (ZMod 2)).map ρ₂ ↔
      φ x * h * (φ x)⁻¹ ∈ (g2Derived (ZMod 2)).map ρ₂ := by
    intro h
    obtain ⟨h', rfl⟩ := φ.surjective h
    rw [← hH, ← map_inv, ← map_mul, ← map_mul]
    change φ.toMonoidHom h' ∈ _ ↔ φ.toMonoidHom (x * h' * x⁻¹) ∈ _
    rw [Subgroup.mem_map_iff_mem φ.injective, Subgroup.mem_map_iff_mem φ.injective]
    exact hx h'
  obtain ⟨g', hg'⟩ := h₂ (φ x) hx'
  obtain ⟨g, rfl⟩ := conjF2Hom_surjective hK g'
  exact ⟨g, φ.injective (by rw [hρ, hg'])⟩

end Field

theorem g2DerivedNormalizerZorn :
    G2DerivedNormalizerZorn := by
  intro K _ _ _ hK
  exact ⟨normalizer_transport hK (modQEquivK hK) _ _ (congr_modQEquivK_symm hK)
      normalizer_two_Q,
    normalizer_transport hK (modOEquivK hK) _ _ (congr_modOEquivK_symm hK) normalizer_two_O⟩

theorem b46OffenderCommEqFix :
    B46OffenderCommEqFix :=
  b46OffenderCommEqFix_of VolI.g2NaturalCover_holds g2DerivedNormalizerZorn g2OffenderZorn

end CFSG.Quasithin.H13
