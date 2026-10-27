module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Rk

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit

@[expose] def L4 : List ℕ := [0, 8, 32, 40]

@[expose] def L8 : List ℕ := [0, 8, 32, 40, 129, 137, 161, 169]

theorem L4_xor : ∀ a ∈ L4, ∀ b ∈ L4, a ^^^ b ∈ L4 := by decide

theorem L8_xor : ∀ a ∈ L8, ∀ b ∈ L8, a ^^^ b ∈ L8 := by decide

theorem L4_o0 : ∀ x ∈ L4, x ∈ o0Codes := by decide

theorem L4_inj : ∀ c ∈ L4, ∀ d ∈ L4, (d = c ∨ d = c ^^^ 129) → c = d := by decide

theorem L8_split : ∀ c ∈ L8, ∃ d ∈ L4, c = d ∨ c = d ^^^ 129 := by decide

theorem L4_sub_L8 : ∀ c ∈ L4, c ∈ L8 := by decide

theorem L4_ell0 : ∀ c ∈ ell0, c ∈ L4 := by decide

theorem act_L4 (g : Gam) (hg : g ∈ Pline) : ∀ c ∈ L4, act g c ∈ L4 := by
  intro c hc
  have : c = 0 ∨ c ∈ ell0 := by revert c; decide
  rcases this with rfl | h
  · rw [act_zero]
    decide
  · exact L4_ell0 _ (hg c h)

@[expose] def lineQ : Subgroup ModQ where
  carrier := {x | ∃ c : O0C, c.1 ∈ L4 ∧ codeQ c = x}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨o0Xor a b, L4_xor _ ha _ hb, codeQ_xor a b⟩
  one_mem' := ⟨o0Zero, by decide, codeQ_zero⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (codeQ_inv a).symm⟩

@[expose] def lineO : Subgroup ModO where
  carrier := {x | ∃ c : O0C, c.1 ∈ L8 ∧ codeO c = x}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨o0Xor a b, L8_xor _ ha _ hb, codeO_xor a b⟩
  one_mem' := ⟨o0Zero, by decide, codeO_zero⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (codeO_inv a).symm⟩

theorem card_lineQ : Nat.card lineQ = 4 := by
  have hc := card_o0C_filter fun c => decide (c ∈ L4)
  have h4 : (o0Codes.filter fun c => decide (c ∈ L4)).length = 4 := by decide +kernel
  rw [h4] at hc
  rw [← hc]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : {c : O0C // decide (c.1 ∈ L4) = true} =>
      (⟨codeQ c.1, c.1, by simpa using c.2, rfl⟩ : lineQ)) ⟨?_, ?_⟩)).symm
  · intro a b h
    have := (codeQ_eq_iff a.1 b.1).1 (congrArg Subtype.val h)
    exact Subtype.ext (Subtype.ext (L4_inj _ (by simpa using a.2) _ (by simpa using b.2) this))
  · rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, by simpa using hc⟩, rfl⟩

theorem card_lineO : Nat.card lineO = 8 := by
  have hc := card_o0C_filter fun c => decide (c ∈ L8)
  have h8 : (o0Codes.filter fun c => decide (c ∈ L8)).length = 8 := by decide +kernel
  rw [h8] at hc
  rw [← hc]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : {c : O0C // decide (c.1 ∈ L8) = true} =>
      (⟨codeO c.1, c.1, by simpa using c.2, rfl⟩ : lineO)) ⟨?_, ?_⟩)).symm
  · intro a b h
    exact Subtype.ext (codeO_injective (congrArg Subtype.val h))
  · rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, by simpa using hc⟩, rfl⟩

end CFSG.Quasithin.H13.U3.GC137.S2

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.U3.GC137.S2

theorem lineQ_stable : ∀ g ∈ Pline, ∀ w ∈ lineQ, g2QAct (ZMod 2) g w ∈ lineQ := by
  rintro g hg _ ⟨c, hc, rfl⟩
  rw [g2QAct_codeQ]
  exact ⟨o0Act g c, act_L4 g hg c.1 hc, rfl⟩

theorem lineO_stable : ∀ g ∈ Pline, ∀ w ∈ lineO, g2OAct (ZMod 2) g w ∈ lineO := by
  rintro g hg _ ⟨c, hc, rfl⟩
  rw [g2OAct_codeO]
  obtain ⟨d, hd, hcd⟩ := L8_split c.1 hc
  refine ⟨o0Act g c, ?_, rfl⟩
  have hd' := act_L4 g hg d hd
  have h129 : (129 : ℕ) ∈ L8 := by decide
  have hd256 : d < 256 := (mem_o0Codes.1 (L4_o0 d hd)).1
  rcases hcd with h | h
  · have : (o0Act g c).1 = act g d := by
      change act g c.1 = _
      rw [h]
    rw [this]
    exact L4_sub_L8 _ hd'
  · have : (o0Act g c).1 = act g d ^^^ 129 := by
      change act g c.1 = _
      rw [h, act_xor g hd256 (by norm_num), act_fix_129]
    rw [this]
    exact L8_xor _ (L4_sub_L8 _ hd') _ h129

theorem lineQ_facts : ∃ l₀ : Subgroup ModQ,
    fixV ((g2Derived (ZMod 2)).map (g2QAct (ZMod 2))) ≤ l₀ ∧
      Nat.card ↥l₀ = 4 * Nat.card ↥(fixV ((g2Derived (ZMod 2)).map (g2QAct (ZMod 2)))) ∧
      ∀ g ∈ Pline, ∀ w ∈ l₀, g2QAct (ZMod 2) g w ∈ l₀ := by
  refine ⟨lineQ, ?_, ?_, lineQ_stable⟩
  · rw [fixV_derived_Q]
    exact bot_le
  · rw [fixV_derived_Q, card_lineQ]
    simp

theorem lineO_facts : ∃ l₀ : Subgroup ModO,
    fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) ≤ l₀ ∧
      Nat.card ↥l₀ = 4 * Nat.card ↥(fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2)))) ∧
      ∀ g ∈ Pline, ∀ w ∈ l₀, g2OAct (ZMod 2) g w ∈ l₀ := by
  refine ⟨lineO, ?_, ?_, lineO_stable⟩
  · rw [fixV_derived_O, Subgroup.zpowers_le]
    exact ⟨⟨129, by decide⟩, by decide, rfl⟩
  · rw [fixV_derived_O, card_zpowers_zO, card_lineO]

end CFSG.Quasithin.H13.U3.GC137
