module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NOrbL
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7NOrbT
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Sub

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def gpairs : List (PL × PL) := genP1L.map fun g => (g, invPL g)

theorem gpairs_check : ∀ p ∈ gpairs, comp p.1 p.2 = idL ∧ p.2.length = 45 ∧
    ∀ x ∈ p.2, x < 45 := by
  decide +kernel

@[expose] def CLs1 : List (List ℕ × List PL) := nws1.map fun w => (w, CLof Pof Qof Al1 w)

@[expose] def CLs2 : List (List ℕ × List PL) := nws2.map fun w => (w, CLof Pof Qof Al2 w)

@[expose] def CL1 (w : List ℕ) : List PL := (CLs1.lookup w).getD []

@[expose] def CL2 (w : List ℕ) : List PL := (CLs2.lookup w).getD []

@[expose] def T1 (w : List ℕ) (p : PL × PL) : List ℕ :=
  nws1.getD ((tgt1.getD (nws1.idxOf w) []).getD (gpairs.idxOf p) 0) []

@[expose] def T2 (w : List ℕ) (p : PL × PL) : List ℕ :=
  nws2.getD ((tgt2.getD (nws2.idxOf w) []).getD (gpairs.idxOf p) 0) []

theorem tab_check : ∀ w ∈ nws2, Pof w = evalAL w ∧ Qof w = evalAL (invAL w) := by
  decide +kernel

theorem nws1_sub : ∀ w ∈ nws1, w ∈ nws2 := by decide +kernel

theorem lookup_map_self {α β : Type} [BEq α] [LawfulBEq α] (f : α → β) {l : List α} {w : α}
    (hw : w ∈ l) : (l.map fun w => (w, f w)).lookup w = some (f w) := by
  induction l with
  | nil => exact absurd hw (by simp)
  | cons a l ih =>
    by_cases h : w = a
    · subst h
      simp
    · have hl : w ∈ l := by
        rcases List.mem_cons.1 hw with h' | h'
        · exact absurd h' h
        · exact h'
      have hb : (w == a) = false := by simpa using h
      simp [List.lookup, hb, ih hl]

theorem CL_check1 : ∀ w ∈ nws1, CL1 w = CLof Pof Qof Al1 w := by
  intro w hw
  simp only [CL1, CLs1, lookup_map_self (CLof Pof Qof Al1) hw, Option.getD_some]

theorem CL_check2 : ∀ w ∈ nws2, CL2 w = CLof Pof Qof Al2 w := by
  intro w hw
  simp only [CL2, CLs2, lookup_map_self (CLof Pof Qof Al2) hw, Option.getD_some]

theorem nws1_check : nws1.Nodup ∧ ([] : List ℕ) ∈ nws1 ∧
    (∀ w ∈ nws1, (Pof w).getD 0 0 = 0) ∧
    (∀ w ∈ nws1, ∀ w' ∈ nws1, w ≠ w' → ∃ l ∈ CL1 w, l ∉ CL1 w') ∧
    ∀ w ∈ nws1, ∀ p ∈ gpairs, T1 w p ∈ nws1 ∧
      ∀ i ∈ gi1, comp (comp p.1 ((CL1 w).getD i [])) p.2 ∈ CL1 (T1 w p) := by
  decide +kernel

theorem nws2_check : nws2.Nodup ∧ ([] : List ℕ) ∈ nws2 ∧
    (∀ w ∈ nws2, (Pof w).getD 0 0 = 0) ∧
    (∀ w ∈ nws2, ∀ w' ∈ nws2, w ≠ w' → ∃ l ∈ CL2 w, l ∉ CL2 w') ∧
    ∀ w ∈ nws2, ∀ p ∈ gpairs, T2 w p ∈ nws2 ∧
      ∀ i ∈ gi2, comp (comp p.1 ((CL2 w).getD i [])) p.2 ∈ CL2 (T2 w p) := by
  decide +kernel

theorem hgl_P1 :
    ∀ s ∈ gensP1, ∃ sL ∈ genP1L, RepL sL (s : P45) := by
  intro s hs
  rw [gensP1] at hs
  rcases hs with ⟨k, rfl⟩ | rfl | rfl | rfl
  · exact ⟨gTL k, List.mem_append.2 (Or.inl (List.mem_map.2 ⟨k, List.mem_range.2 k.2, rfl⟩)),
      repL_gTA k⟩
  · exact ⟨fhatL, by simp [genP1L], repL_fhat⟩
  · exact ⟨c3L, by simp [genP1L], U42.repL_c3⟩
  · exact ⟨DL 1, by simp [genP1L], U42.repL_Dj 1⟩

theorem hgl_pairs :
    ∀ s ∈ gensP1, ∃ p ∈ gpairs, RepL p.1 (s : P45) ∧ RepL p.2 ((s⁻¹ : Ah) : P45) := by
  intro s hs
  obtain ⟨sL, hsL, hrep⟩ := hgl_P1 s hs
  have hc := gpairs_check (sL, invPL sL) (List.mem_map.2 ⟨sL, hsL, rfl⟩)
  exact ⟨(sL, invPL sL), List.mem_map.2 ⟨sL, hsL, rfl⟩, hrep,
    repL_inv_of_comp hrep hc.2.1 hc.2.2 hc.1⟩

theorem card_N1_A1 :
    Nat.card ↥(P1h ⊓ Subgroup.normalizer (A1h : Set Ah)) = 384 := by
  have h : Nat.card ↥(P1h ⊓ Subgroup.normalizer (A1h : Set Ah)) * nws1.length =
      Nat.card ↥P1h :=
    card_norm_of_lists (h1 := A1_check.1) (hmul := A1_check.2.1) A1_check.2.2.2.1 gi1
      gens_check.1 gens_check.2.1
      closure_gensP1 gpairs hgl_pairs nws1 nws1_check.1 Pof Qof
      (fun w hw => (tab_check w (nws1_sub w hw)).1) (fun w hw => (tab_check w (nws1_sub w hw)).2)
      CL1 CL_check1
      (fun w hw => mem_P1h_of_repL (repL_aW w) (by
        rw [← (tab_check w (nws1_sub w hw)).1]; exact nws1_check.2.2.1 w hw)) nws1_check.2.1
      nws1_check.2.2.2.1 T1 nws1_check.2.2.2.2
  have hl : nws1.length = 3 := by decide +kernel
  rw [hl, card_P1h] at h
  omega

theorem card_N1_A2 :
    Nat.card ↥(P1h ⊓ Subgroup.normalizer (A2h : Set Ah)) = 64 := by
  have h : Nat.card ↥(P1h ⊓ Subgroup.normalizer (A2h : Set Ah)) * nws2.length =
      Nat.card ↥P1h :=
    card_norm_of_lists (h1 := A2_check.1) (hmul := A2_check.2.1) A2_check.2.2.2.1 gi2
      gens_check.2.2.1 gens_check.2.2.2
      closure_gensP1 gpairs hgl_pairs nws2 nws2_check.1 Pof Qof
      (fun w hw => (tab_check w hw).1) (fun w hw => (tab_check w hw).2)
      CL2 CL_check2
      (fun w hw => mem_P1h_of_repL (repL_aW w) (by
        rw [← (tab_check w hw).1]; exact nws2_check.2.2.1 w hw)) nws2_check.2.1
      nws2_check.2.2.2.1 T2 nws2_check.2.2.2.2
  have hl : nws2.length = 18 := by decide +kernel
  rw [hl, card_P1h] at h
  omega

end CFSG.Quasithin.H13.F431.U42Aut
