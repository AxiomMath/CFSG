module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.ToAdditive

public section

namespace CFSG.Quasithin

namespace S1421QA17

namespace TXCode

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def mulC (c d : ℕ) : ℕ :=
  mulIdx (c % 128) (if c / 128 = 1 then betaIdx (d % 128) else d % 128) +
    128 * ((c / 128 + d / 128) % 2)

@[expose] def sqC (c : ℕ) : ℕ := mulC c c

@[expose] def centF (u : ℕ) : Finset ℕ := (Finset.range 256).filter (fun c => mulC u c = mulC c u)

@[expose] def n4F (cx : Finset ℕ) : ℕ := (cx.filter fun x => sqC (sqC x) = 0 ∧ sqC x ≠ 0).card

@[expose] def f216F (cx : Finset ℕ) : ℕ :=
  (cx.filter fun x => x ≠ 0 ∧ sqC x = 0 ∧ 16 ≤ (cx.filter fun t => mulC x t = mulC t x).card).card

@[expose] def jCode : ℕ := 129

@[expose] def bCard : ℕ := (centF jCode).card

@[expose] def bN4 : ℕ := n4F (centF jCode)

@[expose] def bF216 : ℕ := f216F (centF jCode)

@[expose] def CritF (u : ℕ) : Prop :=
  bCard < (centF u).card ∨ bN4 < n4F (centF u) ∨ bF216 < f216F (centF u)

instance (u : ℕ) : Decidable (CritF u) := by unfold CritF; infer_instance

theorem bCard_eq : bCard = 32 := by decide +kernel

theorem sqC_jCode : sqC jCode = 0 := by decide +kernel

theorem exists_sq_four : ∃ y ∈ centF jCode, sqC y = 4 := by decide +kernel

theorem sq_cases : ∀ x ∈ centF jCode, sqC x = 0 → (∃ y ∈ centF jCode, sqC y = x) →
    x = 0 ∨ x = 4 := by decide +kernel

theorem crit_all : ∀ u ∈ Finset.range 128, u ≠ 0 → sqC u = 0 → CritF u := by decide +kernel

theorem code_hom_invariants {m : ℕ → ℕ → ℕ} {CX CY : Finset ℕ} {g : ℕ → ℕ}
    (hgY : ∀ a ∈ CX, g a ∈ CY) (hinj : Set.InjOn g CX)
    (hclX : ∀ a ∈ CX, ∀ b ∈ CX, m a b ∈ CX)
    (hhom : ∀ a ∈ CX, ∀ b ∈ CX, g (m a b) = m (g a) (g b)) (h0 : 0 ∈ CX) (hg0 : g 0 = 0) :
    CX.card ≤ CY.card ∧
    (CX.filter fun x => m (m x x) (m x x) = 0 ∧ m x x ≠ 0).card ≤
      (CY.filter fun x => m (m x x) (m x x) = 0 ∧ m x x ≠ 0).card ∧
    (CX.filter fun x => x ≠ 0 ∧ m x x = 0 ∧
        16 ≤ (CX.filter fun t => m x t = m t x).card).card ≤
      (CY.filter fun x => x ≠ 0 ∧ m x x = 0 ∧
        16 ≤ (CY.filter fun t => m x t = m t x).card).card := by
  refine ⟨Finset.card_le_card_of_injOn g hgY hinj, ?_, ?_⟩
  · refine Finset.card_le_card_of_injOn g (fun a ha => ?_)
      (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    rw [Finset.mem_coe, Finset.mem_filter] at ha
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨haX, h4, h2⟩ := ha
    have haa : m a a ∈ CX := hclX a haX a haX
    refine ⟨hgY a haX, ?_, ?_⟩
    · rw [← hhom a haX a haX, ← hhom _ haa _ haa, h4, hg0]
    · intro hz
      apply h2
      rw [← hhom a haX a haX] at hz
      exact hinj haa h0 (hz.trans hg0.symm)
  · refine Finset.card_le_card_of_injOn g (fun a ha => ?_)
      (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    rw [Finset.mem_coe, Finset.mem_filter] at ha
    rw [Finset.mem_coe, Finset.mem_filter]
    obtain ⟨haX, hne, h2, h16⟩ := ha
    refine ⟨hgY a haX, fun hz => hne (hinj haX h0 (hz.trans hg0.symm)), ?_, ?_⟩
    · rw [← hhom a haX a haX, h2, hg0]
    · refine h16.trans (Finset.card_le_card_of_injOn g (fun t ht => ?_)
        (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))))
      rw [Finset.mem_coe, Finset.mem_filter] at ht
      rw [Finset.mem_coe, Finset.mem_filter]
      obtain ⟨htX, hct⟩ := ht
      refine ⟨hgY t htX, ?_⟩
      rw [← hhom a haX t htX, ← hhom t htX a haX, hct]

end TXCode

end S1421QA17

end CFSG.Quasithin
