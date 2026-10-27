module

public import CFSG.Quasithin.Recognition.M12AscHFacts

public section

namespace CFSG.Quasithin

@[expose] def tpow (a : List (Fin 12)) : ℕ → List (Fin 12)
  | 0 => tid
  | k + 1 => tmul a (tpow a k)

@[expose] def tInvTabs : List (List (Fin 12)) :=
  qTabs.filter fun a => a ∉ FTabs ∧ tmul a a = tid

@[expose] def zInvTabs : List (List (Fin 12)) :=
  ascHTabs.filter fun b => tmul b b = tid ∧ b ≠ tid ∧ (b ∉ qTabs ∨ b ∈ FTabs)

@[expose] def pairTabsZ : List (List (Fin 12) × List (Fin 12)) :=
  (tInvTabs ×ˢ zInvTabs).filter fun p => decide (∃ k : ℕ, k < 24 ∧ tpow (tmul p.1 p.2) k = zTab)

theorem tpow_24 : ∀ a ∈ ascHTabs, tpow a 24 = tid := by decide +kernel

theorem pairTabsZ_length : pairTabsZ.length = 240 := by decide +kernel

theorem tInvTabs_nodup : tInvTabs.Nodup := qTabs_nodup.filter _

theorem zInvTabs_nodup : zInvTabs.Nodup := by decide +kernel

theorem pairTabsZ_nodup : pairTabsZ.Nodup := by
  unfold pairTabsZ
  exact (tInvTabs_nodup.product zInvTabs_nodup).filter _

theorem mem_tInvTabs {a : List (Fin 12)} :
    a ∈ tInvTabs ↔ a ∈ qTabs ∧ a ∉ FTabs ∧ tmul a a = tid := by
  simp [tInvTabs]

theorem mem_zInvTabs {b : List (Fin 12)} :
    b ∈ zInvTabs ↔ b ∈ ascHTabs ∧ tmul b b = tid ∧ b ≠ tid ∧ (b ∉ qTabs ∨ b ∈ FTabs) := by
  simp [zInvTabs]

theorem mem_pairTabsZ {p : List (Fin 12) × List (Fin 12)} :
    p ∈ pairTabsZ ↔ (p.1 ∈ qTabs ∧ p.1 ∉ FTabs ∧ tmul p.1 p.1 = tid) ∧
      (p.2 ∈ ascHTabs ∧ tmul p.2 p.2 = tid ∧ p.2 ≠ tid ∧ (p.2 ∉ qTabs ∨ p.2 ∈ FTabs)) ∧
      ∃ k < 24, tpow (tmul p.1 p.2) k = zTab := by
  obtain ⟨a, b⟩ := p
  simp [pairTabsZ, List.mem_product, mem_tInvTabs, mem_zInvTabs, and_assoc]

end CFSG.Quasithin
