module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSModelL32
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSTypeA

public section

set_option synthInstance.maxSize 2000

namespace CFSG.Quasithin.F6.GoldAmS

open Matrix

theorem Q1_le_K1 : ∀ g : SL3, g ∈ Q1 → g ∈ K1 := by decide +kernel

theorem Q2_le_K2 : ∀ g : SL3, g ∈ Q2 → g ∈ K2 := by decide +kernel

theorem Q1_le_K2 : ∀ g : SL3, g ∈ Q1 → g ∈ K2 := by decide +kernel

theorem K1_normalizes_Q1 : ∀ g : SL3, g ∈ K1 → ∀ q : SL3, q ∈ Q1 → g * q * g⁻¹ ∈ Q1 := by
  decide +kernel

theorem K2_normalizes_Q2 : ∀ g : SL3, g ∈ K2 → ∀ q : SL3, q ∈ Q2 → g * q * g⁻¹ ∈ Q2 := by
  decide +kernel

theorem Q1_exp : ∀ q : SL3, q ∈ Q1 → q * q = 1 := by decide +kernel

theorem Q2_exp : ∀ q : SL3, q ∈ Q2 → q * q = 1 := by decide +kernel

theorem K1_cent : ∀ g : SL3, g ∈ K1 → (∀ q : SL3, q ∈ Q1 → g * q = q * g) → g ∈ Q1 := by
  decide +kernel

theorem K2_cent : ∀ g : SL3, g ∈ K2 → (∀ q : SL3, q ∈ Q2 → g * q = q * g) → g ∈ Q2 := by
  decide +kernel

theorem T_moved : ∀ x : SL3, x ∈ K1 ⊓ K2 → x ≠ 1 → ∃ g : SL3, g * x * g⁻¹ ∉ K1 ⊓ K2 := by
  decide +kernel

def q10 : SL3 := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

theorem Q1_ne_Q2 : Q1 ≠ Q2 := by
  intro h
  have h1 : q10 ∈ Q1 := by decide
  rw [h] at h1
  revert h1
  decide

theorem vertexA_K1 : VertexA K1 Q1 where
  le := fun g hg => Q1_le_K1 g hg
  normal := fun g hg q hq => K1_normalizes_Q1 g hg q hq
  card_A := card_K1
  card_Q := card_Q1
  exp := fun q hq => Q1_exp q hq
  cent := fun g hg h => K1_cent g hg fun q hq => h q hq

theorem vertexA_K2 : VertexA K2 Q2 where
  le := fun g hg => Q2_le_K2 g hg
  normal := fun g hg q hq => K2_normalizes_Q2 g hg q hq
  card_A := card_K2
  card_Q := card_Q2
  exp := fun q hq => Q2_exp q hq
  cent := fun g hg h => K2_cent g hg fun q hq => h q hq

theorem typeA_K1_K2 : TypeA K1 K2 :=
  ⟨Q1, Q2, vertexA_K1, vertexA_K2, fun g hg => Q1_le_K2 g hg, Q1_ne_Q2, card_K12⟩

end CFSG.Quasithin.F6.GoldAmS
