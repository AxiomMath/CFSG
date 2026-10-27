module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplR.RadicalParam

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem mem_fixV_Rg4_iff (w : PairN 4) :
    w ∈ fixV Rg4 ↔ ∀ ε : Fin 4 → ZMod 2, radicalHom (Multiplicative.ofAdd ε) w = w := by
  constructor
  · intro h ε
    exact h _ (radicalHom_mem_Rg4 ε)
  · intro h x hx
    rw [← radicalHom_range] at hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨ε, rfl⟩ := Multiplicative.ofAdd.surjective y
    exact h ε

theorem pairVec_mem_fixV_Rg4_iff (a b : Fin 4 → ZMod 2) :
    pairVec a b ∈ fixV Rg4 ↔ a 2 = 0 ∧ a 3 = 0 ∧ b 0 = 0 ∧ b 1 = 0 := by
  rw [mem_fixV_Rg4_iff]
  simp only [radicalHom_pairVec, pairVec_inj]
  constructor
  · intro h
    have h0 := h ![1, 0, 0, 0]
    have h1 := h ![0, 1, 0, 0]
    have h2 := h ![0, 0, 1, 0]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Rfst] using congrFun h0.1 0
    · simpa [Rfst] using congrFun h1.1 0
    · simpa [Rsnd] using congrFun h0.2 2
    · simpa [Rsnd] using congrFun h2.2 2
  · rintro ⟨ha2, ha3, hb0, hb1⟩ ε
    constructor
    · funext i
      fin_cases i <;> simp [Rfst, ha2, ha3]
    · funext i
      fin_cases i <;> simp [Rsnd, hb0, hb1]

private theorem card_fixV_Rg4_aux :
    Nat.card {p : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) //
      p.1 2 = 0 ∧ p.1 3 = 0 ∧ p.2 0 = 0 ∧ p.2 1 = 0} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_fixV_Rg4 : Nat.card ↥(fixV Rg4) = 16 := by
  rw [← card_fixV_Rg4_aux]
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.prodCongr Multiplicative.toAdd Multiplicative.toAdd) ?_)
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  exact pairVec_mem_fixV_Rg4_iff a b

theorem rk_fixV_Rg4 : rk ↥(fixV Rg4) = 4 := by
  unfold rk
  rw [card_fixV_Rg4, show (16 : ℕ) = 2 ^ 4 by norm_num]
  exact padicValNat.prime_pow 4

end CFSG.ASVolI.ChH
