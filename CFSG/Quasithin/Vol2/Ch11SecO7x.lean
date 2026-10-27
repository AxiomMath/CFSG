module

public import CFSG.Quasithin.Vol2.Ch11SecO7s
public import CFSG.Quasithin.Vol2.Ch11SecO7v

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

variable {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y} {X : Type} [Group X]

theorem card_of_isAlt5 {Q : Type} [Group Q] (h : IsAlt 5 Q) : Nat.card Q = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

omit [Finite Y] in
theorem card_dvd_B (e : ModO2 B ≃* X) : Nat.card X ∣ Nat.card ↥B :=
  (Nat.card_congr e.toEquiv).symm ▸ Subgroup.card_quotient_dvd_card _

theorem card_dvd_of_isExt (e : ModO2 B ≃* X) {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V) {N : ℕ}
    (hPY : ∀ (Q : Type) [Group Q], PY Q → Nat.card Q = N) (h : IsExt ↥B PV PY) :
    Nat.card X ∣ N := by
  obtain ⟨V, hVn, hV, hQ⟩ := h
  rw [← Nat.card_congr e.toEquiv, ← hPY _ hQ]
  exact card_modO2_dvd_quot (hPV _ hV)

theorem card_modO2_mul (e : ModO2 B ≃* X) : ∃ b, Nat.card ↥B = Nat.card X * 2 ^ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
  refine ⟨b, ?_⟩
  rw [(CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup, hb,
    Nat.card_congr e.toEquiv]

theorem card_modO2_of_simple (e : ModO2 B ≃* X) [IsSimpleGroup ↥B] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hdvd : q ∣ Nat.card ↥B) : Nat.card X = Nat.card ↥B := by
  rw [← Nat.card_congr e.toEquiv]
  exact Nat.card_congr (modO2EquivOfBot (pCore_eq_bot_of_simple hq hq2 hdvd)).toEquiv


theorem n_eq_two_of_dvd {n : ℕ} (hn : 2 ≤ n) (hl : List11_1_1Two X n ∨ (n = 2 ∧ List11_1_1Three X))
    {N : ℕ} (hN : Nat.card X ∣ N) (h8 : ¬ 2 ^ 8 ∣ N) : n = 2 := by
  rcases hl with h2 | ⟨rfl, -⟩
  · exact list2_n_eq_two hn h2 fun h => h8 (h.trans hN)
  · rfl

theorem two_pow_six_dvd {n : ℕ} (hn : 2 ≤ n) (h : List11_1_1Two X n) : 2 ^ 6 ∣ Nat.card X := by
  obtain ⟨A, u, ⟨hN, -⟩, hA⟩ := list2_profile hn h
  rw [hN]
  exact (Nat.pow_dvd_pow 2 (six_le_of_list2 hn hA)).mul_right u

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
