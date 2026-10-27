module

public import CFSG.Quasithin.Vol2.Ch10SecKRTa
public import CFSG.Quasithin.Vol2.Ch10SecKRTd

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch11.SecA

theorem false_of_card_168 {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {m : ℕ}
    (hD : BarData B m) (hBL : B ≤ L) (hL : Nat.card ↥L = 2 ^ 3 * 21) : False := by
  obtain ⟨a, ha⟩ := hD.card
  have hdvd : Nat.card ↥B ∣ Nat.card ↥L := Subgroup.card_dvd_of_le hBL
  rw [ha, hL] at hdvd
  have h1 : oSL2 m ∣ 2 ^ 3 * 21 := dvd_of_mul_left_dvd hdvd
  have hodd := odd_oSL2_arith (show 1 ≤ m by have := hD.two_le; omega)
  have h2 : oSL2 m ∣ 21 :=
    (Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_left h1
  have h15 : 15 ≤ oSL2 m := by
    rcases hD.two_le.lt_or_eq with h | h
    · have := oSL2_lt_oSL2 h
      simp only [oSL2] at this ⊢
      omega
    · subst h
      decide
  have h21 : oSL2 m ≤ 21 := Nat.le_of_dvd (by norm_num) h2
  apply oSL2_ne_21 (n := m)
  generalize oSL2 m = x at h2 h15 h21 ⊢
  interval_cases x <;> first | rfl | norm_num at h2

theorem card_of_isSL3_two {X : Type} [Group X] (h : IsSL3 (2 ^ 1) X) :
    Nat.card X = 2 ^ 3 * 21 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hF]
  norm_num

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m M : ℕ}

theorem typeB_or_typeC (cfg : B0KConfig G T L I H K M₁ J n m)
    (hA : A312Case (modO2Image M₁ K) (modO2Image M₁ J)) (hM : SecC.C10KH.B56Card M)
    (hc : Nat.card ↥(modO2Image M₁ J) = M ∨ Nat.card ↥(modO2Image M₁ J) = 3 * M) :
    B0KTypeB M₁ K J ∨ B0KTypeC M₁ K J := by
  have hD := barData cfg
  rcases rows_KF1 hD hA hM hc with h2 | h6
  · left
    refine ⟨h2, ?_⟩
    obtain ⟨f, ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩ | ⟨hf, h⟩⟩ :=
      SecC.C10KH.goodLie_of_rank2 hM hc h2.2.1
    · rcases hf.lt_or_eq with hf | rfl
      · exact ⟨f, hf, Or.inl h⟩
      · exact (false_of_card_168 hD (Kbar_le_Jbar cfg) (card_L32 h)).elim
    · rcases hf.lt_or_eq with hf | rfl
      · exact ⟨f, hf, Or.inr (Or.inl h)⟩
      · exact (false_of_card_168 hD (Kbar_le_Jbar cfg) (card_of_isSL3_two h)).elim
    · exact ⟨f, hf, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨f, hf, Or.inr (Or.inr (Or.inr h))⟩
  · exact Or.inr h6

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
