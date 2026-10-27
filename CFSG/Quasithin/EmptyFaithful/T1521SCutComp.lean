module

public import CFSG.Quasithin.EmptyFaithful.T1521SCutDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SCutOrd
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Quasithin.Background.B69Iso
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Ru

public section

namespace CFSG.Quasithin.T1521SCut

open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Orders

theorem card_eq_of_isSporadic {X : Type} [Group X] {s : TauCeti.SporadicName} {n : ℕ}
    (hn : Nat.card (NativeSporadic.Carrier s) = n) (h : IsSporadic s X) : Nat.card X = n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, hn]

theorem card_nativeM23
    : Nat.card (NativeSporadic.Carrier .M23) = 10200960 := by
  show Nat.card ↥NativeSporadic.M23 = 10200960
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem card_mem_sporadicOrders
    {X : Type} [Group X]
    (h : IsSporadic .M11 X ∨ IsSporadic .M12 X ∨ IsSporadic .M22 X ∨ IsSporadic .M23 X ∨
      IsSporadic .M24 X ∨ IsSporadic .J2 X ∨ IsSporadic .HS X ∨ IsSporadic .He X ∨
      IsSporadic .Ru X) :
    Nat.card X ∈ sporadicOrders := by
  rcases h with h | h | h | h | h | h | h | h | h
  · rw [card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 h]
    decide
  · rw [card_eq_of_isSporadic (s := .M12) CFSG.Sporadic.Mathieu.card_M12 h]
    decide
  · rw [card_eq_of_isSporadic (s := .M22) CFSG.Sporadic.Mathieu.card_M22 h]
    decide
  · rw [card_eq_of_isSporadic (s := .M23) card_nativeM23 h]
    decide
  · rw [card_eq_of_isSporadic (s := .M24) CFSG.Sporadic.Mathieu.card_M24 h]
    decide
  · rw [card_eq_of_isSporadic (s := .J2) CFSG.Sporadic.J2.card_J2 h]
    decide
  · rw [card_eq_of_isSporadic (s := .HS) CFSG.Sporadic.HS.card_HS h]
    decide
  · rw [card_eq_of_isSporadic (s := .He) CFSG.Sporadic.He.card_He h]
    decide
  · rw [card_eq_of_isSporadic (s := .Ru) CFSG.Sporadic.Ru.card_Ru h]
    decide

theorem card_isTits
    {X : Type} [Group X] (h : IsTits X) : Nat.card X = 17971200 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Schreier.Tits.card_titsD

theorem card_isThreeD4
    {X : Type} [Group X] (h : Is3D4 2 1 X) : Nat.card X = 211341312 := by
  have h1 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  norm_num [CFSG.Open.ordTrialityD4] at h1
  exact h1

end Orders

section Cut

theorem cut_core {Y : Type} [Group Y] {k N : ℕ}
    (hfam : IsBender1516 Y ∨ (∃ n : ℕ, IsPSL 3 2 n Y) ∨ ∃ n : ℕ, IsPSp4 2 n Y)
    (hN : N = 6048 ∨ N = 17971200 ∨ N = 211341312 ∨ N = 9999360 ∨ N = 20160)
    (h : Nat.card Y * 2 ^ k = N) :
    N = 20160 ∧ Nat.card Y = 20160 ∧ k = 0 ∧ IsPSL 3 2 2 Y := by
  have hNle : N ≤ orderBound := by
    unfold orderBound
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hN40 : N < 2 ^ 40 := by
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hY : Nat.card Y ≤ orderBound := by
    refine le_trans ?_ hNle
    rw [← h]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  obtain ⟨hmem, h20⟩ := famCases hfam hY
  have hk : k < 40 := lt_forty_of_mul_two_pow (famOrders_pos _ hmem) hN40 h
  obtain ⟨h1, h2, h3, h4, h5⟩ := famOrders_mul_two_pow _ hmem k hk
  rcases hN with rfl | rfl | rfl | rfl | rfl
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact absurd h h4
  · obtain ⟨hm, hk0⟩ := h5 h
    exact ⟨rfl, hm, hk0, h20 hm⟩

end Cut

end CFSG.Quasithin.T1521SCut

namespace CFSG.Quasithin

open CFSG.Quasithin.T1521SCut

theorem typeCutComp1521
    : TypeCutComp1521 := by
  intro G _ _ L _ hfam hbad
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  have hcard : Nat.card ↥L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * 2 ^ k := by
    rw [(CFSG.pCore 2 ↥L).card_eq_card_quotient_mul_card_subgroup, hk]
  rcases hbad with (hU | hT | hD) | hS | (hL4 | hL5)
  · have h1 := card_isPSU_three_three_one hU
    have h2 := (cut_core hfam (Or.inl h1) hcard.symm).1
    omega
  · have h1 := card_isTits hT
    have h2 := (cut_core hfam (Or.inr (Or.inl h1)) hcard.symm).1
    omega
  · have h1 := card_isThreeD4 hD
    have h2 := (cut_core hfam (Or.inr (Or.inr (Or.inl h1))) hcard.symm).1
    omega
  · have hs := card_mem_sporadicOrders hS
    have hle : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≤ orderBound := by
      unfold orderBound
      simp only [sporadicOrders, List.mem_cons, List.not_mem_nil, or_false] at hs
      omega
    exact famOrders_ne_sporadic _ (famCases hfam hle).1 _ hs rfl
  · obtain ⟨-, -, hk0, h34⟩ := cut_core hfam (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (by rw [← card_isPSL_four_two_one hL4]; exact hcard.symm)
    have hbot : CFSG.pCore 2 ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0]; rfl)
    have e : ↥L ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (QuotientGroup.quotientBot (G := ↥L)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hbot.symm)
    obtain ⟨-, K4, _, _, hK4, ⟨e4⟩⟩ := hL4
    obtain ⟨-, K3, _, _, hK3, ⟨e3⟩⟩ := h34
    exact B69.not_equiv_sl_four_psl_three (K := K4) (F := K3) (by rw [hK4]; norm_num)
      (by rw [hK3]; norm_num) e4 (e.trans e3)
  · have h1 := card_isPSL_five_two_one hL5
    have h2 := (cut_core hfam (Or.inr (Or.inr (Or.inr (Or.inl h1)))) hcard.symm).1
    omega

end CFSG.Quasithin
