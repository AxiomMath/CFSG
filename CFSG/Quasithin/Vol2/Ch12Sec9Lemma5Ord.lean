module

public import CFSG.Quasithin.Background.F918P2
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.GH74.Orders.LieType
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Ru
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.Orders

namespace L1295B

@[expose] def FourListOrder (N : ℕ) : Prop :=
  (∃ n, 2 ≤ n ∧ (N = ordA 1 (2 ^ n) ∨ N = ordSuzuki (2 ^ n) ∨ N = ordTwistedA 2 (2 ^ n))) ∨
    (∃ n, 1 ≤ n ∧ N = ordA 2 (2 ^ n)) ∨ (∃ n, 2 ≤ n ∧ N = ordBC 2 (2 ^ n)) ∨ N = 360 ∨
    (∃ n, 2 ≤ n ∧ N = ordG2 (2 ^ n)) ∨ N = 6048 ∨ N = 20160 ∨ N = 9999360 ∨ N = 2520 ∨
    N = 443520

theorem ordA_one_two_pow {n : ℕ} (hn : 1 ≤ n) : ordA 1 (2 ^ n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have h : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hn)
  unfold ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton, show (1 + 1 : ℕ) = 2 by rfl, h, Nat.div_one]

theorem ordA_two_eq (q : ℕ) :
    ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  unfold ordA
  rw [show 2 * (2 + 1) / 2 = 3 by rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl,
    Finset.prod_pair (by norm_num)]

theorem two_part_ordA_one {n : ℕ} (hn : 1 ≤ n) : ∃ r, Odd r ∧ ordA 1 (2 ^ n) = 2 ^ n * r :=
  ⟨_, by rw [← pow_mul]; exact odd_two_pow_sub_one (by omega), ordA_one_two_pow hn⟩

theorem two_part_ordSuzuki {n : ℕ} (hn : 1 ≤ n) :
    ∃ r, Odd r ∧ ordSuzuki (2 ^ n) = 2 ^ (n * 2) * r :=
  (profile_ordSuzuki hn).two

theorem two_part_ordTwistedA_two {n : ℕ} (hn : 1 ≤ n) :
    ∃ r, Odd r ∧ ordTwistedA 2 (2 ^ n) = 2 ^ (n * 3) * r :=
  (profile_ordTwistedA (n := 2) le_rfl hn).two

theorem two_part_ordA_two {n : ℕ} (hn : 1 ≤ n) : ∃ r, Odd r ∧ ordA 2 (2 ^ n) = 2 ^ (n * 3) * r :=
  (profile_ordA (n := 2) (by norm_num) hn).two

theorem two_part_ordBC_two {n : ℕ} (hn : 1 ≤ n) : ∃ r, Odd r ∧ ordBC 2 (2 ^ n) = 2 ^ (n * 4) * r :=
  (profile_ordBC (n := 2) hn).two

theorem two_part_ordG2 {n : ℕ} (hn : 1 ≤ n) : ∃ r, Odd r ∧ ordG2 (2 ^ n) = 2 ^ (n * 6) * r :=
  (profile_ordG2 hn).two

theorem ordTwistedA_two_eq (q : ℕ) (hq : 1 ≤ q) :
    ordTwistedA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  have h1 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    rw [show ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq)]; ring]
    exact Int.toNat_natCast _
  have h2 : ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    rw [show ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  unfold ordTwistedA
  rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num), h1, h2]

variable {X : Type} [Group X]

theorem card_of_isPSU_three_three (h : IsPSU 3 3 1 X) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem card_of_isAlt {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k X) : Nat.card X = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

theorem card_of_fourList
    (h : FourList X) : FourListOrder (Nat.card X) := by
  rcases h with ⟨n, hn, hX | hX | hX⟩ | ⟨n, hn, hX⟩ | ⟨n, hn, hX⟩ | hX | ⟨n, hn, hX⟩ | hX |
    hX | hX | hX | hX
  · exact Or.inl ⟨n, hn, Or.inl ((CFSG.Timmesfeld.card_statedClassicalModel_two hX).1 rfl)⟩
  · obtain ⟨-, a, -, -, hcard⟩ := CFSG.GH74.card_of_suzukiModel hX
    exact Or.inl ⟨n, hn, Or.inr (Or.inl hcard)⟩
  · exact Or.inl ⟨n, hn, Or.inr (Or.inr ((CFSG.Timmesfeld.card_statedClassicalModel_two hX).2.1
      rfl))⟩
  · exact Or.inr (Or.inl ⟨n, hn, (CFSG.Timmesfeld.card_statedClassicalModel_two hX).1 rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn,
      (CFSG.Timmesfeld.card_statedClassicalModel_two hX).2.2.1 rfl⟩))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [card_of_isAlt (by norm_num) hX]
    decide
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn,
      (CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hX).1 rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (card_of_isPSU_three_three hX))))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hX).1 rfl]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hX).1 rfl]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))
    rw [card_of_isAlt (by norm_num) hX]
    decide
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
    obtain ⟨e⟩ := hX
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22

theorem not_fourListOrder {N a r : ℕ} (hr : Odd r) (hN : N = 2 ^ a * r)
    (hL2 : 1 ≤ a → ordA 1 (2 ^ a) ≠ N)
    (hSz : ∀ n, 1 ≤ n → n * 2 = a → ordSuzuki (2 ^ n) ≠ N)
    (hU3 : ∀ n, 1 ≤ n → n * 3 = a → ordTwistedA 2 (2 ^ n) ≠ N ∧ ordA 2 (2 ^ n) ≠ N)
    (hSp : ∀ n, 1 ≤ n → n * 4 = a → ordBC 2 (2 ^ n) ≠ N)
    (hG2 : ∀ n, 1 ≤ n → n * 6 = a → ordG2 (2 ^ n) ≠ N)
    (hfix : N ≠ 360 ∧ N ≠ 6048 ∧ N ≠ 20160 ∧ N ≠ 9999360 ∧ N ≠ 2520 ∧ N ≠ 443520) :
    ¬ FourListOrder N := by
  have key : ∀ {m k s : ℕ}, Odd s → m = 2 ^ k * s → m = N → k = a := fun hs hm hmN =>
    eq_of_two_pow_mul_odd hs hr (hm.symm.trans (hmN.trans hN))
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfix
  rintro (⟨n, hn, h | h | h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | ⟨n, hn, h⟩ | h | h | h | h | h)
  · obtain ⟨s, hs, hm⟩ := two_part_ordA_one (by omega : 1 ≤ n)
    have hna := key hs hm h.symm
    subst hna
    exact hL2 (by omega) h.symm
  · obtain ⟨s, hs, hm⟩ := two_part_ordSuzuki (by omega : 1 ≤ n)
    exact hSz n (by omega) (key hs hm h.symm) h.symm
  · obtain ⟨s, hs, hm⟩ := two_part_ordTwistedA_two (by omega : 1 ≤ n)
    exact (hU3 n (by omega) (key hs hm h.symm)).1 h.symm
  · obtain ⟨s, hs, hm⟩ := two_part_ordA_two hn
    exact (hU3 n hn (key hs hm h.symm)).2 h.symm
  · obtain ⟨s, hs, hm⟩ := two_part_ordBC_two (by omega : 1 ≤ n)
    exact hSp n (by omega) (key hs hm h.symm) h.symm
  · exact h1 h
  · obtain ⟨s, hs, hm⟩ := two_part_ordG2 (by omega : 1 ≤ n)
    exact hG2 n (by omega) (key hs hm h.symm) h.symm
  · exact h2 h
  · exact h3 h
  · exact h4 h
  · exact h5 h
  · exact h6 h

theorem not_fourListOrder_M24 : ¬ FourListOrder 244823040 :=
  not_fourListOrder (a := 10) (r := 239085) (by decide) (by norm_num)
    (fun _ => by rw [ordA_one_two_pow (by norm_num)]; norm_num)
    (fun n _ hn => by obtain rfl : n = 5 := by omega
                      norm_num [ordSuzuki])
    (fun n _ hn => absurd hn (by omega)) (fun n _ hn => absurd hn (by omega))
    (fun n _ hn => absurd hn (by omega)) (by norm_num)

theorem not_fourListOrder_J4 : ¬ FourListOrder 86775571046077562880 :=
  not_fourListOrder (a := 21) (r := 41377816699065) (by decide) (by norm_num)
    (fun _ => by rw [ordA_one_two_pow (by norm_num)]; norm_num)
    (fun n _ hn => absurd hn (by omega))
    (fun n _ hn => by
      obtain rfl : n = 7 := by omega
      rw [ordTwistedA_two_eq _ (by norm_num), ordA_two_eq]
      norm_num)
    (fun n _ hn => absurd hn (by omega)) (fun n _ hn => absurd hn (by omega)) (by norm_num)

theorem not_fourListOrder_M23 : ¬ FourListOrder 10200960 :=
  not_fourListOrder (a := 7) (r := 79695) (by decide) (by norm_num)
    (fun _ => by rw [ordA_one_two_pow (by norm_num)]; norm_num)
    (fun n _ hn => absurd hn (by omega)) (fun n _ hn => absurd hn (by omega))
    (fun n _ hn => absurd hn (by omega)) (fun n _ hn => absurd hn (by omega)) (by norm_num)

theorem not_fourListOrder_HS : ¬ FourListOrder 44352000 :=
  not_fourListOrder (a := 9) (r := 86625) (by decide) (by norm_num)
    (fun _ => by rw [ordA_one_two_pow (by norm_num)]; norm_num)
    (fun n _ hn => absurd hn (by omega))
    (fun n _ hn => by
      obtain rfl : n = 3 := by omega
      rw [ordTwistedA_two_eq _ (by norm_num), ordA_two_eq]
      norm_num)
    (fun n _ hn => absurd hn (by omega)) (fun n _ hn => absurd hn (by omega)) (by norm_num)

theorem not_fourListOrder_He : ¬ FourListOrder 4030387200 :=
  not_fourListOrder (a := 10) (r := 3935925) (by decide) (by norm_num)
    (fun _ => by rw [ordA_one_two_pow (by norm_num)]; norm_num)
    (fun n _ hn => by obtain rfl : n = 5 := by omega
                      norm_num [ordSuzuki])
    (fun n _ hn => absurd hn (by omega)) (fun n _ hn => absurd hn (by omega))
    (fun n _ hn => absurd hn (by omega)) (by norm_num)

theorem not_fourListOrder_Ru : ¬ FourListOrder 145926144000 :=
  not_fourListOrder (a := 14) (r := 8906625) (by decide) (by norm_num)
    (fun _ => by rw [ordA_one_two_pow (by norm_num)]; norm_num)
    (fun n _ hn => by obtain rfl : n = 7 := by omega
                      norm_num [ordSuzuki])
    (fun n _ hn => absurd hn (by omega)) (fun n _ hn => absurd hn (by omega))
    (fun n _ hn => absurd hn (by omega)) (by norm_num)

theorem card_M23 :
    Nat.card NativeSporadic.M23 = 10200960 := by
  have h := CFSG.M23.M23Group.card_M23
  rw [← Nat.card_eq_fintype_card] at h
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact h

theorem isSimpleGroup_and_not_fourListOrder
    {Q : Type} [Group Q]
    (h : Nonempty (Q ≃* NativeSporadic.M24) ∨ Nonempty (Q ≃* NativeSporadic.J4) ∨
      Nonempty (Q ≃* NativeSporadic.M23) ∨ Nonempty (Q ≃* NativeSporadic.HS) ∨
      Nonempty (Q ≃* NativeSporadic.He) ∨ Nonempty (Q ≃* NativeSporadic.Ru)) :
    IsSimpleGroup Q ∧ ¬ FourListOrder (Nat.card Q) := by
  rcases h with h | h | h | h | h | h <;> obtain ⟨e⟩ := h
  · refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2 e, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
    exact not_fourListOrder_M24
  · refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J4.isSimpleGroup_J4 e, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J4.card_J4]
    exact not_fourListOrder_J4
  · refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2 e, ?_⟩
    rw [Nat.card_congr e.toEquiv, card_M23]
    exact not_fourListOrder_M23
  · refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS]
    exact not_fourListOrder_HS
  · refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.He.card_He]
    exact not_fourListOrder_He
  · refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ru.isSimpleGroup_Ru e, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ru.card_Ru]
    exact not_fourListOrder_Ru

end L1295B

end CFSG.Quasithin.H13
