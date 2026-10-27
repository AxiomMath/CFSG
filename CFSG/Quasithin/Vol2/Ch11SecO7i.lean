module

public import CFSG.Quasithin.Vol2.Ch11SecO7h
public import CFSG.Quasithin.Vol2.Ch11SecO7a
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint


namespace C10KH

theorem not_list701Excl_fixed2 {Y : Type} [Group Y] {N M A B : ℕ}
    (hY : Nat.card Y = N ∨ Nat.card Y * 3 = N) (hM : M * 3 = N)
    (hA : ¬ 2 ^ (A + 1) ∣ N)
    (hchkA : ∀ m ≤ A, 2 ^ m * ((2 ^ m) ^ 2 - 1) ≠ N ∧
      (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ N ∧
      (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) ≠ N ∧
      (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) ≠ N)
    (hfA : ¬ N ∣ 12096 ∧ 6 < N ∧ N ≠ 60 ∧ N ≠ 360 ∧ N ≠ 2520 ∧ N ≠ 1080 ∧ N ≠ 20160 ∧
      N ≠ 9999360 ∧ N ≠ 244823040)
    (hB : ¬ 2 ^ (B + 1) ∣ M)
    (hchkB : ∀ m ≤ B, 2 ^ m * ((2 ^ m) ^ 2 - 1) ≠ M ∧
      (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ M ∧
      (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) ≠ M ∧
      (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) ≠ M)
    (hfB : ¬ M ∣ 12096 ∧ 6 < M ∧ M ≠ 60 ∧ M ≠ 360 ∧ M ≠ 2520 ∧ M ≠ 1080 ∧ M ≠ 20160 ∧
      M ≠ 9999360 ∧ M ≠ 244823040) : ¬ List701Excl Y := by
  rcases hY with h | h
  · exact not_list701Excl_of_fixed h hA hchkA hfA.1 hfA.2.1 hfA.2.2
  · exact not_list701Excl_of_fixed (by omega) hB hchkB hfB.1 hfB.2.1 hfB.2.2

end C10KH


theorem list11_1_1List701Fact_holds : List11_1_1List701Fact := by
  intro X _ _ n hn hX hA hE Y _ π hπ hker hY
  rcases hX with h2 | ⟨rfl, h3⟩
  · obtain ⟨-, hZ, -⟩ := SecA.factList2Table_holds X n hn h2
    have hYc := C10KH.card_of_central_quot π hπ hker hZ
    rcases h2 with h | h | h | h | h | h | ⟨⟨m, rfl⟩, h⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exfalso
      have hc := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h
      rcases hYc with h' | h'
      · exact C10KH.not_list701Excl_twistedF4 (k := n) (by omega) rfl (Or.inl rfl)
          (by rw [h', hc, mul_one]) hY
      · exact C10KH.not_list701Excl_twistedF4 (k := n) (by omega) rfl (Or.inr rfl)
          (by rw [h', hc]) hY
    · exfalso
      have hc := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two
        (by omega) h.2
      rcases hYc with h' | h'
      · exact C10KH.not_list701Excl_triality (k := n) (by omega) rfl (Or.inl rfl)
          (by rw [h', hc, mul_one]) hY
      · exact C10KH.not_list701Excl_triality (k := n) (by omega) rfl (Or.inr rfl)
          (by rw [h', hc]) hY
    · exfalso
      rw [show 3 * m / 3 = m by omega] at h
      have hc := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two
        (show 1 ≤ m by omega) h.2
      rcases hYc with h' | h'
      · exact C10KH.not_list701Excl_triality (k := m) (by omega) rfl (Or.inl rfl)
          (by rw [h', hc, mul_one]) hY
      · exact C10KH.not_list701Excl_triality (k := m) (by omega) rfl (Or.inr rfl)
          (by rw [h', hc]) hY
  · obtain ⟨h1, h2⟩ := SecA.factList3Table_holds
    have hc1 : ∀ hz : Nat.card (Subgroup.center X) ∣ 3,
        Nat.card Y = Nat.card X ∨ Nat.card Y * 3 = Nat.card X :=
      fun hz => C10KH.card_of_central_quot π hπ hker hz
    have hc2 : Subgroup.center X = ⊥ → Nat.card Y = Nat.card X := fun hz => by
      rcases C10KH.card_of_central_quot π hπ hker (by rw [hz, Subgroup.card_bot]; norm_num)
        with h | h
      · exact h
      · exfalso
        have hk : π.ker = ⊥ := le_bot_iff.mp (hz ▸ hker)
        have := Nat.card_eq_of_bijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp hk, hπ⟩
        have hpos : 0 < Nat.card Y := Nat.card_pos_iff.mpr ⟨⟨1⟩, Finite.of_surjective π hπ⟩
        omega
    rcases h3 with h | h | ⟨p, hp, h5, h8, h⟩ | h | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h |
      h | h
    · exact Or.inr ⟨rfl, Or.inl h⟩
    · exact Or.inr ⟨rfl, Or.inr h⟩
    ·
      exfalso
      have hp11 := eleven_le_of_mod_five hp h5
      have hYX := hc2 (h2 X (Or.inl ⟨p, hp, hp11, h⟩)).2.1
      have hcp := H13.NotLie.card_psl2 h
      have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
        rw [pow_one]
        exact Nat.gcd_eq_left ((Nat.Prime.even_sub_one hp (by omega)).two_dvd)
      rw [hg, pow_one] at hcp
      have hev : 2 ∣ p * (p ^ 2 - 1) :=
        Dvd.dvd.mul_left (even_iff_two_dvd.mp
          (Nat.Odd.sub_odd ((hp.odd_of_ne_two (by omega)).pow) odd_one)) p
      exact C10KH.not_list701Excl_psl2 hp hp11 h8
        (by rw [hYX, hcp, Nat.div_mul_cancel hev]) hY
    ·
      exfalso
      have hYX := hc2 (h2 X (Or.inr (Or.inl h))).2.1
      have hcX : Nat.card X = 7800 := by rw [H13.NotLie.card_psl2 h]; norm_num
      exact C10KH.not_list701Excl_of_fixed (A := 3) (hYX.trans hcX) (by norm_num)
        (by decide) (by norm_num) (by norm_num) (by norm_num) hY
    · cases s
      ·
        exfalso
        have hcX : Nat.card X = 378000 := by rw [SecA.C11P9B.card_of_isSU3 h]; norm_num
        have hYc := hc1 (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inl h)).2.1
        rw [hcX] at hYc
        exact C10KH.not_list701Excl_fixed2 (M := 126000) (A := 4) (B := 4) hYc (by norm_num)
          (by norm_num) (by decide) (by norm_num) (by norm_num) (by decide) (by norm_num) hY
      ·
        exfalso
        have hYX := hc2 (h2 X (Or.inr (Or.inr (Or.inl h)))).2.1
        obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
        have hcX : Nat.card X = 372000 := by
          rw [Nat.card_congr (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
            3 K).symm).toEquiv,
            CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num), hK]
          decide
        exact C10KH.not_list701Excl_of_fixed (A := 5) (hYX.trans hcX) (by norm_num)
          (by decide) (by norm_num) (by norm_num) (by norm_num) hY
    · cases s
      ·
        exfalso
        have hcX : Nat.card X = 126000 := by
          have h0 := SecA.C11P9B.card_mul_gcd_of_isPSU3 (X := X) h
          norm_num at h0
          omega
        have hYc := hc1 (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr h)).2.1
        rw [hcX] at hYc
        exact C10KH.not_list701Excl_fixed2 (M := 42000) (A := 4) (B := 4) hYc (by norm_num)
          (by norm_num) (by decide) (by norm_num) (by norm_num) (by decide) (by norm_num) hY
      ·
        exfalso
        have hYX := hc2 (h2 X (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
        exact C10KH.not_list701Excl_of_fixed (A := 5) (hYX.trans (H13.NotLie.card_psl35 h))
          (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num) hY
    ·
      exfalso
      obtain ⟨e⟩ := h
      have hYc := hc1 (h1 X (Or.inr (Or.inr (Or.inl ⟨e⟩)))).2.1
      rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22] at hYc
      exact C10KH.not_list701Excl_fixed2 (M := 147840) (A := 7) (B := 7) hYc (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by decide) (by norm_num) hY
    ·
      exfalso
      have hYc := hc1 (h1 X (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
      rw [SecA.C10KH.card_of_isHat h, show Nat.card (NativeSporadic.Carrier .M22) = 443520
        from CFSG.Sporadic.Mathieu.card_M22] at hYc
      exact C10KH.not_list701Excl_fixed2 (M := 443520) (A := 7) (B := 7) hYc (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by decide) (by norm_num) hY
    ·
      exfalso
      obtain ⟨e⟩ := h
      have hYc := hc1 (h1 X (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))))).2.1
      rw [(Nat.card_congr e.toEquiv).trans card_nativeM23_1522] at hYc
      exact C10KH.not_list701Excl_fixed2 (M := 3400320) (A := 7) (B := 7) hYc (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by decide) (by norm_num) hY
    ·
      exfalso
      have hYX := hc2 (h2 X (Or.inr (Or.inr (Or.inr (Or.inr h))))).2.1
      obtain ⟨e⟩ := h
      let e' : X ≃* ↥CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
      exact C10KH.not_list701Excl_of_fixed (A := 3)
        (hYX.trans ((Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.J1.card_J))
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num) hY
    ·
      exfalso
      obtain ⟨e⟩ := h
      have hYc := hc1 (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e⟩)).2.1
      rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2] at hYc
      exact C10KH.not_list701Excl_fixed2 (M := 201600) (A := 7) (B := 7) hYc (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by decide) (by norm_num) hY
    ·
      exfalso
      obtain ⟨e⟩ := h
      have hYc := hc1 (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl ⟨e⟩)).2.1
      rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4] at hYc
      exact C10KH.not_list701Excl_fixed2 (M := 28925190348692520960) (A := 21) (B := 21) hYc
        (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
        (by decide +kernel) (by norm_num) hY
    ·
      exfalso
      obtain ⟨e⟩ := h
      have hYc := hc1 (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inl ⟨e⟩)).2.1
      rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS] at hYc
      exact C10KH.not_list701Excl_fixed2 (M := 14784000) (A := 9) (B := 9) hYc (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by decide) (by norm_num) hY
    ·
      exfalso
      obtain ⟨e⟩ := h
      have hYc := hc1 (h1 X (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inl ⟨e⟩)).2.1
      rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru] at hYc
      exact C10KH.not_list701Excl_fixed2 (M := 48642048000) (A := 14) (B := 14) hYc
        (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
        (by decide +kernel) (by norm_num) hY
    · exact absurd h hA
    · exact absurd h hE

end CFSG.Quasithin.Vol2.Ch11.SecE
