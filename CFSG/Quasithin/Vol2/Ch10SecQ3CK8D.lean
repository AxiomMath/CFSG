module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem card_of_alt7 (h : AlternatingNatural L U Z 7) : Nat.card ↥L = 2520 := by
  obtain ⟨π, hπ⟩ := h
  have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  rw [← Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)]
  exact (card_alternatingGroup1527d 7 (by norm_num)).trans (by decide)

theorem card_of_a7Four (h : A7Four L U Z) : Nat.card ↥L = 2520 := by
  obtain ⟨α, π, hπ⟩ := h
  have hinj := FFC.injective_of_faithful_sec (FFC.a7Four_faithful α) hπ
  rw [← Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)]
  exact (card_alternatingGroup1527d 7 (by norm_num)).trans (by decide)

theorem pair_shape (hN : Nat.card ↥L = 2520 ∨ Nat.card ↥L = 7560) (h : B42ModulePair L U Z) :
    AlternatingNatural L U Z 7 ∨ A7Four L U Z := by
  have h7 : 2520 ≤ Nat.card ↥L := by omega
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact (not_sl2 hN h).elim
  · exact (not_sl3 hN h).elim
  · exact (not_sp4 hN h).elim
  · exact (not_g2 hN h).elim
  · exact (not_g2d hN h).elim
  · exact (not_alternatingNatural1527d (by norm_num)
      (lt_of_lt_of_le (by decide) h7) h).elim
  · exact (not_alternatingNatural1527d (by norm_num)
      (lt_of_lt_of_le (by decide) h7) h).elim
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    obtain ⟨F, _, _, Γ₀, hF, -, hhat, -, π, hπ⟩ := h
    have h1 : Nat.card ↥L ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective π hπ.1
    have h2 : Nat.card ↥Γ₀ = 1080 :=
      card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        decide)
    omega
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    exact (not_surj_sl (Or.inl rfl) hN π hπ.1).elim
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    exact (not_surj_sl (Or.inr rfl) hN π hπ.1).elim
  · obtain ⟨π, hπ⟩ := h
    exact (not_surj_sl (Or.inl rfl) hN π hπ.1).elim
  · obtain ⟨π, hπ⟩ := h
    exact (not_surj_sl (Or.inr rfl) hN π hπ.1).elim

theorem part1_shape [Finite V] {H : Subgroup (MulAut V)} (h1 : B51Part1 H L)
    (hN : Nat.card ↥L = 2520 ∨ Nat.card ↥L = 7560) :
    AlternatingNatural L (commV L) (fixV L ⊓ commV L) 7 ∨
      A7Four L (commV L) (fixV L ⊓ commV L) := by
  obtain ⟨-, hc⟩ := h1
  rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
  · exact pair_shape hN hi.2.1
  · obtain ⟨-, n, K, hF, hFin, hK, I, π, -, -, hreal, -⟩ := hii
    have hc := card_eq_of_nat_realizes1527d (hreal 0)
    rw [card_statedSL_three1527d, hK] at hc
    exact (sl3_ne hN hc.symm).elim
  · obtain ⟨-, hn, π, U₁, U₂, -, hr1, -⟩ := hiii
    exact (not_surj_sl hn hN π hr1.1).elim
  · obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
    exact (not_surj_sl hn hN π (hreal ⟨0, hk1⟩).1).elim

theorem part2_direct [Finite V] (h2 : B51Part2 L) (hN : Nat.card ↥L = 2520) :
    IsIntDirect (commV L) (fixV L) ⊤ := by
  by_contra hnd
  have hl := (h2.2 hnd).2
  rcases hl with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h
  · exact not_sl2 (Or.inl hN) h
  · exact not_sp4 (Or.inl hN) h
  · exact not_g2 (Or.inl hN) h
  · exact not_alternatingNatural1527d (n := 6) (by norm_num) (by rw [hN]; decide) h
  · obtain ⟨π, hπ⟩ := h
    have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
    have hc : Nat.card ↥(alternatingGroup (Fin 8)) = Nat.card ↥L :=
      Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
    rw [card_alternatingGroup1527d 8 (by norm_num), hN] at hc
    exact absurd hc (by decide)
  · exact not_g2d (Or.inl hN) h
  · obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hF, hN] at hc
    exact absurd hc (by norm_num)

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8
