module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2m
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3Cs
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankLin3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankMat
public import CFSG.RankThree.ThinCatalog.SporadicJ1
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace A312R1

@[expose] def SmallPrimes (N : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → r ∣ N → r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 43

theorem smallPrimes_of_eq {N a b c d e : ℕ} (hN : N = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 43 ^ e) :
    SmallPrimes N := by
  intro r hr h
  rw [hN] at h
  have key : ∀ {q n : ℕ}, q.Prime → r ∣ q ^ n → r = q := fun hq h =>
    (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h)
  rcases (Nat.Prime.dvd_mul hr).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · exact Or.inl (key Nat.prime_two h)
        · exact Or.inr (Or.inl (key Nat.prime_three h))
      · exact Or.inr (Or.inr (Or.inl (key (by norm_num) h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (key (by norm_num) h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (key (by norm_num) h))))

section Orders

variable {Q : Type} [Group Q]

theorem smallPrimes_sl4 (f : Q ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    SmallPrimes (Nat.card Q) :=
  smallPrimes_of_eq (a := 6) (b := 2) (c := 1) (d := 1) (e := 0) (by
    rw [Nat.card_congr f.toEquiv, H13.card_sl_four_zmod_two]; norm_num)

theorem smallPrimes_alt7 (h : IsAlt 7 Q) : SmallPrimes (Nat.card Q) :=
  smallPrimes_of_eq (a := 3) (b := 2) (c := 1) (d := 1) (e := 0) (by
    rw [H13.card_alt_seven h]; norm_num)

theorem smallPrimes_hat7 (h : H13.IsHatA7 Q) : SmallPrimes (Nat.card Q) :=
  smallPrimes_of_eq (a := 3) (b := 3) (c := 1) (d := 1) (e := 0) (by
    rw [Vol2.Ch11.SecA.card_of_isHat (S := alternatingGroup (Fin 7)) h,
      H13.card_alt_seven (X := alternatingGroup (Fin 7)) ⟨MulEquiv.refl _⟩]; norm_num)

theorem smallPrimes_sl27e49 (h : H13.IsSL27OverE49 Q) : SmallPrimes (Nat.card Q) := by
  obtain ⟨E, -, hE, -, hEn, ⟨f⟩⟩ := h
  have hq : Nat.card (Q ⧸ E) = 7 * (7 ^ 2 - 1) :=
    Vol2.Ch11.SecA.card_of_isSL2 (by norm_num) ⟨f⟩
  refine smallPrimes_of_eq (a := 4) (b := 1) (c := 0) (d := 3) (e := 0) ?_
  rw [E.card_eq_card_quotient_mul_card_subgroup, hq, hE]; norm_num

theorem smallPrimes_l249 (h : IsPSL 2 7 2 Q) : SmallPrimes (Nat.card Q) :=
  smallPrimes_of_eq (a := 4) (b := 1) (c := 2) (d := 2) (e := 0) (by
    rw [Ch10.SecC.C10KH.card_L249 h]; norm_num)

theorem smallPrimes_u37 (h : IsPSU 3 7 1 Q) : SmallPrimes (Nat.card Q) :=
  smallPrimes_of_eq (a := 7) (b := 1) (c := 0) (d := 3) (e := 1) (by
    rw [Ch10.SecC.C10KH.card_U37 h]; norm_num)

theorem smallPrimes_su37 (h : IsSU3 7 Q) : SmallPrimes (Nat.card Q) :=
  smallPrimes_of_eq (a := 7) (b := 1) (c := 0) (d := 3) (e := 1) (by
    rw [Ch10.SecC.C10KH.card_SU37 h]; norm_num)

end Orders

section Rank

variable {X : Type} [Group X] [Finite X] {L : Subgroup X}

theorem two_le_pRank_sl5 (f : ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    2 ≤ CFSG.Open.pRank 3 L :=
  QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv
    (f.trans (specialLinearGroupEquivStatedSL 5 (ZMod 2))) (by norm_num)
    R3c.two_le_pRank_three_statedSL_five_two

theorem two_le_pRank_psl37 (h : IsPSL 3 7 1 ↥L) : 2 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨-, K, _, _, hK, ⟨f⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv f (by norm_num)
    (QuasithinUnique.Lin2.OddRank.two_le_pRank_psl3 (F := K) (p := 3) (by rw [hK]; norm_num))

theorem two_le_pRank_sl37 (h : IsSL3 7 ↥L) : 2 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨K, _, _, hK, ⟨f⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [Nat.card_units, hK]; norm_num)
  have h3 : ω ^ 3 = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have h1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  exact QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv f (by norm_num)
    (R3c.two_le_pRank_three_statedSL_three h3 h1)

theorem two_le_pRank_of_pRank (h : 2 ≤ CFSG.pRank 3 ↥L) : 2 ≤ CFSG.Open.pRank 3 L := by
  rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h

theorem two_le_pRank_m23 (f : ↥L ≃* NativeSporadic.Carrier .M23) : 2 ≤ CFSG.Open.pRank 3 L := by
  have : Finite (NativeSporadic.Carrier .M23) := Finite.of_equiv ↥L f.toEquiv
  obtain ⟨A, hA, hc⟩ := QuasithinUnique.Lin2.OddRank.Mat.hasElemAb_nine_M23
  exact QuasithinUnique.Lin2.OddRank.le_pRank_of_equiv f (by norm_num)
    (SectionRank.le_pRank (by norm_num) le_top hA (k := 2) (by rw [hc]; norm_num))

theorem two_le_pRank_m24 (f : ↥L ≃* NativeSporadic.Carrier .M24) :
    2 ≤ CFSG.Open.pRank 3 L := by
  have : Finite NativeSporadic.M24 := Finite.of_equiv ↥L f.toEquiv
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := SectionRank.M24_sylow3_cubic_witness
  exact two_le_pRank_of_pRank (RankThree.ThinCatalog.two_le_pRank_three_of_mulEquiv
    (G := NativeSporadic.M24) f
    (RankThree.ThinCatalog.two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy))

theorem two_le_pRank_j4 (f : ↥L ≃* NativeSporadic.Carrier .J4) :
    2 ≤ CFSG.Open.pRank 3 L := by
  have : Finite NativeSporadic.J4 := Finite.of_equiv ↥L f.toEquiv
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := SectionRank.J4_sylow3_cubic_witness
  exact two_le_pRank_of_pRank (RankThree.ThinCatalog.two_le_pRank_three_of_mulEquiv
    (G := NativeSporadic.J4) f
    (RankThree.ThinCatalog.two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy))

theorem two_le_pRank_hs (f : ↥L ≃* NativeSporadic.Carrier .HS) :
    2 ≤ CFSG.Open.pRank 3 L := by
  have : Finite NativeSporadic.HS := Finite.of_equiv ↥L f.toEquiv
  obtain ⟨x, y, -, hx, hy, hxy, hQ, -⟩ := SectionRank.HS_sylow3_square_witness
  exact two_le_pRank_of_pRank (RankThree.ThinCatalog.two_le_pRank_three_of_mulEquiv
    (G := NativeSporadic.HS) f
    (RankThree.ThinCatalog.two_le_pRank_of_square_witness Nat.prime_three hx hy hxy hQ))

theorem two_le_pRank_he (f : ↥L ≃* NativeSporadic.Carrier .He) :
    2 ≤ CFSG.Open.pRank 3 L := by
  have : Finite NativeSporadic.He := Finite.of_equiv ↥L f.toEquiv
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := SectionRank.He_sylow3_cubic_witness
  exact two_le_pRank_of_pRank (RankThree.ThinCatalog.two_le_pRank_three_of_mulEquiv
    (G := NativeSporadic.He) f
    (RankThree.ThinCatalog.two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy))

theorem two_le_pRank_ru (f : ↥L ≃* NativeSporadic.Carrier .Ru) :
    2 ≤ CFSG.Open.pRank 3 L := by
  have : Finite NativeSporadic.Ru := Finite.of_equiv ↥L f.toEquiv
  obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := SectionRank.Ru_sylow3_cubic_witness
  exact two_le_pRank_of_pRank (RankThree.ThinCatalog.two_le_pRank_three_of_mulEquiv
    (G := NativeSporadic.Ru) f
    (RankThree.ThinCatalog.two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy))

end Rank

end A312R1

end CFSG.Quasithin.Vol2.Ch10.SecB
