module

public import CFSG.Quasithin.Vol2.Ch10SecKRSg
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.T1515Der

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}

theorem zbot_L5 (hN : Nat.card ↥K = 9999360) (hpart2 : B51Part2 K) :
    fixV K ⊓ commV K = ⊥ := by
  by_contra hZ
  have hnot : ¬ IsIntDirect (commV K) (fixV K) ⊤ := fun hd => hZ (by
    have := hd.2
    rwa [inf_comm] at this)
  obtain ⟨-, hl⟩ := hpart2.2 hnot
  rcases hl with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | hn | hn | hn | hn
  · exact not_binaryNaturalSL_two1527d (Or.inr hN) hn
  · exact not_binaryNaturalSp4_1527d (Or.inr hN) hn
  · exact not_g2Natural1527d (Or.inr hN) hn
  · exact not_alternatingNatural1527d (n := 6) (by norm_num) (by rw [hN]; norm_num [Nat.factorial])
      hn
  · exact not_alternatingNatural1527d (n := 8) (by norm_num) (by rw [hN]; norm_num [Nat.factorial])
      hn
  · exact not_g2NaturalDerived_one1527d (Or.inr hN) hn
  · exact not_binaryNaturalSL_three1527d (Or.inr hN) hn

@[expose] def AltL5 (K : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  SLExteriorTwo K U ⊥ 5 ∨
    (∃ π : ↥(Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) →* ↥K,
      (FFModel.nat (Assembly.LowTwoRank.StatedSL 5 (ZMod 2))).RealizesVia K U ⊥ π) ∨
    SumNatDual K U 5 ∨
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧
      DirectSumOfCopies K U ⊥ (FFModel.nat (Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) k

theorem false_of_nat_four (hN : Nat.card ↥K = 9999360) {U Z : Subgroup V}
    {π : ↥(Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) →* ↥K}
    (h : (FFModel.nat (Assembly.LowTwoRank.StatedSL 4 (ZMod 2))).RealizesVia K U Z π) : False := by
  have h1 := card_eq_of_nat_realizes1527d h
  rw [hN, card_statedSL_four_zmod1527d] at h1
  norm_num at h1

theorem alt_L5_of_b51 (h51 : AsB51) [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {J : Subgroup (MulAut V)} (hB : B51Hyp J K) (hN : Nat.card ↥K = 9999360) :
    AltL5 K (commV K) := by
  obtain ⟨hp1, hp2, -⟩ := h51 V hV J K hB
  have hZ := zbot_L5 hN hp2
  rcases hp1.2 with hi | hii | ⟨n, hiii⟩ | hiv
  · have hpair := hi.2.1
    rw [hZ] at hpair
    rcases hpair with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
    · exact (not_binaryNaturalSL_two1527d (Or.inr hN) h).elim
    · exact (not_binaryNaturalSL_three1527d (Or.inr hN) h).elim
    · exact (not_binaryNaturalSp4_1527d (Or.inr hN) h).elim
    · exact (not_g2Natural1527d (Or.inr hN) h).elim
    · exact (not_g2NaturalDerived_one1527d (Or.inr hN) h).elim
    · exact (not_alternatingNatural1527d (n := 5) (by norm_num)
        (by rw [hN]; norm_num [Nat.factorial]) h).elim
    · exact (not_alternatingNatural1527d (n := 6) (by norm_num)
        (by rw [hN]; norm_num [Nat.factorial]) h).elim
    · exact (not_alternatingNatural1527d (n := 7) (by norm_num)
        (by rw [hN]; norm_num [Nat.factorial]) h).elim
    · exact (not_a7Four1527d (Or.inr hN) h).elim
    · exact (not_tripleA6Six1527d (Or.inr hN) h).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      exact (false_of_nat_four hN hπ).elim
    · exact Or.inr (Or.inl (FFC.BinaryNaturalSL.exists_zmod h))
    · exfalso
      obtain ⟨π, hπ⟩ := h
      have : Finite (FFModel.extSq (ZMod 2) 4).Gam :=
        inferInstanceAs (Finite ↥(Assembly.LowTwoRank.StatedSL 4 (ZMod 2)))
      have h1 := card_le_of_surjective1527d π hπ.1
      rw [hN] at h1
      have h2 : Nat.card (FFModel.extSq (ZMod 2) 4).Gam = 20160 := card_statedSL_four_zmod1527d
      rw [h2] at h1
      norm_num at h1
    · exact Or.inl h
  · exfalso
    obtain ⟨-, n, F, _, _, hF, I, π, -, -, hreal, -⟩ := hii
    exact ne_card_sl3_1527d hF (N := Nat.card ↥K) (Or.inr hN)
      (card_eq_of_nat_realizes1527d (hreal 0)).symm
  · obtain ⟨hn45, π, U₁, U₂, hd, hnat, hdual⟩ := hiii.2
    rcases hn45 with rfl | rfl
    · exact (false_of_nat_four hN hnat).elim
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, π, U₁, U₂, hd, hnat, hdual⟩))
  · obtain ⟨n, hn45, k, hk1, hkn, hds⟩ := hiv.2
    rcases hn45 with rfl | rfl
    · obtain ⟨I, π, -, -, -, hreal⟩ := hds
      exact (false_of_nat_four hN (hreal ⟨0, by omega⟩)).elim
    · exact Or.inr (Or.inr (Or.inr ⟨k, hk1, by omega, hds⟩))

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
