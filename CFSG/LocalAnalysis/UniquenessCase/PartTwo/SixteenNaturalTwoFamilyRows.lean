module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatMany
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSp6Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeL5Conjugates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalOneS1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLFourComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1SchurU4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def S16NaturalTwoFamily
    (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
      SumOfNat (fun H U Z => AlternatingNatural H U Z n)
        (lBar V₀ V hV L) (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) ∨
  (∃ n : ℕ, 9 ≤ n ∧ n ≤ 11 ∧ UC22.IsAlt ↥(lBar V₀ V hV L) n ∧
      SumOfNat (fun H U Z => AlternatingNatural H U Z n)
        (lBar V₀ V hV L) (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) ∨
  (IsSLn ↥(lBar V₀ V hV L) 3 1 ∧
      SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
        (lBar V₀ V hV L) (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) ∨
  (IsSLn ↥(lBar V₀ V hV L) 4 1 ∧
      SumOfNat (fun H U Z => BinaryNaturalSL H U Z 4 1)
        (lBar V₀ V hV L) (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) ∨
  (IsSLn ↥(lBar V₀ V hV L) 5 1 ∧
      SumOfNat (fun H U Z => BinaryNaturalSL H U Z 5 1)
        (lBar V₀ V hV L) (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) ∨
  (IsSpn ↥(lBar V₀ V hV L) 6 1 ∧
      SumOfNat (fun H U Z => NatSpn H U Z 6 1)
        (lBar V₀ V hV L) (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) ∨
  (IsOmegaMinus ↥(lBar V₀ V hV L) 6 1 ∧
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
        (lBar V₀ V hV L) (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) ∨
  (IsOmegaMinus ↥(lBar V₀ V hV L) 8 1 ∧
      SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
        (lBar V₀ V hV L) (wTil V₀ V hV L)
        (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2)

theorem s16nt_case162_of_alt_five_eight
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_1 D V₀ V hV L ∨ Case162_2 D V₀ V hV L := by
  by_cases hs : s15 D.M V₀ V hV L = 1
  · exact Or.inr (s168e3_case162_2_of_star_alt c hs hn5 (by omega) hA hsum)
  · have h2 : 2 ≤ s15 D.M V₀ V hV L := by
      have h1 := Om8Excl.one_le_s15 D.M V₀ V hV L
      omega
    exact Or.inl (s168e3_case162_1_of_sum_two_alternating c h2 hn5 hn8 hA hsum)

theorem s16nt_case162_of_alt_nine_eleven
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn9 : 9 ≤ n) (hn11 : n ≤ 11)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  exact s168e3_case162_2_of_star_alt c
    (s16nt_s15_eq_one_of_alt_nine_eleven c hcomp hn9 hn11 hA)
    (by omega) hn11 hA hsum

theorem s16nt_case162_of_sl_three
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hSL3 : IsSLn ↥(lBar V₀ V hV L) 3 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_1 D V₀ V hV L ∨ Case162_2 D V₀ V hV L := by
  by_cases hs : s15 D.M V₀ V hV L = 1
  · exact Or.inr (s168e3_case162_2_of_star_natSL c hs (by norm_num) (by norm_num) hSL3 hsum)
  · have h2 : 2 ≤ s15 D.M V₀ V hV L := by
      have h1 := Om8Excl.one_le_s15 D.M V₀ V hV L
      omega
    have hL3 : IsL3 ↥(lBar V₀ V hV L) 1 := s16k_isLn_of_isSLn (by norm_num) hSL3
    exact Or.inl (s168e3_case162_1_of_sum_two_l3 c h2 hL3 hsum)

theorem s16nt_case162_of_sl_four
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL4 : IsSLn ↥(lBar V₀ V hV L) 4 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 4 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  exact s168e3_case162_2_of_star_natSL c
    (s15_eq_one_of_sl_four_component_at_three c hcomp hSL4)
    (by norm_num) (by norm_num) hSL4 hsum

theorem s16nt_case162_of_sl_five
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL5 : IsSLn ↥(lBar V₀ V hV L) 5 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 5 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  have hLn5 : IsLn ↥(lBar V₀ V hV L) 5 1 := s16k_isLn_of_isSLn (by norm_num) hSL5
  have hs : s15 D.M V₀ V hV L = 1 := s15_eq_one_of_l5_component_at_three c hcomp hLn5
  exact s168e3_case162_2_of_star_natSL c hs (by norm_num) (by norm_num) hSL5 hsum

theorem s16nt_case162_of_sp_six
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  have hs : s15 D.M V₀ V hV L = 1 := s15_eq_one_of_sp6_component_at_three c hcomp hSp
  exact s168e3_case162_2_of_star_natSp6 c hs hSp hsum

theorem s16nt_case162_of_omega_minus_six
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hOm6 : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c1_isSimpleGroup_of_isOmegaMinus_six hOm6
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    obtain ⟨E, hE, hEcard⟩ := s15k_om6_exists_e27 hOm6
    exact CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num) (H := ⊤) (E := E)
      le_top hE (by rw [hEcard]; norm_num)
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      IsPGroup 2 ↥(Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    have hU4 : IsU4 (Q ⧸ Subgroup.center Q) 1 :=
      CFSG.Blueprint.LieModel.of_mulEquiv eQ.symm (isU4_of_isOmegaMinus_six hOm6)
    have hdvd := rSchurOm6_holds Q hQ hU4
    exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hdvd)
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_simple_component_of_three_rank c hcomp hsimple (r := 3) (by norm_num)
      hrank hcover
  exact s168e3_case162_2_of_star_natOmegaMinus_six c hs hOm6 hsum

theorem s16nt_case162_of_omega_minus_eight
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hOm8 : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  exact s168e3_case162_2_of_star_natOmegaMinus_eight c
    (s16nt_s15_eq_one_of_omega_minus_eight c hcomp hOm8) hOm8 hsum

theorem s16nt_case162_of_natural_two_family
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hfam : S16NaturalTwoFamily V₀ V hV L) :
    Case162_1 D V₀ V hV L ∨ Case162_2 D V₀ V hV L := by
  rcases hfam with ⟨n, h5, h8, hA, hsum⟩ | ⟨n, h9, h11, hA, hsum⟩ |
    ⟨hSL3, hsum⟩ | ⟨hSL4, hsum⟩ | ⟨hSL5, hsum⟩ | ⟨hSp, hsum⟩ | ⟨hOm6, hsum⟩ |
    ⟨hOm8, hsum⟩
  · exact s16nt_case162_of_alt_five_eight c h5 h8 hA hsum
  · exact Or.inr (s16nt_case162_of_alt_nine_eleven c hcomp h9 h11 hA hsum)
  · exact s16nt_case162_of_sl_three c hSL3 hsum
  · exact Or.inr (s16nt_case162_of_sl_four c hcomp hSL4 hsum)
  · exact Or.inr (s16nt_case162_of_sl_five c hcomp hSL5 hsum)
  · exact Or.inr (s16nt_case162_of_sp_six c hcomp hSp hsum)
  · exact Or.inr (s16nt_case162_of_omega_minus_six c hcomp hOm6 hsum)
  · exact Or.inr (s16nt_case162_of_omega_minus_eight c hcomp hOm8 hsum)

theorem s16nt_concl163F_of_natural_two_family
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hfam : S16NaturalTwoFamily V₀ V hV L) :
    Concl163F D V₀ V hV L := by
  rcases s16nt_case162_of_natural_two_family c hcomp hfam with h1 | h2
  · exact Or.inl (Or.inr (Or.inl h1))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h2)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
