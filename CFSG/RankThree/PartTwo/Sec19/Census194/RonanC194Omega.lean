module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaPlanes
public import CFSG.RankThree.PartTwo.Sec19.Census194.Arith
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.RankThree.PartTwo.KFacts.KS21LocalRankOmegaFour

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

namespace OmegaEven

open CFSG CFSG.RankThree.PartTwo.Sec19 CFSG.Open CFSG.SectionRank

theorem exists_odd_prime_dvd_two_pow_sub_one {f : ℕ} (hf : 2 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 := by
  have h4 : 4 ≤ 2 ^ f := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ f - 1 ≠ 1 by omega)
  refine ⟨r, hr, ?_, hrd⟩
  rintro rfl
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega

theorem tooBig_of_four_le_pRank {G : Type} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (h : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup G)) : TooBig G := by
  by_cases hr3 : r = 3
  · subst hr3
    exact tooBig_of_three h
  · exact tooBig_of_prime hr (by have := hr.two_le; omega) (by omega)

theorem localRank_le_pRank_top {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    CFSG.Assembly.RankThreeEven.localRank p G ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  refine csSup_le' ?_
  rintro _ ⟨H, -, rfl⟩
  exact pRank_mono hp.one_lt le_top

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem tooBig_omegaPlus (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hn : 4 ≤ n) :
    TooBig (StatedProj (StatedOmega (StatedQuadPlus n K))) := by
  rcases Nat.eq_or_lt_of_le hf with rfl | hf2
  · exact tooBig_of_three (four_le_pRank_three_omegaPlus hn)
  · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one hf2
    refine tooBig_of_four_le_pRank hr hr2 (hn.trans ?_)
    exact le_pRank_omegaPlus_torus hr hr2 (by rw [Nat.card_units, hK]; exact hrd)

theorem tooBig_omegaMinus (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hn : 4 ≤ n)
    (h1 : ¬ (n = 4 ∧ f = 1)) (h2 : ¬ (n = 4 ∧ f = 2)) (b c : K) :
    TooBig (StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  rcases Nat.lt_or_ge 4 n with hn5 | hn4
  · rcases Nat.eq_or_lt_of_le hf with rfl | hf2
    · exact tooBig_of_three (four_le_pRank_three_omegaMinus hn5 b c)
    · obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one hf2
      refine tooBig_of_four_le_pRank hr hr2 ((by omega : 4 ≤ n - 1).trans ?_)
      exact le_pRank_omegaMinus_torus hr hr2 (by rw [Nat.card_units, hK]; exact hrd) b c
  · obtain rfl : n = 4 := by omega
    have hf3 : 3 ≤ f := by omega
    obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_gt_three_dvd_two_pow_sub_one hf3
    exact tooBig_of_prime hr hr3
      (le_pRank_omegaMinus_torus (n := 4) hr (by omega)
        (by rw [Nat.card_units, hK]; exact hrd) b c)

end Rank

end OmegaEven

open CFSG CFSG.RankThree.PartTwo.Sec19 CFSG.SectionRank OmegaEven

theorem survPOmegaPlus_holds :
    Census194SurvPOmegaPlus := by
  intro Y _ _ n f hR h
  have hodd : Odd (Nat.card (Subgroup.center Y)) :=
    odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨hZ, -⟩ := EvenCover.even_split_orthogonal_odd_cover_catalog_step hR.quasisimple hodd h
  obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ClassicalOdd.charP_of_card hK
  exact hR.false_of_tooBig ((tooBig_omegaPlus hK hf hn).of_mulEquiv
    ((mulEquivQuotientCenterOfEqBot hZ).trans e).symm)

theorem survPOmegaMinus_holds :
    Census194SurvPOmegaMinus := by
  intro Y _ _ n f hR h
  have hodd : Odd (Nat.card (Subgroup.center Y)) :=
    odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨hZ, -⟩ :=
    EvenCover.even_nonsplit_orthogonal_odd_cover_catalog_step hR.quasisimple hodd h
  by_contra hne
  refine hR.false_of_tooBig ?_
  by_cases h42 : n = 4 ∧ f = 2
  · obtain ⟨rfl, rfl⟩ := h42
    obtain ⟨b, c, hirr, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.projOmegaMinus_of_statedClassicalModel h
    let ψ : Y ≃* CFSG.PGLModel.projOmegaMinus 3 (GaloisField 2 2) b c :=
      (mulEquivQuotientCenterOfEqBot hZ).trans φ
    haveI : Finite (CFSG.PGLModel.projOmegaMinus 3 (GaloisField 2 2) b c) :=
      Finite.of_equiv Y ψ.toEquiv
    obtain ⟨r, hr, hr3, hloc⟩ :=
      CFSG.RankThree.PartTwo.KFacts.KS21LocalRank.exists_le_localRank_projOmegaMinus_four hirr
    refine tooBig_of_prime hr hr3 ?_
    rw [pRank_top_eq_of_mulEquiv hr.one_lt ψ]
    exact hloc.trans (localRank_le_pRank_top hr)
  · obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := ClassicalOdd.charP_of_card hK
    exact (tooBig_omegaMinus hK hf hn hne h42 b c).of_mulEquiv
      ((mulEquivQuotientCenterOfEqBot hZ).trans e).symm

theorem idPOmegaMinus_holds :
    Census194IdPOmegaMinus := by
  intro Y _ _ hR h
  have hodd : Odd (Nat.card (Subgroup.center Y)) :=
    odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨hZ, -⟩ :=
    EvenCover.even_nonsplit_orthogonal_odd_cover_catalog_step hR.quasisimple hodd h
  obtain ⟨b, c, hirr, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.projOmegaMinus_of_statedClassicalModel h
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inl ⟨b, c, hirr, ⟨(mulEquivQuotientCenterOfEqBot hZ).trans φ⟩⟩

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
