module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveTorusPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFourTorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanProductRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem s17_45_center_bar2_eq_bot {D : Data G} {L : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    Subgroup.center (Bar2 L) = ⊥ := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  rcases hshape with hL2 | hSz
  · have : IsSimpleGroup (Bar2 L) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
    exact uc22p21k_center_eq_bot hq
  · have : IsSimpleGroup (Bar2 L) :=
      CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    exact uc22p21k_center_eq_bot hq

theorem s17_45_borelChevOver {D : Data G} {L : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34) :
    Inputs1719.BorelChevOver (BarInf L) n := by
  have hZ : Subgroup.center (Bar2 L) = ⊥ := s17_45_center_bar2_eq_bot hL hshape
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  rcases hshape with hL2 | hSz
  · exact Inputs1719.BorelChevOver.of_on hK3 (LieModel.of_mulEquiv e.symm hL2)
      ⟨by decide, by simp⟩
  · exact Inputs1719.BorelChevOver.of_on hK3 (LieModel.of_mulEquiv e.symm hSz)
      ⟨by decide, by simp⟩

theorem s17_45_one_le_pRank_cartan {D : Data G} {L C : Subgroup G} {n : ℕ}
    (hL : L ∈ calC D.M) (hC : CIsCartanOf D.T L C)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hK4 : Inputs1719.K_CartanRankLeThree) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrdvd : r ∣ 2 ^ n - 1) :
    1 ≤ CFSG.Open.pRank r C := by
  have hZ : Subgroup.center (Bar2 L) = ⊥ := s17_45_center_bar2_eq_bot hL hshape
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  have hshapeInf : IsL2 (BarInf L) n ∨ IsSz (BarInf L) n := by
    rcases hshape with hL2 | hSz
    · exact Or.inl (LieModel.of_mulEquiv e.symm hL2)
    · exact Or.inr (LieModel.of_mulEquiv e.symm hSz)
  rcases hshapeInf with hL2 | hSz
  · have hbound := cartanRank_le_pRank_cartan_on hK4 hL hC (by decide) hL2 hr hr2 hrdvd
      (fun _ hdvd => by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact hr.ne_one h
        · exact hr2 h)
      (fun h => absurd h (by decide))
    simpa [CS17LieRank] using hbound
  · have hbound := cartanRank_le_pRank_cartan_on hK4 hL hC (by decide) hSz hr hr2 hrdvd
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    simpa [CS17LieRank] using hbound

theorem s17_45_exists_not_strongly {D : Data G}
    {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hpair : ∃ x ∈ D.M, X = L ⊔ CFSG.Quasithin.conjSubgroup L x ∧ X ≠ L)
    (h1 : R17_1At D V₀ V ctx.hyp125)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34)
    (hK4 : Inputs1719.K_CartanRankLeThree) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧
      ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
  classical
  rcases Nat.even_or_odd n with hnEven | hnOdd
  ·
    have h3dvd : 3 ∣ 2 ^ n - 1 := by
      obtain ⟨k, rfl⟩ := hnEven
      have h4 : (4 : ℕ) ^ k ≡ 1 [MOD 3] := by
        have h1 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
        simpa using h1.pow k
      have hpow : 2 ^ (k + k) = 4 ^ k := by
        rw [show k + k = 2 * k by ring, pow_mul]
        norm_num
      rw [hpow]
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow k 4 (by norm_num))).mp h4.symm
    refine ⟨3, Nat.prime_three, h3dvd, ?_⟩
    intro hstr
    have hk1 : D.k = 1 := by
      have hk12 : D.k = 1 ∨ D.k = 2 := by
        have := TwelveShort.one_le_k D
        have := TwelveSeven.k_le_two D
        omega
      rcases hk12 with h | h
      · exact h
      · exact absurd h (fun hk2 => ((Data.k_eq_two_iff D).mp hk2) hstr)
    have hle1 : CFSG.Open.pRank 3 Dc ≤ 1 :=
      pRank_three_Dc_le_one_of_k_one_of_borel ctx
        (s17_45_borelChevOver ctx.mem_calC hshape hK3) h1 hk1
    have hge2 : 2 ≤ CFSG.Open.pRank 3 Dc := by
      obtain ⟨x, hxM, hXsup, hne⟩ := hpair
      have hCLne : conjClosure D.M L ≠ L := by rw [← ctx.X_eq]; exact hne
      have hc2 : (conjSetOf D.M L).ncard = 2 :=
        ncard_eq_two_of_p42 ctx.mem_calC hxM (by rw [← ctx.X_eq]; exact hXsup) hCLne
      have hG2 : Gamma.ncard = 2 := by
        rw [ctx.ncard_Gamma_eq_card_conjSet, hc2]
      have hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
        rw [s17_45_center_bar2_eq_bot ctx.mem_calC hshape, Subgroup.card_bot]
        decide
      have hC : 1 ≤ CFSG.Open.pRank 3 C :=
        s17_45_one_le_pRank_cartan ctx.mem_calC ctx.cartan hshape hK4 Nat.prime_three
          (by norm_num) h3dvd
      have hle := ctx.ncard_le_pRank_Dc Nat.prime_three (by norm_num) hZ hC
      omega
    omega
  ·
    have hn2 : 2 ≤ n := by
      rcases hshape with hL2 | hSz
      · exact s13_two_le_of_isL2 hL2
      · have h3 := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
        omega
    obtain ⟨r, hr, hrdvd⟩ := s13_exists_prime_dvd (show 1 < n by omega)
    have hstr : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
      intro hs
      obtain ⟨E, hE⟩ :=
        s17_45_pair_torus_inPStar ctx hshape hnOdd hpair hr hrdvd hs
      exact h1.1 E hE
    exact ⟨r, hr, hrdvd, hstr⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
