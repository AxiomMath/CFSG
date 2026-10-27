module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAN3F

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_inP11_of_ne_conjClosure
    (D : Data G) (V₀ V : Subgroup G) (hSg : SigmaStd D)
    (hK3 : Inputs1719.K_BorelTorusAbelian) (hCen : UCK.U3Center) (hSyl : UCK.U3Syl)
    (hBorel : K_U3CartanRank) (hK : K_SU3EightBorelNine) (hK9 : K_SU3EightTorusE9)
    {L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n) (hne : L ≠ UC22.conjClosure D.M L) :
    ∃ X : Subgroup G, F11.InP11 D X := by
  have hn2 : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_two_le_of_isU3 c.shape.2
  have hL : L ∈ calC D.M := c.mem_calC
  have hnn : ¬ (L.subgroupOf D.M).Normal := by
    intro hN
    apply hne
    have hNM : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN
    have hcl : UC22.conjClosure D.M L ≤ L := by
      refine iSup₂_le fun K hK => ?_
      obtain ⟨g, hg, rfl⟩ := hK
      rintro x ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hNM hg) y).1 hy
    exact le_antisymm (uc22p22v_le_conjClosure D.M L) hcl
  have hnn' : ¬ D.M ≤ Subgroup.normalizer (L : Set G) := by
    intro h
    exact hnn ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).2 h)
  have hchev : CIsChevOver (BarInf L) n := by
    obtain ⟨e⟩ := UC22.uc22p21k_barInf_equiv_of_calC c.mem_calC
    have hLie : CFSG.Blueprint.LieModel (BarInf L) .PSU 3 2 n :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm c.shape.2
    exact ⟨.PSU, 3, hLie.admissible, hLie⟩
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.PermSylowTwo.exists_isSylowTwoOf_top (Bar2 L)
  have key : ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hcond : 3 < p ∨ n = 3)
      (hpdvd : p ∣ 2 ^ n + 1) (hZ : ¬ p ∣ Nat.card (Subgroup.center (Bar2 L)))
      (h4 : 4 ≤ CFSG.Open.pRank p D.M), ∃ X : Subgroup G, F11.InP11 D X := by
    intro p hp hp2 hcond hpdvd hZ h4
    have hpsig : p ∈ D.sig := hSg.four_mem p hp hp2 h4
    have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
      sp_of_mem_sig hSg (not_solvable_of_mem_calC hL) hpsig
    have hrank : 1 ≤ CFSG.Open.pRank p
        (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) :=
      hBorel (Bar2 L) n p c.shape hp hpdvd hcond S hS
    obtain ⟨E, hEB, hEel, hperm, hErank⟩ :=
      exists_permuting_elemAbelian_noncyclic_of_calC (D := D) (L := L)
        (X := UC22.conjClosure D.M L) (n := n) (r := p) hL rfl hchev hK3 hnn hZ S hS hrank hp
        hp2
    have hEM : E ≤ D.M :=
      (hEB.trans inf_le_left).trans
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.conjClosure_le hL.1.le)
    have hEnc : ¬ IsCyclic ↥E := by
      intro hcyc
      have h2 : CFSG.Open.pRank p E ≤ 1 :=
        CFSG.SectionRank.pRank_le_one_of_isCyclic hp hcyc
      omega
    exact ⟨E, inP11_of_strongly hp hp2 hstr hEM hEel.isPGroup hEel.2 hEnc hperm⟩
  by_cases hn3 : n = 3
  ·
    subst hn3
    by_cases hZ3 : 3 ∣ Nat.card (Subgroup.center (Bar2 L))
    ·
      have h2 : 1 < (UC22.conjSetOf D.M L).ncard := by
        by_contra hle
        exact hne (conjClosure_eq_of_ncard_le_one (M := D.M) (L := L) (by omega))
      obtain ⟨K₁, hK₁, K₂, hK₂, h₁₂⟩ := (Set.one_lt_ncard (Set.toFinite _)).1 h2
      have h4 : 4 ≤ CFSG.Open.pRank 3 D.M :=
        four_le_pRank_three_of_two_conj_of_three_dvd_center hCen hK9 hL c.shape hZ3 hK₁ hK₂ h₁₂
      have hsig : 3 ∈ D.sig := hSg.four_mem 3 Nat.prime_three (by norm_num) h4
      have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
        sp_of_mem_sig hSg (not_solvable_of_mem_calC hL) hsig
      obtain ⟨E, hEL₀, hEel, hEperm, hErank⟩ :=
        exists_permuting_E9_of_two_conj D V₀ V L hK hCen hK3 c hZ3 hK₁ hK₂ h₁₂
      have hEM : E ≤ D.M := hEL₀.trans
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.conjClosure_le hL.1.le)
      have hEnc : ¬ IsCyclic ↥E := by
        intro hcyc
        have h2 : CFSG.Open.pRank 3 E ≤ 1 :=
          CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcyc
        omega
      exact ⟨E, inP11_of_strongly Nat.prime_three (by norm_num) hstr hEM hEel.isPGroup hEel.2
        hEnc hEperm⟩
    · have h3rank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) :=
        UC22.two_le_pRank_three_of_isSU3 c.shape ⟨1, rfl⟩
      obtain ⟨E0, hE0L, hE0el, a, ha2, hE0card⟩ :=
        exists_elemAbelian_sq_lift_of_isSU3 (L := L) (q := 3) Nat.prime_three
          (by norm_num) h3rank
      have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := by
        have h := calCRankTwice D.M L hL hnn' 3 Nat.prime_three (by norm_num) hZ3 E0 hE0L
          hE0el a hE0card
        omega
      exact key 3 Nat.prime_three (by norm_num) (Or.inr rfl) (by norm_num) hZ3 h4
  ·
    obtain ⟨p, hp, hp3, hpdvd⟩ := uc2_17_36a_exists_prime_gt_three hn2 hn3
    have hp2 : p ≠ 2 := by omega
    have hZ : ¬ p ∣ Nat.card (Subgroup.center (Bar2 L)) := by
      intro hdvd
      have h3 : Nat.card (Subgroup.center (Bar2 L)) ∣ 3 := hCen (Bar2 L) n c.shape
      have hle := Nat.le_of_dvd (by norm_num) (hdvd.trans h3)
      omega
    obtain ⟨E0, hE0L, hE0el, hE0card⟩ :=
      exists_elemAbelian_sq_of_isSU3 hSyl c.shape hp hp3 hpdvd
    have h4 : 4 ≤ CFSG.Open.pRank p D.M := by
      have h := calCRankTwice D.M L hL hnn' p hp hp2 hZ E0 hE0L hE0el 2 hE0card
      omega
    exact key p hp hp2 (Or.inl hp3) hpdvd hZ h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
