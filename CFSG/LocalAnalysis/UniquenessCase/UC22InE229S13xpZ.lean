module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xe
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78p3
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229S13xnZ
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen5
import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
import CFSG.LocalAnalysis.UniquenessCase.UC22S13g
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xn
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.RankThree.PartOne (pElementSubgroup)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

theorem r136bFour_of_r7_8R3p3
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hSig : UC6S846.SigmaStd D) (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h78 : R7_8R3p3 D) (h82 : F08.R82 D) (h846 : F08.R846 D) (h847 : R847Four D)
    (hxn : PartTwo.Setting13 D → ∀ {p : ℕ}, p ∈ D.sig → ∀ {B : Subgroup G},
      F13.Case136b D p B → ∀ {L : Subgroup G}, L ∈ calC D.M → ∀ {n : ℕ}, IsPowTwo n →
      IsU3 (Bar2 L) n → p ∣ 2 ^ n + 1 → ∀ {y : G} (hyM : y ∈ D.M),
      y ∈ Subgroup.normalizer (B : Set G) → orderOf y = p →
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y, hyM⟩ : Bar2 D.M) ∈
        Subgroup.centralizer (barImage D.M L : Set (Bar2 D.M)) → False) :
    R136bFour D := by
  classical
  intro hsig hH p hp B hB
  exfalso
  have hS : PartTwo.Setting13 D := ⟨hsig, hH⟩
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns := PartTwo.s13_normalSimple hThin D hS
  have hsum := PartTwo.s13_pRank_bar_eq_add hThin hCyc D hS hSig hp
  rw [PartTwo.s13_pRank_bar_top hpp hp2] at hsum
  have hlay := PartTwo.s13_pRank_pElementSubgroup_layer (p := p) (ℓ := p) hns hpp hpp
  have hSp : CFSG.Open.pRank p (pElementSubgroup p (Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)))) =
        CFSG.Open.pRank p (F13.Sp D.M p) := by
    rw [← PartTwo.s13_barImage_Sp D.M hpp,
      PartTwo.s13_pRank_barImage hpp hp2 (PartTwo.s13_Sp_le D.M p)]
  have hS1 := hH.smallS p hp
  have h4p := h4 p hp
  have hcomp : ∀ J ∈ PartTwo.s13_compsP (Bar2 D.M) p, ∃ L ∈ calC D.M, barImage D.M L = J ∧
      CFSG.Open.pRank p J = CFSG.Open.pRank p L := by
    intro J hJ
    obtain ⟨L, hL, rfl⟩ :=
      PartTwo.s13_exists_calC_of_component D.M (PartTwo.s13_mem_compsP.mp hJ).1
    exact ⟨L, hL, rfl, PartTwo.s13_pRank_barImage hpp hp2 (PartTwo.s13_le_of_mem_calC hL)⟩
  have hrank : ∀ L ∈ calC D.M, CFSG.Open.pRank p L ≤ 1 ∨
      ((∃ n, IsPowTwo n ∧ IsU3 (Bar2 L) n ∧ p ∣ 2 ^ n + 1) ∧ CFSG.Open.pRank p L ≤ 2) := by
    intro L hL
    rcases hH.thinOrU3 L hL with hthin | ⟨n, hn, hU⟩
    · exact Or.inl (hthin p hpp hp2)
    · by_cases hpn : p ∣ 2 ^ n + 1
      · refine Or.inr ⟨⟨n, hn, hU, hpn⟩, ?_⟩
        rw [← pRank_bar2_eq_of_odd hpp hp2]
        exact CFSG.Quasithin.B69K.pRank_le_two_of_psu3
          (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hU) hpp hp2
      · exact Or.inl (uc22s13xn_pRank_le_one hL hU hpp hp2 hpn)
  have hbig : ∀ T : Finset (Subgroup (Bar2 D.M)), T.card < ∑ J ∈ T, CFSG.Open.pRank p J →
      ∃ J ∈ T, 2 ≤ CFSG.Open.pRank p J := by
    intro T hT
    by_contra hno
    have h := Finset.sum_le_card_nsmul T (fun J => CFSG.Open.pRank p J) 1
      (fun J hJ => by
        have : ¬ 2 ≤ CFSG.Open.pRank p J := fun h2 => hno ⟨J, hJ, h2⟩
        omega)
    rw [smul_eq_mul, mul_one] at h
    omega
  have hrk3 : PartTwo.SigmaRankThree13 D := by
    rintro ⟨q, hq, h3⟩
    have := h4 q hq
    exact absurd h3 (by omega)
  have h133 := r133_of hThin hCyc D h846 h847 hSig.nonempty
  have hshape : ∀ L ∈ calC D.M, ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) := by
    intro L hL
    rcases PartTwo.isL2_or_isU3_of_mem_calC D hS hSig hThin hCyc hrk3 h133 hL with
      ⟨n, hn, h⟩ | ⟨n, hn, h⟩
    exacts [⟨n, hn, Or.inl h⟩, ⟨n, hn, Or.inr h⟩]
  rcases lt_or_ge 2 (PartTwo.s13_compsP (Bar2 D.M) p).card with hcard | hcard
  ·
    obtain ⟨J₁, hJ₁, J₂, hJ₂, J₃, hJ₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hcard
    obtain ⟨L₁, hL₁, rfl, -⟩ := hcomp J₁ hJ₁
    obtain ⟨L₂, hL₂, rfl, -⟩ := hcomp J₂ hJ₂
    obtain ⟨L₃, hL₃, rfl, -⟩ := hcomp J₃ hJ₃
    exact uc22ine229_s13xo_false_p3 hThin hS h78 h82 hB hL₁ hL₂ hL₃ h12 h13 h23
      (hshape L₁ hL₁) (hshape L₂ hL₂) (hshape L₃ hL₃)
  ·
    obtain ⟨J₁, hJ₁, h2J₁⟩ := hbig (PartTwo.s13_compsP (Bar2 D.M) p) (by omega)
    obtain ⟨L₁, hL₁, rfl, hr₁⟩ := hcomp J₁ hJ₁
    obtain ⟨⟨n, hn, hU, hpn⟩, h2⟩ := (hrank L₁ hL₁).resolve_left (by omega)
    have hrest : CFSG.Open.pRank p (barImage D.M L₁) +
        ∑ J ∈ (PartTwo.s13_compsP (Bar2 D.M) p).erase (barImage D.M L₁), CFSG.Open.pRank p J =
          ∑ J ∈ PartTwo.s13_compsP (Bar2 D.M) p, CFSG.Open.pRank p J :=
      Finset.add_sum_erase _ _ hJ₁
    have hC₁ := PartTwo.s13_barImage_isComponent hL₁
    by_cases h1S : 1 ≤ CFSG.Open.pRank p (F13.Sp D.M p)
    ·
      obtain ⟨P, hP, hPN⟩ := hB.2.2.2.2.2
      haveI : Fact p.Prime := ⟨hpp⟩
      have hdvd : p ∣ Nat.card P := by
        obtain ⟨E, hE, -, hcE⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt (F13.Sp D.M p)
        have h1 : p ∣ Nat.card (F13.Sp D.M p) := by
          refine (dvd_pow_self p (show CFSG.Open.pRank p (F13.Sp D.M p) ≠ 0 by omega)).trans ?_
          rw [← hcE]
          exact Subgroup.card_dvd_of_le hE
        have hf := (hpp.dvd_iff_one_le_factorization
          (Nat.card_pos (α := ↥(F13.Sp D.M p))).ne').mp h1
        rw [hP.card_eq]
        exact dvd_pow_self p (by omega)
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) p hdvd
      have hyS : (y : G) ∈ F13.Sp D.M p := hP.le y.2
      have hyM : (y : G) ∈ D.M := PartTwo.s13_Sp_le D.M p hyS
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y, hyM⟩ : Bar2 D.M) ∈
          barImage D.M (F13.Sp D.M p) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyS)
      rw [PartTwo.s13_barImage_Sp D.M hpp] at hmem
      have hle : barImage D.M L₁ ≤ pElementSubgroup p (CFSG.layer (Bar2 D.M)) := by
        rw [PartTwo.s13_pElementSubgroup_layer_eq hns hpp]
        exact le_iSup₂ (f := fun J (_ : J ∈ PartTwo.s13_compsP (Bar2 D.M) p) => J) _ hJ₁
      exact hxn hS hp hB hL₁ hn hU hpn hyM (hPN y.2) ((Subgroup.orderOf_coe y).trans hy)
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)
          (PartTwo.s13_Thirteen2_pElementSubgroup_le p _ hmem))
    ·
      have hcard' := Finset.card_erase_of_mem hJ₁
      obtain ⟨J₂, hJ₂e, h2J₂⟩ :=
        hbig ((PartTwo.s13_compsP (Bar2 D.M) p).erase (barImage D.M L₁)) (by omega)
      have hne := Finset.ne_of_mem_erase hJ₂e
      obtain ⟨L₂, hL₂, rfl, hr₂⟩ := hcomp J₂ (Finset.mem_of_mem_erase hJ₂e)
      obtain ⟨⟨m, hm, hU₂, hpm⟩, -⟩ := (hrank L₂ hL₂).resolve_left (by omega)
      obtain ⟨y, hyL, hyB, hy⟩ := uc22s13xm_exists_elem (PartTwo.s13_le_of_mem_calC hL₂)
        (hH.normal L₂ hL₂) D.sylowM hB.2.1 hB.2.2.1 hB.2.2.2.1 hm (Or.inr hU₂) hpp
        (Or.inr ⟨hU₂, hpm⟩)
      have hyM := PartTwo.s13_le_of_mem_calC hL₂ hyL
      exact hxn hS hp hB hL₁ hn hU hpn hyM (Subgroup.centralizer_le_normalizer _ hyB) hy
        (PartTwo.s13_components_commute hns (PartTwo.s13_barImage_isComponent hL₂) hC₁ hne
          (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyL)))

theorem r136bFour_setup4_of_r7_8R3p3
    (hSE : StronglyEmbeddedFive) (hB3 : BadNoStrongThree) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    (h78 : R7_8R3p3 (UC6.dataOfSetup4 hS hU S)) (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S))
    (h847 : F08.R847 (UC6.dataOfSetup4 hS hU S)) : R136bFour (UC6.dataOfSetup4 hS hU S) :=
  r136bFour_of_r7_8R3p3 hThin hCyc (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (fun _ hp => UC6.four_le_pRank_of_sigma hp) h78 (r82_dataOfSetup4 hS hU S hPart.2.2) h846
    (r847Four_of_r847 _ h847 (by have := hS.rank; omega))
    fun hS13 _ hp _ hB _ hL _ hn hU3 hpn _ hyM hyN hy hyc =>
      uc22ine229_s13xn_false_setup4 hSE hB3 hThin hS hU S hσ hS13
        (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
        (r847E4_of_r847 _ h847 (by have := hS.rank; omega)) hp hB hL hn hU3 hpn hyM hyN hy hyc

theorem uc22ine229_s21_21EB_setup4_of_r7_8R3p3
    (hSE : StronglyEmbeddedFive) (hB3 : BadNoStrongThree)
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    {Ch : Choice2011 G} (h78 : R7_8R3p3 (UC6.dataOfSetup4 hS hU S))
    (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S)) (h847 : F08.R847 (UC6.dataOfSetup4 hS hU S))
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) (h216 : S21_16 (UC6.dataOfSetup4 hS hU S) Ch)
    (h218 : S21_18 (UC6.dataOfSetup4 hS hU S) Ch) (h219 : S21_9N (UC6.dataOfSetup4 hS hU S) Ch)
    (h19 : S21_19 (UC6.dataOfSetup4 hS hU S) Ch) : S21_21EB (UC6.dataOfSetup4 hS hU S) Ch :=
  uc22s13xe_s21_21EB_setup4 hThin hCyc hS hU S
    (r136bFour_setup4_of_r7_8R3p3 hSE hB3 hThin hCyc hS hU S hσ hPart h78 h846 h847) h847 h211
    h216 h218 h219 h19

end CFSG.LocalAnalysis.UniquenessCase.UC22
