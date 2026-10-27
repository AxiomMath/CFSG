module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightFitting
public import CFSG.Quasithin.Vol2.Ch11SecFO2L
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (pElementSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eM_eq_three_of_evenRank {D : Data G} (hDE : DataExt D) (h5 : 5 ∈ D.sig)
    (he3 : CFSG.Open.evenRank G = 3) : eM D.M = 3 := by
  have hge : 3 ≤ eM D.M :=
    (hDE.three_le 5 h5).trans (pRank_le_eM_of_odd_prime (M := D.M) Nat.prime_five (by norm_num))
  have hle : eM D.M ≤ 3 := (eM_le_evenRank D).trans (le_of_eq he3)
  omega

theorem isA5A5Cyclic5_of_layer_le (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV) (h638 : UC6.R6_38 D)
    (hDE : DataExt D) (h5 : 5 ∈ D.sig) (he3 : CFSG.Open.evenRank G = 3) {X : Subgroup G}
    (hXM : X ≤ D.M) (hXn : (X.subgroupOf D.M).Normal)
    (hXA : IsA5xA5 ↥(barImage D.M X))
    (hlayer : CFSG.layer (Bar2 D.M) ≤ barImage D.M X) :
    IsA5A5Cyclic5 ↥(pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let A : Subgroup (Bar2 D.M) := barImage D.M X
  let C : Subgroup (Bar2 D.M) := Subgroup.centralizer (A : Set (Bar2 D.M))
  let Y : Subgroup (Bar2 D.M) := pElementSubgroup 5 C
  have hAn : A.Normal := s13_barImage_normal hXn
  have hXA' : IsA5xA5 ↥A := hXA
  have hCp : IsPGroup 5 ↥Y :=
    isPGroup_pElementSubgroup_centralizer_of_layer_le D hV h22 h23 h638 h5
      (A := A) hlayer
  have hCrank : CFSG.Open.pRank 5 C ≤ 1 :=
    pRank_centralizer_le_one (X := X) (q := 5) (Or.inr rfl) he3 hXA
  have hYrank : CFSG.Open.pRank 5 Y ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 5) (by norm_num)
      (s13_Thirteen2_pElementSubgroup_le 5 C)).trans hCrank
  have hYcyc : IsCyclic ↥Y :=
    CFSG.Quasithin.isCyclic_of_pRank_le_one (p := 5) (by norm_num) le_rfl hCp hYrank
  haveI : A.Normal := hAn
  have hjoin : pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)) = A ⊔ Y :=
    pElementSubgroup_top_eq_sup_of_isA5xA5 (Q := Bar2 D.M) (A := A) hXA'
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    have hMeq : pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M)) = A := by
      rw [hjoin, hYbot, sup_bot_eq]
    have hMrank : CFSG.Open.pRank 5 D.M = 2 := by
      have h1 : CFSG.Open.pRank 5 D.M =
          CFSG.Open.pRank 5 (pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))) := by
        rw [← s13_pRank_bar_top Nat.prime_five (by norm_num) D.M]
        exact (s13_pRank_pElementSubgroup Nat.prime_five (⊤ : Subgroup (Bar2 D.M))).symm
      rw [h1, hMeq, CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact pRank_eq_two_of_isA5xA5 hXA' (Or.inr rfl)
    have h3 := hDE.three_le 5 h5
    omega
  have hAC : A ⊓ C = ⊥ := barImage_inf_centralizer_eq_bot (M := D.M) (X := X) hXA
  have hdisj : A ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ A ⊓ C := ⟨hx.1, s13_Thirteen2_pElementSubgroup_le 5 C hx.2⟩
    rwa [hAC] at hx'
  have hCn : C.Normal := by
    haveI : A.Normal := hAn
    exact Subgroup.normal_centralizer
  have hRchar : (pElementSubgroup 5 (⊤ : Subgroup ↥C)).Characteristic := by
    have heq : pElementSubgroup 5 (⊤ : Subgroup ↥C) = CFSG.pElementsSubgroup 5 ↥C := by
      ext x
      simp [pElementSubgroup, CFSG.pElementsSubgroup, CFSG.IsPElement]
    rw [heq]
    exact CFSG.pElementsSubgroup_characteristic 5 ↥C
  have hYmap : (pElementSubgroup 5 (⊤ : Subgroup ↥C)).map C.subtype = Y := by
    rw [s13_pElementSubgroup_map Nat.prime_five, Subgroup.map_top, Subgroup.range_subtype]
  have hYn : Y.Normal := by
    rw [← hYmap]
    letI : C.Normal := hCn
    letI : (pElementSubgroup 5 (⊤ : Subgroup ↥C)).Characteristic := hRchar
    exact ConjAct.normal_of_characteristic_of_normal
  obtain ⟨e, hYcard⟩ := hCp.exists_card_eq
  have he1 : 1 ≤ e := by
    by_contra h
    have h0 : e = 0 := by omega
    rw [h0] at hYcard
    simp only [pow_zero] at hYcard
    have hsub : Subsingleton ↥Y :=
      (Finite.card_le_one_iff_subsingleton).mp (le_of_eq hYcard)
    exact hYne (Subgroup.eq_bot_of_subsingleton _)
  have hYiso : ↥Y ≃* Multiplicative (ZMod (5 ^ e)) := by
    have h := (zmodCyclicMulEquiv hYcyc).symm
    rw [hYcard] at h
    exact h
  obtain ⟨hAiso⟩ := hXA'
  haveI : Y.Normal := hYn
  have eprod : ↥A × ↥Y ≃* ↥(A ⊔ Y) :=
    CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup (P₁ := A) (P₂ := Y) (fun a ha b hb =>
      Subgroup.commute_of_normal_of_disjoint _ _ hAn hYn (disjoint_iff.2 hdisj)
        a b ha hb) hdisj
  have eprod' : ↥A × ↥Y ≃* ↥(pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))) :=
    eprod.trans (MulEquiv.cast (M := fun x : Subgroup (Bar2 D.M) => ↥x) hjoin.symm)
  refine ⟨e, he1, ⟨eprod'.symm.trans ((hAiso.prodCongr hYiso).trans
    (MulEquiv.prodAssoc (M := alternatingGroup (Fin 5))
      (N := alternatingGroup (Fin 5)) (P := Multiplicative (ZMod (5 ^ e)))))⟩⟩

theorem Hinf_oTwoEOf_le_Opp_five_of_layer_le {D : Data G} {X : Subgroup G} (hXM : X ≤ D.M)
    (hXN : D.M ≤ normalizer (X : Set G)) (hXperf : ⁅X, X⁆ = X) (hXA : IsA5xA5 (Bar2 X))
    (hlayer : CFSG.layer (Bar2 D.M) ≤ barImage D.M X) :
    Hinf (oTwoEOf D.M) ≤ Opp 5 D.M := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpre : ∀ {M H : Subgroup G}, H ≤ M →
      barPreimage M (barImage M H) = H ⊔ pCoreOf 2 M := by
    intro M H hHM
    rw [barPreimage, barImage, Subgroup.comap_map_eq, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hHM, QuotientGroup.ker_mk']
    rfl
  have hKle : Hinf (oTwoEOf D.M) ≤ X ⊔ pCoreOf 2 D.M := by
    calc Hinf (oTwoEOf D.M) ≤ oTwoEOf D.M := uc22p21c_Hinf_le _
      _ = barPreimage D.M (CFSG.layer (Bar2 D.M)) := rfl
      _ ≤ barPreimage D.M (barImage D.M X) :=
          Subgroup.map_mono (Subgroup.comap_mono hlayer)
      _ = X ⊔ pCoreOf 2 D.M := hpre hXM
  have hKX : Hinf (oTwoEOf D.M) ≤ X :=
    CFSG.Quasithin.Vol2.Ch11.SecF.le_of_le_sup_of_perfect
      (uc22p21c_Hinf_perfect (oTwoEOf D.M)) (uc22p21c_isPGroup_pCoreOf D.M)
      ((uc22p21c_pCoreOf_le D.M).trans hXN) hKle
  have hAtop : IsA5xA5 ↥(⊤ : Subgroup (Bar2 X)) :=
    hXA.elim fun e => ⟨(Subgroup.topEquiv (G := Bar2 X)).trans e⟩
  have hbarTop : barImage X (Opp 5 X) = ⊤ := by
    rw [s13_barImage_opp (p := 5) Nat.prime_five (le_refl X), s13_barImage_self]
    exact pElementSubgroup_eq_self_of_isA5xA5 (A := ⊤) hAtop
  have hXopp : X ≤ Opp 5 X := by
    have hstep : X ≤ Opp 5 X ⊔ pCoreOf 2 X := by
      intro x hx
      have hxbar : uc22p21cPi X ⟨x, hx⟩ ∈ barImage X (Opp 5 X) := by
        rw [hbarTop]
        exact Subgroup.mem_top _
      have hxpre : x ∈ barPreimage X (barImage X (Opp 5 X)) :=
        (uc22p21c_mem_barPreimage).2 ⟨hx, hxbar⟩
      have hxpre' : x ∈ barPreimage X (barImage X (pElementSubgroup 5 X)) := hxpre
      rw [hpre (s13_Thirteen2_pElementSubgroup_le 5 X)] at hxpre'
      exact hxpre'
    exact CFSG.Quasithin.Vol2.Ch11.SecF.le_of_le_sup_of_perfect hXperf
      (uc22p21c_isPGroup_pCoreOf X)
      ((uc22p21c_pCoreOf_le X).trans
        (CFSG.LocalAnalysis.RankThreeUC.le_normalizer_pElementSubgroup 5 X)) hstep
  exact (hKX.trans hXopp).trans (s13_Thirteen2_pElementSubgroup_mono hXM)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
