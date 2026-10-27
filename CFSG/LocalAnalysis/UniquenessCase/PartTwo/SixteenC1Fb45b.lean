module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbPerf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbOrb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Fb43ThreeB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21CasesB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_vTil_mul_self {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (w : Vtil V₀ V hV) :
    w * w = 1 := by
  rw [← pow_two]
  exact s15_Infra_vtil_sq_eq_one V₀ V hV w

theorem s16c1_sylow_centralizer (D : Data G) {V : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (hx : Setup1645 D V hV x)
    (hW : E3.wClos V 0 D.T ≤ centralizer ({x.val} : Set G))
    (hN : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M) :
    IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) := by
  let C : Subgroup G := centralizer ({x.val} : Set G)
  let S : Subgroup G := D.T ⊓ C
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hS2 : IsPGroup 2 S := hT.isPGroup.to_le inf_le_left
  have hWS : E3.wClos V 0 D.T ≤ S := le_inf (E3.wClos_le (V := V) 0 D.T) hW
  have hSM : S ≤ D.M := inf_le_left.trans hT.le
  have hNormS : Subgroup.normalizer (S : Set G) ≤ D.M :=
    (E3.e3_15_normalizer (V := V) (i := 0) (H := D.M) (S := D.T) (Y := S)
      hT hSM hS2 hWS).trans hN
  obtain ⟨S', hS'syl, hSS'⟩ := exists_isSylowIn_ge 2 (inf_le_right : S ≤ C) hS2
  have hle : S' ≤ S := by
    by_contra hnot
    have hlt : S < S' := lt_of_le_of_ne hSS' fun h => hnot (h ▸ le_rfl)
    have hU : S.subgroupOf S' < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro hU
      exact (not_le_of_gt hlt) (Subgroup.subgroupOf_eq_top.mp hU)
    haveI : Finite ↥S' := inferInstance
    haveI : Group.IsNilpotent ↥S' := hS'syl.isPGroup.isNilpotent
    obtain ⟨y, hyNorm, hyNotU⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (G := ↥S') (S.subgroupOf S') hU)
    have hyC : (y : G) ∈ C := hS'syl.le y.2
    have hyNormS : (y : G) ∈ Subgroup.normalizer (S : Set G) := by
      have h1 : y ∈ (Subgroup.normalizer S).subgroupOf S' := by
        rw [Subgroup.subgroupOf_normalizer_eq hSS']
        exact hyNorm
      exact h1
    have hyM : (y : G) ∈ D.M := hNormS hyNormS
    have hyNotS : (y : G) ∉ S := hyNotU
    have hP2 : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers (y : G)) :=
      hS'syl.isPGroup.to_le (sup_le hSS' (Subgroup.zpowers_le.mpr y.2))
    have hPMC : S ⊔ Subgroup.zpowers (y : G) ≤ D.M ⊓ C :=
      sup_le (le_inf hSM inf_le_right) (Subgroup.zpowers_le.mpr ⟨hyM, hyC⟩)
    have hSP : S < S ⊔ Subgroup.zpowers (y : G) := by
      refine lt_of_le_of_ne le_sup_left fun h =>
        hyNotS (h.symm ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (y : G)))
    obtain ⟨S'', hS''syl, hPS''⟩ := exists_isSylowIn_ge 2 hPMC hP2
    have hcard : Nat.card ↥S'' = Nat.card ↥S :=
      hS''syl.card_eq.trans hx.sylow.card_eq.symm
    have hlecard : Nat.card ↥(S ⊔ Subgroup.zpowers (y : G)) ≤ Nat.card ↥S :=
      (Subgroup.card_le_of_le hPS'').trans_eq hcard
    exact absurd hlecard (not_le_of_gt (Subgroup.card_lt_of_lt hSP))
  have heq : S = S' := le_antisymm hSS' hle
  change IsSylowIn 2 S C
  exact heq.symm ▸ hS'syl

theorem s16c1_pRank_three_pos {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {x : IntMod V hV}
    (hE : IsE16A5 ↥(barSub V₀ V hV (xInf L x.val))) :
    1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({x.val} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXle : xInf L x.val ≤ stabTil V₀ V :=
    ((perfectCore_le _).trans inf_le_right).trans (s16c1_le_stabTil D hS)
  have hXJ : xInf L x.val ≤ D.M ⊓ centralizer ({x.val} : Set G) :=
    le_inf ((perfectCore_le _).trans (inf_le_right.trans hS.setting.hyp151.le))
      ((perfectCore_le _).trans inf_le_left)
  have h3dvd : 3 ∣ Nat.card ↥(D.M ⊓ centralizer ({x.val} : Set G)) := by
    have hdiv1 : Nat.card ↥(barSub V₀ V hV (xInf L x.val)) ∣
        Nat.card ↥((xInf L x.val).subgroupOf (stabTil V₀ V)) := by
      unfold barSub
      exact Subgroup.card_map_dvd (H := (xInf L x.val).subgroupOf (stabTil V₀ V))
        (actTil V₀ V hV)
    have hcard : Nat.card ↥((xInf L x.val).subgroupOf (stabTil V₀ V)) =
        Nat.card ↥(xInf L x.val) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv
    have h3bar : 3 ∣ Nat.card ↥(barSub V₀ V hV (xInf L x.val)) := by
      rw [s16c1_card_of_isE16A5 hE]
      norm_num
    have h3X : 3 ∣ Nat.card ↥(xInf L x.val) := by
      rw [← hcard]
      exact h3bar.trans hdiv1
    exact h3X.trans (Subgroup.card_dvd_of_le hXJ)
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hx₀G : (x₀ : G) ∈ D.M ⊓ centralizer ({x.val} : Set G) := x₀.2
  have hx₀ord : orderOf (x₀ : G) = 3 := by rwa [Subgroup.orderOf_coe]
  refine CFSG.SectionRank.le_pRank (p := 3)
    (H := D.M ⊓ centralizer ({x.val} : Set G)) (E := Subgroup.zpowers (x₀ : G)) (k := 1)
    (by norm_num) (Subgroup.zpowers_le.mpr hx₀G) ?_ ?_
  · exact CFSG.Open.isElemAbelian_zpowers (by
      rw [← hx₀ord]; exact pow_orderOf_eq_one (x₀ : G))
  · rw [Nat.card_zpowers, hx₀ord, pow_one]

theorem r16_45b_of (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hx : DataExt D) (hσ3 : SigmaThree D)
    (hkit : OmegaKit) (hkitB : OmegaKitB) (h41 : R16_41 D) (h42 : R16_42 D) (h43 : R16_43_1 D) :
    R16_45b D := by
  intro V₀ V L hV hS hc x hx1
  obtain ⟨⟨Q₀, hQ₀, hQ₀inv⟩, hmain⟩ := h41 V₀ V L hV hS hc
  have ha : ∀ Q : Vtil V₀ V hV → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q (lBar V₀ V hV L) →
      Q (mkTil V₀ V hV x) = 0 := by
    intro Q hQ hQinv
    by_contra hne
    exact hx1.not_le (((hmain Q hQ hQinv).2 (mkTil V₀ V hV x) hne).2 x rfl)
  have hz1 : mkTil V₀ V hV x ≠ 1 := s16c1_mkTil_ne_one hS hx1
  have hE : IsE16A5 ↥(ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) :=
    (hmain Q₀ hQ₀ hQ₀inv).1 _ hz1 (ha Q₀ hQ₀ hQ₀inv)
  have h960 : Nat.card (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) = 960 :=
    s16c1_card_of_isE16A5 hE
  have hk := hkit (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  have hkB := hkitB (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  have hW64 : Nat.card (Vtil V₀ V hV) = 64 := by
    have h := Sixteen21.card_vTil_of_case1 hV hc
    simpa using h
  have hperf := s16c1_perfect_of_kit hk.2.1 hk.2.2 hW64 (s16c1_vTil_mul_self hV) hz1 hE
  have hbar := s16c1_barSub_xInf_eq (c23_card_v0_le_four D hS.setting.hyp16)
    (s16c1_le_stabTil D hS) x hperf
  have hc3 : IsE16A5 ↥(barSub V₀ V hV (xInf L x.val)) := by
    rw [hbar]
    exact hE
  have hsyl := s16c1_sylow_lBar hS hkB.1
  have horb := s16c1_orbit_sylow_le_four hS hc hkitB (Sixteen21.card_lBar_of_case1 hV hc) hx1 h960
  have hW0 := s16c1_wClos_le_centralizer D hSg h1219 h21 h22 h42 h43 hkitB hS hc hsyl hz1
    h960 horb
  have hb : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) :=
    s16c1_sylow_centralizer D hx1 hW0
      (r16_43_3_of D hSg h1219 h21 h22 h61 h42 h43 hkitB V₀ V L hV hS hc)
  have hz2 : x.val ^ 2 = 1 := hV.2 x.val x.val_mem
  have hsig : D.sig = {3} := hc.2.2.1
  have hse : IsStronglyPEmbedded 3 D.M := isStronglyPEmbedded_three D hSg h1219 hsig
  refine ⟨ha, hb, hc3, ?_, ?_⟩
  · exact pRank_three_centralizer D h61 (by rw [hsig]; exact Set.mem_singleton 3) hse hx1.ne_one
      ⟨1, by simpa using hz2⟩ hx1.not_le (s16c1_pRank_three_pos hS hc3)
  · intro q hq hq3
    exact pRank_le_two_of_twoLocal D hx hσ3 hsig hc.2.2.2 hq hq3
      (uc22p22u_isTwoLocal_centralizer hx1.ne_one hz2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
