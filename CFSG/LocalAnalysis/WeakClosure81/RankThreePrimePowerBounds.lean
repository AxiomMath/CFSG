module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASIn
public import CFSG.LocalAnalysis.WeakClosure81.RankThreeWreathedBounds
public import CFSG.Quasithin.EmptyFaithful.E22SL3
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IH
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47FldComp
public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinNum
public import CFSG.LocalAnalysis.WeakClosure81.PSLThreeInnerMaximal
public import CFSG.LocalAnalysis.WeakClosure81.PSLThreeInnerTorus
public import CFSG.LocalAnalysis.WeakClosure81.PSLThreeOuterCentralizer
public import CFSG.LocalAnalysis.WeakClosure81.PSUThreeInnerMaximal
public import CFSG.LocalAnalysis.WeakClosure81.PSUThreeOuterCentralizer
public import CFSG.LocalAnalysis.WeakClosure81.PSUThreeOuterPairs
public import CFSG.LocalAnalysis.WeakClosure81.PSUThreeInnerTorus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open scoped MatrixGroups

private theorem inE_one_top_of_nParam_le_one {G : Type} [Group G] [Finite G]
    (h : CFSG.Quasithin.E1.nParam (⊤ : Subgroup G) ≤ 1) :
    CFSG.Quasithin.E1.InE 1 (⊤ : Subgroup G) :=
  (CFSG.Quasithin.E1.nParam_le_iff (H := (⊤ : Subgroup G)) (n := 1) Nat.one_pos).mp
    (by exact_mod_cast h)

private theorem nParam_le_one_psl_q1
    {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf2 : 2 ≤ f)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hP : LieModel ↥(CFSG.generalizedFitting Q) .PSL 3 p f)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤)
    (hq1 : p ^ f % 4 = 1) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
  by_cases hf3 : 3 ≤ f
  · exact nParam_le_one_of_lieModel_PSL_three_of_three_le hp hp2 hf3 hq1 hs hnab hP hT hFT
  · have h5 : 5 < p ^ f := by
      have := CFSG.RankThree.PartTwo.Sec4.HeringPin.nine_le_pow hp hp2 hf2
      omega
    exact nParam_le_one_of_lieModel_PSL_three_of_five_lt hp hp2 h5 hq1 hs hnab hP hT hFT

private theorem nParam_le_one_psu_q3
    {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf2 : 2 ≤ f)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hP : LieModel ↥(CFSG.generalizedFitting Q) .PSU 3 p f)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤)
    (hq3 : p ^ f % 4 = 3) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 :=
  nParam_le_one_of_lieModel_PSU_three_of_two_le hp hp2 hf2 hq3 hs hnab hP hT hFT

private theorem nParam_le_one_psl_pure
    {Q : Type} [Group Q] [Finite Q] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hAS : SecE3.AlmostSimple (CFSG.generalizedFitting Q))
    (hLtop : CFSG.generalizedFitting Q = ⊤)
    (hP : LieModel ↥(CFSG.generalizedFitting Q) .PSL 3 p f) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
  classical
  obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hP
  letI : Field K := hKfld
  letI : Finite K := hKfin
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := CFSG.LieType.BorelTits.charP_of_natCard_eq hKcard
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting Q) := hAS.simple
  haveI : IsSimpleGroup (projectiveSL 3 K) := e.symm.isSimpleGroup
  let eQ : Q ≃* projectiveSL 3 K :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)).trans e
  rw [CFSG.Quasithin.E1.Eleven.nParam_top_mulEquiv eQ]
  exact CFSG.Quasithin.E22S.nParam_projectiveSL_three_le_one (K := K) (p := p) hp2

private theorem settingL3_psl3_of_qmod4_three
    {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf2 : 2 ≤ f)
    (hK : Nat.card K = p ^ f) (hq3 : p ^ f % 4 = 3)
    (hAS : SecE3.AlmostSimple L) (e : ↥L ≃* projectiveSL 3 K)
    (hGL : ∃ g : Q, g ∉ L)
    (hLie : LieModel ↥L .PSL 3 p f) :
    SecU1.L3I.SettingL3 L := by
  classical
  haveI : L.Normal := hAS.normal
  have hfodd : Odd f :=
    CFSG.GH74.KGroups.L3Eps.odd_of_pow_mod_four_eq_three (hp.odd_of_ne_two hp2) hq3
  have hf3 : 3 ≤ f := by
    obtain ⟨k, hk⟩ := hfodd
    omega
  have hq9 : 9 ≤ p ^ f := CFSG.RankThree.PartTwo.Sec4.HeringPin.nine_le_pow hp hp2 hf2
  have hq5 : 5 ≤ p ^ f := by omega
  have hq7 : 7 ≤ p ^ f := by omega
  have hoddK : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2K : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hoddK
  refine
    { almostSimple := hAS
      two_dvd := ?_
      inner_conj := ?_
      inner_max := ?_
      inner_nParam := ?_
      inner_torus := ?_
      outer := ?_
      outer_pair := ?_ }
  · rw [Nat.card_congr e.toEquiv]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P47Fld.two_dvd_card_projectiveSL3 h2K
  · intro x hxL y hyL hx2 hy2
    let xL : ↥L := ⟨x, hxL⟩
    let yL : ↥L := ⟨y, hyL⟩
    have hx2' : orderOf xL = 2 := by
      dsimp [xL]
      simpa only [Subgroup.orderOf_mk] using hx2
    have hy2' : orderOf yL = 2 := by
      dsimp [yL]
      simpa only [Subgroup.orderOf_mk] using hy2
    have hxe : orderOf (e xL) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hx2'
    have hye : orderOf (e yL) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hy2'
    obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psl3
      (K := K) hoddK (a := e xL) (b := e yL) hxe hye
    refine ⟨((e.symm g : ↥L) : Q), (e.symm g).2, ?_⟩
    have hconjL : e.symm g * xL * (e.symm g)⁻¹ = yL := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
    exact congrArg (fun t : ↥L => (t : Q)) hconjL
  · intro x hxL hx2
    exact isCoatom_centralizer_of_psl3_graph_extension hp hp2 hK hfodd hAS e hGL hxL hx2
  · intro x hxL hx2
    exact nParam_centralizer_le_one_of_psl3 hp hp2 hf3 hK hAS hxL hx2 e
  · intro x hxL y hyL hx2 hy2 hxy hcomm U hU hUle
    obtain ⟨P, hPL, hPprime, hPne2, hPU, hPnotx, -⟩ :=
      exists_inner_torus_of_psl3 (K := K) (hq4 := by rw [hK]; exact hq3)
        (hq7 := by rw [hK]; exact hq7) hAS.normal e hxL hyL hx2 hy2 hxy hcomm U hU hUle
    exact ⟨P, hPprime, hPne2, hPU, hPnotx⟩
  · intro b hbL hb2
    exact sigmaFacts_psl3_outer hAS hp hp2 hfodd hq5 hLie hbL hb2
  · exact outer_pair_psl3_of_almostSimple hAS hp2 hq3 hLie

private theorem nParam_le_one_psl_q3_of_lt_top
    {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} {p f : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hf2 : 2 ≤ f)
    (hK : Nat.card K = p ^ f) (hq3 : p ^ f % 4 = 3)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hP : LieModel ↥(CFSG.generalizedFitting Q) .PSL 3 p f)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤)
    (hGL : ∃ g : Q, g ∉ CFSG.generalizedFitting Q)
    (e : ↥(CFSG.generalizedFitting Q) ≃* projectiveSL 3 K) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
  have hAS : SecE3.AlmostSimple (CFSG.generalizedFitting Q) :=
    SecE3.almostSimple_generalizedFitting hs hnab hT.2.1 hFT
  have hSetting : SecU1.L3I.SettingL3 (CFSG.generalizedFitting Q) :=
    settingL3_psl3_of_qmod4_three hp hp2 hf2 hK hq3 hAS e hGL hP
  exact SecU1.L3I.nParam_le_one_of_settingL3 SecU1.torusMember_holds
    SecU1.componentMember_holds hSetting

private theorem settingL3_psu3_of_qmod4_one
    {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {K : Type} [Field K]
    {p f : ℕ} (hp2 : p ≠ 2) (hf2 : 2 ≤ f)
    (hU : UnitaryFieldData p f K) (hq1 : p ^ f % 4 = 1)
    (hAS : SecE3.AlmostSimple L)
    (e : ↥L ≃* StatedProj (StatedSU 3 (p ^ f) K))
    (hLie : LieModel ↥L .PSU 3 p f) :
    SecU1.L3I.SettingL3 L := by
  classical
  haveI : L.Normal := hAS.normal
  haveI : Finite K := hU.finite
  have hp : p.Prime := hU.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := hU.charP
  have hq9 : 9 ≤ p ^ f := CFSG.RankThree.PartTwo.Sec4.HeringPin.nine_le_pow hp hp2 hf2
  have hq5 : 5 ≤ p ^ f := by omega
  refine
    { almostSimple := hAS
      two_dvd := ?_
      inner_conj := ?_
      inner_max := ?_
      inner_nParam := ?_
      inner_torus := ?_
      outer := ?_
      outer_pair := ?_ }
  · have hord : orderOf (unitaryProj hU 3 (unitaryInvT hU)) = 2 :=
      CFSG.RankThree.Classical.orderOf_unitaryProj_unitaryInvT hU hp2
    have htwoU : 2 ∣ Nat.card (unitaryPSU hU 3) := by
      rw [← hord]
      exact orderOf_dvd_natCard _
    have hcardU : Nat.card (unitaryPSU hU 3) =
        Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) :=
      Nat.card_congr
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := 3) (by norm_num)).toEquiv
    have htwoSP : 2 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) := by
      rwa [hcardU] at htwoU
    rw [Nat.card_congr e.toEquiv]
    exact htwoSP
  · intro x hxL y hyL hx2 hy2
    let xL : ↥L := ⟨x, hxL⟩
    let yL : ↥L := ⟨y, hyL⟩
    have hx2' : orderOf xL = 2 := by
      dsimp [xL]
      simpa only [Subgroup.orderOf_mk] using hx2
    have hy2' : orderOf yL = 2 := by
      dsimp [yL]
      simpa only [Subgroup.orderOf_mk] using hy2
    have hxe : orderOf (e xL) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hx2'
    have hye : orderOf (e yL) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact hy2'
    obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psu3
      hU hp2 (a := e xL) (b := e yL) hxe hye
    refine ⟨((e.symm g : ↥L) : Q), (e.symm g).2, ?_⟩
    have hconjL : e.symm g * xL * (e.symm g)⁻¹ = yL := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hg]
    exact congrArg (fun t : ↥L => (t : Q)) hconjL
  · intro x hxL hx2
    exact isCoatom_centralizer_of_almostSimple_psu3 hAS hLie hp2 hf2 hxL hx2
  · intro x hxL hx2
    by_cases hf3 : 3 ≤ f
    · exact nParam_centralizer_le_one_of_psu3 hU hp2 hf3 hAS hxL hx2 e
    · exact nParam_centralizer_le_one_of_psu3_of_five_lt hU hp2 (by omega) hAS hxL hx2 e
  · intro x hxL y hyL hx2 hy2 hxy hcomm U hU2 hUle
    obtain ⟨P, hPL, hPprime, hPne2, hPU, hPnotx⟩ :=
      inner_torus_psu3_model hU hp2 hf2 hq1 e hxL hyL hx2 hy2 hxy hcomm U hU2 hUle
    exact ⟨P, hPprime, hPne2, hPU, hPnotx⟩
  · intro b hbL hb2
    exact sigmaFacts_psu3_outer hAS hp hp2 hf2 hLie hbL hb2
  · exact outer_pair_psu3 hAS hLie

private theorem nParam_le_one_psu_q1
    {Q : Type} [Group Q] [Finite Q] {T : Subgroup Q} {p f : ℕ} {K : Type} [Field K]
    (hp2 : p ≠ 2) (hf2 : 2 ≤ f)
    (hU : UnitaryFieldData p f K) (hq1 : p ^ f % 4 = 1)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hP : LieModel ↥(CFSG.generalizedFitting Q) .PSU 3 p f)
    (hT : IsSylowIn 2 T ⊤) (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤)
    (e : ↥(CFSG.generalizedFitting Q) ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
  have hAS : SecE3.AlmostSimple (CFSG.generalizedFitting Q) :=
    SecE3.almostSimple_generalizedFitting hs hnab hT.2.1 hFT
  have hSetting : SecU1.L3I.SettingL3 (CFSG.generalizedFitting Q) :=
    settingL3_psu3_of_qmod4_one hp2 hf2 hU hq1 hAS e hP
  exact SecU1.L3I.nParam_le_one_of_settingL3 SecU1.torusMember_holds
    SecU1.componentMember_holds hSetting

theorem asch4_11ASPow_holds :
    Asch4_11ASPow := by
  intro Q _ _ T p f hp hp2 hf2 hs hnab hP hT hFT
  classical
  let L : Subgroup Q := CFSG.generalizedFitting Q
  have hAS : SecE3.AlmostSimple L :=
    SecE3.almostSimple_generalizedFitting hs hnab hT.2.1 hFT
  haveI : L.Normal := hAS.normal
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hqmod4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 :=
    Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqodd)
  have hmain : E1.nParam (⊤ : Subgroup Q) ≤ 1 := by
    rcases hP with hPSL | hPSU
    · rcases hqmod4 with hq1 | hq3
      · exact nParam_le_one_psl_q1 hp hp2 hf2 hs hnab hPSL hT hFT hq1
      · by_cases hLtop : L = ⊤
        · exact nParam_le_one_psl_pure hp hp2 hAS hLtop hPSL
        · have hGL : ∃ g : Q, g ∉ L := by
            by_contra h
            push Not at h
            exact hLtop ((Subgroup.eq_top_iff' L).mpr h)
          obtain ⟨K, hKfld, hKfin, hKcard, ⟨e⟩⟩ :=
            CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hPSL
          letI : Field K := hKfld
          letI : Finite K := hKfin
          exact nParam_le_one_psl_q3_of_lt_top hp hp2 hf2 hKcard hq3 hs hnab hPSL hT hFT hGL e
    · rcases hqmod4 with hq1 | hq3
      · obtain ⟨-, hf1, K, hKfld, hKfin, hKcard, ⟨e⟩⟩ :=
          CFSG.GH74.Generic.lieModel_psu_data hPSU
        letI : Field K := hKfld
        letI : Finite K := hKfin
        have hU : UnitaryFieldData p f K :=
          ⟨hp, hf1, by rw [hKcard, ← pow_mul, Nat.mul_comm]⟩
        exact nParam_le_one_psu_q1 hp2 hf2 hU hq1 hs hnab hPSU hT hFT e
      · exact nParam_le_one_psu_q3 hp hp2 hf2 hs hnab hPSU hT hFT hq3
  exact inE_one_top_of_nParam_le_one hmain

end CFSG.LocalAnalysis.WeakClosure81

end
