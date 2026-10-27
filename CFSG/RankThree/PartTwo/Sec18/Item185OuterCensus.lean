module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterBase
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Cases
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Rank2
public import CFSG.RankThree.PartTwo.Sec19.SimsC198RankOdd
public import CFSG.RankThree.PartTwo.Sec19.SimsC198RankSpor
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowSpor
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowAlt
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Lin
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Lin2
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo
import CFSG.RankThree.PartTwo.Sec4.Item49Small
import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofOddModels
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp Alt42One Alt42Two Alt42Three Alt42Four
  Alt42Five Alt42Six Alt42Eight Alt42Nine)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27 AutNoE27)

section Facts

private theorem card_fixedSubgroup_congr_eq {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (σ : MulAut X) :
    Nat.card (fixedSubgroup σ) = Nat.card (fixedSubgroup (MulAut.congr e σ)) := by
  have hfix : fixedSubgroup (MulAut.congr e σ) = (fixedSubgroup σ).map e.toMonoidHom := by
    ext t
    constructor
    · intro ht
      refine Subgroup.mem_map.mpr ⟨e.symm t, ?_, e.apply_symm_apply t⟩
      show σ (e.symm t) = e.symm t
      apply e.injective
      rw [e.apply_symm_apply]
      exact ht
    · rintro ⟨s, hs, rfl⟩
      have hs' : σ s = s := hs
      show e (σ (e.symm (e s))) = e s
      rw [e.symm_apply_apply, hs']
  rw [hfix, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

private theorem isSimpleGroup_of_isQuasisimple_center_eq_bot {G : Type} [Group G]
    (hQ : CFSG.IsQuasisimple G) (hZ : Subgroup.center G = ⊥) : IsSimpleGroup G := by
  haveI := hQ.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem not_isSimpleGroup_projSL_two_three_one :
    ¬ IsSimpleGroup (projSL 2 (GaloisField 3 1)) := by
  intro hs
  have hK : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num), pow_one]
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [hK]
    exact ⟨1, by norm_num⟩
  have hcard : Nat.card (projSL 2 (GaloisField 3 1)) = 12 := by
    rw [CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof.card_projSL_two_of_odd hodd, hK]
    norm_num
  have hfin : Finite (projSL 2 (GaloisField 3 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hsolv : Group.IsSolvable (projSL 2 (GaloisField 3 1)) :=
    TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
      (a := 2) (b := 1) (by rw [hcard]; norm_num)
  haveI : IsMulCommutative (projSL 2 (GaloisField 3 1)) :=
    ⟨⟨(IsSimpleGroup.comm_iff_isSolvable).mpr hsolv⟩⟩
  have hp := Group.is_simple_iff_prime_card.mp hs
  rw [hcard] at hp
  norm_num at hp

theorem noOmega_projSL_two {p e : ℕ} [Fact p.Prime] (hK : 4 ≤ p ^ e) :
    NoOmega (projSL 2 (GaloisField p e)) := by
  clear hK
  have e₀ := CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p e)
  haveI : Finite (projSL 2 (GaloisField p e)) := Finite.of_equiv _ e₀.toEquiv.symm
  apply noOmega_of_fixed_facts
  intro σ hσ hσ3
  have hα3 : (MulAut.congr e₀ σ) ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut (MulAut.congr e₀ σ) := by
    rw [CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr]
    exact hσ
  obtain ⟨τ, hτ3, ⟨ee⟩⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eqLocus_mulEquiv_psl2 hα3 hout
  have hKq : Nat.card (GaloisField p e) = Nat.card (GH74.GLS.IVK.fixedField τ) ^ 3 := by
    have h := GH74.GLS.IVK.fixedField_card_pow τ
    rw [hτ3] at h
    exact h.symm
  have h2 : 1 < Nat.card (GH74.GLS.IVK.fixedField τ) := GH74.GLS.IVK.one_lt_card_fixedField τ
  by_cases h4 : 4 ≤ Nat.card (GH74.GLS.IVK.fixedField τ)
  · left
    obtain ⟨hZ, hQ, -, -⟩ :=
      CFSG.RankThree.PartTwo.KFacts.fixedPoints_facts_of_mulEquiv_psl2 e₀ h4 hKq hσ3 hσ
    have hsimp : IsSimpleGroup (fixedSubgroup σ) :=
      isSimpleGroup_of_isQuasisimple_center_eq_bot hQ hZ
    refine ⟨⊤, Subgroup.normal_top, MulEquiv.isSimpleGroup Subgroup.topEquiv, ?_, ?_⟩
    · intro hcomm
      obtain ⟨a, b, hab⟩ := hQ.2.2
      apply hab
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact congrArg Subtype.val (hcomm ⟨x, Subgroup.mem_top x⟩ ⟨y, Subgroup.mem_top y⟩)
    · rw [Subgroup.coe_top, Subgroup.centralizer_univ]
      exact hZ
  · right
    have hcardeq : Nat.card (fixedSubgroup σ) =
        Nat.card (CFSG.GorensteinWalter.PSL2 (GH74.GLS.IVK.fixedField τ)) := by
      rw [card_fixedSubgroup_congr_eq e₀ σ]
      exact Nat.card_congr ee.toEquiv
    rw [hcardeq, CFSG.Wreathed.ProjectiveTwoParameterUniqueness.card_projective_two_field]
    have h3 : Nat.card (GH74.GLS.IVK.fixedField τ) ≤ 3 := by omega
    generalize Nat.card (GH74.GLS.IVK.fixedField τ) = q at h2 h3 ⊢
    interval_cases q <;> norm_num

theorem not_three_dvd_outer_projSL_three_three :
    ¬ 3 ∣ Nat.card (Outer (projSL 3 (GaloisField 3 1))) :=
  Sec4.Item49Small.not_three_dvd_card_outer_projSL (n := 3) (e := 1) (by norm_num) le_rfl
    (by norm_num)

theorem not_three_dvd_outer_projSU_three_three :
    ¬ 3 ∣ Nat.card (Outer (projSU 3 3 1)) :=
  Sec4.Item49Small.not_three_dvd_card_outer_projSU (n := 3) (e := 1) (by norm_num) le_rfl
    (by norm_num)

end Facts

section Cases


private theorem not_three_dvd_outer_j3_of_mulEquiv (S : Type) [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .J3) : ¬ 3 ∣ Nat.card (Outer S) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .J3) := Finite.of_equiv S e.toEquiv
  exact not_three_dvd_outer_of_mulEquiv e
    (Sec4.RonanK429H.not_three_dvd_outer_of_le_two Sec4.card_outer_J3)

theorem not_three_dvd_outer_j3 : ¬ 3 ∣ Nat.card (Outer (Sec4.Spor .J3)) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .J3 ≃* Sec4.Spor .J3 := b
  haveI : Finite (Sec4.Spor .J3) := CFSG.Sporadic.Presentation.J3.finite_card_le.1
  exact not_three_dvd_outer_j3_of_mulEquiv (Sec4.Spor .J3) b'.symm

private theorem not_three_dvd_outer_mcl_of_mulEquiv (S : Type) [Group S] [Finite S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .McL) : ¬ 3 ∣ Nat.card (Outer S) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .McL) := Finite.of_equiv S e.toEquiv
  exact not_three_dvd_outer_of_mulEquiv e
    (Sec4.RonanK429H.not_three_dvd_outer_of_le_two Sec4.card_outer_McL)

theorem not_three_dvd_outer_mcl : ¬ 3 ∣ Nat.card (Outer (Sec4.Spor .McL)) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .McL ≃* Sec4.Spor .McL := b
  haveI : Finite (Sec4.Spor .McL) := CFSG.Sporadic.Presentation.McL.finite_card_le.1
  exact not_three_dvd_outer_mcl_of_mulEquiv (Sec4.Spor .McL) b'.symm

private theorem not_three_dvd_outer_onan_of_mulEquiv (S : Type) [Group S]
    (e : S ≃* Blueprint.NativeSporadic.Carrier .ONan) : ¬ 3 ∣ Nat.card (Outer S) :=
  not_three_dvd_outer_of_mulEquiv e fun h3 =>
    absurd (Nat.dvd_trans h3 (CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four).1)
      (by norm_num)

theorem not_three_dvd_outer_onan : ¬ 3 ∣ Nat.card (Outer (Sec4.Spor .ONan)) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .ONan ≃* Sec4.Spor .ONan := b
  exact not_three_dvd_outer_onan_of_mulEquiv (Sec4.Spor .ONan) b'.symm

theorem outerCase_one : OuterCase Alt42One := by
  intro X _ _ hX P A B c hd hP
  obtain ⟨p, e, hp, hp2, he, ⟨φ⟩⟩ := hP
  have hq := hd.quotient hX
  by_cases h4 : 4 ≤ p ^ e
  · exact noOuterData_of_noOmega (center_quotient_eq_bot hX)
      (NoOmega.of_mulEquiv φ (noOmega_projSL_two h4)) _ _ _ _ hq
  · have h3 : 3 ≤ p := by have := hp.out.two_le; omega
    have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    have hp3 : p = 3 := by omega
    subst hp3
    have he1 : e = 1 := by
      by_contra hne
      have h2e : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst he1
    haveI := isSimpleGroup_quotient hX
    exact not_isSimpleGroup_projSL_two_three_one φ.symm.isSimpleGroup

theorem outerCase_two : OuterCase Alt42Two := OuterCase.of_autNoE27 fun S _ _ hP => by
  obtain ⟨p, e, hp, hp3, he1, he2, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ := hP
  all_goals have h3e : ¬ 3 ∣ e := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  · exact autNoE27_of_mulEquiv φ (autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL (Nat.ne_of_gt hp3) he1 h3e))
  · exact autNoE27_of_mulEquiv φ (autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU (Nat.ne_of_gt hp3) he1
        (lt_of_lt_of_le (by omega : 2 < p) (Nat.le_self_pow (by omega : e ≠ 0) p)) h3e))

theorem outerCase_three : OuterCase Alt42Three :=
  OuterCase.of_rankHyp fun X _ _ hX hP => by
    obtain ⟨hr, ⟨φ⟩⟩ := hP
    exact Sec19.SimsC198.false_of_rankHyp_ree27 hX hr φ

theorem outerCase_four : OuterCase Alt42Four :=
  OuterCase.of_rankHyp fun X _ _ hX hP => by
    obtain ⟨p, hp, hp3, ⟨q, hq, hq1, hG⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ := hP
    · exact Sec19.SimsC198.false_of_rankHyp_G2_large hX (by omega) hq1 hG
    · exact Sec19.SimsC198.false_of_rankHyp_PSp4 hX hp3 φ
    · exact Sec19.SimsC198.false_of_rankHyp_PSL4 hX hp3 φ
    · exact Sec19.SimsC198.false_of_rankHyp_PSU4 hX hp3 φ

theorem outerCase_five : OuterCase Alt42Five :=
  OuterCase.of_not_three_dvd_outer fun S _ _ hP => by
    obtain ⟨n, h5, h12, ⟨φ⟩⟩ := hP
    exact not_three_dvd_outer_of_mulEquiv φ
      (Sec4.RonanK429.not_three_dvd_outer_alternatingGroup h5)

open RankThree.PartTwo.Sec4.RonanK429 in
theorem outerCase_six : OuterCase Alt42Six := by
  intro X _ _ hX P A B c hd hP
  obtain ⟨s, hs, ⟨φ⟩⟩ := hP
  have hq := hd.quotient hX
  haveI : Finite (Sec4.Spor s) := Finite.of_equiv _ φ.toEquiv
  simp only [Sec4.sporadics42, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_m11).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_m12).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_m22).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_m23).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_m24).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_j1).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_j2).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ not_three_dvd_outer_j3) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_j4).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ not_three_dvd_outer_mcl) _ _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_hs).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_he).1) _ _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ (spor_ru).1) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ not_three_dvd_outer_onan) _ _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  · exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  · exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  · exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ

theorem outerCase_eight : OuterCase Alt42Eight := by
  intro X _ _ hX P A B c hd hP
  have hq := hd.quotient hX
  rcases hP with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨b, c', hbc, ⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ |
    ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact noOuterData_of_not_three_dvd_outer (not_three_dvd_outer_of_mulEquiv φ
      (Sec4.Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (n := 5) (by norm_num)))
      _ _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_PSU5_two hX le_rfl φ
  · exact noOuterData_of_not_three_dvd_outer (not_three_dvd_outer_of_mulEquiv φ
      (Sec4.Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (n := 6) (by norm_num)))
      _ _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_PSU6_two hX φ
  · exact noOuterData_of_not_three_dvd_outer (not_three_dvd_outer_of_mulEquiv φ
      (Sec4.Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (n := 7) (by norm_num)))
      _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ Sec19.SimsC198.sp62_not_three_dvd_outer) _ _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_Sp8_two hX φ
  · exact Sec19.SimsC198.false_of_rankHyp_OmegaPlus_two hX φ
  · exact noOuterData_of_not_three_dvd_outer (not_three_dvd_outer_of_mulEquiv φ
      (Sec4.RonanK429F.Om8.not_three_dvd_card_outer_projOmegaMinus hbc)) _ _ _ _ hq
  · exact noOuterData_of_not_three_dvd_outer
      (not_three_dvd_outer_of_mulEquiv φ Sec19.SimsC198.l44_not_three_dvd_outer) _ _ _ _ hq
  · exact Sec19.SimsC198.false_of_rankHyp_Sp6_four hX φ
  · exact Sec19.SimsC198.false_of_rankHyp_PSU5_two hX (by norm_num) φ
  · exact Sec19.SimsC198.false_of_rankHyp_PSU5_two hX (by norm_num) φ
  · exact Sec19.SimsC198.false_of_rankHyp_F4_two hX φ

theorem outerCase_nine : OuterCase Alt42Nine := by
  intro X _ _ hX P A B c hd hP
  have hq := hd.quotient hX
  rcases hP with ⟨e, he1, he3, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · by_cases he : e = 1
    · subst he
      exact noOuterData_of_not_three_dvd_outer
        (not_three_dvd_outer_of_mulEquiv φ not_three_dvd_outer_projSL_three_three) _ _ _ _ hq
    · exact Sec19.SimsC198.false_of_rankHyp_PSL3_three hX (by omega) φ
  · by_cases he : e = 1
    · subst he
      exact noOuterData_of_not_three_dvd_outer
        (not_three_dvd_outer_of_mulEquiv φ not_three_dvd_outer_projSU_three_three) _ _ _ _ hq
    · exact Sec19.SimsC198.false_of_rankHyp_PSU3_three hX (by omega) φ
  · exact Sec19.SimsC198.false_of_rankHyp_G2_three hX φ
  · exact Sec19.SimsC198.false_of_rankHyp_PSL4_three hX φ
  · exact Sec19.SimsC198.false_of_rankHyp_PSU4_three hX φ

end Cases

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
