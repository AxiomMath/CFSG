module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150Acts
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150Cfg
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150D4
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150AutL3
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Defs
public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Final
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank

theorem false_of_acts_odd (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    {Y : Type} [Group Y] [Finite Y] (hY : SectionFourHyp Y)
    {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    {c : Y} (hcA : c ∈ A) (hc : c ∉ Sec4.thetaQuotCentralizer Λ)
    {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c) (hLΛ : L ≤ Λ)
    (hAL : A ≤ Subgroup.normalizer (L : Set Y)) (hAL9 : Nat.card ↥(A ⊓ L) = 9)
    {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hJ : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) : False := by
  obtain ⟨-, -, hLperf⟩ := Sylow155R3.Thm90.thetaComponentsAt_facts hL
  have hθ := Sec12.Hering129L.OTwoL3.ks129OTwoL3_holds ↥L (Sec4.sectionFourHyp_subgroup hY L)
    hLperf ⟨p, e, inferInstance, hp2, he, hJ⟩
  obtain ⟨hconcl, -, hK⟩ :=
    conclS429_and_iso_of_acts h1 h2 hY hΛ hA hA27 hAN hcA hc hL hLΛ hAL hAL9 he hJ hθ
  have hp : p.Prime := Fact.out
  have h2n : ∀ n : ℕ, 1 ≤ n → ¬ Sec4.IsoLThreePi ↥(imageS Λ L) 2 n := fun n hn hK2 => by
    have hdvd : p ∣ 2 ^ n :=
      Sec19.Step1917EqProof.eq_of_isoLThreePi he hn hK hK2 ▸ dvd_pow_self p (by omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  rcases hconcl.2 with (⟨⟨φ⟩, -⟩ | ⟨n, hn, hK2, -⟩) | ⟨n, hn, hK2, -⟩
  · exact Sec14.not_isoLThreePi_alternating_seven p e
      (Sec4.RonanK429.isoLThreePi_of_mulEquiv φ.symm hK)
  · exact h2n n hn hK2
  · exact h2n n hn hK2

theorem noTwo_of_acts_even (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h44 : Sec4.Item4_4) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] [Finite Y] (hY : SectionFourHyp Y)
    {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    {c : Y} (hcA : c ∈ A) (hc : c ∉ Sec4.thetaQuotCentralizer Λ)
    {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c) (hLΛ : L ≤ Λ)
    (hAL : A ≤ Subgroup.normalizer (L : Set Y)) (hAL9 : Nat.card ↥(A ⊓ L) = 9)
    {e : ℕ} (he : 1 ≤ e) (hJ : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 e) :
    NoTwoNormalized (imageS Λ L) ∧ NoTwoCentAut (imageS Λ L) := by
  obtain ⟨-, -, hLperf⟩ := Sylow155R3.Thm90.thetaComponentsAt_facts hL
  have hθ := Sec12.Hering129L.OTwo.theta_eq_pCore_two_of_isoLThreePi_even h44 hGA
    (Sec4.sectionFourHyp_subgroup hY L) hLperf he hJ
  have hcfg := cfgS429_of_acts hΛ hA hA27 hAN hcA hc hL hLΛ hAL hAL9 he hJ hθ
  obtain ⟨hKs, hsurv⟩ :=
    survivors_of_acts h1 h2 h44 hGA hY hΛ hA hA27 hAN hcA hc hL hLΛ hAL hAL9 he hJ
  have hσ : Liebeck155R1T150.Pump.actOnS Λ ⟨c, hAN hcA⟩ ^ 3 = 1 := by
    have hc3 : (⟨c, hAN hcA⟩ : ↥(Subgroup.normalizer (Λ : Set Y))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA.2 c hcA)
    rw [← map_pow, hc3, map_one]
  rcases hsurv with h | h
  · exact ⟨noTwoNormalized_of_survL3 hKs h,
      noTwoCentAut_of_survL3_pow_three hcfg.le_autFix hKs hcfg.isSubnormal hσ h⟩
  · exact ⟨noTwoNormalized_of_survD4 hKs h, noTwoCentAut_of_survD4 hKs h⟩

theorem noTwo_of_acts_l3 (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h44 : Sec4.Item4_4) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {Y : Type} [Group Y] [Finite Y] (hY : SectionFourHyp Y)
    {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {A : Subgroup Y} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    {c : Y} (hcA : c ∈ A) (hc : c ∉ Sec4.thetaQuotCentralizer Λ)
    {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c) (hLΛ : L ≤ Λ)
    (hAL : A ≤ Subgroup.normalizer (L : Set Y)) (hAL9 : Nat.card ↥(A ⊓ L) = 9)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hJ : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) :
    NoTwoNormalized (imageS Λ L) ∧ NoTwoCentAut (imageS Λ L) := by
  by_cases hp2 : p = 2
  · subst hp2
    exact noTwo_of_acts_even h1 h2 h44 hGA hY hΛ hA hA27 hAN hcA hc hL hLΛ hAL hAL9 he hJ
  · exact (false_of_acts_odd h1 h2 hY hΛ hA hA27 hAN hcA hc hL hLΛ hAL hAL9 hp2 he hJ).elim

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem res1T150Acts_l3 (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h44 : Sec4.Item4_4) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h149 : Sec16.Item149S14) {P : ∀ (Y : Type) [Group Y], Prop} :
    Liebeck155R1T150.Res1T150Acts GagenL3.Res1L3Q P := by
  refine res1T150Acts_of_noTwo h149 ?_
  intro G _ _ A c L X K Y M T P' Yc z τ j hj hj1
  set Yj := Subgroup.centralizer ({j} : Set G) with hYj
  intro Λ hΛ hAΛ c' hc' hLΛ hcc
  have hAY : A ≤ Yj := Liebeck155R1T150.Pump.a_le_centralizer_of_mem_j τ hj
  have hLY : L ≤ Yj := τ.l_le.trans (τ.x_le_centralizer_of_mem_j (h149 G A c L τ.std) hj)
  have hcY : c ∈ Yj := hAY τ.std.mem_A
  obtain rfl : c' = ⟨c, hcY⟩ := Subtype.ext hc'
  obtain ⟨p, e, hp, he, hJ⟩ := τ.q.1
  have hA27 : Nat.card (A.subgroupOf Yj) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv).trans τ.std.card_eq
  have hAL : A.subgroupOf Yj ≤
      Subgroup.normalizer ((L.subgroupOf Yj : Subgroup ↥Yj) : Set ↥Yj) :=
    fun x hx => Subgroup.mem_normalizer_iff.mpr fun y =>
      Subgroup.mem_normalizer_iff.mp (τ.std.mem_lA.2.1 hx) (y : G)
  have hAL9 : Nat.card ↥(A.subgroupOf Yj ⊓ L.subgroupOf Yj) = 9 := by
    have hhyp := τ.at_of.1
    have h1' : A.subgroupOf Yj ⊓ L.subgroupOf Yj = (A ⊓ L).subgroupOf Yj := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h1', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAY)).toEquiv]
    have h2' := hhyp.2
    rw [τ.std.card_eq] at h2'
    omega
  exact noTwo_of_acts_l3 h1 h2 h44 hGA (Liebeck155R1T150.Pump.sectionFourHyp_centralizer τ hj1) hΛ
    (Liebeck155R1T150.Pump.isElemAbelian_subgroupOf τ.std.isElemAbelian) hA27 hAΛ
    (Subgroup.mem_subgroupOf.mpr τ.std.mem_A) hcc
    (Liebeck155R1T150.Pump.subgroupOf_mem_thetaComponentsAt τ.std.mem_thetaComponentsAt hLY hcY)
    (fun x hx => (Subgroup.mem_inf.mp (hLΛ hx)).1) hAL hAL9 he
    (Sec4.RonanK429.isoLThreePi_of_mulEquiv
      (Liebeck155R1T150.Pump.thetaQuotEquivSubgroupOf hLY) hJ)

theorem res1Thm150b_l3 (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover)
    (h44 : Sec4.Item4_4) (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h149 : Sec16.Item149S14)
    {P : ∀ (Y : Type) [Group Y], Prop} : Res1Thm150b GagenL3.Res1L3Q P :=
  Liebeck155R1T150.res1Thm150b_of_acts h45 h48 h149 (res1T150Acts_l3 h1 h2 h44 hGA h149)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150
