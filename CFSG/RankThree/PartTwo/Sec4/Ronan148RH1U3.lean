module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1L3
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoUThree
public import CFSG.RankThree.PartTwo.KFacts.K71SU3
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
public import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.RankThree.PartOne.S10.PlaneLocalRankContract
public import CFSG.RankThree.PartTwo.Sec10.Sec10XStepsS
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Move
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Sp
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA9
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLUsed
public import CFSG.Walter.J1Props
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix

namespace U3

variable {m : ℕ} {K : Type} [Field K]

theorem eq_one_of_commute_mulEquiv (h : UnitaryFieldData 2 m K) (hq : 2 ^ m % 3 = 1)
    {S' : Type} [Group S'] (e : S' ≃* unitarySU 2 m K 3) {y c : S'} (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hyc : y * c = c * y) (hc2 : c ^ 2 = 1) : c = 1 := by
  have h1 := RonanKChevTwo.su_three_eq_one_of_commute h hq (x := e y) (c := e c)
    (by rw [← map_pow, hy3, map_one]) (by rw [Ne, map_eq_one_iff e e.injective]; exact hy1)
    (by rw [← map_mul, ← map_mul, hyc]) (by rw [← map_pow, hc2, map_one])
  exact (map_eq_one_iff e e.injective).mp h1

theorem false_of_quasisimple_le (h : UnitaryFieldData 2 m K) (hq : 2 ^ m % 3 = 1) {S' : Type}
    [Group S'] [Finite S'] (e : S' ≃* unitarySU 2 m K 3) {y : S'} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (Q : Subgroup S') (hQC : Q ≤ Subgroup.centralizer ({y} : Set S')) (hQ : IsQuasisimple Q) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev := CFSG.RankThree.OddKernel.even_card_of_isQuasisimple hQ
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (even_iff_two_dvd.mp hev)
  have hc2 : (c : S') ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one]
  have hcy : y * c = c * y := (Subgroup.mem_centralizer_singleton_iff.mp (hQC c.2)).symm
  have h1 := eq_one_of_commute_mulEquiv h hq e hy3 hy1 hcy hc2
  have : c = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hc
  norm_num at hc

theorem two_lt_of_mod_three (hm : 1 ≤ m) (hq : 2 ^ m % 3 = 1) : 2 < 2 ^ m := by
  have h2 : 2 ≤ 2 ^ m :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2' : 2 ^ m ≠ 2 := fun h => by rw [h] at hq; norm_num at hq
  omega

theorem noCfgS427_su3 (h : UnitaryFieldData 2 m K) (hq : 2 ^ m % 3 = 1) :
    NoCfgS427 (unitarySU 2 m K 3) := by
  have := h.finite
  intro σ h3 h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  by_cases hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut σ
  · obtain ⟨x, rfl, hx3, hx1⟩ := RonanKChevTwo.exists_conj_of_isInnerAut
      (RonanKChevTwo.conj_injective_of_center_eq_bot (RonanKChevTwo.center_su_three_eq_bot h hq))
      hord hin
    rw [autFix_conj]
    intro Q hQC hQ _ _
    exact false_of_quasisimple_le h hq (MulEquiv.refl _) hx3 hx1 Q hQC hQ
  · have hq2 := two_lt_of_mod_three h.one_le hq
    let ψ : unitarySU 2 m K 3 ≃* unitaryPSU h 3 := MulEquiv.ofBijective (unitaryProj h 3)
      ⟨CFSG.RankThree.PartTwo.KFacts.unitaryProj_three_injective h hq, unitaryProj_surjective h 3⟩
    obtain ⟨hZ, hqs⟩ := CFSG.RankThree.PartTwo.KFacts.fixedPoints_facts_of_mulEquiv_unitaryPSU h hq
      hq2 ψ h3 hin
    obtain ⟨τσ, hτσ, τ, hτ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.exists_congr_eq_psuField_of_mulEquiv_unitaryPSU h hq hq2 ψ h3 hin
    obtain ⟨f₀, hf, hf₀, hcard⟩ :=
      CFSG.RankThree.PartTwo.KFacts.exists_card_fixedField_of_orderOf_eq_three h hτσ
    have h₀ : UnitaryFieldData 2 f₀ (fixedField τσ) := ⟨h.prime, hf₀, hcard⟩
    have hinj : Function.Injective ((unitaryProj h 3).comp
        (CFSG.RankThree.PartTwo.KFacts.suIncl h h₀
          (CFSG.RankThree.PartTwo.KFacts.bar_coe_fixedField h hf h₀))) :=
      (CFSG.RankThree.PartTwo.KFacts.unitaryProj_three_injective h hq).comp
        (CFSG.RankThree.PartTwo.KFacts.suIncl_injective h h₀ _)
    obtain ⟨eC⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_eqLocus_mulEquiv τ σ _ hinj fun y => by
      rw [hτ]
      exact CFSG.RankThree.PartTwo.KFacts.mem_range_unitaryProj_comp_suIncl_iff h hq hf h₀ y
    have hfix : Sec4.autFix σ = σ.toMonoidHom.eqLocus (MonoidHom.id _) := by
      ext y
      rfl
    rw [hfix]
    obtain ⟨hs, hna⟩ := CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple hqs hZ
    haveI := hs
    refine good427_of_le_simple le_rfl hna ?_ fun _ hQC _ => hQC
    have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h₀ (n := 3) (by norm_num)
    have hp : ∏ i ∈ Finset.Icc 2 3, (((2 ^ f₀ : ℕ) : ℤ) ^ i - (-1) ^ i) =
        (((2 ^ f₀ : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ f₀ : ℕ) : ℤ) ^ 3 + 1) := by
      rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
      norm_num
    rw [hp] at hc
    intro h60
    have hC : (Nat.card (unitarySU 2 f₀ (fixedField τσ) 3) : ℤ) = 60 := by
      rw [← Nat.card_congr eC.toEquiv, h60]
      norm_num
    rw [show unitarySU 2 f₀ (fixedField τσ) 3 = CFSG.Open.StatedSU 3 (2 ^ f₀) (fixedField τσ) from
      rfl] at hC
    rw [hC] at hc
    have hQ : (2 : ℤ) ≤ ((2 ^ f₀ : ℕ) : ℤ) := by
      have : 2 ≤ 2 ^ f₀ := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
      exact_mod_cast this
    set Q : ℤ := ((2 ^ f₀ : ℕ) : ℤ)
    have e1 : (8 : ℤ) ≤ Q ^ (3 * (3 - 1) / 2) := by
      norm_num
      nlinarith
    have e2 : (3 : ℤ) ≤ Q ^ 2 - 1 := by nlinarith
    have e3 : (9 : ℤ) ≤ Q ^ 3 + 1 := by nlinarith
    have e4 : (27 : ℤ) ≤ (Q ^ 2 - 1) * (Q ^ 3 + 1) := by nlinarith
    have e5 : (216 : ℤ) ≤ Q ^ (3 * (3 - 1) / 2) * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) := by nlinarith
    omega

theorem center_eq_bot_of_su3
    [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ m) ^ 2)
    (hm : 1 ≤ m)
    {L : Type} [Group L] [Finite L] (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* CFSG.Open.StatedSU 3 (2 ^ m) K) : Subgroup.center L = ⊥ := by
  haveI : Group.IsPerfect L := hL.1
  have hodd : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  set π : L →* CFSG.Open.StatedSU 3 (2 ^ m) K :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hker : π.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' _ x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have h := CFSG.SectionRank.EvenCover.even_unitary_three_perfect_odd_extension_trivial hK hm hsurj
    (by rw [hker]) (by rw [hker]; exact hodd)
  rw [← hker, h]

end U3

open U3

section Rows




theorem two_pow_mod_three_of_even
    {m : ℕ} (hm : Even m) : 2 ^ m % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem rowOf427_su3_even
    : ∀ m : ℕ, 1 ≤ m → Even m → RowOf427 (projSU 3 2 m) := by
  intro m hm hev S _ _ _ _ ⟨eSX⟩
  have hq : 2 ^ m % 3 = 1 := two_pow_mod_three_of_even hev
  have hcard : Nat.card (GaloisField 2 (2 * m)) = 2 ^ (2 * m) :=
    GaloisField.card 2 (2 * m) (by omega)
  have h : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) := ⟨Nat.prime_two, hm, hcard⟩
  have hK : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_unitaryPSU_mulEquiv_projSU h
  let ψ : unitarySU 2 m (GaloisField 2 (2 * m)) 3 ≃* unitaryPSU h 3 :=
    MulEquiv.ofBijective (unitaryProj h 3)
      ⟨CFSG.RankThree.PartTwo.KFacts.unitaryProj_three_injective h hq, unitaryProj_surjective h 3⟩
  let eX : projSU 3 2 m ≃* unitarySU 2 m (GaloisField 2 (2 * m)) 3 := φ.symm.trans ψ.symm
  refine row427_of_noCfg_qs ?_ ?_ ?_
  · intro L _ _ _ hL hZ3 ⟨e'⟩
    exact center_eq_bot_of_su3 hK hm hL hZ3 ((e'.trans eSX).trans eX)
  · intro S' _ _ ⟨e'⟩
    exact NoCfgS427.of_mulEquiv ((e'.trans eSX).trans eX) (noCfgS427_su3 h hq)
  · intro S' _ _ ⟨e'⟩ y hy1 hy3 Q hQC hQ _
    exact (false_of_quasisimple_le h hq ((e'.trans eSX).trans eX) hy3 hy1 Q hQC hQ).elim

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
