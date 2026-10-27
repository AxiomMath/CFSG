module

public import Mathlib
public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldGlue
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSU3
import CFSG.RankThree.Automorphisms.UnitaryCoprime
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.NearPSolvable
public import Certificates.Certificate43
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SuzukiBruhatNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.Classical.SteinbergBTHigherUnitaryPrimeSubfield
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfield
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical (fieldFixedPSU)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem unitary_prime_numerics {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hodd : Odd p)
    (hpT : ¬ p ∣ Nat.card (unitaryPSU h n)) : p ≠ ℓ ∧ 3 < p ∧ n < p ∧ ¬ p ∣ ℓ ^ f + 1 := by
  have := h.finite
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (unitaryPSU h n)
      CFSG.Assembly.LowTwoRank.StatedLieTag.PSU n ℓ f := by
    refine ⟨⟨h.prime, h.one_le, hn, fun heq => hq ⟨congrArg Prod.fst heq,
      congrArg Prod.snd heq⟩⟩, K, inferInstance, inferInstance, ?_,
      ⟨unitaryPSUEquiv h (by omega)⟩⟩
    rw [h.card, ← pow_mul, mul_comm]
  have hform := (unitary_model_outer_two_part_bound _ n ℓ f hmodel).1
  have hdvd : ℓ ^ f + 1 ∣ Nat.card (unitaryPSU h n) :=
    CFSG.RankThree.Automorphisms.add_one_dvd_card_unitaryPSU h hn
  have key : ¬ (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 n, (((ℓ ^ f : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    intro hpdvd
    rw [← hform] at hpdvd
    have hpd : p ∣ Nat.card (unitaryPSU h n) * Nat.gcd n (ℓ ^ f + 1) := by
      exact_mod_cast hpdvd
    rcases hp.dvd_mul.mp hpd with h1 | h1
    · exact hpT h1
    · exact hpT (h1.trans ((Nat.gcd_dvd_right _ _).trans hdvd))
  have hpq : ¬ p ∣ ℓ ^ f := fun hpq => by
    refine key (Dvd.dvd.mul_right (dvd_pow (Int.natCast_dvd_natCast.mpr hpq) ?_) _)
    have : 6 ≤ n * (n - 1) := le_trans (by norm_num : 6 ≤ 3 * 2) (Nat.mul_le_mul hn (by omega))
    omega
  have hnp : n < p := by
    by_contra hlt
    push Not at hlt
    refine key (Dvd.dvd.mul_left ?_ _)
    have hcop : IsCoprime ((ℓ ^ f : ℕ) : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).symm)
    have hferm := (Int.ModEq.pow_card_sub_one_eq_one hp hcop).symm.dvd
    obtain ⟨k, hk⟩ := hodd
    have hp2 := hp.two_le
    have hev : Even (p - 1) := ⟨k, by omega⟩
    have hmem : p - 1 ∈ Finset.Icc 2 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem (fun j => ((ℓ ^ f : ℕ) : ℤ) ^ j - (-1) ^ j)
      hmem)
    simp only [hev.neg_one_pow]
    exact hferm
  refine ⟨?_, by omega, hnp, fun hd => hpT (hd.trans hdvd)⟩
  rintro rfl
  exact hpq (dvd_pow_self p (by have := h.one_le; omega))

theorem fieldClauses_primeFormP
    {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hodd : Odd p)
    (hexc : ¬(n = 3 ∧ ℓ = 2 ∧ f = p))
    (hpT : ¬ p ∣ Nat.card (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hNL : SubfieldNonLocalizedPSU) :
    FieldClauses p (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  rintro ⟨a, ha⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨eP⟩, -, -, -, -, -, -, hFker, -, hinn, hDI⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set T' := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT'
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner T' with hI
  have hpT' : ¬ p ∣ Nat.card (unitaryPSU h n) := by
    rwa [← Nat.card_congr eP.toEquiv]
  obtain ⟨-, -, hnp, hqp⟩ := unitary_prime_numerics h hn hq hp hodd hpT'
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have hDcop : Nat.Coprime (Nat.card D) p := by
    rw [← Subgroup.relIndex_mul_card I D, inf_of_le_left hID]
    exact Nat.Coprime.mul_left
      (Nat.Coprime.coprime_dvd_left hDI ((Nat.Prime.coprime_iff_not_dvd hp).2 hqp).symm)
      (CFSG.RankThree.Automorphisms.coprime_card_inner hp hpT)
  have haD : a ∉ D := fun haD => by
    have hdvd := orderOf_dvd_natCard (⟨a, haD⟩ : D)
    rw [Subgroup.orderOf_mk, ha] at hdvd
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDcop.symm hdvd)
  set F := primeFormFieldFactor h hC hn hq with hF
  have hFa : F a ≠ 1 := fun h1 => haD (by rw [← hFker]; exact h1)
  have hFap : F a ^ p = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hσ : orderOf (F a) = p := orderOf_eq_prime hFap hFa
  obtain ⟨hpf, -, -, -, -, -, -, -, -, hsimp, -⟩ :=
    CFSG.RankThree.Classical.higher_unitary_prime_subfield_fixed_group_and_full_centralizer
      h hn hnp hp hq (F a) hσ
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
    rintro ⟨hn3, h2⟩
    obtain ⟨hℓ2, hfp⟩ := Nat.prime_two.pow_eq_iff.mp h2
    exact hexc ⟨hn3, hℓ2, by rw [← Nat.div_mul_cancel hpf, hfp, one_mul]⟩
  obtain ⟨hsC, hnc, hfix, hzp, hcard⟩ := hsimp hq₀
  have hord : orderOf (primeFormFieldHom h hC (F a)) = p := by
    rw [← Nat.card_zpowers]
    exact hcard
  have hCeq : signalizerFixedSubgroup (primeFormFieldHom h hC (F a)) = fieldFixedPSU h n (F a) :=
    Subgroup.ext fun x => Iff.rfl
  have hsC' : IsSimpleGroup (signalizerFixedSubgroup (primeFormFieldHom h hC (F a))) := by
    rw [hCeq]
    exact hsC
  have hnC : ∃ x y : signalizerFixedSubgroup (primeFormFieldHom h hC (F a)), x * y ≠ y * x := by
    rw [hCeq]
    push Not at hnc
    exact hnc
  have hFS := fStarSimple_of_simple hsC' hnC
  refine ⟨primeFormFieldHom h hC (F a), hord, fixedClauses_of_stabilizer hord hFS
    (hNL h n hn p hp hodd hexc hpT (F a) hσ) ?_⟩
  intro g hg
  have hmem : g ∈ fixingSubgroup (MulAut T') (fieldFixedPSU h n (F a) : Set T') := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    exact hg y hy
  rw [hfix, hzp] at hmem
  exact hmem

theorem nearPSolvable_statedPSU_three_two
    {T : Type} [Group T] {p : ℕ}
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 p) (hp : p.Prime)
    (hpT : ¬ p ∣ Nat.card T) : signalizerNearPSolvable p T := by
  obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hm
  have hcard : Nat.card K = 2 ^ (2 * p) := by rw [hK, ← pow_mul, mul_comm]
  let e : T ≃* GLAProj (GLASUGroup (Fin 3) K (2 ^ p)) := eT
  let e' : T ≃* PSU3 2 p :=
    e.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative p hp.two_le hcard)
  have hcop : Nat.Coprime p (Nat.card (PSU3 2 p)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpT
  exact CFSG.SignalizerFunctorTheorem.TransportA.nearPSolvable_of_mulEquiv e'.symm
    (nearPSolvable_psu3 hp hcop)

theorem nearOrField_statedPSU
    {T : Type} [Group T] [Finite T] {n ℓ f p : ℕ}
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU n ℓ f) (hp : p.Prime)
    (hodd : Odd p) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedPSU) :
    CFSG.Open.signalizerNearPSolvable p T ∨ FieldClauses p T := by
  by_cases hexc : n = 3 ∧ ℓ = 2 ∧ f = p
  · obtain ⟨rfl, rfl, rfl⟩ := hexc
    exact Or.inl (nearPSolvable_statedPSU_three_two hm hp hpT)
  · refine Or.inr ?_
    obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq' : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n))
    let e' : T ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
    have hpT' : ¬ p ∣ Nat.card
        (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      rwa [← Nat.card_congr e'.toEquiv]
    exact FieldClauses.of_mulEquiv e'.symm
      (fieldClauses_primeFormP h hn hq' hp hodd hexc hpT' hNL)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
