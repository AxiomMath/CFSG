module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3L3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Psu3Ord
public import CFSG.Quasithin.EmptyFaithful.T1515eC
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.RankThree.SubgroupLists.FieldThreeFamilies
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import Certificates.Certificate8026Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory

theorem su3PSU3Case_holds : SU3PSU3Case := by
  intro p hpf hp7 K _ _ hK M H hctx r f hr hr2 hf K' _ _ hK' e
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have hdet := hctx.det
  have hZ := hctx.center
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have hK3 : (3 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_three (by omega)
  have hK5 : (5 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_five (by omega)
  have hrf : Fact r.Prime := ⟨hr⟩
  have hcharK' : CharP K' r :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr (by rw [hK', ← pow_mul])
  by_cases hq4 : 4 ≤ r ^ f
  swap
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_lt_four' hr hr2 hf (by omega)
    exact (false_of_psu33 hK3 hdet hZ3 hK' e).elim
  have hqodd : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
  have hF2 : (2 : K') ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K') = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K' r] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this)
  obtain ⟨eL⟩ := nonempty_mulEquiv_leviPSU3 (K := K') (r ^ f) (by omega)
  set L := (leviPSU3 (K := K') (r ^ f)).map e.symm.toMonoidHom with hLdef
  have : Group.IsPerfect (StatedSU 2 (r ^ f) K') := isPerfect_statedSU_two hK' hq4
  have : Group.IsPerfect (leviPSU3 (K := K') (r ^ f)) :=
    Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  have hLp : Group.IsPerfect L := Group.IsPerfect.map _
  have hLcard : Nat.card L = r ^ f * ((r ^ f) ^ 2 - 1) := by
    rw [← card_statedSU_two hK', Nat.card_congr eL.toEquiv]
    exact (Nat.card_congr ((leviPSU3 (K := K') (r ^ f)).equivMapOfInjective _
      e.symm.injective).toEquiv).symm
  have hL : L ≠ ⊥ := by
    intro h
    have h1 : Nat.card L = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hLcard] at h1
    have : 4 * (4 ^ 2 - 1) ≤ r ^ f * ((r ^ f) ^ 2 - 1) := Nat.mul_le_mul hq4
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq4 2) 1)
    omega
  set t := e.symm (negDiagPSU3 (K := K') hqodd) with ht
  have ht2 : t ^ 2 = 1 := by rw [ht, ← map_pow, negDiagPSU3_sq, map_one]
  have ht1 : t ≠ 1 := fun h =>
    negDiagPSU3_ne_one hF2 hqodd (e.symm.injective (by rw [← ht, h, map_one]))
  have hLt : ∀ x ∈ L, x * t = t * x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ht, ← map_mul, leviPSU3_commute hqodd y hy]
  have hcard := card_perfect_of_le_centralizer_K hp2 hK hdet hZ ht2 ht1 L hL hLt
  rw [hLcard] at hcard
  have hq : r ^ f = 5 ∨ r ^ f = p ∨ r ^ f = p ^ 2 :=
    eq_of_card_perfect_cases hq4 hp.one_lt.le hcard
  have hmul := CFSG.Quasithin.card_statedProj_statedSU_three_mul_gcd hr hf hK'
  have hS : Nat.card (H ⧸ Subgroup.center H) =
      Nat.card (StatedProj (StatedSU 3 (r ^ f) K')) := Nat.card_congr e.toEquiv
  have hHdvd := card_dvd_of_qctx hK hctx
  rw [card_eq_quotient_mul H] at hHdvd
  generalize Nat.card (StatedProj (StatedSU 3 (r ^ f) K')) = n at hmul hS
  rcases hq with h5 | hqp | hqp2
  · obtain ⟨rfl, rfl⟩ := (Nat.prime_five.pow_eq_iff).mp h5
    obtain ⟨s, g, hs5, hs1, hg⟩ := exists_rational_five_psu3 (K := K')
    exact (hK5 (five_eq_zero_of_rational_five hdet hZ3 (s := e.symm s) (g := e.symm g)
      (by rw [← map_pow, hs5, map_one]) (fun h => hs1 (e.symm.injective (by rw [h, map_one])))
      (by rw [← map_inv, ← map_mul, ← map_mul, hg, map_pow]))).elim
  · rw [hqp] at hmul
    have hS' : Nat.card (H ⧸ Subgroup.center H) * Nat.gcd 3 (p + 1) =
        Nat.card ↥(StatedSU 3 (p ^ 1) K) := by
      rw [hS, hmul, card_su3_eq hK]
    have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
    have := charP_of_card_sq (p := p) hK
    have hperf : Group.IsPerfect ↥(StatedSU 3 (p ^ 1) K) :=
      CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd hK1 (n := 3) (by norm_num)
        (by intro h; simp at h; omega)
    exact eq_top_of_card_psu3 hperf hctx (Nat.gcd_dvd_left 3 _) hS'
  · rw [hqp2] at hmul
    have h6 : p ^ 6 ∣ Nat.card (H ⧸ Subgroup.center H) * Nat.gcd 3 (p ^ 2 + 1) := by
      rw [hS, hmul]
      exact ⟨((p ^ 2) ^ 2 - 1) * ((p ^ 2) ^ 3 + 1), by ring⟩
    exact (false_of_p_six_dvd (by omega) (Nat.gcd_dvd_left 3 _) h6 hHdvd).elim

end CFSG.Quasithin.A312U3
