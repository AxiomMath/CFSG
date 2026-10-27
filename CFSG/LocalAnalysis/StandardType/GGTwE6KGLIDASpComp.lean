module

public import CFSG.Open.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.RankThree.PartOne.KFOUT3.CycUnits
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.Fischer.Uniq.CompTau
import CFSG.Monster.Existence.Defs
import CFSG.Open.MonsterY443Defs
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial CFSG.Open CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Factors

open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r g : ℕ} {K : Type} [Field K]

private theorem charP_two_kglSpC [Finite K] (hK : Nat.card K = 2 ^ g) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := g) (by rw [Fintype.card_eq_nat_card, hK])

private theorem not_three_dvd_kglSpC {q : ℕ} (hq : q = 2 ^ g) (hg : 3 ∣ 2 ^ g + 1) :
    ¬ 3 ∣ q - 1 := by
  have := Nat.one_le_two_pow (n := g)
  rw [hq]
  omega

private theorem primaryFactor_cases_kglSpC [Finite K] [CharP K 2] (h3 : ¬ 3 ∣ Nat.card K - 1)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) {h : K[X]} (hh : h ∈ primaryFactors (spEnd x)) :
    h = X - 1 ∨ h = X ^ 2 + X + 1 := by
  obtain ⟨hhi, hhm, hhd⟩ := mem_primaryFactors.mp hh
  have hdvd : minpoly K (spEnd x) ∣ (X - 1) * (X ^ 2 + X + 1) := minpoly.dvd K _ (by
    rw [show ((X - 1) * (X ^ 2 + X + 1) : K[X]) = X ^ 3 - 1 by ring, map_sub, map_pow, aeval_X,
      map_one, spEnd_pow hx3, sub_self])
  rcases hhi.prime.dvd_or_dvd (hhd.trans hdvd) with h1 | h1
  · exact Or.inl (eq_of_monic_of_associated hhm CFSG.RankThree.Classical.monic_X_sub_one
      (hhi.associated_of_dvd CFSG.RankThree.Classical.irreducible_X_sub_one h1))
  · exact Or.inr (eq_of_monic_of_associated hhm (by monicity!)
      (hhi.associated_of_dvd (CFSG.RankThree.PartOne.KFOUT3.irreducible_quad h3) h1))

private theorem reciprocal_cyc_kglSpC :
    reciprocalPolynomial (X ^ 2 + X + 1 : K[X]) = X ^ 2 + X + 1 := by
  have hd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hX : reflect 2 (X : K[X]) = X := by
    rw [← pow_one (X : K[X]), reflect_monomial]
    rfl
  have h0 : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by simp
  have hrev : (X ^ 2 + X + 1 : K[X]).reverse = X ^ 2 + X + 1 := by
    rw [Polynomial.reverse, hd]
    simp [reflect_add, reflect_monomial, hX]
    ring
  rw [reciprocalPolynomial, h0, hrev, inv_one, map_one, one_mul]

private theorem orbit_cases_kglSpC [Finite K] [CharP K 2] (h3 : ¬ 3 ∣ Nat.card K - 1)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) {O : Set K[X]} (hO : O ∈ reciprocalOrbits (spEnd x)) :
    O = {X - 1} ∨ O = {X ^ 2 + X + 1} := by
  obtain ⟨h, hh, rfl⟩ := hO
  dsimp only
  rcases primaryFactor_cases_kglSpC h3 hx3 hh with rfl | rfl
  · exact Or.inl (by rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton])
  · exact Or.inr (by rw [reciprocal_cyc_kglSpC, Set.pair_eq_singleton])

end Factors

theorem sp_component_eq_fixed_or_unitary_of_odd {r g : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ g) (hg : 3 ∣ 2 ^ g + 1) (hr : 2 ≤ r) {x : StatedSp r K}
    (hx3 : x ^ 3 = 1) (hx1 : proj r K x ≠ 1) (T : Subgroup (StatedProj (StatedSp r K)))
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (MulAut.conj (proj r K x)))) :
    T = (⁅spSupported x {X - 1}, spSupported x {X - 1}⁆).map (proj r K) ∨
      T = (⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆).map (proj r K) := by
  classical
  haveI := charP_two_kglSpC hK
  have hg1 : 1 ≤ g := Nat.pos_of_ne_zero (by rintro rfl; norm_num at hg)
  have hxne : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have ha : orderOf (proj r K x) = 3 := orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hg1 hK
    Nat.prime_three (by norm_num) (by norm_num) (by omega) _ ha).2 x rfl
    (orderOf_eq_prime hx3 hxne)
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  haveI : Finite ↥(reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  open CFSG.HardMathSupport.Solomon.Coordinator in
  obtain ⟨O, -, rfl⟩ := LieComp.components_conj_of_orbit_family (proj r K)
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective hZc x
    (fun O : ↥(reciprocalOrbits (spEnd x)) => spSupported x (O : Set K[X]))
    (fun i j hij p hp q hq => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) p hp q hq)
    hjoin (fun O => LieSemisimple.quasisimple_or_solvable_spSupported (by norm_num)
      (Nat.le_self_pow (by omega) 2) (altPrimaryData_spLin h3K hx3).squarefree blocks O) T hT
  rcases orbit_cases_kglSpC (not_three_dvd_kglSpC hK hg) hx3 O.2 with hO | hO
  · exact Or.inl (by rw [hO])
  · exact Or.inr (by rw [hO])

end CFSG.StandardType.SCFourCover

end
