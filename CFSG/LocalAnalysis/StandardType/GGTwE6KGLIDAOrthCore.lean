module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDADefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAOrthFixed
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAUnitaryBridge
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie
import CFSG.RankThree.PartOne.S15K.OrthModel
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie

private theorem primaryFactor_selfDual {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) (h3 : ¬ 3 ∣ Nat.card K - 1) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) :
    reciprocalPolynomial h = h := by
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hdvd : h ∣ X ^ 3 - C 1 := by
    simpa using hx.dvd_X_pow_sub_one hh
  have hirr₀ : Irreducible (X ^ 2 + X + 1 : K[X]) :=
    CFSG.RankThree.PartOne.KFOUT3.irreducible_quad (K := K) h3
  have hdvd₂ : h ∣ X ^ 2 + X + 1 :=
    CFSG.AGLEmbedding.ToralCensus.dvd_X_sq_add_X_add_one hirr hmon hdvd hne
  have hh2 : h = X ^ 2 + X + 1 :=
    CFSG.AGLEmbedding.ToralCensus.eq_of_dvd_of_natDegree_eq_two hirr₀
      CFSG.AGLEmbedding.ToralCensus.monic_X_sq_add_X_add_one (dvd_refl _)
      CFSG.AGLEmbedding.ToralCensus.natDegree_X_sq_add_X_add_one hirr hmon hdvd₂
  rw [hh2, CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one]

theorem ggInnerOrUnitaryOnComps_projOrthDerived {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {g : ℕ} (hK : Nat.card K = 2 ^ g) (hg : 3 ∣ 2 ^ g + 1) :
    GGInnerOrUnitaryOnComps (CFSG.RankThree.Classical2.ProjOrthDerived Q) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := g)
    (by rw [Fintype.card_eq_nat_card, hK])
  have h3ℓ : 3 ≠ ringChar K := by rw [ringChar.eq (R := K) 2]; norm_num
  haveI : Nontrivial V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have h3K : ¬ 3 ∣ Nat.card K - 1 := by
    have : 0 < 2 ^ g := Nat.two_pow_pos g
    rw [hK]
    omega
  intro a c ha3 ha1 hc3 hac J hJ hstab
  obtain ⟨x, y, rfl, rfl, hx, hfix, hy⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_lift_of_commute hQ hT Nat.prime_three
      (by norm_num) h3ℓ ha3 ha1 hac
  rw [hfix] at hJ
  have hy3 : y ^ 3 = 1 := by
    apply CFSG.RankThree.PartOne.S15K.mk_injective_orth (Q := Q) hQ
    rw [map_pow, hc3, map_one]
  rcases exists_component_dichotomy Nat.prime_three (by norm_num) hQ hT h3ℓ hx J hJ with
    ⟨h, hh, hne, hq, hJeq⟩ | ⟨hlist, F, hFq, hFle, hFn, hJeq⟩
  · haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hself := primaryFactor_selfDual hx h3K hh hne
    have hq' : CFSG.Open.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) :=
      ⟨hq.1.commutator_eq_top, hq.2.1⟩
    obtain ⟨ℓ, f, hU, B, hBs, hBl, -, g', π', hsurj, hker, hconj⟩ :=
      exists_sesqSUConjData hx (by decide) hh hne hself.symm hq' y hy J hJeq hstab
    haveI : CharP (AdjoinRoot h) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
    obtain rfl : ℓ = 2 := CharP.eq (AdjoinRoot h) hU.charP inferInstance
    exact Or.inr (ggUnitaryOn_of_sesqSUConj hJ.2.2 hBs hBl π' hsurj hker g' fun s =>
      (CFSG.GroupActions.subgroupStabRestrict_apply (H := J)
        (⟨MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y), hstab⟩ :
          CFSG.GroupActions.subgroupStabAut J) (π' s)).symm.trans
        (congrArg Subtype.val (hconj s)))
  · exact Or.inl (hJeq ▸ ggInnerOn_orth_fixedFactor hK hx hlist hFq hFle hFn hy hy3)

end CFSG.StandardType.SCFourCover

end
