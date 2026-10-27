module

public import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagLinear
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagOrthPaired
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAOrthFixed
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAUnitaryBridge
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonal
import CFSG.RankThree.PartOne.S15K.OrthModel
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.SCFourCover

section Orthogonal

open Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem ggInnerDiagOnComps_projOrthDerived {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {g : ℕ} (hK : Nat.card K = 2 ^ g) :
    GGInnerDiagOnComps (CFSG.RankThree.Classical2.ProjOrthDerived Q) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := g)
    (by rw [Fintype.card_eq_nat_card, hK])
  have h3ℓ : 3 ≠ ringChar K := by rw [ringChar.eq (R := K) 2]; norm_num
  haveI : Nontrivial V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
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
    have hq' : CFSG.Open.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) :=
      ⟨hq.1.commutator_eq_top, hq.2.1⟩
    by_cases hself : h = reciprocalPolynomial h
    ·
      obtain ⟨ℓ, f, hU, B, hBs, hBl, -, g', π', hsurj, hker, hconj⟩ :=
        exists_sesqSUConjData hx (by decide) hh hne hself hq' y hy J hJeq hstab
      haveI : CharP (AdjoinRoot h) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
      obtain rfl : ℓ = 2 := CharP.eq (AdjoinRoot h) hU.charP inferInstance
      exact Or.inr (Or.inl (ggUnitaryOn_of_sesqSUConj hJ.2.2 hBs hBl π' hsurj hker g' fun s =>
        (CFSG.GroupActions.subgroupStabRestrict_apply (H := J)
          (⟨MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y), hstab⟩ :
            CFSG.GroupActions.subgroupStabAut J) (π' s)).symm.trans
          (congrArg Subtype.val (hconj s))))
    ·
      exact Or.inr (Or.inr
        (ggLinearOn_orth_paired hx hh hne hself hq' y hy J hJ.2.2 hJeq hstab))
  · exact Or.inl (hJeq ▸ ggInnerOn_orth_fixedFactor hK hx hlist hFq hFle hFn hy hy3)

end Orthogonal

open CFSG CFSG.Assembly CFSG.Blueprint TableB in
theorem ggInnerDiagOnComps_omegaMinus {K : Type} [Field K] [Finite K] {g m : ℕ}
    (hK : Nat.card K = 2 ^ g) (hm : 3 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGInnerDiagOnComps (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) := by
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := m + 1)
    (by omega) hbc
  have e : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) K b c)) :=
    (CFSG.Open.StatedAPI.mapMkEquivStatedProj (LargeEvenOmega (LargeEvenQMinus m b c))).symm.trans
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.omegaModelEquivOfReindex
        (Equiv.sumAssoc (Fin m) (Fin m) (Fin 2)) (Q := LargeEvenQMinus m b c)
        (Q' := CFSG.Open.StatedQuadMinus (m + 1) K b c) fun _ => rfl)
  exact ggInnerDiagOnComps_of_mulEquiv
    (e.trans (CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.projOrthEquiv
      (CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) K b c))).symm
    (ggInnerDiagOnComps_projOrthDerived hQ hT hK)

end CFSG.StandardType.SCFourCover

end
