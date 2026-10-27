module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix
public import CFSG.RankThree.PartOne.KE6.EqpTorus
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE.CTTorus
public import CFSG.RankThree.PartOne.KE6.EqpArith
public import CFSG.RankThree.PartOne.KE6.Phi3Arith
public import CFSG.RankThree.PartOne.KE6.Phi3Lattice
public import CFSG.RankThree.PartOne.KE6.Phi3Torus
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

private theorem entrywise_eq_self_of_entrywise_frobenius {τ : Tag} {K : Type} [Field K] [CharP K 2]
    {A : Module.End K (RootModule τ K)} (hA : entrywise (frobenius K 2) A = A) (σ : K →+* K) :
    entrywise σ A = A := by
  have hcoord : ∀ (b c : Label τ), σ (A (Finsupp.single b 1) c) = A (Finsupp.single b 1) c := by
    intro b c
    have hbc : frobenius K 2 (A (Finsupp.single b 1) c) = A (Finsupp.single b 1) c := by
      have h2 := congrArg (fun v : RootModule τ K => v c)
        (LinearMap.congr_fun hA (Finsupp.single b 1))
      simpa only [entrywise_single, Finsupp.mapRange_apply] using h2
    have he : A (Finsupp.single b 1) c * (A (Finsupp.single b 1) c - 1) = 0 := by
      have h2 : (A (Finsupp.single b 1) c) ^ 2 - A (Finsupp.single b 1) c = 0 := by
        rw [← frobenius_def]
        exact sub_eq_zero.mpr hbc
      calc A (Finsupp.single b 1) c * (A (Finsupp.single b 1) c - 1)
          = (A (Finsupp.single b 1) c) ^ 2 - A (Finsupp.single b 1) c := by
            rw [pow_two, mul_sub, mul_one]
        _ = 0 := h2
    rcases mul_eq_zero.mp he with h | h
    · rw [h, map_zero]
    · rw [sub_eq_zero.mp h, map_one]
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single]
  ext c
  simp only [Finsupp.mapRange_apply]
  exact hcoord b c

theorem units_map_entrywiseHom_eq_self_of_frobenius {τ : Tag} {K : Type} [Field K] [CharP K 2]
    {g : ModGL τ K} (hg : Units.map (entrywiseHom (frobenius K 2)) g = g) (σ : K →+* K) :
    Units.map (entrywiseHom σ) g = g := by
  have hA : entrywise (frobenius K 2) (g : Module.End K (RootModule τ K)) =
      (g : Module.End K (RootModule τ K)) := by
    have h := congrArg Units.val hg
    simpa [Units.coe_map, entrywiseHom] using h
  apply Units.ext
  simpa [Units.coe_map, entrywiseHom] using entrywise_eq_self_of_entrywise_frobenius hA σ

section Certs

theorem entrywise_eq_self_of_baseChangeGL_eq
    {K : Type} [Field K] [CharP K 2] {L : Type}
    [Field L] [Algebra K L] [CharP L 2] {g0 y : ModGL .E6 L}
    (hg0 : Units.map (entrywiseHom (frobenius L 2)) g0 = g0 * eqpN L)
    (hy : negPhi (frobenius L 2) (eqpN L) y = y) {x : ModGL .E6 K}
    (hx : baseChangeGL (algebraMap K L) x = g0 * y * g0⁻¹) (σ : K →+* K) :
    Units.map (entrywiseHom σ) x = x := by
  have hbc : ∀ b : K, frobenius L 2 (algebraMap K L b) = algebraMap K L (frobenius K 2 b) := by
    intro b
    rw [frobenius_def, frobenius_def, map_pow]
  have h1 : Units.map (entrywiseHom (frobenius L 2)) (baseChangeGL (algebraMap K L) x) =
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom (frobenius K 2)) x) :=
    CFSG.RankThree.Chevalley.entrywise_baseChangeGL_eq (algebraMap K L) (frobenius L 2)
      (frobenius K 2) hbc x
  have h2 : Units.map (entrywiseHom (frobenius L 2)) (baseChangeGL (algebraMap K L) x) =
      baseChangeGL (algebraMap K L) x := by
    rw [hx]
    simp only [map_mul, map_inv, hg0]
    have hnf : eqpN L * Units.map (entrywiseHom (frobenius L 2)) y * (eqpN L)⁻¹ = y := by
      rw [← negPhi_apply]
      exact hy
    rw [mul_inv_rev]
    rw [show (g0 * eqpN L) * Units.map (entrywiseHom (frobenius L 2)) y * ((eqpN L)⁻¹ * g0⁻¹)
        = g0 * (eqpN L * Units.map (entrywiseHom (frobenius L 2)) y * (eqpN L)⁻¹) * g0⁻¹ by
          group]
    rw [hnf]
  refine units_map_entrywiseHom_eq_self_of_frobenius (τ := .E6) (K := K) ?_ σ
  exact baseChangeGL_injective (τ := .E6) (algebraMap K L) (h1.symm.trans h2)

end Certs

end CFSG.StandardType.ExcFrames.E6QPlusThree
