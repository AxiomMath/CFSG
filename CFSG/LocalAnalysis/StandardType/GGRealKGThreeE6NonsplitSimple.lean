module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitKernel
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitFrame
public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegJ
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitPair

public section

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE6 CFSG.SeitzReduction.F4Pilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Steinberg.Adjoint


theorem rootSpan_signedSimpleRoots_singleton {τ : Tag} {L : Type} [Field L] (i : Fin τ.rank) :
    rootSpan τ L (signedSimpleRoots ({i} : Set (Fin τ.rank))) =
      rootRankOneGroup τ L (Pi.single i 1) := by
  have hset : signedSimpleRoots ({i} : Set (Fin τ.rank)) =
      ({Pi.single i 1, -Pi.single i 1} : Set (Fin τ.rank → ℤ)) := by
    ext α
    simp [signedSimpleRoots]
  rw [hset, rootSpan, iSup_insert, iSup_singleton, rootRankOneGroup,
    CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (isRoot_single τ i)]

theorem exists_singleton_realization {K : Type} [Field K] [Finite K] [CharP K 2]
    (D : E6QPlusThreeFrame K) (F : ExcFrame .E6 K 3 D.frame.range)
    (hw : F.w = e6W0) {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1)
    (hcoord : ∀ s, baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.frame s : ModGL .E6 K) =
      F.D.g0 * e6ThreeDiag ζ hζ s * F.D.g0⁻¹)
    (hq : 4 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K + 1)
    (a : Fin Tag.F4.rank) (i : Fin Tag.E6.rank)
    (hoi : (show Finset (Fin Tag.E6.rank) from TwistTag.E6.orbit a) = {i}) :
    ∃ (r : adjointGroup .E6 K) (J : Subgroup (adjointGroup .E6 K)), r ∈ J ∧
      (∀ s, r * D.frame (Multiplicative.ofAdd s) * r⁻¹ =
        D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (simple .F4 a) s))) ∧
      IsComponentOf J (Subgroup.centralizer (SuSplitRootGen.torusFix D.frame
        (TableBExc.torusAct .F4 3 (simple .F4 a)))) ∧ 3 ∣ Nat.card J := by
  classical
  let γ : Fin Tag.E6.rank → ℤ := Pi.single i 1
  have hγ : IsRoot .E6 γ := isRoot_single .E6 i
  have hii : (show Fin TwistTag.E6.tag.rank from i) ∈ TwistTag.E6.orbit a := by
    have h := congrArg (fun O : Finset (Fin Tag.E6.rank) => i ∈ O) hoi
    exact (Iff.of_eq h).mpr (Finset.mem_singleton_self _)
  have hρi : (show Equiv.Perm (Fin Tag.E6.rank) from TwistTag.E6.perm) i = i := by
    have h := TwistTag.E6.perm_mem_orbit hii
    have hi' : (show Fin Tag.E6.rank from TwistTag.E6.perm i) ∈
        (show Finset (Fin Tag.E6.rank) from TwistTag.E6.orbit a) := h
    rw [hoi, Finset.mem_singleton] at hi'
    exact hi'
  have he6ρi : CFSG.RankThree.E6.e6Rho i = i := by
    have heq : CFSG.RankThree.E6.e6Rho = TwistTag.E6.perm := by
      ext j
      fin_cases j <;> decide
    rw [heq]
    exact hρi
  have hneg : F.w • γ = -γ := by
    rw [hw, e6W0_smul]
    change -(permLattice CFSG.RankThree.E6.e6Rho (Pi.single i 1)) = -Pi.single i 1
    rw [permLattice_single, he6ρi]
  let Y := ggKGExcY F
  have hY : Function.Injective Y := ggKGExcY_injective F
  have hYC : ∀ x, Y x ∈ adjointGroup .E6 (AlgebraicClosure K) := by
    intro x
    rw [ggKGExcY_apply]
    exact mul_mem (mul_mem (inv_mem F.D.g0_mem)
      (baseChangeGL_mem_adjointGroup (algebraMap K (AlgebraicClosure K)) x.2)) F.D.g0_mem
  have hYframe : ∀ s, Y (D.frame s) = e6ThreeDiag ζ hζ s := by
    intro s
    rw [ggKGExcY_apply, hcoord s]
    group
  let H := {s : Fin Tag.F4.rank → ZMod 3 // TableBExc.torusAct .F4 3 (simple .F4 a) s = s}
  let T : H → adjointGroup .E6 K := fun s => D.frame (Multiplicative.ofAdd s.1)
  let b : H → Fin Tag.E6.rank → (AlgebraicClosure K)ˣ :=
    fun s => TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s.1)
  have hYT : ∀ s : H, Y (T s) = rootDiagUnit .E6 (b s) := fun s =>
    hYframe (Multiplicative.ofAdd s.1)
  have hker : familyKernel b = signedSimpleRoots ({i} : Set (Fin Tag.E6.rank)) := by
    change familyKernel (fun s : H =>
      TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s.1)) = _
    have h := familyKernel_twE6ThreeFrame hζo hζ a
    change familyKernel (fun s : H =>
        TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s.1)) =
      signedSimpleRoots ((show Finset (Fin Tag.E6.rank) from TwistTag.E6.orbit a) :
        Set (Fin Tag.E6.rank)) at h
    simpa only [hoi, Finset.coe_singleton] using h
  have hJ : (rootSpan .E6 (AlgebraicClosure K) (familyKernel b)).comap Y =
      ggRealKGNegJ F γ := by
    rw [hker, rootSpan_signedSimpleRoots_singleton, ← ggRealKGNegJ_eq_comap_rootRankOneGroup]
  have hQ : CFSG.IsQuasisimple (ggRealKGNegJ F γ) :=
    ggRealKGNegJ_quasisimple (Or.inr (Or.inr (Or.inr rfl))) F hγ hneg hq
  have hfix : SuSplitRootGen.torusFix D.frame (TableBExc.torusAct .F4 3 (simple .F4 a)) =
      Set.range T := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨Multiplicative.toAdd s, hs⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Multiplicative.ofAdd s.1, s.2, rfl⟩
  have hcomp : IsComponentOf (ggRealKGNegJ F γ)
      (Subgroup.centralizer (SuSplitRootGen.torusFix D.frame
        (TableBExc.torusAct .F4 3 (simple .F4 a)))) := by
    rw [hfix]
    have h := isComponentOf_comap_rootSpan_familyKernel Y hY hYC T b hYT (hJ.symm ▸ hQ)
    rwa [hJ] at h
  obtain ⟨r, hrJ, hrY⟩ := ggRealKGNegJ_weyl (Or.inr (Or.inr (Or.inr rfl))) F hγ hneg hq
  refine ⟨r, ggRealKGNegJ F γ, hrJ, ?_, hcomp,
    ggRealKGNegJ_dvd_card (Or.inr (Or.inr (Or.inr rfl))) F hγ hneg hq h3⟩
  intro s
  apply hY
  rw [map_mul, map_mul, map_inv, hrY, hYframe, hYframe]
  have hworb : TwistTag.E6.orbitReflection a = simple .E6 i := by
    have hlist : ∀ (a : Fin Tag.F4.rank) (i : Fin Tag.E6.rank),
        (show Finset (Fin Tag.E6.rank) from TwistTag.E6.orbit a) = {i} →
          (show List (Fin Tag.E6.rank) from TwistTag.E6.orbitWord a) = [i] := by decide
    change (coxeterSystem Tag.E6).wordProd (TwistTag.E6.orbitWord a) = simple .E6 i
    have hword := hlist a i hoi
    change (TwistTag.E6.orbitWord a : List (Fin TwistTag.E6.tag.rank)) =
      [show Fin TwistTag.E6.tag.rank from i] at hword
    rw [hword]
    change simple .E6 i * 1 = simple .E6 i
    exact mul_one _
  have hwγ : rootReflection γ = TwistTag.E6.orbitReflection a := by
    rw [hworb]
    simpa only [one_mul, inv_one, mul_one] using
      rootReflection_eq_conj (w := (1 : WeylGroup .E6)) (j := i) (one_smul _ _)
  rw [hwγ]
  have h := monomial_conj_e6ThreeDiag hζ
    (canonicalRep_mem_monomialSubgroup (AlgebraicClosure K) (TwistTag.E6.orbitReflection a))
    (mapsRootLines_canonicalRep (TwistTag.E6.orbitReflection a))
    (TwistTag.E6.orbitReflection_mem a) s
  have hfold : (foldedWeylEquiv TwistTag.E6)
      ⟨TwistTag.E6.orbitReflection a, TwistTag.E6.orbitReflection_mem a⟩ =
        simple Tag.F4 a := foldedWeylEquiv_orbitReflection TwistTag.E6 a
  rwa [hfold] at h

theorem rootSpan_signedSimpleRoots_pair {L : Type} [Field L] (i j : Fin Tag.E6.rank) :
    rootSpan .E6 L (signedSimpleRoots ({i, j} : Set (Fin Tag.E6.rank))) =
      rootRankOneGroup .E6 L (Pi.single i 1) ⊔ rootRankOneGroup .E6 L (Pi.single j 1) := by
  have hset : signedSimpleRoots ({i, j} : Set (Fin Tag.E6.rank)) =
      ({Pi.single i 1, -Pi.single i 1, Pi.single j 1, -Pi.single j 1} :
        Set (Fin Tag.E6.rank → ℤ)) := by
    ext α
    simp only [signedSimpleRoots, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left]
    tauto
  rw [hset, rootSpan, iSup_insert, iSup_insert, iSup_insert, iSup_singleton,
    rootRankOneGroup, rootRankOneGroup,
    CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (isRoot_single .E6 i),
    CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (isRoot_single .E6 j), sup_assoc]

theorem exists_pair_realization {K : Type} [Field K] [Finite K] [CharP K 2]
    (D : E6QPlusThreeFrame K) (F : ExcFrame .E6 K 3 D.frame.range)
    (hw : F.w = e6W0) {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1)
    (hcoord : ∀ s, baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.frame s : ModGL .E6 K) =
      F.D.g0 * e6ThreeDiag ζ hζ s * F.D.g0⁻¹)
    (hq : 4 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K + 1)
    (a : Fin Tag.F4.rank) (i j : Fin Tag.E6.rank) (hij : i < j)
    (hoi : (show Finset (Fin Tag.E6.rank) from TwistTag.E6.orbit a) = {i, j}) :
    ∃ (r : adjointGroup .E6 K) (J : Subgroup (adjointGroup .E6 K)), r ∈ J ∧
      (∀ s, r * D.frame (Multiplicative.ofAdd s) * r⁻¹ =
        D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (simple .F4 a) s))) ∧
      IsComponentOf J (Subgroup.centralizer (SuSplitRootGen.torusFix D.frame
        (TableBExc.torusAct .F4 3 (simple .F4 a)))) ∧ 3 ∣ Nat.card J := by
  classical
  have hpair : ∀ (a : Fin Tag.F4.rank) (i j : Fin Tag.E6.rank), i < j →
      (show Finset (Fin Tag.E6.rank) from TwistTag.E6.orbit a) = {i, j} →
      CFSG.RankThree.E6.e6Rho i = j ∧ CFSG.RankThree.E6.e6Rho j = i ∧
      iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) = 0 ∧
      (show List (Fin Tag.E6.rank) from TwistTag.E6.orbitWord a) = [i, j] := by
    decide +kernel
  obtain ⟨hρi, hρj, horth, hword⟩ := hpair a i j hij hoi
  let β : Fin Tag.E6.rank → ℤ := Pi.single i 1
  let γ : Fin Tag.E6.rank → ℤ := Pi.single j 1
  have hβ : IsRoot .E6 β := isRoot_single .E6 i
  have hγ : IsRoot .E6 γ := isRoot_single .E6 j
  have hβγ : F.w • β = -γ := by
    rw [hw, e6W0_smul]
    change -permLattice CFSG.RankThree.E6.e6Rho (Pi.single i 1) = -Pi.single j 1
    rw [permLattice_single, hρi]
  have hγβ : F.w • γ = -β := by
    rw [hw, e6W0_smul]
    change -permLattice CFSG.RankThree.E6.e6Rho (Pi.single j 1) = -Pi.single i 1
    rw [permLattice_single, hρj]
  obtain ⟨J, hJdef, hJmap, hQ, hJdvd, r, hrJ, hrY⟩ :=
    e6NonsplitPair_rationalRoot F hβ hγ horth hβγ hγβ hq
  let Y := ggKGExcY F
  have hY : Function.Injective Y := ggKGExcY_injective F
  have hYC : ∀ x, Y x ∈ adjointGroup .E6 (AlgebraicClosure K) := by
    intro x
    rw [ggKGExcY_apply]
    exact mul_mem (mul_mem (inv_mem F.D.g0_mem)
      (baseChangeGL_mem_adjointGroup (algebraMap K (AlgebraicClosure K)) x.2)) F.D.g0_mem
  have hYframe : ∀ s, Y (D.frame s) = e6ThreeDiag ζ hζ s := by
    intro s
    rw [ggKGExcY_apply, hcoord s]
    group
  let H := {s : Fin Tag.F4.rank → ZMod 3 // TableBExc.torusAct .F4 3 (simple .F4 a) s = s}
  let T : H → adjointGroup .E6 K := fun s => D.frame (Multiplicative.ofAdd s.1)
  let b : H → Fin Tag.E6.rank → (AlgebraicClosure K)ˣ :=
    fun s => TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s.1)
  have hYT : ∀ s : H, Y (T s) = rootDiagUnit .E6 (b s) := fun s =>
    hYframe (Multiplicative.ofAdd s.1)
  have hker : familyKernel b = signedSimpleRoots ({i, j} : Set (Fin Tag.E6.rank)) := by
    have h := familyKernel_twE6ThreeFrame hζo hζ a
    change familyKernel (fun s : H =>
        TableBExc.E6Three.zetaVec ζ hζ (twE6ThreeFrame s.1)) =
      signedSimpleRoots ((show Finset (Fin Tag.E6.rank) from TwistTag.E6.orbit a) :
        Set (Fin Tag.E6.rank)) at h
    simpa only [hoi, Finset.coe_insert, Finset.coe_singleton] using h
  have hJ : (rootSpan .E6 (AlgebraicClosure K) (familyKernel b)).comap Y = J := by
    rw [hker, rootSpan_signedSimpleRoots_pair, hJdef]
    ext x
    obtain ⟨Fr, hFr, hΦ⟩ := F.frob
    change (Y x ∈ rootRankOneGroup .E6 (AlgebraicClosure K) β ⊔
      rootRankOneGroup .E6 (AlgebraicClosure K) γ) ↔
      (Y x ∈ rootRankOneGroup .E6 (AlgebraicClosure K) β ⊔
        rootRankOneGroup .E6 (AlgebraicClosure K) γ ∧ F.D.step (Y x) = Y x)
    exact (and_iff_left (ggRealKGNeg_step_Y F hFr hΦ x)).symm
  have hfix : SuSplitRootGen.torusFix D.frame (TableBExc.torusAct .F4 3 (simple .F4 a)) =
      Set.range T := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨Multiplicative.toAdd s, hs⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Multiplicative.ofAdd s.1, s.2, rfl⟩
  have hcomp : IsComponentOf J (Subgroup.centralizer (SuSplitRootGen.torusFix D.frame
      (TableBExc.torusAct .F4 3 (simple .F4 a)))) := by
    rw [hfix]
    have h := isComponentOf_comap_rootSpan_familyKernel Y hY hYC T b hYT (hJ.symm ▸ hQ)
    rwa [hJ] at h
  refine ⟨r, J, hrJ, ?_, hcomp, hJdvd h3⟩
  intro s
  apply hY
  rw [map_mul, map_mul, map_inv, hrY, hYframe, hYframe]
  have hworb : rootReflection β * rootReflection γ = TwistTag.E6.orbitReflection a := by
    change rootReflection (Pi.single i 1) * rootReflection (Pi.single j 1) = _
    rw [← simple_eq_rootReflection i, ← simple_eq_rootReflection j]
    change simple .E6 i * simple .E6 j =
      (coxeterSystem .E6).wordProd (TwistTag.E6.orbitWord a)
    change (TwistTag.E6.orbitWord a : List (Fin TwistTag.E6.tag.rank)) =
      [show Fin TwistTag.E6.tag.rank from i, show Fin TwistTag.E6.tag.rank from j] at hword
    rw [hword]
    change simple .E6 i * simple .E6 j = simple .E6 i * (simple .E6 j * 1)
    rw [mul_one]
  rw [hworb]
  have h := monomial_conj_e6ThreeDiag hζ
    (canonicalRep_mem_monomialSubgroup (AlgebraicClosure K) (TwistTag.E6.orbitReflection a))
    (mapsRootLines_canonicalRep (TwistTag.E6.orbitReflection a))
    (TwistTag.E6.orbitReflection_mem a) s
  have hfold : (foldedWeylEquiv TwistTag.E6)
      ⟨TwistTag.E6.orbitReflection a, TwistTag.E6.orbitReflection_mem a⟩ =
        simple Tag.F4 a := foldedWeylEquiv_orbitReflection TwistTag.E6 a
  rwa [hfold] at h

theorem exists_simple_realization {K : Type} [Field K] [Finite K] [CharP K 2]
    (D : E6QPlusThreeFrame K) (F : ExcFrame .E6 K 3 D.frame.range)
    (hw : F.w = e6W0) {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1)
    (hcoord : ∀ s, baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.frame s : ModGL .E6 K) =
      F.D.g0 * e6ThreeDiag ζ hζ s * F.D.g0⁻¹)
    (hq : 4 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K + 1) (a : Fin Tag.F4.rank) :
    ∃ (r : adjointGroup .E6 K) (J : Subgroup (adjointGroup .E6 K)), r ∈ J ∧
      (∀ s, r * D.frame (Multiplicative.ofAdd s) * r⁻¹ =
        D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (simple .F4 a) s))) ∧
      IsComponentOf J (Subgroup.centralizer (SuSplitRootGen.torusFix D.frame
        (TableBExc.torusAct .F4 3 (simple .F4 a)))) ∧ 3 ∣ Nat.card J := by
  fin_cases a
  · exact exists_pair_realization D F hw hζo hζ hcoord hq h3 0 0 5 (by decide) (by decide)
  · exact exists_pair_realization D F hw hζo hζ hcoord hq h3 1 2 4 (by decide) (by decide)
  · exact exists_singleton_realization D F hw hζo hζ hcoord hq h3 2 3 (by decide)
  · exact exists_singleton_realization D F hw hζo hζ hcoord hq h3 3 1 (by decide)

end CFSG.StandardType.ExcFrames.E6QPlusThree

end
