module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.Quasithin.Background.HMultNorm
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Quasithin.Background.HSp4Model
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mult
open scoped Matrix Kronecker

private theorem sp4TwoNat_involution_aux (K : Type) [Field K] [Finite K]
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {f : ℕ} (hf : Odd f)
    {π : ↥(StatedSp 2 K) →* ↥H} (hKcard : Nat.card K = 2 ^ f)
    (hsum : SumOfNatVia (FFModel.nat (StatedSp 2 K)) H ⊤ ⊥ 2 π)
    {t : MulAut W} (ht : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hord : orderOf t = 2) : 2 * f ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  classical
  obtain ⟨I, e, hreal, he, hcoord⟩ :=
    exists_coords_of_sumOfNatVia (StatedSp 2 K) hsum
  have hπ : Function.Surjective π := (hreal 0).1
  have hHmap : H.map (congrHom e) = natImage (diagSub 2 (StatedSp 2 K)) :=
    map_congrHom_eq_natImage_diag (StatedSp 2 K) hπ e he
  let T : MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K) := congrHom e t
  have hTnorm : T ∈ Subgroup.normalizer
      (natImage (diagSub 2 (StatedSp 2 K)) :
        Set (MulAut (StdMod (Fin 2 × (Fin 2 ⊕ Fin 2)) K))) := by
    have hmapN := Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    have hmem : congrHom e t ∈
        (Subgroup.normalizer (H : Set (MulAut W))).map (congrHom e) :=
      Subgroup.mem_map_of_mem (congrHom e) ht
    rw [hmapN, hHmap] at hmem
    exact hmem
  obtain ⟨A, σ, B, -, hAsemi, hTsemi, hTform, -⟩ :=
    exists_of_mem_normalizer_diag (Γ := StatedSp 2 K) (k := 2)
      (CFSG.Quasithin.H.Sp4.hasScalarCommutant_statedSp (K := K)) hTnorm
  have ht2 : t ^ 2 = 1 := by
    simpa [hord] using pow_orderOf_eq_one t
  have hT2 : T ^ 2 = 1 := by
    change congrHom e t ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have htne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hTne : T ≠ 1 := by
    intro h
    have h' : congrHom e t = 1 := by simpa [T] using h
    have h'' : congrHom e t = congrHom e 1 := by
      rw [h', map_one]
    exact htne (congrHom_injective e h'')
  obtain ⟨m, hfm⟩ := hf
  have hf1 : 1 ≤ f := by omega
  have hσ : σ = RingEquiv.refl K := by
    by_contra hσne
    have hdvd : 2 ∣ f :=
      (rkIdx_fixV_of_semilinear_two (n := f) hf1 hKcard hTsemi hσne hT2).1
    obtain ⟨k, hk⟩ := hdvd
    omega
  have hAlin : IsSemilinear A (RingEquiv.refl K) := by
    rw [hσ] at hAsemi
    exact hAsemi
  have hAlin' : ∀ (c : K) (w : Fin 2 ⊕ Fin 2 → K),
      toAddMap A (c • w) = c • toAddMap A w := by
    intro c w
    simpa using hAlin c w
  have hbound : 2 * f ≤ rkIdx (fixV (Subgroup.zpowers T)) := by
    by_cases hBscalar : ∃ c : K,
        (B : Matrix (Fin 2) (Fin 2) K) = c • (1 : Matrix (Fin 2) (Fin 2) K)
    · obtain ⟨c, hBc⟩ := hBscalar
      have hc0 : c ≠ 0 := by
        rintro rfl
        have hB0 : (B : Matrix (Fin 2) (Fin 2) K) = 0 := by simpa using hBc
        have hone : (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
          calc (1 : Matrix (Fin 2) (Fin 2) K)
              = (B : Matrix (Fin 2) (Fin 2) K) *
                  ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
                (Units.mul_inv B).symm
            _ = 0 := by rw [hB0, Matrix.zero_mul]
        have h1 : (1 : K) = 0 := by
          simpa using congrArg Matrix.det hone
        exact one_ne_zero h1
      have hAinj : Function.Injective (toAddMap A) := by
        intro u v h
        have := congrArg (toAddMap A⁻¹) h
        rwa [toAddMap_apply_inv, toAddMap_apply_inv] at this
      have hAinv' : ∀ (c : K) (w : Fin 2 ⊕ Fin 2 → K),
          toAddMap A⁻¹ (c • w) = c • toAddMap A⁻¹ w := by
        intro c w
        apply hAinj
        rw [toAddMap_inv_apply, hAlin' c (toAddMap A⁻¹ w), toAddMap_inv_apply]
      let As : MulAut (StdMod (Fin 2 ⊕ Fin 2) K) :=
        { toFun := fun x =>
            Multiplicative.ofAdd (c • toAddMap A (Multiplicative.toAdd x))
          invFun := fun x =>
            Multiplicative.ofAdd (c⁻¹ • toAddMap A⁻¹ (Multiplicative.toAdd x))
          left_inv := by
            intro x
            apply Multiplicative.toAdd.injective
            simp only [toAdd_ofAdd]
            show c⁻¹ • toAddMap A⁻¹ (c • toAddMap A (Multiplicative.toAdd x)) =
              Multiplicative.toAdd x
            rw [hAinv' c (toAddMap A (Multiplicative.toAdd x)), smul_smul,
              inv_mul_cancel₀ hc0, one_smul, toAddMap_apply_inv]
          right_inv := by
            intro x
            apply Multiplicative.toAdd.injective
            simp only [toAdd_ofAdd]
            show c • toAddMap A (c⁻¹ • toAddMap A⁻¹ (Multiplicative.toAdd x)) =
              Multiplicative.toAdd x
            rw [hAlin' c⁻¹ (toAddMap A⁻¹ (Multiplicative.toAdd x)), smul_smul,
              mul_inv_cancel₀ hc0, one_smul, toAddMap_inv_apply]
          map_mul' := by
            intro x y
            apply Multiplicative.toAdd.injective
            simp only [toAdd_ofAdd, toAdd_mul, toAddMap_add, smul_add, ofAdd_add] }
      have hAlinear : IsSemilinear As (RingEquiv.refl K) := by
        intro c' v
        change toAddMap As (c' • v) = c' • toAddMap As v
        show c • toAddMap A (c' • v) = c' • (c • toAddMap A v)
        rw [hAlin' c' v, smul_comm]
      have hdiag : ∀ (v : Fin 2 × (Fin 2 ⊕ Fin 2) → K)
          (p : Fin 2 × (Fin 2 ⊕ Fin 2)),
          toAddMap T v p = toAddMap As (fun i => v (p.1, i)) p.2 := by
        intro v p
        rw [hTform v p, hBc]
        have hsum : (fun i => ∑ j,
            (c • (1 : Matrix (Fin 2) (Fin 2) K)) p.1 j * v (j, i)) =
            c • (fun i => v (p.1, i)) := by
          funext i
          rw [Finset.sum_eq_single p.1]
          · simp [Pi.smul_apply]
          · intro b _ hb
            simp [Matrix.one_apply, hb, Ne.symm hb]
          · intro hp
            exact (hp (Finset.mem_univ _)).elim
        rw [hsum, hAlin' c (fun i => v (p.1, i))]
        rfl
      have hAne : As ≠ 1 := by
        intro hAs1
        apply hTne
        refine toAddMap_injective fun v => ?_
        funext p
        rw [hdiag v p]
        have hfix : toAddMap As (fun i => v (p.1, i)) = fun i => v (p.1, i) := by
          rw [hAs1]
          exact toAddMap_one _
        rw [hfix]
        rfl
      have hdiag_rk := rkIdx_fixV_of_diag_formula (k := 2) (A := As) hdiag
      have hAle : f ≤ rkIdx (fixV (Subgroup.zpowers As)) :=
        le_rkIdx_fixV_of_linear (n := f) hKcard hAlinear hAne
      rw [hdiag_rk]
      omega
    · have hBnon : ∀ c : K,
          (B : Matrix (Fin 2) (Fin 2) K) ≠
            c • (1 : Matrix (Fin 2) (Fin 2) K) := by
        intro c hc
        exact hBscalar ⟨c, hc⟩
      have hbig := le_rkIdx_fixV_of_nonscalar (n := f) (k := 2)
        (B := (B : Matrix (Fin 2) (Fin 2) K)) hKcard hAlin hTform hBnon
      have hcard : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
      rw [hcard] at hbig
      omega
  have htrans : rkIdx (fixV (Subgroup.zpowers T)) =
      rkIdx (fixV (Subgroup.zpowers t)) := by
    have hz : (Subgroup.zpowers t).map (congrHom e) = Subgroup.zpowers T := by
      rw [MonoidHom.map_zpowers]
    rw [← hz, rkIdx_fixV_map_congrHom]
  rwa [htrans] at hbound

theorem k_Sp4TwoNat_involution_holds : K_Sp4TwoNat_involution := by
  intro W _ _ _ H f hf hdata t ht hord
  obtain ⟨-, K, hKfield, hKfinite, π, hKcard, hsum⟩ := hdata
  exact @sp4TwoNat_involution_aux K hKfield hKfinite W _ _ H f hf π hKcard hsum t ht hord

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
