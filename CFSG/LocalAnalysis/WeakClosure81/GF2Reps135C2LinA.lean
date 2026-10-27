module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2EndB
import CFSG.GroupTheory.E3Params
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
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcTag
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs
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

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {t : MulAut W}

@[expose] def SemilinearBy (t : MulAut W) (σ : ↥(LEnd L) ≃+* ↥(LEnd L)) : Prop :=
  ∀ (φ : ↥(LEnd L)) (w : Additive W),
    ((σ φ : AddMonoid.End (Additive W)) (Additive.ofMul (t (Additive.toMul w)))) =
      Additive.ofMul (t (Additive.toMul ((φ : AddMonoid.End (Additive W)) w)))

theorem w135c2_exists_sigma (htN : ∀ g ∈ L, t * g * t⁻¹ ∈ L) (ht2 : orderOf t = 2) :
    ∃ σ : ↥(LEnd L) ≃+* ↥(LEnd L), (∀ φ, σ (σ φ) = φ) ∧ SemilinearBy t σ := by
  classical
  have ht2' : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2] at h
  have ht_mul : t * t = 1 := by rwa [pow_two] at ht2'
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_mul
  have htN' : ∀ g ∈ L, t * g * t ∈ L := by
    intro g hg
    have h := htN g hg
    rwa [htinv] at h
  have ht_apply_apply : ∀ u : W, t (t u) = u := by
    intro u
    rw [← MulAut.mul_apply, ht_mul, MulAut.one_apply]
  let tA : Additive W ≃+ Additive W := MulEquiv.toAdditive t
  have htA_apply_apply : ∀ x : Additive W, tA (tA x) = x := by
    intro x
    have hx : x = Additive.ofMul (Additive.toMul x) := (ofMul_toMul x).symm
    rw [hx]
    show Additive.ofMul (t (t (Additive.toMul x))) = Additive.ofMul (Additive.toMul x)
    rw [ht_apply_apply]
  have hmem : ∀ φ : ↥(LEnd L),
      (tA.toAddMonoidHom.comp (φ.1.comp tA.toAddMonoidHom)) ∈ LEnd L := by
    intro φ g hg x
    show tA (φ.1 (tA ((MulEquiv.toAdditive g) x))) =
      (MulEquiv.toAdditive g) (tA (φ.1 (tA x)))
    have hg' : t * g * t ∈ L := htN' g hg
    have hφcomm : ∀ h ∈ L, ∀ y : Additive W,
        φ.1 ((MulEquiv.toAdditive h) y) = (MulEquiv.toAdditive h) (φ.1 y) :=
      fun h hh y => φ.2 h hh y
    have h1 : ∀ y : Additive W, tA ((MulEquiv.toAdditive g) y) =
        (MulEquiv.toAdditive (t * g * t)) (tA y) := by
      intro y
      have hy : y = Additive.ofMul (Additive.toMul y) := (ofMul_toMul y).symm
      rw [hy]
      show Additive.ofMul (t (g (Additive.toMul y))) =
        Additive.ofMul ((t * g * t) (t (Additive.toMul y)))
      rw [MulAut.mul_apply, MulAut.mul_apply, ht_apply_apply]
    have h2 : ∀ y : Additive W, tA ((MulEquiv.toAdditive (t * g * t)) y) =
        (MulEquiv.toAdditive g) (tA y) := by
      intro y
      have hy : y = Additive.ofMul (Additive.toMul y) := (ofMul_toMul y).symm
      rw [hy]
      show Additive.ofMul (t ((t * g * t) (Additive.toMul y))) =
        Additive.ofMul (g (t (Additive.toMul y)))
      rw [MulAut.mul_apply, MulAut.mul_apply, ht_apply_apply]
    rw [h1 x, hφcomm (t * g * t) hg' (tA x), h2 (φ.1 (tA x))]
  let σfun : ↥(LEnd L) → ↥(LEnd L) := fun φ =>
    ⟨tA.toAddMonoidHom.comp (φ.1.comp tA.toAddMonoidHom), hmem φ⟩
  have hlr : Function.Involutive σfun := by
    intro φ
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    show tA (tA (φ.1 (tA (tA x)))) = φ.1 x
    rw [htA_apply_apply, htA_apply_apply]
  let σh : ↥(LEnd L) →+* ↥(LEnd L) :=
  { toFun := σfun
    map_zero' := by
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro x
      change tA ((0 : AddMonoid.End (Additive W)) (tA x)) =
        (0 : AddMonoid.End (Additive W)) x
      simp
    map_one' := by
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro x
      show tA (tA x) = x
      exact htA_apply_apply x
    map_mul' := by
      intro φ ψ
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro x
      show tA (φ.1 (ψ.1 (tA x))) = tA (φ.1 (tA (tA (ψ.1 (tA x)))))
      rw [htA_apply_apply]
    map_add' := by
      intro φ ψ
      apply Subtype.ext
      apply AddMonoidHom.ext
      intro x
      show tA (φ.1 (tA x) + ψ.1 (tA x)) = tA (φ.1 (tA x)) + tA (ψ.1 (tA x))
      rw [map_add] }
  let σ : ↥(LEnd L) ≃+* ↥(LEnd L) :=
    RingEquiv.ofBijective σh (Function.Involutive.bijective hlr)
  refine ⟨σ, ?_, ?_⟩
  · intro φ
    rw [RingEquiv.ofBijective_apply, RingEquiv.ofBijective_apply]
    exact hlr φ
  · intro φ w
    show tA (φ.1 (tA (tA w))) = tA (φ.1 w)
    rw [htA_apply_apply]

theorem w135c2_linear (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥) (ht2 : orderOf t = 2)
    {k : ℕ} (hk : Nat.card ↥(LEnd L) = 2 ^ k) (σ : ↥(LEnd L) ≃+* ↥(LEnd L))
    (hσ : SemilinearBy t σ) (hid : ∀ φ, σ φ = φ) :
    ∃ r : ℕ, 1 ≤ r ∧ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) = k * r := by
  classical
  letI : Field ↥(LEnd L) := (w135c2_lend_isField hW hirr).toField
  letI : Module ↥(LEnd L) (Additive W) := Module.compHom (Additive W) (LEnd L).subtype
  let tA : Additive W ≃+ Additive W := MulEquiv.toAdditive t
  have hcomm : ∀ (φ : ↥(LEnd L)) (w : Additive W), φ.1 (tA w) = tA (φ.1 w) := by
    intro φ w
    have h := hσ φ w
    rw [hid φ] at h
    exact h
  let tL : Additive W →ₗ[↥(LEnd L)] Additive W :=
  { toFun := tA
    map_add' := tA.map_add
    map_smul' := fun c w => (hcomm c w).symm }
  let τ : Additive W →ₗ[↥(LEnd L)] Additive W := tL - 1
  let S : Subgroup W := fixV (Subgroup.zpowers t)
  have hτapply : ∀ x : Additive W, τ x = tA x - x := fun x => rfl
  have hkeriff : ∀ a : Additive W, a ∈ τ.ker ↔ Additive.toMul a ∈ S := by
    intro a
    change a ∈ τ.ker ↔ Additive.toMul a ∈ fixV (Subgroup.zpowers t)
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
    constructor
    · intro ha
      rw [LinearMap.mem_ker] at ha
      have h : tA a = a := sub_eq_zero.mp (by rw [← hτapply]; exact ha)
      apply Additive.ofMul.injective
      show (MulEquiv.toAdditive t) a = a
      exact h
    · intro ha
      rw [LinearMap.mem_ker]
      have h : tA a = a := by
        have h' := congrArg Additive.ofMul ha
        show (MulEquiv.toAdditive t) a = a
        exact h'
      rw [hτapply, h, sub_self]
  have hcardker : Nat.card ↥τ.ker = Nat.card ↥S :=
    Nat.card_congr (Equiv.subtypeEquiv (Additive.toMul : Additive W ≃ W) hkeriff)
  haveI : Module.Finite ↥(LEnd L) (Additive W) := Module.Finite.of_finite
  have hcardV : Nat.card (Additive W) =
      Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) (Additive W) :=
    Module.natCard_eq_pow_finrank
  have hcardker2 : Nat.card ↥τ.ker =
      Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) ↥τ.ker :=
    Module.natCard_eq_pow_finrank
  have hrk : Module.finrank ↥(LEnd L) (Additive W) =
      Module.finrank ↥(LEnd L) ↥τ.range + Module.finrank ↥(LEnd L) ↥τ.ker :=
    (LinearMap.finrank_range_add_finrank_ker τ).symm
  have key : Nat.card ↥S * S.index =
      Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) ↥τ.range * Nat.card ↥S := by
    calc Nat.card ↥S * S.index
        = Nat.card (Additive W) :=
          (Subgroup.card_mul_index S).trans (Nat.card_congr Additive.toMul).symm
      _ = Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) (Additive W) := hcardV
      _ = Nat.card ↥(LEnd L) ^ (Module.finrank ↥(LEnd L) ↥τ.range +
            Module.finrank ↥(LEnd L) ↥τ.ker) := by rw [hrk]
      _ = Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) ↥τ.range *
            Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) ↥τ.ker := by rw [pow_add]
      _ = Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) ↥τ.range * Nat.card ↥S := by
            rw [← hcardker, hcardker2]
  have hSne : Nat.card ↥S ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hkey' : Nat.card ↥S * S.index =
      Nat.card ↥S * Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) ↥τ.range :=
    key.trans (Nat.mul_comm _ _)
  have hindex : S.index = Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) ↥τ.range :=
    Nat.mul_left_cancel (Nat.pos_of_ne_zero hSne) hkey'
  have hindex2 : S.index = 2 ^ (k * Module.finrank ↥(LEnd L) ↥τ.range) := by
    rw [hindex, hk, ← pow_mul]
  have htne : t ≠ 1 := by
    intro ht1
    rw [ht1, orderOf_one] at ht2
    omega
  have hτne : τ ≠ 0 := by
    intro hτ
    apply htne
    ext w
    have hval : τ (Additive.ofMul w) = 0 := by rw [hτ]; rfl
    have h : tA (Additive.ofMul w) = Additive.ofMul w :=
      sub_eq_zero.mp (by rw [← hτapply]; exact hval)
    exact Additive.ofMul.injective h
  have hrange_ne : τ.range ≠ ⊥ := fun h => hτne ((LinearMap.range_eq_bot).mp h)
  have hdrange : 1 ≤ Module.finrank ↥(LEnd L) ↥τ.range := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hrange_ne ((Submodule.finrank_eq_zero).mp h0)
  refine ⟨Module.finrank ↥(LEnd L) ↥τ.range, hdrange, ?_⟩
  rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx]
  change padicValNat 2 S.index = k * Module.finrank ↥(LEnd L) ↥τ.range
  rw [hindex2, padicValNat.prime_pow]

end CFSG.LocalAnalysis.WeakClosure81
