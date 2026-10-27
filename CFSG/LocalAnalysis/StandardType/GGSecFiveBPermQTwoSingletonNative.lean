module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCentralizer
public import CFSG.GH74.GLS.Basic
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBlock
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.Statements
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSylowUnique
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType.QTwoSingletonNative

open Polynomial Matrix CoordSL SLNS Subgroup CFSG.RankThree.CALinearPlane CFSG.GH74.GLS

theorem oPrimeResidual_specialLinear_eq_top {F : Type} [Field F] [CharP F 2] (n : ℕ) :
    oPrimeResidual 2 (SpecialLinearGroup (Fin n) F) = ⊤ := by
  apply top_unique
  rw [← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin n) (K := F)]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨1, ?_⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  change (SpecialLinearGroup.transvection hij c) ^ 2 = 1
  rw [sq, ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero]
  simp

section Frame

variable {F : Type} [Field F] {g : F[X]} [Fact (Irreducible g)] {m s d : ℕ}
  (ε : Fin m ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin d)

private theorem mem_complement_of_fixed_block {u : SpecialLinearGroup (Fin m) F} {j : Fin s}
    (hfix : ∀ z : AdjoinRoot g,
      frameForm g ε (u : Matrix (Fin m) (Fin m) F) (Pi.single j z, 0) = (Pi.single j z, 0))
    (hpres : ∀ v : (Fin s → AdjoinRoot g) × (Fin d → F), v.1 j = 0 →
      (frameForm g ε (u : Matrix (Fin m) (Fin m) F) v).1 j = 0) :
    u ∈ coordBlockSL F (fixS ε {j}) := by
  rw [mem_coordBlockSL_iff]
  intro p q hpq
  have hcol (v) : (u : Matrix (Fin m) (Fin m) F) *ᵥ frameCoords g ε v =
      frameCoords g ε (frameForm g ε (u : Matrix (Fin m) (Fin m) F) v) :=
    (frameCoords_frameForm g ε _ v).symm
  have hentry : (u : Matrix (Fin m) (Fin m) F) p q =
      ((u : Matrix (Fin m) (Fin m) F) *ᵥ Pi.single q 1) p := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hnot (x : Fin m) (hx : x ∉ fixS ε {j}) : ∃ a, ε x = Sum.inl (a, j) := by
    rcases hεx : ε x with ⟨a, k⟩ | l
    · have hk : k = j := by simpa [mem_fixS, inT, hεx] using hx
      exact ⟨a, by simp [hk]⟩
    · simp [mem_fixS, inT, hεx] at hx
  by_cases hqj : ∃ a, ε q = Sum.inl (a, j)
  · obtain ⟨a, hεq⟩ := hqj
    have hq : Pi.single q (1 : F) = frameCoords g ε (Pi.single j ((rootPB g).basis a), 0) := by
      rw [frameCoords_single_basis, ← hεq, Equiv.symm_apply_apply]
    rw [hentry, hq, hcol, hfix, ← hq, Pi.single_apply]
  · have hpj : ∃ a, ε p = Sum.inl (a, j) := by
      rcases hpq with hp | hq
      · exact hnot p hp
      · exact False.elim (hqj (hnot q hq))
    obtain ⟨a, hεp⟩ := hpj
    have hpq' : p ≠ q := fun h => hqj ⟨a, h ▸ hεp⟩
    rcases hεq : ε q with ⟨b, k⟩ | l
    · have hjk : j ≠ k := fun h => hqj ⟨b, h ▸ hεq⟩
      have hq : Pi.single q (1 : F) = frameCoords g ε (Pi.single k ((rootPB g).basis b), 0) := by
        rw [frameCoords_single_basis, ← hεq, Equiv.symm_apply_apply]
      rw [hentry, hq, hcol, frameCoords_apply, hεp]
      simp only [Sum.elim_inl]
      rw [hpres _ (Pi.single_eq_of_ne hjk _), map_zero, Finsupp.zero_apply, if_neg hpq']
    · have hq : Pi.single q (1 : F) = frameCoords g ε (0, Pi.single l 1) := by
        funext x
        rw [frameCoords_apply]
        rcases hεx : ε x with ⟨b, k⟩ | l'
        · have hxq : x ≠ q := fun h => by rw [h, hεq] at hεx; simp at hεx
          simp [Pi.single_eq_of_ne hxq]
        · simp only [Sum.elim_inr]
          by_cases hll : l' = l
          · subst l'
            have hxq : x = q := ε.injective (hεx.trans hεq.symm)
            subst x
            simp
          · have hxq : x ≠ q := fun h => by
              rw [h, hεq] at hεx
              exact hll (by simpa using hεx.symm)
            rw [Pi.single_eq_of_ne hxq, Pi.single_eq_of_ne hll]
      rw [hentry, hq, hcol, frameCoords_apply, hεp]
      simp only [Sum.elim_inl]
      rw [hpres _ rfl, map_zero, Finsupp.zero_apply, if_neg hpq']

variable [Finite F] [CharP F 2] {hC : (rootMat g).det = 1}

theorem mem_complement_of_pow_two_of_comm {u : SpecialLinearGroup (Fin m) F} {j : Fin s}
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3)
    (hu : Commute (nsSL ε hC (kT {j})) u) {k : ℕ} (hpow : u ^ (2 ^ k) = 1) :
    u ∈ coordBlockSL F (fixS ε {j}) := by
  obtain ⟨hblock, hpres⟩ := QTwoBlocks.frameForm_block_of_comm ε hC hprim hu
  let lam := (frameForm g ε (u : Matrix (Fin m) (Fin m) F) (Pi.single j 1, 0)).1 j
  have hp (n : ℕ) : frameForm g ε ((u : Matrix (Fin m) (Fin m) F) ^ n)
      (Pi.single j 1, 0) = (Pi.single j (lam ^ n), 0) := by
    induction n with
    | zero => simp [frameForm_one]
    | succ n ih =>
      rw [pow_succ', frameForm_mul, LinearMap.comp_apply, ih,
        hblock, pow_succ]
  have hmatpow : (u : Matrix (Fin m) (Fin m) F) ^ (2 ^ k) = 1 := by
    let mu : SpecialLinearGroup (Fin m) F →* Matrix (Fin m) (Fin m) F :=
      SpecialLinearGroup.coeMonoidHom
    calc (u : Matrix (Fin m) (Fin m) F) ^ (2 ^ k) = mu (u ^ (2 ^ k)) :=
          (map_pow mu u (2 ^ k)).symm
      _ = mu 1 := congrArg mu hpow
      _ = 1 := map_one mu
  have hlam : lam ^ (2 ^ k) = 1 := by
    have h := hp (2 ^ k)
    rw [hmatpow, frameForm_one, LinearMap.id_apply] at h
    simpa using (congrArg (fun v => v.1 j) h).symm
  have hlam1 : lam = 1 := by
    let _ : CharP (AdjoinRoot g) 2 := (Algebra.charP_iff F (AdjoinRoot g) 2).mp inferInstance
    have hscalar : ∀ (n : ℕ) (a : AdjoinRoot g), a ^ (2 ^ n) = 1 → a = 1 := by
      intro n
      induction n with
      | zero => intro a ha; simpa using ha
      | succ n ih =>
        intro a ha
        apply ih a
        have hsq : (a ^ (2 ^ n)) ^ 2 = 1 := by
          calc (a ^ (2 ^ n)) ^ 2 = a ^ (2 ^ n * 2) := (pow_mul a (2 ^ n) 2).symm
            _ = a ^ (2 ^ (n + 1)) := congrArg (fun t : ℕ => a ^ t) (pow_succ 2 n).symm
            _ = 1 := ha
        exact CharTwo.sq_injective (hsq.trans (one_pow 2).symm)
    exact hscalar k lam hlam
  exact mem_complement_of_fixed_block ε (fun z => by simpa [lam, hlam1] using hblock z) hpres

theorem oPrimeResidualOf_inf_centralizer_nsSL_eq
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) 3) (S : Finset (Fin s)) (j : Fin s) :
    oPrimeResidualOf 2 (coordBlockSL F (fixS ε Sᶜ) ⊓
      centralizer ({nsSL ε hC (kT {j})} : Set (SpecialLinearGroup (Fin m) F))) =
        coordBlockSL F (fixS ε (S \ {j})ᶜ) := by
  classical
  let C := coordBlockSL F (fixS ε Sᶜ) ⊓
    centralizer ({nsSL ε hC (kT {j})} : Set (SpecialLinearGroup (Fin m) F))
  let J := fixS ε (S \ {j})ᶜ
  have hsets : fixS ε Sᶜ ∩ fixS ε {j} = J := by
    ext p
    rcases hεp : ε p with ⟨a, i⟩ | l <;> simp [J, mem_fixS, inT, hεp]
  have hJS : J ⊆ fixS ε Sᶜ := by
    rw [← hsets]
    exact Finset.inter_subset_left
  have hJC (u : SpecialLinearGroup (Fin m) F) (hu : u ∈ coordBlockSL F J) : u ∈ C := by
    change u ∈ coordBlockSL F (fixS ε Sᶜ) ∧
      u ∈ centralizer ({nsSL ε hC (kT {j})} : Set (SpecialLinearGroup (Fin m) F))
    refine ⟨?_, ?_⟩
    · rw [mem_coordBlockSL_iff] at hu ⊢
      intro p q hpq
      exact hu p q (by
        rcases hpq with hp | hq
        · exact Or.inl fun hp' => hp (hJS hp')
        · exact Or.inr fun hq' => hq (hJS hq'))
    · rw [mem_centralizer_singleton_iff]
      exact (QTwoBlocks.nsSL_commute_of_mem_coordBlockSL ε hC (S := S \ {j})
        (fun i hi => by simp [kT, (Finset.mem_sdiff.mp hi).2]) hu).symm
  apply le_antisymm
  · change (oPrimeResidual 2 C).map C.subtype ≤ coordBlockSL F J
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨k, hk⟩
    have huC : (u : SpecialLinearGroup (Fin m) F) ∈
        centralizer ({nsSL ε hC (kT {j})} : Set (SpecialLinearGroup (Fin m) F)) := u.2.2
    have hucomm : Commute (nsSL ε hC (kT {j})) (u : SpecialLinearGroup (Fin m) F) :=
      (mem_centralizer_singleton_iff.mp huC).symm
    have hfix : (u : SpecialLinearGroup (Fin m) F) ∈ coordBlockSL F (fixS ε {j}) :=
      mem_complement_of_pow_two_of_comm ε hprim hucomm (congrArg Subtype.val hk)
    have hmem : (u : SpecialLinearGroup (Fin m) F) ∈
        coordBlockSL F (fixS ε Sᶜ) ⊓ coordBlockSL F (fixS ε {j}) := ⟨u.2.1, hfix⟩
    rwa [coordBlockSL_inf, hsets] at hmem
  · let f : SpecialLinearGroup (Fin J.card) F →* C :=
      (blockSLOn F J).codRestrict C fun u => hJC _ ((range_blockSLOn (k := F) J) ▸ ⟨u, rfl⟩)
    have hmap : (oPrimeResidual 2 (SpecialLinearGroup (Fin J.card) F)).map f ≤
        oPrimeResidual 2 C := by
      rw [Subgroup.map_le_iff_le_comap]
      refine (Subgroup.closure_le _).mpr ?_
      rintro u ⟨k, hk⟩
      exact Subgroup.subset_closure ⟨k, by rw [← map_pow, hk, map_one]⟩
    rw [oPrimeResidual_specialLinear_eq_top] at hmap
    rw [← range_blockSLOn]
    rintro _ ⟨u, rfl⟩
    exact ⟨f u, hmap ⟨u, Subgroup.mem_top _, rfl⟩, rfl⟩

end Frame

end CFSG.StandardType.QTwoSingletonNative
