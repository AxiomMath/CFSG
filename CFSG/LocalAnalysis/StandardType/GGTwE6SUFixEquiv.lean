module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.Open.StatedSUFieldChange
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.KGL.TwLayer

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
open scoped MatrixGroups commutatorElement

variable {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ}

theorem nonempty_statedSU_equiv_fixSubgroup {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hν : 3 ≤ ν)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) :
    Nonempty (StatedSU ν (ℓ ^ f) K ≃* fixSubgroup (stdUnitaryEquiv (ν := ν) σ)) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set Φ := stdUnitaryEquiv (ν := ν) σ with hΦ
  set F : Subfield L := (iterateFrobenius L ℓ (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hσmap : ∀ M : Matrix (Fin ν) (Fin ν) L, M.map σ.toRingHom = M.map (· ^ ℓ ^ f) := by
    intro M
    ext i j
    simp [hσ]
  have hfix : ∀ X : SL(ν, L), X ∈ fixSubgroup Φ ↔
      Matrix.SpecialLinearGroup.toGL X ∈ unitarySet (ℓ ^ f) ν := by
    intro X
    rw [mem_fixSubgroup, hΦ, stdUnitaryEquiv_apply]
    have hdetX : IsUnit ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)).det := by
      rw [← hσmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, X.2, map_one]
      exact isUnit_one
    constructor
    · intro h
      have hstd : stdUnitary σ.toRingHom X = X := h
      have h1 : (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ =
          (X : Matrix (Fin ν) (Fin ν) L) := by
        rw [← hσmap, ← coe_stdUnitary, hstd]
      have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = 1 := by
        have e1 : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
            (X : Matrix (Fin ν) (Fin ν) L) = ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
              (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ := by rw [h1]
        rw [e1, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdetX, Matrix.transpose_one]
      refine ⟨fun i j => ?_, X.2, hu⟩
      have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom X = invTransposeSL X := by
        have := congrArg invTransposeSL hstd
        rwa [stdUnitary, MonoidHom.comp_apply, invTransposeSL_invTransposeSL] at this
      have h2 : Matrix.SpecialLinearGroup.map σ.toRingHom
          (Matrix.SpecialLinearGroup.map σ.toRingHom X) = X := by
        rw [hmap, slMap_invTransposeSL, ← MonoidHom.comp_apply invTransposeSL, ← stdUnitary, hstd]
      have h3 := congrArg (fun Y : SL(ν, L) => (Y : Matrix (Fin ν) (Fin ν) L) i j) h2
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ] at h3
      rw [← pow_mul, ← sq] at h3
      exact h3
    · rintro ⟨-, -, hu'⟩
      have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = 1 := hu'
      apply Subtype.ext
      rw [coe_stdUnitary, hσmap]
      have : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹ =
          (X : Matrix (Fin ν) (Fin ν) L)ᵀ := by
        refine Matrix.inv_eq_left_inv ?_
        rw [← Matrix.transpose_transpose ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)),
          ← Matrix.transpose_mul, hu, Matrix.transpose_one]
      rw [this, Matrix.transpose_transpose]
  let Ψ : StatedSU ν (ℓ ^ f) F →* SL(ν, L) := statedSUToSL F ν (ℓ ^ f)
  have hΨmem : ∀ Y, Ψ Y ∈ fixSubgroup Φ := fun Y =>
    (hfix _).2 ((mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩)
  let e : StatedSU ν (ℓ ^ f) F ≃* fixSubgroup Φ := MulEquiv.ofBijective (Ψ.codRestrict _ hΨmem)
    ⟨fun Y Z h => statedSUToSL_injective F ν (ℓ ^ f) (congrArg Subtype.val h), fun X => by
      obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) X).mpr
        ((hfix X).1 X.2)
      exact ⟨Y, Subtype.ext hY⟩⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype F := Fintype.ofFinite F
  exact ⟨(CFSG.Open.StatedSUFieldChange.statedSUEquiv
    (FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hFcard])) ν (ℓ ^ f)).trans e⟩

end CFSG.StandardType.KGL.TwLayer

end
