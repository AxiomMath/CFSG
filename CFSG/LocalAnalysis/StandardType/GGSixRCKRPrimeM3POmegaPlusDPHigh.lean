module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSLBlock
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagDualPair
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlag
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFEBlockPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)
open scoped Matrix

theorem rckM3_POmegaPlus_dualPairHigh
    (k f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (heε : e * ε = e)
    (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆) :
    RCKSpinFlagModel (Spin.quadPlus (k + 3) (GaloisField 2 f)) J' 4 := by
  classical
  obtain ⟨-, -, hstar_e, he_star, hεeq⟩ :=
    dualPair_star_POmegaPlus (k + 3) (by omega) S hSU hS hε he heε hne
  obtain ⟨K, _, _, _, _, _, ρ, hdegK, hbij, hρ⟩ :=
    exists_blockAction_dualPair_POmegaPlus (k + 3) (by omega) S hSU hS hodd hε he heε hne hdeg
  have : FiniteDimensional K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K _
  have hKcard : Nat.card K =
      2 ^ (f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) := by
    rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 f) (V := K),
      GaloisField.card (p := 2) (n := f) (by omega), hdegK, pow_mul]
  have hq : 2 ≤ f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e :=
    calc 2 = 1 * 2 := by norm_num
      _ ≤ _ := Nat.mul_le_mul hf hdeg
  have hiso : ∀ y : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))),
      ∀ b ∈ some (QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))),
      ∀ m m' : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
      b ((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) y :
          Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) *ᵥ m)
        ((Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) y :
          Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) *ᵥ
            m') = b m m' := by
    intro y b hb m m'
    rw [Option.mem_some_iff] at hb
    subst hb
    rw [Spin.spinMatrix_mulVec, Spin.spinMatrix_mulVec, Spin.polar_spinAction]
  have hQunit : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))).det :=
    (Matrix.nondegenerate_iff_det_ne_zero.mp
      (LinearMap.BilinForm.Nondegenerate.toMatrix'
        (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)))).isUnit
  have hcomm : ∀ g : ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3)
      (GaloisField 2 f))) S ε),
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) * e =
      e * (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) g :
        Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) := by
    intro g
    have hgS := (Subgroup.mem_comap.mp g.2).1
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute he.1 ?_).eq
    rintro _ ⟨s, hs, rfl⟩
    have h := congrArg Units.val ((Subgroup.mem_centralizer_iff.mp hgS) s hs)
    rw [Units.val_mul, Units.val_mul] at h
    exact h.symm
  have hflag : ∀ R : Subgroup (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)),
      (∀ x ∈ R, x ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range) →
      (∀ x ∈ R, (x : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) * e = e * (x : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
          (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))) →
      (∀ x ∈ R, (x : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) * (1 - ε) = 1 - ε) → (∀ x ∈ R, x * x = 1) →
      ∀ U₁ U₂ : Submodule (GaloisField 2 f) (Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f),
      U₁ ≤ U₂ →
      (∀ x ∈ R, x ≠ 1 →
        LinearMap.range (Matrix.toLin' (((x : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
          (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) - 1) * e)) = U₁ ∧
        LinearMap.ker (Matrix.toLin' ((x : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
          (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) - 1)) ⊓
          LinearMap.range (Matrix.toLin' e) = U₂) →
      GLGeoFlag (some (QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)))) R := by
    intro R hRj hRc hRfix hinv U₁ U₂ hU hfl
    refine glGeoFlag_polar_of_dualPair hQunit he.2.1 he_star hstar_e ?_ hRc ?_ hinv hU hfl
    · intro x hx m m'
      obtain ⟨y, rfl⟩ := hRj x hx
      exact hiso y _ rfl m m'
    · intro x hx
      rw [← hεeq]
      exact hRfix x hx
  obtain ⟨k', κ, hk', hnorm, hrange, hcent, hflags⟩ :=
    rckRP_slModel_of_slBlock (G := ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
      (B := some (QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)))) hiso he.2.2.1
      hJe hKcard hq (LinearEquiv.ofEq _ _ (by rw [Matrix.toLin'_apply'])) ρ hbij.1
      (by rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hbij.2])
      (fun g w => hρ g w) hcomm hflag
  obtain ⟨β₀, hβ₀, hlong⟩ := RCKK1I.rckExists_longRoot (ggU .PSL (k' + 1)
    (f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)) (by
      change 0 < k'
      omega)
  refine rckSpinFlagModel_of_rootFlags κ hnorm (Or.inl rfl) hrange hcent hflags hβ₀ hlong ?_
  have hroot : Nat.card ((ggU .PSL (k' + 1)
      (f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)).D.rootGroup β₀) =
      2 ^ (f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :=
    card_rootGroup_specialLinear_galoisField (by omega) hβ₀
  rw [hroot]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hq

end CFSG.StandardType.RCKRP
