module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSUBlock
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlag
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFEBlockPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAut
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoOrth
import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)
open scoped Matrix

theorem rckM3_POmegaPlus_selfDualHigh
    (k f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆) :
    RCKSpinFlagModel (Spin.quadPlus (k + 3) (GaloisField 2 f)) J' 4 := by
  classical
  obtain ⟨l, K, _, _, _, _, _, τ, ρ, H, hdl, hl2, hdegK, -, hτ2, hτne, hτF, hρinj, hρ, hHsymm,
      hHnd, hHtr, hHinv, hHsurj⟩ :=
    exists_blockAction_selfDual_POmegaPlus (k + 3) (by omega) f
      (GaloisField.card (p := 2) (n := f) (by omega)) S hSU hS hodd hε hJe he hdeg
  have : FiniteDimensional K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K _
  have hlf : 2 ≤ l * f :=
    calc 2 = 2 * 1 := by norm_num
      _ ≤ l * f := Nat.mul_le_mul hl2 hf
  have hKcard : Nat.card K = (2 ^ (l * f)) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 f) (V := K),
      GaloisField.card (p := 2) (n := f) (by omega), hdegK, hdl, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have : NeZero (k + 3) := ⟨by omega⟩
  have : Finite ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (Spin.coe_ker_spinMatrix_quadPlus (n := k + 3) (K := GaloisField 2 f))
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
  let eW : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[GaloisField 2 f]
      LinearMap.range (Matrix.toLin' e) :=
    LinearEquiv.ofEq _ _ (by rw [Matrix.toLin'_apply'])
  have hB : ∀ b ∈ some (QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))),
      (∀ m m' n : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f, b (m + m') n = b m n + b m' n) ∧
      (∀ m n : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f, b ((1 - e) *ᵥ m) (e *ᵥ n) = 0) ∧
      (∀ w w' : LinearMap.range (Matrix.mulVecLin e),
        b (eW w) (eW w') = Algebra.trace (GaloisField 2 f) K (H w w')) ∧
      ∀ c : GaloisField 2 f, τ (algebraMap _ K c) = algebraMap _ K c := by
    intro b hb
    rw [Option.mem_some_iff] at hb
    subst hb
    refine ⟨fun m m' n => QuadraticMap.polar_add_left _ m m' n, fun m n => ?_,
      fun w w' => (hHtr w w').symm, hτF⟩
    rw [QuadraticMap.polar_comm, Geo.polar_mulVec_eq_polar_formAdj_mulVec _ hQunit, hε.2.2.2.1,
      Matrix.mulVec_mulVec, mul_sub, mul_one, he.2.1.eq, sub_self, Matrix.zero_mulVec,
      QuadraticMap.polar_zero_right]
  obtain ⟨t, m, κ, htag, hnorm, hrange, hcent, hflags, horder⟩ :=
    rckRP_exists_model_of_suBlock
      (G := ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
      (B := some (QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)))) hiso he.2.1
      hJe hKcard hlf hτ2 hτne H hHsymm hHnd eW ρ hρinj hHinv
      (fun g hg _ => MonoidHom.mem_range.mpr (hHsurj g hg)) (fun g w => hρ g w) hB
  have hrank : 0 < (ggU t m (l * f)).D.rank := by
    rcases htag with rfl | rfl
    · obtain ⟨-, -, -, hm3, -⟩ := hnorm
      rw [ggU_PSU_rank m (l * f) (by omega)]
      omega
    · obtain ⟨-, -, -, hm2, -⟩ := hnorm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      change 0 < m'
      omega
  obtain ⟨β₀, hβ₀, hlong⟩ := RCKK1I.rckExists_longRoot (ggU t m (l * f)) hrank
  refine rckSpinFlagModel_of_rootFlags κ hnorm (htag.elim (fun h => Or.inr (Or.inl h)) Or.inl)
    hrange hcent hflags hβ₀ hlong ?_
  rw [horder β₀ hβ₀ hlong]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hlf

end CFSG.StandardType.RCKRP
