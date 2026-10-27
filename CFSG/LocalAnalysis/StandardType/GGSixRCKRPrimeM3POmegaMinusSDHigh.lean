module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFEBlockPOmegaMinusSD
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSUBlock
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlag
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Open (StatedLieTag)
open scoped Matrix

local notation "QM(" n ", " f ")" =>
  Spin.quadMinus n (GaloisField 2 f) (Prod.fst (minusCoeffs 2 f)) (Prod.snd (minusCoeffs 2 f))
local notation "IdxM(" n ")" => Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2

private theorem rckSD_rank_pos
    {t : StatedLieTag} {k q : ℕ} (ht : t = .PSU ∨ t = .PSL)
    (hadm : CFSG.Open.StatedLieAdmissible t k 2 q) : 0 < (ggU t k q).D.rank := by
  have hf : 1 ≤ q := hadm.2.1
  rcases ht with rfl | rfl
  · have hk : 3 ≤ k := hadm.2.2.1
    have e : ggU .PSU k q = ⟨SU (unitaryInvolution (GaloisField 2 (2 * q)) 2 q) k,
        rootDatum (card_galoisField_two_mul 2 q hf) k⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    show 0 < k / 2
    omega
  · have hk : 2 ≤ k := hadm.2.2.1
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    show 0 < m
    omega

theorem rckM3_POmegaMinus_selfDualHigh
    (n f : ℕ) (hf : 1 ≤ f) (hn : 4 ≤ n)
    (S : Set (GL (IdxM(n)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix QM(n, f)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (IdxM(n)) (IdxM(n)) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin QM(n, f)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup ↥(spinGroup QM(n, f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix QM(n, f)) S e,
        glBlockCentralizer (Spin.spinMatrix QM(n, f)) S e⁆) :
    RCKSpinFlagModel QM(n, f) J' 4 := by
  classical
  have hirr : ∀ t : GaloisField 2 f,
      t ^ 2 + (minusCoeffs 2 f).1 * t + (minusCoeffs 2 f).2 ≠ 0 := minusCoeffs_irr 2 f
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨l, K, _, _, _, _, _, τ, ρ, H, hl, hl2, hπdeg, -, hτ2, hτne, hτF, hinjρ, hρ, hHsymm,
      hHnd, hHtr, hHinv, hHsurj⟩ :=
    exists_blockAction_selfDual_POmegaMinus n hirr hn f hc S hSU hS hodd hε hJe he hdeg
  have : FiniteDimensional K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K _
  have hq : 2 ≤ l * f :=
    calc 2 = 2 * 1 := by norm_num
      _ ≤ l * f := Nat.mul_le_mul hl2 hf
  have hfin : Module.finrank (GaloisField 2 f) K = 2 * l := hπdeg.trans hl
  have hK : Nat.card K = (2 ^ (l * f)) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 f) (V := K),
      GaloisField.card (p := 2) (n := f) (by omega), hfin, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hinj : Function.Injective (Spin.spinMatrix QM(n, f)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero (GaloisField 2 f) 2))
  have : Finite ↥(spinGroup QM(n, f)) := Finite.of_injective _ hinj
  have hiso : ∀ y : ↥(spinGroup QM(n, f)),
      ∀ b ∈ some (QuadraticMap.polar QM(n, f)),
      ∀ m m' : IdxM(n) → GaloisField 2 f,
      b ((Spin.spinMatrix QM(n, f) y : Matrix (IdxM(n)) (IdxM(n)) (GaloisField 2 f)) *ᵥ m)
        ((Spin.spinMatrix QM(n, f) y : Matrix (IdxM(n)) (IdxM(n)) (GaloisField 2 f)) *ᵥ m') =
          b m m' := by
    intro y b hb m m'
    rw [Option.mem_some_iff] at hb
    subst hb
    rw [Spin.spinMatrix_mulVec, Spin.spinMatrix_mulVec, Spin.polar_spinAction]
  have hG : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin QM(n, f))).det :=
    (Matrix.nondegenerate_iff_det_ne_zero.mp
      (LinearMap.BilinForm.Nondegenerate.toMatrix'
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) hirr))).isUnit
  have hpol : ∀ u v : IdxM(n) → GaloisField 2 f,
      QuadraticMap.polar QM(n, f) u v =
        dotProduct u ((LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin QM(n, f))).mulVec v) := by
    intro u v
    have h := Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix'
      (QuadraticMap.polarBilin QM(n, f))) u v
    rw [Matrix.toBilin'_toMatrix'] at h
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact h
  have heT : eᵀ * (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin QM(n, f))) =
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin QM(n, f))) * e := by
    have h0 : formAdj (RingHom.id (GaloisField 2 f)) (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin QM(n, f))) e = e := hε.2.2.2.1
    have h1 : (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin QM(n, f)))⁻¹ * eᵀ *
        (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin QM(n, f))) = e := by
      simpa [formAdj] using h0
    calc eᵀ * (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin QM(n, f)))
        = (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin QM(n, f))) *
            ((LinearMap.toMatrix₂' (GaloisField 2 f)
              (QuadraticMap.polarBilin QM(n, f)))⁻¹ * eᵀ *
            (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin QM(n, f)))) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG,
            Matrix.one_mul]
      _ = (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin QM(n, f))) * e := by
          rw [h1]
  have horth : ∀ m n' : IdxM(n) → GaloisField 2 f,
      QuadraticMap.polar QM(n, f) ((1 - e) *ᵥ m) (e *ᵥ n') = 0 := by
    intro m n'
    have hdot : ∀ (A : Matrix (IdxM(n)) (IdxM(n)) (GaloisField 2 f))
        (u w : IdxM(n) → GaloisField 2 f), (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
      intro A u w
      rw [← Matrix.vecMul_transpose A u, ← Matrix.dotProduct_mulVec u Aᵀ w]
    have hmat : (1 - e)ᵀ * (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin QM(n, f))) * e = 0 := by
      have h1 : (1 - e)ᵀ = 1 - eᵀ := by rw [Matrix.transpose_sub, Matrix.transpose_one]
      rw [h1, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, heT, Matrix.mul_assoc,
        he.2.1.eq, sub_self]
    rw [hpol]
    calc ((1 - e) *ᵥ m) ⬝ᵥ ((LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin QM(n, f))) *ᵥ (e *ᵥ n'))
        = m ⬝ᵥ ((1 - e)ᵀ *ᵥ ((LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin QM(n, f))) *ᵥ (e *ᵥ n'))) := hdot (1 - e) m _
      _ = m ⬝ᵥ (((1 - e)ᵀ * (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin QM(n, f))) * e) *ᵥ n') := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [hmat, Matrix.zero_mulVec]
          simp [dotProduct]
  obtain ⟨t, k, κ, htag, hnorm, hrange, hcent, hflags, hroot⟩ :=
    rckRP_exists_model_of_suBlock (Spin.spinMatrix QM(n, f))
      (B := some (QuadraticMap.polar QM(n, f))) hiso he.2.1 hJe (K := K)
      (W := LinearMap.range (Matrix.mulVecLin e)) (q := l * f) hK hq hτ2 hτne H hHsymm hHnd
      (LinearEquiv.ofEq _ _ (by rw [Matrix.toLin'_apply'])) ρ hinjρ hHinv
      (fun g hg _ => by
        obtain ⟨u, hu⟩ := hHsurj g hg
        exact ⟨u, hu⟩)
      (fun g w => hρ g w)
      (by
        intro b hb
        rw [Option.mem_some_iff] at hb
        subst hb
        refine ⟨fun m₁ m₂ m => by simp only [QuadraticMap.polar_add_left], horth,
          fun w w' => (hHtr w w').symm, hτF⟩)
  have hrank : 0 < (ggU t k (l * f)).D.rank := rckSD_rank_pos htag hnorm.2
  obtain ⟨β₀, hβ₀, hlong⟩ := RCKK1I.rckExists_longRoot (ggU t k (l * f)) hrank
  refine rckSpinFlagModel_of_rootFlags κ hnorm
    (htag.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inl h) hrange hcent hflags hβ₀ hlong ?_
  rw [hroot β₀ hβ₀ hlong]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (l * f) := Nat.pow_le_pow_right (by norm_num) hq

end CFSG.StandardType.RCKRP
