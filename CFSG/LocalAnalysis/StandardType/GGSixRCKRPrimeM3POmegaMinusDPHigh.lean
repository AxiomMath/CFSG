module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFEBlockPOmegaMinus
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSLBlock
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagDualPair
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlag
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)
open scoped Matrix

local notation "QM(" n ", " f ")" =>
  Spin.quadMinus n (GaloisField 2 f) (Prod.fst (minusCoeffs 2 f)) (Prod.snd (minusCoeffs 2 f))
local notation "IdxM(" n ")" => Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2

theorem rckM3_POmegaMinus_dualPairHigh
    (n f : ℕ) (hf : 1 ≤ f) (hn : 4 ≤ n)
    (S : Set (GL IdxM(n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix QM(n, f)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix IdxM(n) IdxM(n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin QM(n, f)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (heε : e * ε = e)
    (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    {J' : Subgroup ↥(spinGroup QM(n, f))}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix QM(n, f)) S ε : Subgroup ↥(spinGroup QM(n, f))),
        (glBlockCentralizer (Spin.spinMatrix QM(n, f)) S ε : Subgroup ↥(spinGroup QM(n, f)))⁆) :
    RCKSpinFlagModel QM(n, f) J' 4 := by
  classical
  have hirr : ∀ t : GaloisField 2 f,
      t ^ 2 + (minusCoeffs 2 f).1 * t + (minusCoeffs 2 f).2 ≠ 0 := minusCoeffs_irr 2 f
  obtain ⟨-, -, hstar_e, he_star, hεeq⟩ :=
    dualPair_star_POmegaMinus n hirr hn S hSU hS hε he heε hne
  obtain ⟨K, _, _, _, _, _, ρ, hdegK, hbij, hρ⟩ :=
    exists_blockAction_dualPair_POmegaMinus n hirr hn S hSU hS hodd hε he heε hne hdeg
  have : FiniteDimensional K (LinearMap.range (Matrix.mulVecLin e)) :=
    Module.Finite.of_restrictScalars_finite (GaloisField 2 f) K _
  have hKcard : Nat.card K =
      2 ^ (f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) := by
    rw [Module.natCard_eq_pow_finrank (K := GaloisField 2 f) (V := K),
      GaloisField.card (p := 2) (n := f) (by omega), hdegK, pow_mul]
  have hq : 2 ≤ f * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e :=
    calc 2 = 1 * 2 := by norm_num
      _ ≤ _ := Nat.mul_le_mul hf hdeg
  have hiso : ∀ y : ↥(spinGroup QM(n, f)),
      ∀ b ∈ some (QuadraticMap.polar QM(n, f)),
      ∀ m m' : IdxM(n) → GaloisField 2 f,
      b ((Spin.spinMatrix QM(n, f) y : Matrix IdxM(n) IdxM(n) (GaloisField 2 f)) *ᵥ m)
        ((Spin.spinMatrix QM(n, f) y : Matrix IdxM(n) IdxM(n) (GaloisField 2 f)) *ᵥ m') =
          b m m' := by
    intro y b hb m m'
    rw [Option.mem_some_iff] at hb
    subst hb
    rw [Spin.spinMatrix_mulVec, Spin.spinMatrix_mulVec, Spin.polar_spinAction]
  have hQunit : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin QM(n, f))).det :=
    (Matrix.nondegenerate_iff_det_ne_zero.mp
      (LinearMap.BilinForm.Nondegenerate.toMatrix'
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) hirr))).isUnit
  have hcomm : ∀ g : ↥(glBlockCentralizer (Spin.spinMatrix QM(n, f)) S ε),
      (Spin.spinMatrix QM(n, f) (g : ↥(spinGroup QM(n, f))) :
        Matrix IdxM(n) IdxM(n) (GaloisField 2 f)) * e =
      e * (Spin.spinMatrix QM(n, f) (g : ↥(spinGroup QM(n, f))) :
        Matrix IdxM(n) IdxM(n) (GaloisField 2 f)) := by
    intro g
    have hgS := (Subgroup.mem_comap.mp g.2).1
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute he.1 ?_).eq
    rintro _ ⟨s, hs, rfl⟩
    have h := congrArg Units.val ((Subgroup.mem_centralizer_iff.mp hgS) s hs)
    rw [Units.val_mul, Units.val_mul] at h
    exact h.symm
  have hflag : ∀ R : Subgroup (GL IdxM(n) (GaloisField 2 f)),
      (∀ x ∈ R, x ∈ (Spin.spinMatrix QM(n, f)).range) →
      (∀ x ∈ R, (x : Matrix IdxM(n) IdxM(n) (GaloisField 2 f)) * e =
        e * (x : Matrix IdxM(n) IdxM(n) (GaloisField 2 f))) →
      (∀ x ∈ R, (x : Matrix IdxM(n) IdxM(n) (GaloisField 2 f)) * (1 - ε) = 1 - ε) →
      (∀ x ∈ R, x * x = 1) →
      ∀ U₁ U₂ : Submodule (GaloisField 2 f) (IdxM(n) → GaloisField 2 f),
      U₁ ≤ U₂ →
      (∀ x ∈ R, x ≠ 1 →
        LinearMap.range (Matrix.toLin' (((x : Matrix IdxM(n) IdxM(n) (GaloisField 2 f)) - 1) * e)) =
            U₁ ∧
        LinearMap.ker (Matrix.toLin' ((x : Matrix IdxM(n) IdxM(n) (GaloisField 2 f)) - 1)) ⊓
          LinearMap.range (Matrix.toLin' e) = U₂) →
      GLGeoFlag (some (QuadraticMap.polar QM(n, f))) R := by
    intro R hRj hRc hRfix hinv U₁ U₂ hU hfl
    refine glGeoFlag_polar_of_dualPair hQunit he.2.1 he_star hstar_e ?_ hRc ?_ hinv hU hfl
    · intro x hx m m'
      obtain ⟨y, rfl⟩ := hRj x hx
      exact hiso y _ rfl m m'
    · intro x hx
      rw [← hεeq]
      exact hRfix x hx
  obtain ⟨k', κ, hk', hnorm, hrange, hcent, hflags⟩ :=
    rckRP_slModel_of_slBlock (G := ↥(spinGroup QM(n, f)))
      (Spin.spinMatrix QM(n, f))
      (B := some (QuadraticMap.polar QM(n, f))) hiso he.2.2.1
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
