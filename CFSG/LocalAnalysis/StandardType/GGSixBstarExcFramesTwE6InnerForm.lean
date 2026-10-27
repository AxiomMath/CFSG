module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Exceptional

private theorem exists_inner_normalForm_of_ringEquiv {K : Type} [Field K] [Finite K] {f p : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {θ : K →+* K} (hθ : σ.toRingHom = θ) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 K θ)) (hα : α ^ p = 1) :
    ∃ (x : ↥(graphFixedRootGroup TwistTag.E6 K θ)) (δ : K ≃+* K), δ ^ p = 1 ∧
      ∀ h, ((α h : _) : ModGL TwistTag.E6.tag K) =
        (x : ModGL TwistTag.E6.tag K) * Units.map (entrywiseHom δ.toRingHom) h *
          (x : ModGL TwistTag.E6.tag K)⁻¹ := by
  subst hθ
  have hgcd : Nat.gcd 3 (2 ^ f + 1) = 1 := by
    have h : Nat.gcd 3 (2 ^ f + 1) ∣ 3 := Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime Nat.prime_three).1 h with h1 | h3'
    · exact h1
    · exact absurd (h3' ▸ Nat.gcd_dvd_right 3 (2 ^ f + 1)) h3
  obtain ⟨-, -, -, -, -, -, hfa, hex, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form (p := 2) (f := f)
      Nat.prime_two hf K hK σ hσ
  obtain ⟨g, u, δ, hgα⟩ := hex α
  have hδp : δ ^ p = 1 := by
    have h1 : (Θ α) ^ p = 1 := by rw [← map_pow, hα, map_one]
    rwa [hΘ α g u δ hgα] at h1
  obtain ⟨y, hy⟩ := CFSG.HardMathSupport.Lang.Coordinator.compatDiagAutHom_mem_inner
    (q := 2 ^ f) hK hσ hgcd u
  refine ⟨g * y, δ, hδp, ?_⟩
  intro h
  have hαy : α = MulAut.conj (g * y) * fieldActor σ δ := by
    rw [hgα, ← hy, ← map_mul]
  rw [hαy]
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    hfa δ h]

theorem exists_inner_normalForm_twistedE6 {f p : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hα : α ^ p = 1) :
    ∃ (x : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (δ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f)), δ ^ p = 1 ∧
      ∀ h, ((α h : _) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          Units.map (entrywiseHom δ.toRingHom) h *
            (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹ :=
  exists_inner_normalForm_of_ringEquiv (θ := frobQ 2 f) hf
    (TwE6Toral.card_galoisField_two_mul f hf) (frobQEquiv hf) (frobQ_apply 2 f) rfl h3 α hα

end ExcFrames

end CFSG.StandardType
