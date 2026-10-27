module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoResidualSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputL3Overgroup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoRArgument
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoO2Ky
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem caseTwoG2_of_uniqueTwoLocalKy (hL3 : L3Overgroup)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hP1 : t.UniqueTwoLocalKy) : t.CaseTwoG2 := by
  intro p hp h76 hN _hIIa hZ _hrank hO hX
  by_contra hHnot
  have hXnot : ¬ t.Xz ≤ c.S.M := fun hXle =>
    hHnot ((t.centralizer_y_le_iff hK32 hGA hSp hK332 hOut hp hN hZ).mpr hXle)
  have hKyX : t.Ky ≤ t.Xz := t.Ky_le_Xz hK32 hGA hSp
  have hKZ : ⁅CFSG.Open.pCoreOf 2 t.Kyhat, t.Zhat⁆ ≠ ⊥ := fun hbot => by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hO2X : CFSG.Open.pCoreOf 2 t.Xz = ⊥ := by
      by_contra hne
      have hV2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 t.Xz) :=
        CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 t.Xz
      have hH2L : CFSG.Open.IsTwoLocal
          (Subgroup.normalizer (CFSG.Open.pCoreOf 2 t.Xz : Set G)) :=
        ⟨CFSG.Open.pCoreOf 2 t.Xz, hne, hV2, rfl⟩
      have hXnorm : t.Xz ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 t.Xz : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 t.Xz
      exact hXnot (hXnorm.trans (hP1 _ hH2L (hKyX.trans hXnorm)))
    have hN2 : IsPGroup 2 ↥t.d.N := by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl]
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 t.d.M
    have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
    have hOzNorm : (t.Oz.subgroupOf t.Xz).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer t.Oz_le_Xz).mpr
        (CFSG.ABGLocalTools.le_normalizer_map_subtype t.Xz (CFSG.pPrimeCore 3 ↥t.Xz))
    have hNOz2 : IsPGroup 2 ↥(t.d.N ⊓ t.Oz) := hN2.to_le inf_le_left
    have hNOzNorm : ((t.d.N ⊓ t.Oz).subgroupOf t.Oz).Normal := by
      refine Subgroup.Normal.mk fun x hx g => ?_
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have hxg : ((g * x * g⁻¹ : ↥t.Oz) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl
      rw [hxg]
      exact Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_normalizer_iff.mp (hMN (hO g.2)) (x : G)).mp hx.1,
          (g * x * g⁻¹).2⟩
    have hNOzle : t.d.N ⊓ t.Oz ≤ CFSG.Open.pCoreOf 2 t.Oz :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right hNOzNorm hNOz2
    have hsubOX : CFSG.Open.IsSubnormal t.Oz t.Xz :=
      CFSG.Open.IsSubnormal.step t.Oz_le_Xz hOzNorm (CFSG.Open.IsSubnormal.refl t.Xz)
    have hcore : CFSG.Open.pCoreOf 2 t.Oz ≤ CFSG.Open.pCoreOf 2 t.Xz :=
      CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hsubOX
    have hNOzbot : t.d.N ⊓ t.Oz = ⊥ := by
      rw [eq_bot_iff]
      exact hNOzle.trans (hcore.trans (le_of_eq hO2X))
    have hKyO : t.Ky ⊓ t.Oz = ⊥ := by
      have hle : t.Ky ⊓ t.Oz ≤ t.d.N ⊓ t.Oz :=
        le_inf (t.Ky_inf_Oz_le hK32 hGA hSp) inf_le_right
      exact eq_bot_iff.mpr (hle.trans (le_of_eq hNOzbot))
    have hmapbot : (⁅(t.Ky ⊓ t.d.N).subgroupOf t.Xz, t.Z.subgroupOf t.Xz⁆).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) = ⊥ := by
      have h1 : ((t.Ky ⊓ t.d.N).subgroupOf t.Xz).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) = t.O2Kyhat := rfl
      have h2 : (t.Z.subgroupOf t.Xz).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) = t.Zhat := rfl
      rw [Subgroup.map_commutator, h1, h2, ← t.pCoreOf_Kyhat hK32 hGA hSp, hbot]
    have hcomm : ⁅t.Ky ⊓ t.d.N, t.Z⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.mpr fun a ha z hz => ?_
      have haK : a ∈ t.Ky := ha.1
      have haX : a ∈ t.Xz := hKyX haK
      have hzX : z ∈ t.Xz := t.Z_le_Xz hz
      have hzK : z ∈ t.Ky := t.Dz_le_Ky (t.Z_le_Dz hz)
      have hmemX : ⁅a, z⁆ ∈ t.Xz :=
        t.Xz.mul_mem (t.Xz.mul_mem (t.Xz.mul_mem haX hzX) (t.Xz.inv_mem haX))
          (t.Xz.inv_mem hzX)
      have hsubA : (⟨a, haX⟩ : ↥t.Xz) ∈ (t.Ky ⊓ t.d.N).subgroupOf t.Xz :=
        Subgroup.mem_subgroupOf.mpr ha
      have hsubZ : (⟨z, hzX⟩ : ↥t.Xz) ∈ t.Z.subgroupOf t.Xz :=
        Subgroup.mem_subgroupOf.mpr hz
      have hπ : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)
          ⁅(⟨a, haX⟩ : ↥t.Xz), ⟨z, hzX⟩⁆ = 1 := by
        have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)
            ⁅(⟨a, haX⟩ : ↥t.Xz), ⟨z, hzX⟩⁆ ∈ (⊥ : Subgroup t.Xhat) := by
          rw [← hmapbot]
          exact Subgroup.mem_map_of_mem _ (Subgroup.commutator_mem_commutator hsubA hsubZ)
        simpa using hmem
      have hker : (⟨⁅a, z⁆, hmemX⟩ : ↥t.Xz) ∈ CFSG.pPrimeCore 3 ↥t.Xz := by
        have h1 := (QuotientGroup.eq_one_iff
          (N := CFSG.pPrimeCore 3 ↥t.Xz) ⁅(⟨a, haX⟩ : ↥t.Xz), ⟨z, hzX⟩⁆).mp hπ
        have heq : (⁅(⟨a, haX⟩ : ↥t.Xz), ⟨z, hzX⟩⁆ : ↥t.Xz) = ⟨⁅a, z⁆, hmemX⟩ := by
          refine Subtype.ext ?_
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        rwa [heq] at h1
      have hmemO : ⁅a, z⁆ ∈ t.Oz :=
        Subgroup.mem_map.mpr ⟨⟨⁅a, z⁆, hmemX⟩, hker, rfl⟩
      have hmemKy : ⁅a, z⁆ ∈ t.Ky :=
        t.Ky.mul_mem (t.Ky.mul_mem (t.Ky.mul_mem haK hzK) (t.Ky.inv_mem haK))
          (t.Ky.inv_mem hzK)
      have hmem : ⁅a, z⁆ ∈ t.Ky ⊓ t.Oz := Subgroup.mem_inf.mpr ⟨hmemKy, hmemO⟩
      rw [hKyO] at hmem
      simpa using hmem
    exact t.commutator_Ky_inf_N_Z_ne_bot hcomm
  obtain ⟨g, hgY, r, hr, hr5, hgord, hrdvd, hgcent⟩ := hL3 t.Xhat hX t.Zhat t.Yhat t.Kyhat
    t.card_Zhat (t.normalizer_Zhat_le_Yhat hp hN hZ) t.Yhat_le_normalizer_Kyhat
    (t.commutator_Kyhat hK32 hGA hSp) t.Zhat_le_Kyhat hKZ
  exact hHnot (t.centralizer_y_le_of_centralizes_Kyhat hK32 hGA hSp hSE hr hr5 hrdvd hgY hgord
    fun k hk => by simpa [t.pCoreOf_Kyhat hK32 hGA hSp] using hgcent k hk)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
