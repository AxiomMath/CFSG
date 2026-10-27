module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGen.Core
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.Open.StatedDefs
import CFSG.RankThree.PartTwo.Sec8.Hering418FU4Blk
import CFSG.SignalizerFunctorTheorem.NonLocal.UData
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGenProof

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open Matrix
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec4.Item419Res3
  (blkSU2L blkSU2L_le nonempty_blkSU2L_mulEquiv sl2_block_facts coe_blkGL2L blk2L)
open CFSG.RankThree.PartTwo.Sec8.Hering418
  (diagU_mem_unitarySU diagU_vec4 bar_inv_mul_inv blk2L_comm_diagonal)
open CFSG.RankThree.PartOne.KFU (diagU diagU_val)

private lemma blk2L_mulVec_e0 {K : Type} [Field K] (Y : Matrix (Fin 2) (Fin 2) K) :
    (blk2L Y) *ᵥ (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) =
      (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) := by
  ext i
  rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
  fin_cases i <;> simp [blk2L]

theorem genLine_statedSU_four {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K)
    (hf : 2 ≤ f) :
    GenLine 3 (StatedSU 4 (2 ^ f) K) (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) := by
  classical
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  set V : Subgroup (GL (Fin 4) K) := blkSU2L f K with hVdef
  have hfacts := sl2_block_facts h (nonempty_blkSU2L_mulEquiv h)
  have hVperf : Group.IsPerfect ↥V := by
    rw [hVdef]
    exact (hfacts.1 hf).1.1
  have hVle : V ≤ StatedSU 4 (2 ^ f) K := by
    rw [hVdef]
    exact blkSU2L_le h
  have hVcard : Nat.card ↥V = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [hVdef]
    exact (hfacts.1 hf).2
  have hcommV : ⁅V, V⁆ = V := Subgroup.isPerfect_iff.mp hVperf
  have h3 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have hmod : 1 ≡ 4 ^ f [MOD 3] := by
      simpa using (by decide : 1 ≡ 4 [MOD 3]).pow f
    have hdvd : 3 ∣ 4 ^ f - 1 := Nat.ModEq.dvd' hmod
    have h42 : (2 ^ f) ^ 2 = 4 ^ f := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm f 2]
    rwa [h42]
  have h3dvd : 3 ∣ Nat.card ↥V := by
    rw [hVcard]
    exact dvd_mul_of_dvd_right h3 (2 ^ f)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨xV, hxVord⟩ := exists_prime_orderOf_dvd_card' (G := ↥V) 3 h3dvd
  let x : GL (Fin 4) K := xV
  have hxV : x ∈ V := xV.2
  have hx3 : x ^ 3 = 1 := by
    have h1 : xV ^ 3 = 1 := by rw [← hxVord]; exact pow_orderOf_eq_one xV
    simpa [x] using congrArg (fun z : ↥V => (z : GL (Fin 4) K)) h1
  have hx1 : x ≠ 1 := by
    intro hx
    have hxV1 : xV = 1 := Subtype.val_injective (by simpa [x] using hx)
    have : orderOf xV = 1 := by rw [hxV1, orderOf_one]
    omega
  obtain ⟨u, hunorm, hune⟩ :=
    CFSG.SignalizerFunctorTheorem.NonLocal.exists_norm_one_unit_ne_inv h
  have hbaru : h.bar (u : K) * (u : K) = 1 := by rw [mul_comm]; exact hunorm
  have hbaruinv : h.bar ((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) = 1 :=
    bar_inv_mul_inv h hbaru
  let d : Fin 4 → Kˣ := ![u, u⁻¹, 1, 1]
  let w : GL (Fin 4) K := diagU d
  have hd : ∀ i, h.bar (d i : K) * (d i : K) = 1 := by
    intro i
    fin_cases i
    · simpa [d] using hbaru
    · simpa [d] using hbaruinv
    · simp [d]
    · simp [d]
  have hp : ∏ i, d i = 1 := by
    rw [Fin.prod_univ_four]
    simp [d]
  have hw_mem : w ∈ StatedSU 4 (2 ^ f) K := by
    simpa [w, d] using diagU_mem_unitarySU h hd hp
  have hwmat : ((w : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K), 1, 1] := by
    simpa [w, d] using diagU_vec4 u u⁻¹ 1 1
  have hcomm : w * x = x * w := by
    have hxV' : x ∈ blkSU2L f K := hxV
    obtain ⟨Y, -, hY⟩ := hxV'
    have hxmat : ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        blk2L (Y : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hY, coe_blkGL2L]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hwmat, hxmat]
    exact blk2L_comm_diagonal (Y : Matrix (Fin 2) (Fin 2) K) (u : K) ((u⁻¹ : Kˣ) : K) 1
  have hwx : w * x * w⁻¹ = x := by
    rw [hcomm]
    group
  rw [GenLine]
  refine ⟨V, x, w, hVle, ?_, hcommV, hxV, hx3, hx1, hw_mem, ?_, ?_⟩
  ·
    intro v hv
    have hv' : v ∈ blkSU2L f K := hv
    obtain ⟨Y, -, hY⟩ := hv'
    rw [← hY, coe_blkGL2L]
    exact blk2L_mulVec_e0 (Y : Matrix (Fin 2) (Fin 2) K)
  ·
    rintro ⟨c, hc⟩
    have h0 : (u : K) = c := by
      have := congrFun hc 0
      simpa [w, d, Matrix.mulVec_diagonal, diagU_val] using this
    have h1 : ((u⁻¹ : Kˣ) : K) = c := by
      have := congrFun hc 1
      simpa [w, d, Matrix.mulVec_diagonal, diagU_val] using this
    exact hune (Units.ext (h0.trans h1.symm)).symm
  ·
    rw [hwx]
    exact Subgroup.mem_zpowers x

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGenProof

end
