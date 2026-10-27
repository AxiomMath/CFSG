module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
import CFSG.RankThree.PartTwo.Sec4.Item413AutU3
import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndexProof
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofFieldTools

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Res

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars StatedSU)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

theorem cube_of_pow_two_pow (k : ℕ) : ∃ a b : ℤ, ∀ {M : Type*} [CommGroup M] {x y : M},
    x ^ 2 ^ k = y ^ 3 → (y ^ a * x ^ b) ^ 3 = x := by
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) ((3 : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left k (by norm_num))
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨a, b, fun {M} _ {x y} hxy => ?_⟩
  have hxy' : x ^ ((2 ^ k : ℕ) : ℤ) = y ^ ((3 : ℕ) : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact hxy
  have h1 : (y ^ a * x ^ b) ^ 3 = (y ^ ((3 : ℕ) : ℤ)) ^ a * x ^ (b * ((3 : ℕ) : ℤ)) := by
    rw [← zpow_natCast (y ^ a * x ^ b), mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul,
      mul_comm a]
  rw [h1, ← hxy', ← zpow_mul, ← zpow_add, mul_comm ((2 ^ k : ℕ) : ℤ) a, hab, zpow_one]

variable {K : Type} [Field K]

theorem isInnerAut_commutator_linear [Finite K] (α β : MulAut (projectiveSL 3 K)) {k : ℕ}
    (hk : (α * β * α⁻¹ * β⁻¹) ^ 2 ^ k = 1) : IsInnerAut (α * β * α⁻¹ * β⁻¹) := by
  have hmem := OuterDerived.commutator_mem_linearAutGroup (le_refl 3) α β
  rw [Sec4.linearAutGroup_three_eq_range] at hmem
  obtain ⟨A, hA⟩ := hmem
  have hAk : A ^ 2 ^ k ∈ StatedScalars (Fin 3) K := by
    rw [← Sec4.ker_conjAut_three, MonoidHom.mem_ker, map_pow, hA, hk]
  obtain ⟨c, hc⟩ := hAk
  have hdet : GeneralLinearGroup.det A ^ 2 ^ k = c ^ 3 := by
    rw [← map_pow, ← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := cube_of_pow_two_pow k
  rw [← hA]
  exact Sec14.Item148Rank.isInnerAut_conjAut_of_det_eq_cube148 A (hab hdet)

variable {p f : ℕ}

theorem pow_succ_eq_one_of_scalar_mem (h : UnitaryFieldData p f K) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h) : c ^ (p ^ f + 1) = 1 := by
  rw [mem_unitaryIsom3] at hc
  have h00 := congrFun (congrFun hc 0) 0
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply,
    Fin.sum_univ_three, UnitaryFieldData.bar_apply] at h00
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
  simpa using h00

theorem isInnerAut_commutator_unitary (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    (α β : MulAut (unitaryPSU h 3)) {k : ℕ} (hk : (α * β * α⁻¹ * β⁻¹) ^ 2 ^ k = 1) :
    IsInnerAut (α * β * α⁻¹ * β⁻¹) := by
  obtain ⟨A, hA⟩ := commutator_mem_psuConj_range h hq2 α β
  have hAk : ((A ^ 2 ^ k : unitaryIsom3 h) : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    rw [← Sec4.psuConj_eq_one_iff, map_pow, hA, hk]
  obtain ⟨c, hc⟩ := hAk
  have hcmem : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h := by
    rw [hc]
    exact (A ^ 2 ^ k).2
  have hcn : c ^ (p ^ f + 1) = 1 := pow_succ_eq_one_of_scalar_mem h hcmem
  have hdn : GeneralLinearGroup.det (A : GL (Fin 3) K) ^ (p ^ f + 1) = 1 :=
    det_pow_succ_eq_one_of_mem h A.2
  have hdet : GeneralLinearGroup.det (A : GL (Fin 3) K) ^ 2 ^ k = c ^ 3 := by
    rw [← map_pow, show (A : GL (Fin 3) K) ^ 2 ^ k = ((A ^ 2 ^ k : unitaryIsom3 h) :
      GL (Fin 3) K) from rfl, ← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  obtain ⟨a, b, hab⟩ := cube_of_pow_two_pow k
  have hu3 := hab hdet
  have hun : (c ^ a * GeneralLinearGroup.det (A : GL (Fin 3) K) ^ b) ^ (p ^ f + 1) = 1 := by
    rw [mul_pow, ← zpow_natCast, ← zpow_natCast (GeneralLinearGroup.det _ ^ b), ← zpow_mul,
      ← zpow_mul, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hcn,
      hdn, one_zpow, one_zpow, one_mul]
  rw [← hA]
  exact isInnerAut_psuConj_of_det_eq_pow_three h A hu3 hun

theorem isInnerAut_commutator_of_two_pow {X : Type} [Group X] {π : Bool}
    (hK : Sec4.PiField π p f K) (hq2 : 2 < p ^ f)
    (e : X ≃* projImage (Sec4.slPi π 3 (p ^ f) K)) (α β : MulAut X) {k : ℕ}
    (hk : (α * β * α⁻¹ * β⁻¹) ^ 2 ^ k = 1) : IsInnerAut (α * β * α⁻¹ * β⁻¹) := by
  have := hK.finite
  cases π
  ·
    have hU : UnitaryFieldData p f K := hK.unitary
    let φ : X ≃* unitaryPSU hU 3 := e.trans
      ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
        (StatedSU 3 (p ^ f) K)).symm.trans (unitaryPSUEquiv hU (by norm_num)).symm)
    rw [← isInnerAut_congr φ, map_mul, map_mul, map_mul, map_inv, map_inv]
    refine isInnerAut_commutator_unitary hU hq2 _ _ (k := k) ?_
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hk, map_one]
  ·
    let φ : X ≃* projectiveSL 3 K := e.trans (Sec4.pslEquivProjective (p ^ f) K)
    rw [← isInnerAut_congr φ, map_mul, map_mul, map_mul, map_inv, map_inv]
    refine isInnerAut_commutator_linear _ _ (k := k) ?_
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hk, map_one]

end CFSG.RankThree.PartTwo.Sec16.Proof1613Res
