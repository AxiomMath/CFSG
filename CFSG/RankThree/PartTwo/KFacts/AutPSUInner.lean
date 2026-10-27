module

public import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
public import CFSG.RankThree.PartTwo.KFacts.AutPSUDet

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem psuConj_mem_range_conj_of_det_eq_pow {A : unitaryIsom3 h} {u : Kˣ}
    (hu : h.norm (u : K) = 1) (hdet : GeneralLinearGroup.det (A : GL (Fin 3) K) = u ^ 3) :
    psuConj h A ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  have hu' : h.norm ((u⁻¹ : Kˣ) : K) = 1 := by
    rw [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv,
      ← UnitaryFieldData.norm, hu, inv_one]
  have hsu := scalar_mem_unitaryIsom3_of_norm hu'
  set B : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A with hB
  have hBI : B ∈ unitaryIsom3 h := mul_mem hsu A.2
  have hdetB : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hdet, inv_pow,
      inv_mul_cancel]
  have hBSU : B ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨?_, hBI⟩
    rw [← GeneralLinearGroup.val_det_apply, hdetB, Units.val_one]
  have hAB : psuConj h A = psuConj h ⟨B, hBI⟩ := by
    have : (⟨B, hBI⟩ : unitaryIsom3 h) = ⟨_, hsu⟩ * A := rfl
    rw [this, map_mul, psuConj_eq_one_of_coe_eq_scalar (A := ⟨_, hsu⟩) rfl, one_mul]
  rw [hAB, show (⟨B, hBI⟩ : unitaryIsom3 h) = ⟨(⟨B, hBSU⟩ : unitarySU p f K 3),
    unitarySU_le_unitaryIsom3 hBSU⟩ from rfl, ← conj_mk_eq_psuConj]
  exact ⟨_, rfl⟩

theorem cube_mem_range_conj_of_mem_psuConj_range {β : MulAut (unitaryPSU h 3)}
    (hβ : β ∈ (psuConj h).range) :
    β ^ 3 ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  obtain ⟨A, rfl⟩ := hβ
  rw [← map_pow]
  refine psuConj_mem_range_conj_of_det_eq_pow (u := GeneralLinearGroup.det (A : GL (Fin 3) K)) ?_
    (by rw [Subgroup.coe_pow, map_pow])
  rw [GeneralLinearGroup.val_det_apply]
  exact norm_det_of_mem_unitaryIsom3 A.2

theorem mem_range_conj_of_mem_psuConj_range_of_coprime {β : MulAut (unitaryPSU h 3)}
    (hβ : β ∈ (psuConj h).range) {m : ℕ} (hm : Nat.Coprime m 3) (hβm : β ^ m = 1) :
    β ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  set S := (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range
  have h3 : β ^ 3 ∈ S := cube_mem_range_conj_of_mem_psuConj_range hβ
  have hab : ((m : ℤ) * Nat.gcdA m 3 + ((3 : ℕ) : ℤ) * Nat.gcdB m 3) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hm, Nat.cast_one]
  have hβ' : β = (β ^ m) ^ Nat.gcdA m 3 * (β ^ 3) ^ Nat.gcdB m 3 := by
    rw [← zpow_natCast β m, ← zpow_natCast β 3, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_add, hab, zpow_one]
  rw [hβ', hβm, _root_.one_zpow, one_mul]
  exact S.zpow_mem h3 _

end CFSG.RankThree.PartTwo.KFacts
