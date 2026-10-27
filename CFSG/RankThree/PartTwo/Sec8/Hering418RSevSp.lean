module

public import CFSG.RankThree.PartTwo.Sec8.Hering418RCrit
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofSp62
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Res417Four (sm6 mk6)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 mat6 mat6_apply mat6_injective card_H6 ε6)
open CFSG.Assembly.RankThreeEven (projSp)
open scoped Matrix

local instance decEqH6 : DecidableEq H6 := inferInstance

@[expose] def z7M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 1, 0, 0, 0; 1, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 1; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0]

@[expose] def z7Mi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 1, 1, 0]

theorem z7_check : sm6 z7M * sm6 z7Mi = 1 ∧ sm6 z7Mi * sm6 z7M = 1 ∧
    (sm6 z7M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 z7M = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def z7 : H6 := mk6 z7M z7Mi z7_check

@[expose] def z7Vec : Fin 6 → ZMod 2 := ![1, 0, 0, 1, 0, 0]

@[expose] def kryM : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 1; 0, 1, 0, 1, 1, 1; 0, 0, 1, 0, 1, 1;
     1, 1, 1, 0, 1, 0; 0, 1, 1, 1, 0, 1; 0, 0, 1, 1, 1, 0]

@[expose] def kryMi : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 1, 0, 0, 1; 1, 1, 1, 1, 1, 1; 1, 1, 0, 1, 0, 0;
     0, 1, 0, 0, 1, 1; 1, 0, 0, 1, 1, 0; 0, 1, 1, 0, 1, 0]

theorem z7M_pow_seven : z7M ^ 7 = 1 := by decide +kernel

theorem kryM_mul_kryMi : kryM * kryMi = 1 := by decide +kernel

theorem kryM_apply : ∀ k j : Fin 6, kryM k j = ((z7M ^ (j : ℕ)) *ᵥ z7Vec) k := by
  have h : ∀ x : Fin 6 × Fin 6, kryM x.1 x.2 = ((z7M ^ (x.2 : ℕ)) *ᵥ z7Vec) x.1 := by
    decide +kernel
  intro k j
  exact h (k, j)

theorem poly_cube_check : ∀ a : Fin 6 → ZMod 2,
    (∑ i : Fin 6, a i • z7M ^ (i : ℕ)) ^ 3 = 1 → ∑ i : Fin 6, a i • z7M ^ (i : ℕ) = 1 := by
  decide +kernel

theorem sum_smul_pow_mulVec (a : Fin 6 → ZMod 2) :
    (∑ i : Fin 6, a i • z7M ^ (i : ℕ)) *ᵥ z7Vec = kryM *ᵥ a := by
  funext r
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, kryM_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem eq_one_of_commute_z7M (C : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hC : C * z7M = z7M * C)
    (h3 : C ^ 3 = 1) : C = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 6 → ZMod 2, a = kryMi *ᵥ (C *ᵥ z7Vec) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 6) (Fin 6) (ZMod 2),
      P = ∑ i : Fin 6, a i • z7M ^ (i : ℕ) := ⟨_, rfl⟩
  have hCc : Commute C z7M := hC
  have hPz : Commute P z7M := by
    rw [hP]
    exact Commute.sum_left _ _ _ fun i _ => ((Commute.refl z7M).pow_left (i : ℕ)).smul_left (a i)
  have hPv : P *ᵥ z7Vec = C *ᵥ z7Vec := by
    rw [hP, sum_smul_pow_mulVec, ha, Matrix.mulVec_mulVec, kryM_mul_kryMi, Matrix.one_mulVec]
  have hcore : ∀ j : ℕ, C *ᵥ ((z7M ^ j) *ᵥ z7Vec) = P *ᵥ ((z7M ^ j) *ᵥ z7Vec) := by
    intro j
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hCc.pow_right j).eq,
      (hPz.pow_right j).eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hPv]
  have hcolK : ∀ (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (r c : Fin 6),
      (M * kryM) r c = (M *ᵥ ((z7M ^ (c : ℕ)) *ᵥ z7Vec)) r := by
    intro M r c
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, kryM_apply]
  have hCK : C * kryM = P * kryM := by
    ext r c
    rw [hcolK, hcolK, hcore]
  have hCP : C = P := by
    calc C = C * (kryM * kryMi) := by rw [kryM_mul_kryMi, mul_one]
      _ = (C * kryM) * kryMi := (Matrix.mul_assoc _ _ _).symm
      _ = (P * kryM) * kryMi := by rw [hCK]
      _ = P * (kryM * kryMi) := Matrix.mul_assoc _ _ _
      _ = P := by rw [kryM_mul_kryMi, mul_one]
  rw [hCP, hP] at h3 ⊢
  exact poly_cube_check a h3

theorem mat6_mk6 (M Mi : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (h : sm6 M * sm6 Mi = 1 ∧ sm6 Mi * sm6 M = 1 ∧
      (sm6 M)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sm6 M = Matrix.fromBlocks 0 1 (-1) 0) :
    mat6 (mk6 M Mi h) = M := by
  rw [mat6_apply]
  show (sm6 M).submatrix ε6 ε6 = M
  unfold sm6
  rw [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

theorem mat6_z7 : mat6 z7 = z7M :=
  mat6_mk6 z7M z7Mi z7_check

theorem z7M_ne_one : z7M ≠ 1 := by
  decide +kernel

theorem orderOf_z7 : orderOf z7 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpow : z7 ^ 7 = 1 := by
    apply mat6_injective
    rw [map_pow, mat6_z7, z7M_pow_seven, map_one]
  have hne : z7 ≠ 1 := by
    intro h
    apply z7M_ne_one
    rw [← mat6_z7, h, map_one]
  exact orderOf_eq_prime hpow hne

theorem noCommute37_H6 : NoCommute37 H6 := by
  intro y z hy hz hyz
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hzc : Nat.card (Subgroup.zpowers z) = 7 := by rw [Nat.card_zpowers, hz]
  have hz7c : Nat.card (Subgroup.zpowers z7) = 7 := by rw [Nat.card_zpowers, orderOf_z7]
  have hzP : IsPGroup 7 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [hzc, pow_one])
  have hz7P : IsPGroup 7 (Subgroup.zpowers z7) :=
    IsPGroup.of_card (n := 1) (by rw [hz7c, pow_one])
  have hzi : ¬ 7 ∣ (Subgroup.zpowers z).index := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers z)
    rw [hzc, card_H6] at h
    have h' : (Subgroup.zpowers z).index = 207360 := by omega
    rw [h']
    norm_num
  have hz7i : ¬ 7 ∣ (Subgroup.zpowers z7).index := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers z7)
    rw [hz7c, card_H6] at h
    have h' : (Subgroup.zpowers z7).index = 207360 := by omega
    rw [h']
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H6 (hzP.toSylow hzi) (hz7P.toSylow hz7i)
  have hmap : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z7 := by
    have h1 : ((g • hzP.toSylow hzi : Sylow 7 H6) : Subgroup H6) =
        ((hz7P.toSylow hz7i : Sylow 7 H6) : Subgroup H6) := by
      rw [hg]
    rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at h1
    exact h1
  have hz7mem : z7 ∈ (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom := by
    rw [hmap]
    exact Subgroup.mem_zpowers z7
  obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz7mem
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hgz : g * z ^ j * g⁻¹ = z7 := hxz
  have hyzc : Commute y z := hyz
  have hcomm : Commute (g * y * g⁻¹) (g * z ^ j * g⁻¹) := by
    unfold Commute SemiconjBy
    calc g * y * g⁻¹ * (g * z ^ j * g⁻¹) = g * (y * z ^ j) * g⁻¹ := by group
      _ = g * (z ^ j * y) * g⁻¹ := by rw [(hyzc.zpow_right j).eq]
      _ = g * z ^ j * g⁻¹ * (g * y * g⁻¹) := by group
  rw [hgz] at hcomm
  have hy3 : y ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy] at h
  have hy'3 : (g * y * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  have hC : mat6 (g * y * g⁻¹) * z7M = z7M * mat6 (g * y * g⁻¹) := by
    rw [← mat6_z7, ← map_mul, ← map_mul, hcomm.eq]
  have hC3 : mat6 (g * y * g⁻¹) ^ 3 = 1 := by
    rw [← map_pow, hy'3, map_one]
  have hC1 := eq_one_of_commute_z7M _ hC hC3
  have hy'1 : g * y * g⁻¹ = 1 := mat6_injective (by rw [hC1, map_one])
  have hy1 : y = 1 := by
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [hy'1, mul_one, inv_mul_cancel]
  rw [hy1, orderOf_one] at hy
  norm_num at hy

theorem noCommute37_projSp : NoCommute37 (projSp 3 (GaloisField 2 1)) := by
  intro y z hy hz hyz
  refine noCommute37_H6 (Item434SmallTwoIII.sp62Equiv y) (Item434SmallTwoIII.sp62Equiv z)
    ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact hy
  · rw [MulEquiv.orderOf_eq]
    exact hz
  · rw [← map_mul, ← map_mul, hyz]

end CFSG.RankThree.PartTwo.Sec8.Hering418
