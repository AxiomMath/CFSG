module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRank
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommRank
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagCommonAux
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Unitary

open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggNSPosPE_one_le_f_aux {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ f + 1) :
    1 ≤ f := by
  by_contra hf
  have hf0 : f = 0 := by omega
  have hp_dvd_two : p ∣ 2 := by simpa [hf0] using hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd_two)

theorem ggNSPosPE_unitaryFieldData_aux {f : ℕ} (hcard : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    UnitaryFieldData 2 f K :=
  ⟨Nat.prime_two, hf, by rw [hcard, ← pow_mul, mul_comm f 2]⟩

theorem ggNSPosPE_scalar_isUnitary_iff {f n : ℕ} (hn : 0 < n) (c : Kˣ) :
    ggIsUnitaryMat (p := 2) (f := f) (GeneralLinearGroup.scalar (Fin n) c) ↔
      (c : K) ^ (2 ^ f + 1) = 1 := by
  have h0 : Fin n := ⟨0, hn⟩
  have key : ∀ x : K, conjTr (unitaryInvolution K 2 f) (Matrix.scalar (Fin n) x) =
      Matrix.scalar (Fin n) (x ^ 2 ^ f) := by
    intro x
    ext i j
    simp only [conjTr, Matrix.scalar_apply, Matrix.transpose_apply, Matrix.map_apply,
      unitaryInvolution_apply]
    by_cases hij : i = j
    · subst hij; simp [iterateFrobenius_def]
    · simp [Matrix.diagonal_apply, Ne.symm hij]
      intro h
      exact absurd h hij
  have hprod : ∀ x y : K, (Matrix.scalar (Fin n) x : Matrix (Fin n) (Fin n) K) * Matrix.scalar (Fin n) y =
      Matrix.scalar (Fin n) (x * y) := by
    intro x y
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  constructor
  · intro h
    rw [ggIsUnitaryMat, GeneralLinearGroup.coe_scalar] at h
    rw [key, hprod] at h
    have h1 := congrFun (congrFun h h0) h0
    simp [Matrix.scalar_apply] at h1
    rw [pow_succ]
    exact h1
  · intro h
    rw [ggIsUnitaryMat, GeneralLinearGroup.coe_scalar, key, hprod, ← pow_succ, h]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply]

theorem ggNSPosPE_isUnitaryMat_pow {f n : ℕ} {g : GL (Fin n) K}
    (hg : ggIsUnitaryMat (p := 2) (f := f) g) (k : ℕ) :
    ggIsUnitaryMat (p := 2) (f := f) (g ^ k) := by
  induction k with
  | zero =>
      unfold ggIsUnitaryMat
      rw [pow_zero, Units.val_one, conjTr_one, Matrix.one_mul]
  | succ k ih =>
      rw [pow_succ]
      exact ggNSPosPE_isUnitaryMat_mul ih hg

theorem ggNSPosPE_norm_one_of_pow_scalar {p f n : ℕ} (hn : 0 < n) {g : GL (Fin n) K} {u : Kˣ}
    (hg : ggIsUnitaryMat (p := 2) (f := f) g) (hgp : g ^ p = GeneralLinearGroup.scalar (Fin n) u) :
    (u : K) ^ (2 ^ f + 1) = 1 :=
  (ggNSPosPE_scalar_isUnitary_iff hn u).mp (hgp ▸ ggNSPosPE_isUnitaryMat_pow hg p)

theorem ggNSPosPE_normalize_lift {G : Type} [Group G] {p f n : ℕ} (hn : 0 < n) {ψ : Su K 2 f n →* G}
    (hdata : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) {b : G} {g : GL (Fin n) K}
    (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) {u c : Kˣ}
    (hgp : g ^ p = GeneralLinearGroup.scalar (Fin n) u) (hc : c ^ p = u) :
    ∃ g' : GL (Fin n) K, GGInducesUnitary (p := 2) (f := f) ψ b g' ∧ g' ^ p = 1 := by
  classical
  have hu : (u : K) ^ (2 ^ f + 1) = 1 := ggNSPosPE_norm_one_of_pow_scalar hn hg.1 hgp
  have hc_norm : (c : K) ^ (2 ^ f + 1) = 1 := by
    refine TableBUD.eq_one_of_fixed_of_pow hdata hpq (TableBUD.norm_pow_fixed hdata (c : K)) ?_
    rw [← pow_mul, mul_comm (2 ^ f + 1) p, pow_mul]
    have hc' : (c : K) ^ p = (u : K) := by rw [← Units.val_pow_eq_pow_val, hc]
    rw [hc', hu]
  set a : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) c⁻¹ with ha
  have haU : ggIsUnitaryMat (p := 2) (f := f) a := by
    rw [ha]
    exact (ggNSPosPE_scalar_isUnitary_iff hn c⁻¹).mpr (by
      rw [Units.val_inv_eq_inv_val, inv_pow, hc_norm, inv_one])
  have hcentral : ∀ y : GL (Fin n) K, a * y = y * a := by
    intro y
    rw [ha]
    exact Matrix.GeneralLinearGroup.scalar_commute c⁻¹ y
  have hcomm : Commute a g := hcentral g
  refine ⟨a * g, ?_, ?_⟩
  · refine ⟨ggNSPosPE_isUnitaryMat_mul haU hg.1, ?_⟩
    intro x
    obtain ⟨y, hy, hact⟩ := hg.2 x
    refine ⟨y, ?_, hact⟩
    rw [hy]
    have h1 : a * (g * (x : GL (Fin n) K) * g⁻¹) = (g * (x : GL (Fin n) K) * g⁻¹) * a := hcentral _
    rw [show ((a * g) * (x : GL (Fin n) K) * (a * g)⁻¹) =
      a * (g * (x : GL (Fin n) K) * g⁻¹) * a⁻¹ by group]
    rw [h1]
    group
  · have hap : a ^ p = GeneralLinearGroup.scalar (Fin n) ((c⁻¹) ^ p) := by
      rw [ha]
      exact (map_pow (GeneralLinearGroup.scalar (Fin n)) c⁻¹ p).symm
    rw [hcomm.mul_pow, hap, hgp, ← map_mul]
    rw [inv_pow, hc, inv_mul_cancel]
    rfl

end CFSG.StandardType

end
