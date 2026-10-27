module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeANormal
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

theorem mem_diagImage_of_commute_pTorsion
    {d n p : ℕ} {K : Type} [Field K] [Finite K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφ : UnitTB.Model φ) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (c : L')
    (hc : ∀ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) →
        s ^ p = 1 → c * φ s = φ s * c) :
    ∃ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
        φ s = c := by
  classical
  obtain ⟨s, hs⟩ := hφ.surj c
  have hn0 : n ≠ 0 := by
    have hn1 : 1 ≤ n := hφ.field.one_le
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hmod2 : 2 ^ n % 2 = 0 := by
      have hdvd : 2 ∣ 2 ^ n := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        exact ⟨2 ^ m, by rw [pow_succ']⟩
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hmod : (2 ^ n + 1) % 2 = 1 := by
      rw [Nat.add_mod, hmod2]
    have hdvd : (2 ^ n + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hpq
    have h01 : (0 : ℕ) = 1 := by rw [← hdvd, hmod]
    exact Nat.zero_ne_one h01
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hφ.field hp hpq
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζnorm : ζ ^ (2 ^ n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  have hsd : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
    refine isDiag_of_conj_comm_U hφ.field (by omega) hφ.ker hζnorm hζinv (fun k l _ D hD => ?_)
    have hDp : D ^ p = 1 := by
      refine pow_eq_one_of_diagSU hD (fun i => ?_)
      rw [TypeA.ggPairVec_apply, mul_pow]
      split_ifs <;> simp [hζ.pow_eq_one]
    have hcs : c * φ D = φ D * c := hc D ⟨TypeA.ggPairVec k l ζ, hD⟩ hDp
    have hφsD : φ s * φ D = φ D * φ s := by rw [hs]; exact hcs
    calc MulAut.conj (φ s) * MulAut.conj (φ D)
        = MulAut.conj (φ s * φ D) := by rw [map_mul]
      _ = MulAut.conj (φ D * φ s) := by rw [hφsD]
      _ = MulAut.conj (φ D) * MulAut.conj (φ s) := by rw [map_mul]
  refine ⟨s, ?_, hs⟩
  refine ⟨fun i => ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact hsd hij

theorem mem_diagImage_of_commute_pTorsion_coprime
    {d n p : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hφ : UnitTB.Model φ) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (c : L')
    (hc : ∀ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) →
        s ^ p = 1 → c * φ s = φ s * c) :
    ∃ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
        φ s = c := by
  classical
  obtain ⟨s, hs⟩ := hφ.surj c
  have hn0 : n ≠ 0 := by
    have hn1 : 1 ≤ n := hφ.field.one_le
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hmod2 : 2 ^ n % 2 = 0 := by
      have hdvd : 2 ∣ 2 ^ n := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        exact ⟨2 ^ m, by rw [pow_succ']⟩
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hmod : (2 ^ n + 1) % 2 = 1 := by
      rw [Nat.add_mod, hmod2]
    have hdvd : (2 ^ n + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hpq
    have h01 : (0 : ℕ) = 1 := by rw [← hdvd, hmod]
    exact Nat.zero_ne_one h01
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hφ.field hp hpq
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζnorm : ζ ^ (2 ^ n + 1) = 1 := by
    obtain ⟨k, hk⟩ := hpq
    rw [hk, pow_mul, hζ.pow_eq_one, one_pow]
  have hkey : ∀ k i : Fin d, k ≠ i →
      ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k i = 0 := by
    intro k i hki
    obtain ⟨D, hDm⟩ := LineU.exists_diagSU hφ.field (u := TypeA.ggPairVec i k ζ)
      (LineU.ggPairVec_norm_one hζnorm i k) (TypeA.prod_ggPairVec ζ hζ0)
    have hDp : D ^ p = 1 :=
      LineU.pow_eq_one_of_diagSU hDm (TypeA.pow_ggPairVec hζ.pow_eq_one)
    have hcD : c * φ D = φ D * c := hc D ⟨_, hDm⟩ hDp
    set T : ↥(unitarySU 2 n K d) := s * D * s⁻¹ * D⁻¹ with hT
    have hTker : φ T = 1 := by
      rw [hT, map_mul, map_mul, map_mul, map_inv, map_inv, hs, hcD]
      group
    obtain ⟨c₀, hc₀⟩ := hφ.ker T hTker
    have hc₀d : c₀ ^ d = 1 := by
      have hdet := ((mem_unitarySU_iff hφ.field).mp T.2).1
      rw [hc₀, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
      exact hdet
    have hTD : T * D = s * D * s⁻¹ := by rw [hT]; group
    have hpow : (T * D) ^ p = 1 := by
      rw [hTD, conj_pow, hDp, mul_one, mul_inv_cancel]
    have hc₀p : c₀ ^ p = 1 := by
      have hmat : (((T * D) ^ p : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
          (1 : GL (Fin d) K) := by rw [hpow]; rfl
      have hmat' : (((T : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ^ p = 1 := by
        have := congrArg (fun x : GL (Fin d) K => (x : Matrix (Fin d) (Fin d) K)) hmat
        simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Units.val_pow_eq_pow_val,
          Units.val_mul, Units.val_one] using this
      rw [hc₀, hDm, diagonal_mul_diagonal, diagonal_pow] at hmat'
      have h1 := congrFun (congrFun hmat' i) i
      rw [diagonal_apply_eq, one_apply_eq] at h1
      simp only [Pi.pow_apply] at h1
      rw [mul_pow, TypeA.pow_ggPairVec hζ.pow_eq_one, mul_one] at h1
      exact h1
    have hc₀1 : c₀ = 1 := by
      have h1 : c₀ ^ Nat.gcd p d = 1 := pow_gcd_eq_one.mpr ⟨hc₀p, hc₀d⟩
      rwa [hp.coprime_iff_not_dvd.mpr hpd, pow_one] at h1
    have hT1 : T = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hc₀, hc₀1, diagonal_one]
      rfl
    have hsD : s * D = D * s := by
      have h1 : s * D * s⁻¹ = D := by rw [← hTD, hT1, one_mul]
      calc s * D = (s * D * s⁻¹) * s := by group
        _ = D * s := by rw [h1]
    have hmat : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have := congrArg (fun x : ↥(unitarySU 2 n K d) =>
        ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hsD
      simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have h1 := congrFun (congrFun hmat k) i
    rw [hDm, mul_diagonal, diagonal_mul, TypeA.ggPairVec_apply, TypeA.ggPairVec_apply,
      if_pos rfl, if_neg (Ne.symm hki), if_neg hki, if_pos rfl, mul_one, one_mul] at h1
    by_contra h0
    exact hζinv (mul_left_cancel₀ h0 (by rw [h1, mul_comm]))
  refine ⟨s, ⟨fun i => ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i, ?_⟩, hs⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [diagonal_apply_ne _ hij]
    exact hkey i j hij

end CFSG.StandardType
