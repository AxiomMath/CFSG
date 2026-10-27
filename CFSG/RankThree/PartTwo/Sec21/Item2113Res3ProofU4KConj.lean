module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofU4KDefs
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.KFU (torusSU mem_torusSU_iff diagU diagU_val diagU_mul diagU_pow
  diagU_one diagU_injective det_diagU exists_diagU_of_isDiag exists_unitary_conj_diag
  unitarySU_le_primeFormUnitary)

variable {f : ℕ} {K : Type} [Field K]

theorem bar_det_mul_det_idGram (hU : UnitaryFieldData 2 f K) {g : GL (Fin 4) K}
    (hg : g ∈ primeFormUnitary hU (idGram K 4)) :
    hU.bar (g : Matrix (Fin 4) (Fin 4) K).det * (g : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  have h1 := mem_primeFormUnitary.mp hg
  simp only [idGram, Units.val_one, Matrix.mul_one] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  have h3 : ((g : Matrix (Fin 4) (Fin 4) K).map hU.bar).det =
      hU.bar (g : Matrix (Fin 4) (Fin 4) K).det := by
    rw [RingHom.map_det]
    rfl
  rw [h3] at h2
  exact h2

theorem diagU_mem_primeFormUnitary (hU : UnitaryFieldData 2 f K) {d : Fin 4 → Kˣ}
    (hd : ∀ i, hU.bar (d i : K) * (d i : K) = 1) :
    diagU d ∈ primeFormUnitary hU (idGram K 4) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  rw [diagU_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext hd)

theorem exists_conj_mem_torusSU (hU : UnitaryFieldData 2 f K) (hpq : 3 ∣ 2 ^ f + 1)
    {g : GL (Fin 4) K} (hg : g ∈ unitarySU 2 f K 4) (hg3 : g ^ 3 = 1) :
    ∃ u ∈ unitarySU 2 f K 4, u * g * u⁻¹ ∈ torusSU 3 4 K := by
  classical
  have hle := unitarySU_le_primeFormUnitary (n := 4) hU
  set g' : primeFormUnitary hU (idGram K 4) := ⟨g, hle hg⟩ with hg'
  have hcomm : ∀ x ∈ Subgroup.zpowers g', ∀ y ∈ Subgroup.zpowers g', x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact zpow_mul_comm g' i j
  have hg'3 : g' ^ 3 = 1 := Subtype.ext (by simpa [hg'] using hg3)
  have hpow : ∀ x ∈ Subgroup.zpowers g', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hg'3,
      _root_.one_zpow]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag hU Nat.prime_three hpq (Subgroup.zpowers g') hcomm
    hpow
  obtain ⟨e, he⟩ := exists_diagU_of_isDiag (hP g' (Subgroup.mem_zpowers g'))
  have he' : diagU e = (P : GL (Fin 4) K)⁻¹ * g * P := he
  set δ : Kˣ := Matrix.GeneralLinearGroup.det (P : GL (Fin 4) K) with hδ
  have hδP : (δ : K) = ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det :=
    Matrix.GeneralLinearGroup.val_det_apply _
  have hbarδ : hU.bar (δ : K) * (δ : K) = 1 := by
    rw [hδP]
    exact bar_det_mul_det_idGram hU P.2
  set dδ : Fin 4 → Kˣ := fun i => if i = 0 then δ⁻¹ else 1 with hdδ
  set D : GL (Fin 4) K := diagU dδ with hD
  have hDU : D ∈ primeFormUnitary hU (idGram K 4) := by
    refine diagU_mem_primeFormUnitary hU fun i => ?_
    by_cases hi : i = 0
    · simp only [hdδ, hi, ite_true, Units.val_inv_eq_inv_val, map_inv₀]
      rw [← mul_inv, hbarδ, inv_one]
    · simp [hdδ, hi]
  have hdetD : (D : Matrix (Fin 4) (Fin 4) K).det = ((δ⁻¹ : Kˣ) : K) := by
    rw [hD, det_diagU, Fin.prod_univ_four]
    simp [hdδ]
  set Q : GL (Fin 4) K := (P : GL (Fin 4) K) * D with hQ
  have hQU : Q ∈ unitarySU 2 f K 4 := by
    rw [unitarySU_eq_gramSU hU 4]
    refine ⟨mul_mem P.2 hDU, ?_⟩
    rw [hQ, Units.val_mul, Matrix.det_mul, hdetD, ← hδP, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  have hDe : D⁻¹ * diagU e * D = diagU e := by
    have h1 : D * diagU e = diagU e * D := by rw [hD, diagU_mul, diagU_mul, mul_comm]
    calc D⁻¹ * diagU e * D = D⁻¹ * (diagU e * D) := by group
      _ = D⁻¹ * (D * diagU e) := by rw [h1]
      _ = diagU e := by group
  have hconj : Q⁻¹ * g * Q⁻¹⁻¹ = diagU e := by
    rw [← hDe, he', inv_inv, hQ]
    group
  refine ⟨Q⁻¹, inv_mem hQU, ?_⟩
  have hmem : Q⁻¹ * g * Q⁻¹⁻¹ ∈ unitarySU 2 f K 4 :=
    mul_mem (mul_mem (inv_mem hQU) hg) (inv_mem (inv_mem hQU))
  rw [hconj] at hmem ⊢
  refine mem_torusSU_iff.mpr ⟨e, fun i => ?_, ?_, rfl⟩
  · have h1 : diagU (e ^ 3) = (1 : GL (Fin 4) K) := by
      rw [← diagU_pow, ← hconj, conj_pow, hg3, mul_one, mul_inv_cancel]
    have h2 : e ^ 3 = 1 := diagU_injective (h1.trans diagU_one.symm)
    exact congrFun h2 i
  · have hdet := ((mem_unitarySU_iff hU).mp hmem).1
    rw [det_diagU] at hdet
    exact Units.ext (by rw [Units.coe_prod, Units.val_one]; exact hdet)

theorem item2115U4KConjTorus_holds : Item2115U4KConjTorus := by
  intro f K _ hU _ hpq g hg hg3
  exact exists_conj_mem_torusSU hU hpq hg hg3

end CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof
