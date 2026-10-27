module

public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import Certificates.Certificate16008
public import Certificates.Certificate3161

public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native CFSG.Blueprint

theorem three_facts :
    xThree ^ 40 = 1 ∧ xThree ^ 20 ≠ 1 ∧ xThree ^ 8 ≠ 1 ∧ hThree ^ 8 = 1 ∧ hThree ^ 4 ≠ 1 ∧
      (∀ i, qThree i ^ 3 = 1 ∧ qThree i ≠ 1) ∧ zThree ^ 3 = 1 ∧ zThree ≠ 1 ∧
      (∀ i, qThree i * zThree = zThree * qThree i) ∧
      (∀ i j : Fin 8, i < j →
        bcomm (qThree i) (qThree j) = zThree ^ ((threeCommRows.getD i []).getD j 0)) ∧
      xThree⁻¹ * zThree * xThree = zThree * zThree ∧
      hThree⁻¹ * zThree * hThree = zThree * zThree ∧
      (∀ i : Fin 8, xThree⁻¹ * qThree i * xThree =
        (List.ofFn fun j => qThree j ^ (threeXRows.getD i []).getD j 0).prod *
          zThree ^ threeCVec.getD i 0) ∧
      ∀ i : Fin 8, hThree⁻¹ * qThree i * hThree =
        (List.ofFn fun j => qThree j ^ (threeYRows.getD i []).getD j 0).prod *
          zThree ^ threeDVec.getD i 0 :=
  Certificates.certificate3161

theorem orderOf_xThree :
    orderOf xThree = 40 := by
  obtain ⟨h40, h20, h8, -⟩ := three_facts
  exact orderOf_eq_of_exact (rs := [2, 5]) (by norm_num) h40 (by simpa using ⟨h20, h8⟩)
    (by decide)

theorem orderOf_hThree :
    orderOf hThree = 8 := by
  obtain ⟨-, -, -, h8, h4, -⟩ := three_facts
  exact orderOf_eq_of_exact (rs := [2]) (by norm_num) h8 (by simpa using h4) (by decide)

theorem orderOf_qThree
    (i : Fin 8) : orderOf (qThree i) = 3 := by
  obtain ⟨-, -, -, -, -, hq, -⟩ := three_facts
  exact orderOf_of_prime (by norm_num) (hq i)

theorem orderOf_zThree :
    orderOf zThree = 3 := by
  obtain ⟨-, -, -, -, -, -, hz3, hz1, -⟩ := three_facts
  exact orderOf_of_prime (by norm_num) ⟨hz3, hz1⟩

theorem comm_qThree_zThree
    (i : Fin 8) : qThree i * zThree = zThree * qThree i := by
  obtain ⟨-, -, -, -, -, -, -, -, hqz, -⟩ := three_facts
  exact hqz i

theorem bcomm_qThree
    (i j : Fin 8) :
    bcomm (qThree i) (qThree j) = zThree ^ (MThree i j).val := by
  obtain ⟨-, -, -, -, -, -, hz3, -, -, hc, -⟩ := three_facts
  exact bcomm_all hz3 (by exact Certificates.certificate16008.2.2.2.2.2.2.2.1)
    (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.1)
    (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.1) hc i j

theorem zThree_conj_x :
    xThree⁻¹ * zThree * xThree = zThree ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := three_facts
  rw [h, sq]

theorem zThree_conj_h :
    hThree⁻¹ * zThree * hThree = zThree ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := three_facts
  rw [h, sq]

theorem XThree_val (i j : Fin 8) :
    (XThree i j).val = (threeXRows.getD i []).getD j 0 :=
  rowsMat_val (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.1 i j)

theorem YThree_val (i j : Fin 8) :
    (YThree i j).val = (threeYRows.getD i []).getD j 0 :=
  rowsMat_val (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.2.1 i j)

theorem cThree_val (i : Fin 8) :
    (cThree i).val = threeCVec.getD i 0 := by
  rw [cThree, rowsVec, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.2.2.1 i)]

theorem dThree_val (i : Fin 8) :
    (dThree i).val = threeDVec.getD i 0 := by
  rw [dThree, rowsVec, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by exact Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)]

theorem conj_x_qThree
    (i : Fin 8) :
    xThree⁻¹ * qThree i * xThree =
      (List.ofFn fun j => qThree j ^ (XThree i j).val).prod * zThree ^ (cThree i).val := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := three_facts
  rw [h i]
  simp only [XThree_val, cThree_val]

theorem conj_h_qThree
    (i : Fin 8) :
    hThree⁻¹ * qThree i * hThree =
      (List.ofFn fun j => qThree j ^ (YThree i j).val).prod * zThree ^ (dThree i).val := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := three_facts
  rw [h i]
  simp only [YThree_val, dThree_val]

theorem MThree_mul_inv :
    MThree * rowsMat 3 8 threeCommInvRows = 1 :=
  Certificates.certificate16008.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem isUnit_det_MThree : IsUnit MThree.det := by
  have h := congrArg Matrix.det MThree_mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

theorem isUnit_MThree :
    IsUnit MThree := (Matrix.isUnit_iff_isUnit_det _).2 isUnit_det_MThree

theorem rank_MThree : MThree.rank = 8 := by
  rw [Matrix.rank_of_isUnit _ isUnit_MThree, Fintype.card_fin]

theorem pinned_B_three_primary_exact_relations :
    orderOf xThree = 40 ∧ orderOf hThree = 8 ∧ (∀ i, orderOf (qThree i) = 3) ∧
      orderOf zThree = 3 ∧ (∀ i, bcomm (qThree i) zThree = 1) ∧
      (∀ i j, bcomm (qThree i) (qThree j) = zThree ^ (MThree i j).val) ∧ MThree.rank = 8 ∧
      xThree⁻¹ * zThree * xThree = zThree ^ 2 ∧ hThree⁻¹ * zThree * hThree = zThree ^ 2 ∧
      (∀ i, xThree⁻¹ * qThree i * xThree =
        (List.ofFn fun j => qThree j ^ (XThree i j).val).prod * zThree ^ (cThree i).val) ∧
      ∀ i, hThree⁻¹ * qThree i * hThree =
        (List.ofFn fun j => qThree j ^ (YThree i j).val).prod * zThree ^ (dThree i).val :=
  ⟨orderOf_xThree, orderOf_hThree, orderOf_qThree, orderOf_zThree,
    fun i => bcomm_eq_one_iff.2 (comm_qThree_zThree i), bcomm_qThree, rank_MThree,
    zThree_conj_x, zThree_conj_h, conj_x_qThree, conj_h_qThree⟩

end CFSG.Monster.B.Pinned
