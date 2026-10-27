module

public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import Certificates.Certificate3159
public import Certificates.Certificate15954

public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native CFSG.Blueprint


theorem five_facts :
    xFive ^ 5 = 1 ∧ xFive ≠ 1 ∧ hFive ^ 8 = 1 ∧ hFive ^ 4 ≠ 1 ∧ wFive ^ 40 = 1 ∧
      wFive ^ 20 ≠ 1 ∧ wFive ^ 8 ≠ 1 ∧ (∀ i, qFive i ^ 5 = 1 ∧ qFive i ≠ 1) ∧ zFive ^ 5 = 1 ∧
      zFive ≠ 1 ∧ (∀ i, qFive i * zFive = zFive * qFive i) ∧
      (∀ i j : Fin 4, i < j →
        bcomm (qFive i) (qFive j) = zFive ^ ((fiveCommRows.getD i []).getD j 0)) ∧
      xFive * zFive = zFive * xFive ∧
      ∀ i : Fin 4, xFive⁻¹ * qFive i * xFive =
        (List.ofFn fun j => qFive j ^ (fiveActRows.getD i []).getD j 0).prod *
          zFive ^ fiveActC.getD i 0 :=
  Certificates.certificate3159

theorem orderOf_xFive :
    orderOf xFive = 5 := by
  obtain ⟨h5, h1, -⟩ := five_facts
  exact orderOf_of_prime (by norm_num) ⟨h5, h1⟩

theorem orderOf_hFive :
    orderOf hFive = 8 := by
  obtain ⟨-, -, h8, h4, -⟩ := five_facts
  exact orderOf_eq_of_exact (rs := [2]) (by norm_num) h8 (by simpa using h4) (by decide)

theorem orderOf_wFive :
    orderOf wFive = 40 := by
  obtain ⟨-, -, -, -, h40, h20, h8, -⟩ := five_facts
  exact orderOf_eq_of_exact (rs := [2, 5]) (by norm_num) h40 (by simpa using ⟨h20, h8⟩)
    (by decide)

theorem orderOf_qFive
    (i : Fin 4) : orderOf (qFive i) = 5 := by
  obtain ⟨-, -, -, -, -, -, -, hq, -⟩ := five_facts
  exact orderOf_of_prime (by norm_num) (hq i)

theorem orderOf_zFive :
    orderOf zFive = 5 := by
  obtain ⟨-, -, -, -, -, -, -, -, hz5, hz1, -⟩ := five_facts
  exact orderOf_of_prime (by norm_num) ⟨hz5, hz1⟩

theorem bcomm_qFive
    (i j : Fin 4) : bcomm (qFive i) (qFive j) = zFive ^ (MFive i j).val := by
  obtain ⟨-, -, -, -, -, -, -, -, hz5, -, -, hc, -⟩ := five_facts
  exact bcomm_all hz5 Certificates.certificate15954.2.2.2.2.1
    Certificates.certificate15954.2.2.2.2.2.1 Certificates.certificate15954.2.2.2.2.2.2
    hc i j

theorem comm_qFive_zFive
    (i : Fin 4) : qFive i * zFive = zFive * qFive i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hqz, -⟩ := five_facts
  exact hqz i

theorem xFive_mul_zFive :
    xFive * zFive = zFive * xFive := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hxz, -⟩ := five_facts
  exact hxz

theorem conj_qFive (i : Fin 4) :
    xFive⁻¹ * qFive i * xFive =
      (List.ofFn fun j => qFive j ^ (fiveActRows.getD i []).getD j 0).prod *
        zFive ^ fiveActC.getD i 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hact⟩ := five_facts
  exact hact i

theorem pinned_B_five_primary_exact_relations :
    orderOf xFive = 5 ∧ orderOf hFive = 8 ∧ orderOf wFive = 40 ∧ (∀ i, orderOf (qFive i) = 5) ∧
      orderOf zFive = 5 ∧ (∀ i, bcomm (qFive i) zFive = 1) ∧ xFive⁻¹ * zFive * xFive = zFive ∧
      (∀ i j, bcomm (qFive i) (qFive j) = zFive ^ (MFive i j).val) ∧
      MFive = !![0, 1, 4, 1; 4, 0, 0, 2; 1, 0, 0, 1; 4, 3, 4, 0] ∧
      xFive⁻¹ * qFive 0 * xFive = qFive 2 ∧ xFive⁻¹ * qFive 1 * xFive = qFive 3 ∧
      xFive⁻¹ * qFive 2 * xFive = qFive 0 ^ 2 * qFive 1 ^ 2 * qFive 2 ^ 4 * qFive 3 ^ 2 ∧
      xFive⁻¹ * qFive 3 * xFive = qFive 0 * qFive 1 ^ 4 * qFive 2 ^ 4 * zFive := by
  have hxz : xFive⁻¹ * zFive * xFive = zFive := by
    rw [mul_assoc, ← xFive_mul_zFive, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨orderOf_xFive, orderOf_hFive, orderOf_wFive, orderOf_qFive, orderOf_zFive,
    fun i => bcomm_eq_one_iff.2 (comm_qFive_zFive i), hxz, bcomm_qFive, MFive_eq,
    ?_, ?_, ?_, ?_⟩
  · have := conj_qFive 0
    simp [List.ofFn_succ, fiveActRows, fiveActC] at this
    exact this
  · have := conj_qFive 1
    simp [List.ofFn_succ, fiveActRows, fiveActC] at this
    exact this
  · have := conj_qFive 2
    simp [List.ofFn_succ, fiveActRows, fiveActC, mul_assoc] at this
    simp only [mul_assoc]
    exact this
  · have := conj_qFive 3
    simp [List.ofFn_succ, fiveActRows, fiveActC, mul_assoc] at this
    simp only [mul_assoc]
    exact this

end CFSG.Monster.B.Pinned
