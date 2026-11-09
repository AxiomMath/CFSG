module

public import CFSG.LieType.Chevalley.SignStabilizerDataE8Inputs

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CertificateChecks.Batch3952

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem height_tupleVec {τ : Tag} (C : RootCertificate τ) (t : List ℕ) (c : Fin τ.rank → ℤ) :
    height (C.tupleVec t c) = ∑ j, c j * height (C.root (t.getD j 0)) := by
  unfold height RootCertificate.tupleVec
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

@[expose] def dTestH {τ : Tag} (C : RootCertificate τ) (ht : List ℤ) (Δ t : List ℕ) : Bool :=
  Δ.all fun β => decide (0 < ((List.finRange τ.rank).map fun j =>
    C.root β j * ht.getD (t.getD j 0) (-64)).sum)

theorem dTest_eq_dTestH {τ : Tag} (C : RootCertificate τ) (ht : List ℤ)
    (hspec : ∀ k, height (C.root k) = ht.getD k (-64)) (Δ t : List ℕ) :
    C.dTest Δ t = dTestH C ht Δ t := by
  unfold RootCertificate.dTest dTestH
  congr 1
  funext β
  rw [height_tupleVec, Fin.sum_univ_def]
  simp only [hspec]

@[expose] def checkH {τ : Tag} (C : RootCertificate τ) (S : StabCert) (ht : List ℤ) : Bool :=
  S.elems.contains (List.range τ.rank) &&
  S.simple.all (fun β => decide (β < C.roots.length) && decide (0 < height (C.root β)) &&
    decide (Even (maskPairing (listMask S.mask) (C.root β)))) &&
  S.elems.all fun t => (List.finRange τ.rank).all fun i =>
    !(dTestH C ht S.simple (C.tupleImage i t)) || S.elems.contains (C.tupleImage i t)

theorem check_eq_checkH {τ : Tag} (C : RootCertificate τ) (S : StabCert) (ht : List ℤ)
    (hspec : ∀ k, height (C.root k) = ht.getD k (-64)) :
    S.check C = checkH C S ht := by
  unfold StabCert.check checkH
  simp only [dTest_eq_dTestH C ht hspec]

@[expose] def e8HeightTable : List ℤ :=
  [1, 1, 1, 1, 1, 1, 1, 1, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, 3, -2, 3, 3,
    -2, 3, -2, 3, -2, 3, -2, 3, -2, -3, 4, 4, -3, -3, 4, 4, -3, 4, -3, 4, -3, 4, -3, -4, -4, 5, 5,
    -4, -4, 5, 5, 5, -4, 5, -4, 5, -4, -5, -5, 6, 6, 6, -5, -5, -5, 6, 6, 6, -5, 6, -5, -6, -6, -6,
    7, 7, 7, 7, -6, -6, -6, 7, 7, 7, -6, -7, -7, -7, -7, 8, 8, 8, 8, -7, -7, -7, 8, 8, -8, -8, -8,
    -8, 9, 9, 9, 9, -8, -8, 9, 9, -9, -9, -9, -9, 10, 10, 10, 10, 10, -9, -9, 10, -10, -10, -10,
    -10, -10, 11, 11, 11, 11, 11, -10, 11, -11, -11, -11, -11, -11, 12, 12, 12, 12, 12, -11, -12,
    -12, -12, -12, -12, 13, 13, 13, 13, 13, -13, -13, -13, -13, -13, 14, 14, 14, 14, -14, -14, -14,
    -14, 15, 15, 15, 15, -15, -15, -15, -15, 16, 16, 16, 16, -16, -16, -16, -16, 17, 17, 17, 17,
    -17, -17, -17, -17, 18, 18, 18, -18, -18, -18, 19, 19, 19, -19, -19, -19, 20, 20, -20, -20, 21,
    21, -21, -21, 22, 22, -22, -22, 23, 23, -23, -23, 24, -24, 25, -25, 26, -26, 27, -27, 28, -28,
    29, -29]

theorem e8HeightTable_spec : ∀ k, height (e8Certificate.root k) = e8HeightTable.getD k (-64) := by
  intro k
  by_cases hk : k < 240
  · have h : ∀ k : Fin 240, height (e8Certificate.root k) = e8HeightTable.getD k (-64) := by
      decide +kernel
    exact h ⟨k, hk⟩
  · have h1 : e8Certificate.roots.getD k 0 = 0 :=
      List.getD_eq_default _ _ (by have : e8Certificate.roots.length = 240 := (by decide +kernel); omega)
    have h2 : e8HeightTable.getD k (-64) = -64 :=
      List.getD_eq_default _ _ (by have : e8HeightTable.length = 240 := (by decide +kernel); omega)
    rw [RootCertificate.root, h1, h2]
    decide +kernel

private theorem e8SignOrbit_check_0 : OrbitCheck .E8 e8SignReps e8SignOrbit := by
  unfold OrbitCheck
  decide +kernel

private theorem e8SignStab0_check_1 : e8SignStab0.check e8Certificate = true := by
  decide +kernel

private theorem e8SignStab0_passing_2 : (e8SignStab0.passing e8Certificate).length ≤ 1 := by
  decide +kernel

private theorem e8SignStab1_check_3 : e8SignStab1.check e8Certificate = true := by
  rw [check_eq_checkH e8Certificate e8SignStab1 e8HeightTable e8HeightTable_spec]
  decide +kernel

private theorem e8SignStab1_passing_4 : (e8SignStab1.passing e8Certificate).length ≤ 1 := by
  decide +kernel

private theorem e8SignStab2_check_5 : e8SignStab2.check e8Certificate = true := by
  rw [check_eq_checkH e8Certificate e8SignStab2 e8HeightTable e8HeightTable_spec]
  decide +kernel

private theorem e8SignStab2_passing_6 : (e8SignStab2.passing e8Certificate).length ≤ 1 := by
  decide +kernel

end CertificateChecks.Batch3952

namespace Certificates

open CertificateChecks

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem certificate3952 : OrbitCheck .E8 e8SignReps e8SignOrbit
    ∧ e8SignStab0.check e8Certificate = true ∧ (e8SignStab0.passing e8Certificate).length ≤ 1
    ∧ e8SignStab1.check e8Certificate = true ∧ (e8SignStab1.passing e8Certificate).length ≤ 1
    ∧ e8SignStab2.check e8Certificate = true ∧ (e8SignStab2.passing e8Certificate).length ≤ 1 := by
  exact ⟨CertificateChecks.Batch3952.e8SignOrbit_check_0, CertificateChecks.Batch3952.e8SignStab0_check_1,
    CertificateChecks.Batch3952.e8SignStab0_passing_2, CertificateChecks.Batch3952.e8SignStab1_check_3,
    CertificateChecks.Batch3952.e8SignStab1_passing_4, CertificateChecks.Batch3952.e8SignStab2_check_5,
    CertificateChecks.Batch3952.e8SignStab2_passing_6⟩

end Certificates
