module

public import CFSG.RankThree.PartOne.KE.E7ThreeLatticeInputs
import Certificates.Kernel.E7T3.ChecksK
import CFSG.Certificates.Kernel.E7T3.Sound

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint.Chevalley
  CFSG.KC.E7T3 CFSG.KD.E7T3 CertificateChecks.KernelE7T3K

namespace CertificateChecks.Batch14976

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint.Chevalley
  CFSG.KC.E7T3 CFSG.KD.E7T3 CertificateChecks.KernelE7T3K

theorem data_ok : DataOK s0 s1 s2 s3 roots := by
  have h := ch14976kS0
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, v0⟩, v1⟩, v2⟩, v3⟩ := h
  have hr := ch14976kD0
  rw [beq_iff_eq] at hr
  exact dataOK_of h0 h1 h2 h3 v0 v1 v2 v3 hr ch14976kR0

theorem certs_good : ∀ c ∈ e7T3Certs, c.Good := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have h := ch14976k_good i (lt_of_lt_of_eq hi ch14976k_len.1)
  rw [List.getD_eq_getElem _ _ hi] at h
  exact good_of_goodK data_ok h

theorem flats : ∀ i j : Fin 21, i < j → ∃ c ∈ e7T3Certs, ∀ l : Fin 21,
    (edet3 (e7T3G i) (e7T3G j) (e7T3G l) = (0, 0) ↔ l.val ∈ c.cls) :=
  flats_of_flatsK ((allNK_iff 21 _).2 ch14976k_flats)

end CertificateChecks.Batch14976

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint.Chevalley in
theorem certificate14976 : (CFSG.LieType.Chevalley.laplaceDet 7
      (toMat 7 (lcols 7 e7T3ColsList)) = 1)
    ∧ (lmul 7 (lcols 7 e7T3ColsList) e7T3BinvList = lid 7)
    ∧ (lmulVec 7 e7T3WList e7T3FList = e7T3FList)
    ∧ (RowsOK (fun i : Fin 21 => e7T3G i))
    ∧ (∀ l ∈ Tag.E7.artifactRoots, ∃ i : Fin 21, RowIs l i)
    ∧ (∀ c ∈ e7T3Certs, c.Good)
    ∧ (∀ k : Fin 21, ∃ c ∈ e7T3Certs, c.cls = [k.val])
    ∧ (∀ i j : Fin 21, i < j → ∃ c ∈ e7T3Certs, ∀ l : Fin 21,
        (edet3 (e7T3G i) (e7T3G j) (e7T3G l) = (0, 0) ↔ l.val ∈ c.cls))
    ∧ (∀ c ∈ e7T3Certs, ∀ cm ∈ c.comps, cm.kind = 2 → ∀ l ∈ e7StdRoots (e7T3Nodes 2),
        lmulVec 7 (e7wl (e7T3NegD4 ++ cm.u)) (e7T3Perm 2 cm.rot l) =
          vneg 7 (lmulVec 7 (e7wl cm.u) (e7T3Perm 2 cm.rot l)))
    ∧ (∀ c ∈ e7T3Certs, c.comps.map E7T3Comp.kind ∈
        ([[0], [1], [2], [3], [0, 1]] : List (List ℕ)))
    ∧ (∀ c ∈ e7T3Certs, c.comps.map E7T3Comp.kind = [1] →
        [1, 0, 0, 0, 0, 0, 0] ∉ c.rootList)
    ∧ (∀ c ∈ e7T3Certs, c.rootList.length ≤ 30) :=
  ⟨ch14976k_det, ch14976k_inv, ch14976k_fix, ch14976k_rows, ch14976k_cover,
    CertificateChecks.Batch14976.certs_good, ch14976k_singles, CertificateChecks.Batch14976.flats, ch14976k_negD4, ch14976k_kinds,
    ch14976k_e0, ch14976k_size⟩

end Certificates
