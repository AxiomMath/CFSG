module

public import Certificates.Data.R3E417.G23

public section

namespace CertificateChecks.Batch8176

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.RankThree.PartTwo.Sec4.Res417Five.G23

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)

private theorem decR_oneR_0 : decR oneR = 1 := by
  decide +kernel

private theorem dec14_x0c_1 : dec14 x0c = decR x0r := by
  decide +kernel

private theorem dec14_x1c_2 : dec14 x1c = decR x1r := by
  decide +kernel

private theorem dec14_y0c_3 : dec14 y0c = decR y0r := by
  decide +kernel

private theorem dec14_y1c_4 : dec14 y1c = decR y1r := by
  decide +kernel

private theorem uR_eq_5 :
    mulR (mulR (mulR (n0R ()) (n1R ())) x0r) (mulR (n1iR ()) (n0iR ())) = uLit := by
  decide +kernel

private theorem x13R_eq_6 : mulR (mulR (n1R ()) x0r) (n1iR ()) = x13Lit := by
  decide +kernel

private theorem x12R_eq_7 :
    mulR (mulR (n1R ()) (mulR (mulR (n0R ()) x1r) (n0iR ()))) (n1iR ()) = x12Lit := by
  decide +kernel

private theorem iR_eq_8 : mulR x1r y1r = iLit := by
  decide +kernel

private theorem jR_eq_9 : mulR y1r x1r = jLit := by
  decide +kernel

private theorem cubes_10 : mulR (mulR x1r x1r) x1r = oneR ∧ mulR (mulR uLit uLit) uLit = oneR ∧
    mulR (mulR x13Lit x13Lit) x13Lit = oneR ∧ mulR (mulR x12Lit x12Lit) x12Lit = oneR := by
  decide +kernel

private theorem comms_11 : mulR x13Lit x12Lit = mulR x12Lit x13Lit ∧
    mulR x13Lit uLit = mulR uLit x13Lit ∧ mulR x12Lit uLit = mulR uLit x12Lit ∧
    mulR x13Lit x1r = mulR x1r x13Lit ∧ mulR x12Lit x1r = mulR x1r x12Lit ∧
    mulR uLit x1r = mulR x1r uLit := by
  decide +kernel

private theorem q8_rels_12 : mulR (mulR (mulR iLit iLit) iLit) iLit = oneR ∧
    mulR (mulR (mulR jLit jLit) jLit) jLit = oneR ∧
    mulR jLit iLit = mulR (mulR (mulR iLit iLit) iLit) jLit := by
  decide +kernel

private theorem xa_rels_13 : mulR x1r jLit = mulR iLit x1r ∧
    mulR x1r iLit = mulR (mulR (mulR (mulR iLit jLit) jLit) jLit) x1r := by
  decide +kernel

private theorem u_rels_14 : mulR uLit iLit = mulR iLit uLit ∧
    mulR uLit jLit = mulR jLit uLit := by
  decide +kernel

private theorem xa_i_entries_15 :
    entR (mulR x1r iLit) 1 1 = 0 ∧ entR (mulR iLit x1r) 1 1 = 2 := by
  decide +kernel

private theorem cols_16 :
    (∀ r : Fin 14, decR x1r r 13 = (1 : M14) r 13) ∧
    ¬ (∀ r : Fin 14, decR uLit r 13 = (1 : M14) r 13) ∧
    ¬ (∀ r : Fin 14, decR x13Lit r 5 = (1 : M14) r 5) ∧
    (∀ r : Fin 14, decR x13Lit r 10 = (1 : M14) r 10) ∧
    ¬ (∀ r : Fin 14, decR x12Lit r 10 = (1 : M14) r 10) ∧
    (∀ r : Fin 14, decR x13Lit r 8 = (1 : M14) r 8) ∧
    (∀ r : Fin 14, decR x12Lit r 8 = (1 : M14) r 8) ∧
    ¬ (∀ r : Fin 14, decR uLit r 8 = (1 : M14) r 8) ∧
    (∀ r : Fin 14, decR x13Lit r 3 = (1 : M14) r 3) ∧
    (∀ r : Fin 14, decR x12Lit r 3 = (1 : M14) r 3) ∧
    (∀ r : Fin 14, decR uLit r 3 = (1 : M14) r 3) ∧
    ¬ (∀ r : Fin 14, decR x1r r 3 = (1 : M14) r 3) := by
  decide +kernel

end CertificateChecks.Batch8176

namespace Certificates

open CertificateChecks

local notation "M14" => Matrix (Fin 14) (Fin 14) (ZMod 3)

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.RankThree.PartTwo.Sec4.Res417Five.G23 in
theorem certificate8176 : decR oneR = 1 ∧
    (dec14 x0c = decR x0r ∧ dec14 x1c = decR x1r ∧ dec14 y0c = decR y0r ∧
      dec14 y1c = decR y1r) ∧
    mulR (mulR (mulR (n0R ()) (n1R ())) x0r) (mulR (n1iR ()) (n0iR ())) = uLit ∧
    mulR (mulR (n1R ()) x0r) (n1iR ()) = x13Lit ∧
    mulR (mulR (n1R ()) (mulR (mulR (n0R ()) x1r) (n0iR ()))) (n1iR ()) = x12Lit ∧
    mulR x1r y1r = iLit ∧
    mulR y1r x1r = jLit ∧
    (mulR (mulR x1r x1r) x1r = oneR ∧ mulR (mulR uLit uLit) uLit = oneR ∧
      mulR (mulR x13Lit x13Lit) x13Lit = oneR ∧ mulR (mulR x12Lit x12Lit) x12Lit = oneR) ∧
    (mulR x13Lit x12Lit = mulR x12Lit x13Lit ∧ mulR x13Lit uLit = mulR uLit x13Lit ∧
      mulR x12Lit uLit = mulR uLit x12Lit ∧ mulR x13Lit x1r = mulR x1r x13Lit ∧
      mulR x12Lit x1r = mulR x1r x12Lit ∧ mulR uLit x1r = mulR x1r uLit) ∧
    (mulR (mulR (mulR iLit iLit) iLit) iLit = oneR ∧
      mulR (mulR (mulR jLit jLit) jLit) jLit = oneR ∧
      mulR jLit iLit = mulR (mulR (mulR iLit iLit) iLit) jLit) ∧
    (mulR x1r jLit = mulR iLit x1r ∧
      mulR x1r iLit = mulR (mulR (mulR (mulR iLit jLit) jLit) jLit) x1r) ∧
    (mulR uLit iLit = mulR iLit uLit ∧ mulR uLit jLit = mulR jLit uLit) ∧
    (entR (mulR x1r iLit) 1 1 = 0 ∧ entR (mulR iLit x1r) 1 1 = 2) ∧
    ((∀ r : Fin 14, decR x1r r 13 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 13) ∧
      ¬ (∀ r : Fin 14, decR uLit r 13 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 13) ∧
      ¬ (∀ r : Fin 14, decR x13Lit r 5 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 5) ∧
      (∀ r : Fin 14, decR x13Lit r 10 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 10) ∧
      ¬ (∀ r : Fin 14, decR x12Lit r 10 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 10) ∧
      (∀ r : Fin 14, decR x13Lit r 8 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 8) ∧
      (∀ r : Fin 14, decR x12Lit r 8 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 8) ∧
      ¬ (∀ r : Fin 14, decR uLit r 8 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 8) ∧
      (∀ r : Fin 14, decR x13Lit r 3 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 3) ∧
      (∀ r : Fin 14, decR x12Lit r 3 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 3) ∧
      (∀ r : Fin 14, decR uLit r 3 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 3) ∧
      ¬ (∀ r : Fin 14, decR x1r r 3 = (1 : Matrix (Fin 14) (Fin 14) (ZMod 3)) r 3)) := by
  exact ⟨CertificateChecks.Batch8176.decR_oneR_0, ⟨CertificateChecks.Batch8176.dec14_x0c_1, CertificateChecks.Batch8176.dec14_x1c_2,
      CertificateChecks.Batch8176.dec14_y0c_3, CertificateChecks.Batch8176.dec14_y1c_4⟩, CertificateChecks.Batch8176.uR_eq_5, CertificateChecks.Batch8176.x13R_eq_6,
    CertificateChecks.Batch8176.x12R_eq_7, CertificateChecks.Batch8176.iR_eq_8, CertificateChecks.Batch8176.jR_eq_9, CertificateChecks.Batch8176.cubes_10,
    CertificateChecks.Batch8176.comms_11, CertificateChecks.Batch8176.q8_rels_12, CertificateChecks.Batch8176.xa_rels_13, CertificateChecks.Batch8176.u_rels_14,
    CertificateChecks.Batch8176.xa_i_entries_15, CertificateChecks.Batch8176.cols_16⟩

end Certificates
