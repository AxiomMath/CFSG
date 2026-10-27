module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.CharacterTheory.PSL2Table
public import CFSG.GH74.GLS.Stage4.Q9.TablesInputs
import Certificates.Kernel.Q9SL.Glue

public section

open CertificateChecks.KernelQ9SL

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.Stage4 in
open CFSG.GH74.GLS.Stage4.Q9 in
open CFSG.GH74.GLS.Stage4.Q9.Tables in
open CFSG CFSG.PSL2Table in
open scoped MatrixGroups in
open Tables in
theorem certificate5102 : (∀ M : SL2, M ∈ allSL2)
    ∧ (∀ j : Fin 7, repIdx (repList j) = j)
    ∧ (∀ M ∈ allSL2, ∃ c ∈ allSL2, IsRepOf (repList (repIdx M)) (conjSL c M))
    ∧ (∀ j : Fin 7, ∀ d ∈ allSL2,
    repIdx (conjSL d (repList j)) = j ∧ repIdx (conjSL d (repList j * minusOne)) = j)
    ∧ (∀ M ∈ allSL2, repIdx (M * minusOne) = repIdx M)
    ∧ (∀ M ∈ allSL2, repIdx (sigmaAut M) = classSwap (repIdx M))
    ∧ (∀ M ∈ allSL2, repIdx (invSL M) = repIdx M)
    ∧ (∀ j : Fin 7,
    (Finset.univ.filter fun M : SL2 => repIdx M = j).card = ![2, 80, 80, 90, 180, 144, 144] j)
    ∧ (∀ M ∈ allSL2, (repIdx M = 0 ↔ M = 1 ∨ M = minusOne))
    ∧ (∀ M ∈ allSL2, ordL (innerL M) = orderFn (repIdx M) (trSL2 M)) :=
  ⟨allSL2_mem, c5102_repList, c5102_spec, c5102_conj, c5102_neg, c5102_sigma, c5102_inv,
    c5102_card, c5102_zero, c5102_ord⟩

end Certificates
