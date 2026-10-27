module

public import Certificates.Data.SmithD6E23a
public import Mathlib.Logic.Relation
import Certificates.Kernel.SmithD6Ea.Chain
import Certificates.Kernel.SmithD6Pinned.Holds
import Certificates.Kernel.SmithD6Ea.Facts

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.SmithD6Pinned in
open CFSG.SmithD6 in
theorem certificate38803 : (∀ t < 5, ∃ S : List Nat, S.length = ea7Sizes[t]! ∧ S.Nodup ∧
      ∀ x ∈ S, x < 365211 ∧ Relation.ReflTransGen
        (fun a b => ∃ q, ea7InY (ea7Bases.take t) q = true ∧ tvImg q a = b) ea7Bases[t]! x) ∧
    (ea7I.length = 1578 ∧
      (∀ q ∈ ea7I, ∀ a, ea7IsA a = true → ea7IsA (tvImg q a) = true) ∧
      ea7InX 31 = true ∧ ea7InX 557 = true ∧ ea7InX 1083 = true ∧
      tvImg 557 31 = 1083 ∧ tvImg 1083 31 = 557 ∧
      ea7InX ea7Bases[0]! = true ∧ ea7IsA ea7Bases[0]! = false) :=
  ⟨SmithD6Ea.ea7Chain_of_pinned pinnedModel.lineKeys_toList pinnedModel.lineIdx_of_memB
      pinnedModel.lineKeys_lineIdx,
    SmithD6Ea.ea7OddA_of_pinned pinnedModel.lineKeys_toList pinnedModel.lineIdx_of_memB
      pinnedModel.lineKeys_lineIdx⟩

end Certificates
