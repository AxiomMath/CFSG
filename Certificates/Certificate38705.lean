module

public import Certificates.Data.SmithD6Stab
public import Mathlib.Logic.Relation
import all Certificates.Kernel.SmithD6StabTree.Glue
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithD6 CertificateChecks.SmithD6Pinned

open CFSG.SmithD6 in
theorem certificate38705 : (∀ c < 6, stabRep c < 365211 ∧ stabCls (stabRep c) = c) ∧
    (∀ g < stabGens.size, stabGens[g]! < 365211 ∧ tvImg stabGens[g]! 0 = 0) ∧
    (∀ v < 365211, Relation.ReflTransGen (fun u v => ∃ g < stabGens.size, tvImg stabGens[g]! u = v)
      (stabRep (stabCls v)) v) ∧
    chkStabCard = true ∧ chkStabNc = true ∧ chkStabOrd = true := by
  have hK := pinnedModel.lineKeys_toList
  have hL := pinnedModel.lineIdx_of_memB
  refine ⟨fun c hc => ?_, SmithD6StabTree.stabGens_facts_of_pinned hK hL,
    SmithD6StabTree.stabReach_of_pinned hK hL, SmithD6Stab.chkStabCard_true hK,
    SmithD6Nc.chkStabNc_of_pinned hK hL, SmithD6Stab.chkStabOrd_true hK⟩
  obtain ⟨hlt, -, hcls, -⟩ := SmithD6Stab.rep_facts hK hc
  rw [SmithD6Stab.stabRep_eq hK hc]
  exact ⟨hlt, hcls⟩

end Certificates
