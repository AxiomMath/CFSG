module

public import CFSG.Monster.B.TwoA.Sp8.T8Inputs
public import CFSG.Monster.B.TwoA.Sp8.WordRel
public import Certificates.Data.CFSGNative.MonsterB.P0Rank
import Certificates.Kernel.T8K.Facts

public section

namespace Certificates

open CertificateChecks.KernelT8K.Facts in
open CFSG.Monster.B.TwoA.Sp8.WordRel CFSG.Open MonsterB.P0Rank in
theorem certificate812463 : 
    (∀ gs ∈ [gensA1, gensA2, gensA4'],
      IsElemAbelian 2 (Subgroup.closure {g | ∃ c ∈ gs, g = wordX (nfWord c)})) ∧
    (∀ τ < 2 ^ 9, wordX xWord * wordX (tWord τ) * (wordX xWord)⁻¹ =
      wordX (tWord (colsAct xT9 τ))) ∧
    (∀ τ < 2 ^ 9, wordX yWord * wordX (tWord τ) * (wordX yWord)⁻¹ =
      wordX (tWord (colsAct yT9 τ))) :=
  ⟨elemAbelian, fun τ _ => xConj τ, fun τ _ => yConj τ⟩

end Certificates
