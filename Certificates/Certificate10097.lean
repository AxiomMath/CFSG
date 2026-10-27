module

public import CFSG.YGroups.Exact.Y321Inputs
public import CFSG.YGroups.Exact.Model
import Certificates.Kernel.YModel.Y321
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace Certificates

open CFSG.YGroups CertificateChecks.KernelYModel

open CFSG.YGroups CFSG.Monster.B.Co2 in
open CFSG.Certificates.CosetEnumeration (evalWord) in
theorem certificate10097 :
    (Finite (YGroup 3 2 1) ∧ Nat.card (YGroup 3 2 1) ≤ 2903040) ∧
    (y321Arrays.size = 7 ∧
      (∀ c < 7, CFSG.Monster.B.Co2.Rep 56 y321Arrays[c]! (arrGen 56 y321Arrays c)) ∧
      (∀ w ∈ yRels 3 2 1, CFSG.Certificates.CosetEnumeration.evalWord (arrGen 56 y321Arrays) w = 1) ∧
      2903040 ≤ Nat.card (arrClosure 56 y321Arrays)) := by
  refine ⟨y321_le, y321_size, fun c hc => ?_, evalWord_arrGen_eq_one y321_perms y321_relators,
    ?_⟩
  · have h := rep_letterOf y321_perms c
    rwa [ModelNative.letterOf, ite_eq_left (by rw [y321_size]; exact hc)] at h
  · have h := chainSizes_prod_le_card y321_chain.1
    rw [y321_chain.2] at h
    exact (by norm_num : (2903040 : ℕ) = ([56, 27, 16, 10, 6, 2] : List ℕ).prod).trans_le h

end Certificates
