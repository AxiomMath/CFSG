module

public import CFSG.YGroups.Y322CentralInputs
public import CFSG.YGroups.Defs
import Certificates.Kernel.YModel.Y322
import Certificates.Kernel.YModel.Y322H

public section

namespace Certificates

open CertificateChecks.KernelYModel

open CFSG.YGroups CFSG.Monster.B.Co2.Native in
theorem certificate10103 :
    (eqA 728 (ModelNative.evalW 728 y322Arrays y322WordF1)
      (ModelNative.evalW 728 y322Arrays y322WordF2) = true ∧
      (∀ c < 8, eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ [c]))
      (ModelNative.evalW 728 y322Arrays (c :: y322WordF1)) = true) ∧
      eqA 728 (ModelNative.evalW 728 y322Arrays (y322WordF1 ++ y322WordF1))
      (ModelNative.evalW 728 y322Arrays []) = true)
    ∧ (ModelNative.chainOK 728 y322HSubArrays #[] #[0, 1, 2, 3, 4, 5] = true ∧
      ModelNative.chainSizes 728 y322HSubArrays #[] #[0, 1, 2, 3, 4, 5] = [56, 27, 16, 10, 6, 2])
    ∧ (y322HActArrays.size = 8 ∧ ModelNative.permsOK 3159 y322HActArrays = true ∧
      ModelNative.relatorsOK 3159 y322HActArrays (yRels 3 2 2) = true ∧
      ModelNative.chainOK 3159 y322HActArrays #[] #[0, 1, 2, 3, 4, 5, 6] = true ∧
      ModelNative.chainSizes 3159 y322HActArrays #[] #[0, 1, 2, 3, 4, 5, 6] =
      [3159, 288, 35, 12, 3, 2, 2] ∧
      (∀ c < 7, (y322HActArrays[c]!)[0]! = 0)) := by
  refine ⟨⟨y322_w_f12, ?_, y322_w_ff⟩, y322_chain1, ⟨y322H_size, y322H_perms, y322H_relators,
    y322H_chain0.1, y322H_chain0.2, y322H_fix0⟩⟩
  intro c hc
  interval_cases c
  exacts [y322_w_fc0, y322_w_fc1, y322_w_fc2, y322_w_fc3, y322_w_fc4, y322_w_fc5, y322_w_fc6,
    y322_w_fc7]

end Certificates
