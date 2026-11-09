
module

public import CFSG.Certificates.Kernel.BSeed.Render
public import CFSG.Certificates.Kernel.BSeed.Rows
public import CFSG.Monster.B.Pinned.GeneratorDeterminantsBase
import all CFSG.Blueprint.NativeSporadic

public section

namespace CertificateChecks.KernelBSeed

open CFSG.KC.BSeed CFSG.Blueprint.NativeSporadic

theorem rows1_ok : rowsListOK A1R BRows1 0 4370 = true := by
  decide +kernel

theorem rows2_ok : rowsListOK A2R BRows2 0 4370 = true := by
  decide +kernel

theorem genA₁_eq : CFSG.Monster.B.genA₁ = rowsMat 4370 A1R := by
  obtain ⟨hl, hr⟩ := rowsListOK_spec rows1_ok
  rw [CFSG.Monster.B.genA₁, BSeed1, decode_render 4370 BRows1 hl]
  funext i j
  rw [rowsMat, rowsMat, hr i.val (by omega), Nat.zero_add]

theorem genA₂_eq : CFSG.Monster.B.genA₂ = rowsMat 4370 A2R := by
  obtain ⟨hl, hr⟩ := rowsListOK_spec rows2_ok
  rw [CFSG.Monster.B.genA₂, BSeed2, decode_render 4370 BRows2 hl]
  funext i j
  rw [rowsMat, rowsMat, hr i.val (by omega), Nat.zero_add]

end CertificateChecks.KernelBSeed

end
