module

public import CFSG.Sporadic.Recognition.LyonsAmalgamModelY
import Certificates.Kernel.LyTr.Y1080
import Certificates.Kernel.LyY.Norm
import Certificates.Kernel.LyY.Aut

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.LyonsSims

open Subgroup CFSG.Sporadic.Recognition.LyonsSims.Ly1080 in
theorem certificate6111 : tablesOK = true ∧ erelOK = true ∧ genOK = true ∧ CFSG.Sporadic.Recognition.LyonsSims.Ly1080.txyEnumOK = true ∧ sigmaTxyOK = true ∧
    center ↥Y0 = ⊥ ∧
    (∀ t ∈ Txy0, ¬ ∀ i < 4, t * ug i * t⁻¹ = sigma0 * ug i * sigma0⁻¹) ∧
    (Nat.card Y0 ≤ 349920 →
      (∀ n ∈ Y0, (∀ t ∈ Txy0, n * t * n⁻¹ ∈ Txy0) → n ∈ Txy0) ∧ Nat.card (MulAut ↥Y0) ≤ 699840) :=
  ⟨KernelLyTr.tablesOK1080_of, KernelLyTr.erelOK1080_of, KernelLyTr.genOK1080_of,
    KernelLyTr.txyEnumOK1080_of, KernelLyTr.sigmaTxyOK1080_of, KernelLyY.center_Y0,
    KernelLyY.not_inner, fun hcard => ⟨KernelLyY.normalizer_Txy0 hcard
      (Ly1080.card_Txy0_of KernelLyTr.tablesOK1080_of KernelLyTr.txyEnumOK1080_of),
      KernelLyY.card_mulAut_Y0_le⟩⟩

end Certificates
