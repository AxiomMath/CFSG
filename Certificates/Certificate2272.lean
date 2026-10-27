module

public import CFSG.Sporadic.SmallOddCore.HSCheckInputs
import Certificates.Kernel.SporSch.PairHS.HS2272Main

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
open CFSG.Monster.B.Co2.Native Subgroup in
theorem certificate2272 : (∀ x : Fin 3850, x ≠ 0 → ∃ s ∈ hsP, s 0 = 0 ∧ s x ≠ x)
    ∧ ((permOK 3850 (hsCentTbl 5) && tblEq 3850 (hsCentTbl 5) hsPGTbls[0]!) = true)
    ∧ (hsU ^ 2 = 1 ∧ hsU ≠ 1 ∧ hsU ∉ hsP ∧ ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP)
    ∧ (∀ r ∈ hsRows, permOK 3850 r.rep = true ∧ tp 3850 r.rep ∈ hsR ∧
        orderOf (tp 3850 r.rep) = 2 ∧ (r.outer = true ↔ tp 3850 r.rep ∉ hsP) ∧
        CFSG.Sporadic.SmallOddCore.hsC r =
          hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) ∧
        Nat.card ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) =
          r.centOrder ∧
        (conjClass hsP (tp 3850 r.rep)).ncard = r.classSize ∧
        CFSG.oddCore ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) = ⊥)
    ∧ (hsS ≤ hsR ∧ Nat.card hsS = 1024)
    ∧ (∀ t ∈ hsR, orderOf t = 2 → ∃ r ∈ hsRows, ∃ g ∈ hsP, t = g * tp 3850 r.rep * g⁻¹)
    ∧ (∃ x ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set (Equiv.Perm (Fin 3850))),
        orderOf x = 5 ∧
        ∃ y ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set (Equiv.Perm (Fin 3850))),
          orderOf (x * (y * x * y⁻¹)) = 6)
    ∧ (∀ T ∈ hsSylowGenTbls, permOK 3850 T = true) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := KernelSporSch.HS72.facts2272
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun T hT => ?_⟩
  simp only [CFSG.Sporadic.SmallOddCore.hsSylowGenTbls, List.mem_map, List.mem_range] at hT
  obtain ⟨i, hi, rfl⟩ := hT
  exact KernelSporSch.HS72.permOK_T (by omega)

end Certificates
