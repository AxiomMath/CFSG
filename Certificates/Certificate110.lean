module

public import CFSG.Certificates.PresentationLetters
public import CFSG.Sporadic.Bridge.M11Data

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.M11Data

namespace CertificateChecks.Batch110

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.M11Data

open CFSG.Certificates.CosetEnumeration

private theorem facts_0 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 0 4000 = true := by
  decide +kernel

private theorem facts_1 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 4000 4000 = true := by
  decide +kernel

private theorem facts_2 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 8000 4000 = true := by
  decide +kernel

private theorem facts_3 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 12000 4000 = true := by
  decide +kernel

private theorem facts_4 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 16000 4000 = true := by
  decide +kernel

private theorem facts_5 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 20000 4000 = true := by
  decide +kernel

private theorem facts_6 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 24000 4000 = true := by
  decide +kernel

private theorem facts_7 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 28000 4000 = true := by
  decide +kernel

private theorem facts_8 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 32000 4000 = true := by
  decide +kernel

private theorem facts_9 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 36000 4000 = true := by
  decide +kernel

private theorem facts_10 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 40000 4000 = true := by
  decide +kernel

private theorem facts_11 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 44000 4000 = true := by
  decide +kernel

private theorem facts_12 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 48000 4000 = true := by
  decide +kernel

private theorem facts_13 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 52000 4000 = true := by
  decide +kernel

private theorem facts_14 : factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 56000 14 = true := by
  decide +kernel

private theorem cover_0 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 0 20000 = true := by
  decide +kernel

private theorem cover_1 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 20000 20000 = true := by
  decide +kernel

private theorem cover_2 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 40000 20000 = true := by
  decide +kernel

private theorem cover_3 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 60000 20000 = true := by
  decide +kernel

private theorem cover_4 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 80000 20000 = true := by
  decide +kernel

private theorem cover_5 : coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 100000 2592 = true := by
  decide +kernel

private theorem liveCount_eq : liveCount live 25648 = 7920 := by
  decide +kernel

private theorem live_zero : live 0 = true := by
  decide +kernel

end CertificateChecks.Batch110

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.M11Data in
open CFSG.Certificates.CosetEnumeration in
theorem certificate110 : (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 0 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 4000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 8000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 12000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 16000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 20000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 24000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 28000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 32000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 36000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 40000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 44000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 48000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 52000 4000 = true)
    ∧ (factsOK 25648 5 fx fc fy kind wi fs ft fo refs pl (invLetter 2) words [] 56000 14 = true)
    ∧ (coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 0 20000 = true)
    ∧ (coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 20000 20000 = true)
    ∧ (coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 40000 20000 = true)
    ∧ (coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 60000 20000 = true)
    ∧ (coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 80000 20000 = true)
    ∧ (coverOK 25648 4 56014 fx fc fy (invLetter 2) ffi live 100000 2592 = true)
    ∧ (liveCount live 25648 = 7920)
    ∧ (live 0 = true) := by
  exact ⟨CertificateChecks.Batch110.facts_0, CertificateChecks.Batch110.facts_1, CertificateChecks.Batch110.facts_2, CertificateChecks.Batch110.facts_3, CertificateChecks.Batch110.facts_4, CertificateChecks.Batch110.facts_5, CertificateChecks.Batch110.facts_6, CertificateChecks.Batch110.facts_7, CertificateChecks.Batch110.facts_8, CertificateChecks.Batch110.facts_9, CertificateChecks.Batch110.facts_10, CertificateChecks.Batch110.facts_11, CertificateChecks.Batch110.facts_12, CertificateChecks.Batch110.facts_13, CertificateChecks.Batch110.facts_14, CertificateChecks.Batch110.cover_0, CertificateChecks.Batch110.cover_1, CertificateChecks.Batch110.cover_2, CertificateChecks.Batch110.cover_3, CertificateChecks.Batch110.cover_4, CertificateChecks.Batch110.cover_5, CertificateChecks.Batch110.liveCount_eq, CertificateChecks.Batch110.live_zero⟩

end Certificates
