module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23OrbitInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.A5.G3.M23 Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

namespace CertificateChecks.Batch17025

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.A5.G3.M23 Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

private theorem nxt_spec_0 : ∀ i : Fin 23, evalW tGens (wd i) i = nxt i := by
  decide +kernel

private theorem cyc_1 : ∀ y z : Fin 23, tau y = tau z → ∃ k : Fin 16, nxt^[k.val] y = z := by
  decide +kernel

private theorem pat_card_cases_2 : ∀ pat : Fin 4 → Bool, pat 0 = true →
    (Finset.univ.filter (fun y => pat (tau y) = true)).card ∣ 1920 →
    pat = ![true, false, false, false] ∨ pat = ![true, true, false, false] ∨
      pat = ![true, false, true, false] := by
  decide +kernel

private theorem pat_card_cases'_3 : ∀ pat : Fin 4 → Bool, pat 1 = true → pat 0 = false → pat 2 = false →
    (Finset.univ.filter (fun y => pat (tau y) = true)).card ∣ 1920 →
    pat = ![false, true, false, false] := by
  decide +kernel

end CertificateChecks.Batch17025

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.G3 CFSG.QuasithinUnique.A5.G3.M23 Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat in
theorem certificate17025 : (
 ∀ i : Fin 23, evalW tGens (wd i) i = nxt i 
)
    ∧ (
 ∀ y z : Fin 23, tau y = tau z → ∃ k : Fin 16, nxt^[k.val] y = z 
)
    ∧ (
 ∀ pat : Fin 4 → Bool, pat 0 = true →
    (Finset.univ.filter (fun y => pat (tau y) = true)).card ∣ 1920 →
    pat = ![true, false, false, false] ∨ pat = ![true, true, false, false] ∨
      pat = ![true, false, true, false] 
)
    ∧ (
 ∀ pat : Fin 4 → Bool, pat 1 = true → pat 0 = false → pat 2 = false →
    (Finset.univ.filter (fun y => pat (tau y) = true)).card ∣ 1920 →
    pat = ![false, true, false, false] 
) := by
  exact ⟨@CertificateChecks.Batch17025.nxt_spec_0, @CertificateChecks.Batch17025.cyc_1, @CertificateChecks.Batch17025.pat_card_cases_2, @CertificateChecks.Batch17025.pat_card_cases'_3⟩

end Certificates
