module

public import CFSG.GH74.KGroups.L33Inputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K273013
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier
  CFSG.Certificates.Kernel.PkCV

namespace Certificates

open CertificateChecks

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier in
theorem certificate273013 : (elemsT QA).all (fun g => !(orderIs g 26) && !(orderIs g 39)) = true := by
  rw [elemsT_eq_elemsC, List.all_map]
  have h26 := fun g : Equiv.Perm (Fin 26) => orderIs_eq_orderIsP g (m := 26) (by norm_num) [2, 13]
    (fun p hp hd => by
      have : p ∣ 2 * 13 := hd
      rcases (Nat.Prime.dvd_mul hp).1 this with h | h <;>
        simp [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h])
    (by decide)
  have h39 := fun g : Equiv.Perm (Fin 26) => orderIs_eq_orderIsP g (m := 39) (by norm_num) [3, 13]
    (fun p hp hd => by
      have : p ∣ 3 * 13 := hd
      rcases (Nat.Prime.dvd_mul hp).1 this with h | h <;>
        simp [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h])
    (by decide)
  simp only [Function.comp_def, h26, h39, orderIsP_ev]
  exact KernelPermCent.k273013

end Certificates
