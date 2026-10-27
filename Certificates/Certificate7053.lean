module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Inputs
import Certificates.Kernel.J4F2.OrbitL52

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit CFSG.Quasithin.JonesParshall in
open CFSG.Quasithin.JonesParshall.Curtis in
open scoped Matrix in
theorem certificate7053 :
    (∀ t : Fin 25, ∀ l : Fin 10,
       (fun k => wedgeMat ((trSL' t : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l) =
         decodeV (l52Col.getD (10 * t + l) 0))
    ∧ (∀ c < 1024, c ≠ 0 →
       applyC (l52Words.getD c []) (l52BaseC (l52Cls.getD c false)) = c ∧
         ∀ t ∈ l52Words.getD c [], t < 25)
    ∧ ((Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = true).card = 155)
    ∧ ((Finset.univ.filter fun c : Fin 1024 => c.val ≠ 0 ∧ l52Cls.getD c false = false).card =
       868) := KernelJ4F2.c7053

end Certificates
