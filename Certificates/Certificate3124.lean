
module

public import Certificates.Certificate3124Base
import all Certificates.Certificate3124Base


public section

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census
open CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT CFSG.KC.Bfs CertificateChecks.Orb14

namespace CertificateChecks.Batch3124

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census
open CFSG.KC.Orb14 CFSG.KC.U6Orb CFSG.KLie.CT CFSG.KC.Bfs CertificateChecks.Orb14

theorem singTree_ok_1 : treeOK singGenArr singT singI 693 = true := by
  rw [singI_eq, singT_eq]
  exact treeOK_of_perm pgS treeShape

end CertificateChecks.Batch3124

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census in

theorem certificate3124 : (∀ (k : Fin 17) (i : Fin 693),
       (singGenArr[(k : ℕ)]!)[(i : ℕ)]! = (singGen k i : ℕ))
    ∧ (treeOK singGenArr singT singI 693 = true)
    ∧ (treeOK n6PermsArr natT natI 891 = true)
    ∧ (schreierOK singGenArr singT singI singPart 693 = true)
    ∧ (schreierOK n6PermsArr natT natI natPart 891 = true)
    ∧ (natCertOK (selAct singGenArr singT singI o14PtSel) o14PtSel.size
       (fun x => decide (x < 693)) (o14PtOrb[0]!)[0]! (singCert 0) = true)
    ∧ (natCertOK (selAct singGenArr singT singI o14PtSel) o14PtSel.size
       (fun x => decide (x < 693)) (o14PtOrb[1]!)[0]! (singCert 1) = true)
    ∧ (natCertOK (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size
       (fun x => decide (x < 891)) (natOf (o14PlOrb[0]!)[0]!) (natCert 0) = true)
    ∧ (natCertOK (selAct n6PermsArr natT natI o14PlSel) o14PlSel.size
       (fun x => decide (x < 891)) (natOf (o14PlOrb[1]!)[0]!) (natCert 1) = true)
    ∧ (∀ y < 693, (singPart[y]! = 0 ∧ (singCert 0).pts.contains y = true) ∨
       (singPart[y]! = 1 ∧ (singCert 1).pts.contains y = true))
    ∧ (∀ y < 891, (natPart[y]! = 0 ∧ (natCert 0).pts.contains y = true) ∨
       (natPart[y]! = 1 ∧ (natCert 1).pts.contains y = true))
    ∧ (∀ i < 693, (i ∈ o14PtOrb[0]! ↔ singPart[i]! = 0) ∧
       (i ∈ o14PtOrb[1]! ↔ singPart[i]! = 1))
    ∧ (∀ j : Fin 891, ((b6Iso j : ℕ) ∈ o14PlOrb[0]! ↔ natPart[(j : ℕ)]! = 0) ∧
       ((b6Iso j : ℕ) ∈ o14PlOrb[1]! ↔ natPart[(j : ℕ)]! = 1))
    ∧ ((Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = 0).card = 126 ∧
       (Finset.univ.filter fun y : Fin 693 => singPart[(y : ℕ)]! = 1).card = 567)
    ∧ ((Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = 0).card = 324 ∧
       (Finset.univ.filter fun y : Fin 891 => natPart[(y : ℕ)]! = 1).card = 567)
    ∧ (∀ p : Fin 891,
       ((Finset.univ.filter fun i : Fin 693 =>
           singPart[(i : ℕ)]! = 0 ∧ expand p (singVec i) = singVec i).card,
         (Finset.univ.filter fun i : Fin 693 =>
           singPart[(i : ℕ)]! = 1 ∧ expand p (singVec i) = singVec i).card) =
         if (p : ℕ) ∈ o14PlOrb[0]! then (0, 21) else (6, 15))
    ∧ (∀ p < 891, ¬ (p ∈ o14PlOrb[0]! ∧ p ∈ o14PlOrb[1]!)) := by
  exact ⟨CertificateChecks.Batch3124.singGenArr_eq_0, CertificateChecks.Batch3124.singTree_ok_1, CertificateChecks.Batch3124.natTree_ok_2,
    CertificateChecks.Batch3124.singSchreier_ok_3, CertificateChecks.Batch3124.natSchreier_ok_4, CertificateChecks.Batch3124.singCert_ok0_5,
    CertificateChecks.Batch3124.singCert_ok1_6, CertificateChecks.Batch3124.natCert_ok0_7, CertificateChecks.Batch3124.natCert_ok1_8, CertificateChecks.Batch3124.singCov_9,
    CertificateChecks.Batch3124.natCov_10, CertificateChecks.Batch3124.singPart_spec_11, CertificateChecks.Batch3124.natPart_spec_12,
    CertificateChecks.Batch3124.card_singPart_13, CertificateChecks.Batch3124.card_natPart_14, CertificateChecks.Batch3124.incid_check_15,
    CertificateChecks.Batch3124.plList_spec_16⟩

end Certificates
