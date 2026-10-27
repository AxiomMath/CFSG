module

public import Certificates.Data.Co3CentDefs
public import CFSG.Sporadic.Schreier.Co3Cert
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover
import Certificates.Kernel.Co3Cent.Assemble
import Certificates.Certificate2152
import Certificates.Certificate2158

public section

public section

namespace Certificates

open CertificateChecks

open Subgroup CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.Co3Cent CFSG.HardMathSupport.Dickson.I271.L28Presentation in
theorem certificate17370 :
    (XB ^ 3 = 1 ∧ XB ≠ 1 ∧ XB ∈ co3P ∧ Nat.card (closure (permsA 276 (dGens ()))) = 243 ∧
      closure (permsA 276 (dGens ())) ≤ centralizer {XB} ⊓ co3P ∧
      (∀ g ∈ centralizer {XB} ⊓ co3P, ∀ r ∈ closure (permsA 276 (dGens ())),
        g * r * g⁻¹ ∈ closure (permsA 276 (dGens ()))) ∧
      centralizer (closure (permsA 276 (dGens ())) : Set (Equiv.Perm (Fin 276))) ⊓
        (centralizer {XB} ⊓ co3P) ≤ closure (permsA 276 (dGens ()))) ∧
    (XA ^ 3 = 1 ∧ XA ≠ 1 ∧ XA ∈ co3P ∧ Nat.card (closure (permsA 276 (rGens ()))) = 243 ∧
      closure (permsA 276 (rGens ())) ≤ centralizer {XA} ⊓ co3P ∧
      (∀ g ∈ centralizer {XA} ⊓ co3P, ∀ r ∈ closure (permsA 276 (rGens ())),
        g * r * g⁻¹ ∈ closure (permsA 276 (rGens ()))) ∧
      centralizer (closure (permsA 276 (rGens ())) : Set (Equiv.Perm (Fin 276))) ⊓
        (centralizer {XA} ⊓ co3P) ≤ closure (permsA 276 (rGens ()))) ∧
    (closure (permsA 276 (lGens ())) ≤ closure (permsA 276 (cGens ())) ∧
      ⁅closure (permsA 276 (cGens ())), closure (permsA 276 (cGens ()))⁆ ≤
        closure (permsA 276 (lGens ())) ∧
      Nat.card (closure (permsA 276 (lGens ()))) = 504 ∧
      ∀ w ∈ l28Words,
        CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
          (fun i : Fin 2 => CFSG.Monster.B.Co2.permOfArr 276 (lGens ())[i.val]!) w = 1) := KernelCo3Cent.kproof

end Certificates

end
