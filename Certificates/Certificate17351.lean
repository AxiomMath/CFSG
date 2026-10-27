module

public import Certificates.Data.Co2CentDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover
import Certificates.Kernel.Co2Cent.Assemble
import Certificates.Certificate2012
import Certificates.Certificate3115
import Certificates.Certificate3117
import Certificates.Certificate17350
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Cert.Cert

public section

namespace Certificates

open CertificateChecks

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Sporadic.Co2Cert CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.Co2Cent
  CFSG.HardMathSupport.Dickson.I271.U42Presentation in
theorem certificate17351 :
    (∀ k, 0 < k → k < 81 → ∃ h ∈ co2P, ∃ c : Equiv.Perm (Fin 2300), (c = co2XA ∨ c = co2XB) ∧
      ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ h * dEltP k * h⁻¹ = c ^ e) ∧
    (∃ h ∈ co2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ h * dEltP 5 * h⁻¹ = co2XA ^ e) ∧
    (∃ h ∈ co2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ h * dEltP 4 * h⁻¹ = co2XB ^ e) ∧
    (co2XA ^ 3 = 1 ∧ co2XA ≠ 1 ∧ co2XA ∈ co2P ∧
      Nat.card (closure (permsA 2300 (co2RGens ()))) = 243 ∧
      closure (permsA 2300 (co2RGens ())) ≤ centralizer {co2XA} ⊓ co2P ∧
      (∀ g ∈ centralizer {co2XA} ⊓ co2P, ∀ r ∈ closure (permsA 2300 (co2RGens ())),
        g * r * g⁻¹ ∈ closure (permsA 2300 (co2RGens ()))) ∧
      centralizer (closure (permsA 2300 (co2RGens ())) : Set (Equiv.Perm (Fin 2300))) ⊓
        (centralizer {co2XA} ⊓ co2P) ≤ closure (permsA 2300 (co2RGens ()))) ∧
    (co2XB ^ 3 = 1 ∧ co2XB ≠ 1 ∧ co2XB ∈ co2P ∧ Nat.card Lsub = 25920 ∧
      Lsub ≤ centralizer {co2XB} ⊓ co2P ∧
      (∀ g ∈ centralizer {co2XB} ⊓ co2P, ∀ l ∈ Lsub, g * l * g⁻¹ ∈ Lsub) ∧
      (∀ g ∈ centralizer {co2XB} ⊓ co2P, (∀ l ∈ Lsub, l * g = g * l) → g ^ 3 = 1) ∧
      ∀ w ∈ u42Words,
        CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW CFSG.HardMathSupport.Dickson.I271.uvGen w = 1) ∧
    ∀ (t : Array ℕ) (G : Equiv.Perm (Fin 2300)), CFSG.Monster.B.Co2.Rep 2300 t G →
      siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0 t = true → G ∈ Lsub := KernelCo2Cent.kproof

end Certificates
