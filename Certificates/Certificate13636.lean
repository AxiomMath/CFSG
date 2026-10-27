
module


public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeDefs
import Certificates.Kernel.Co2Three.Glue
public import CFSG.Sporadic.Co2Cert.Cert

public section

namespace Certificates

open CertificateChecks.KernelCo2Three

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.RankThree.Native
open CFSG.Sporadic.Co2Cert (co2P)
open CFSG.Monster.B.Co2 (permOfArr)

open CertificateChecks.KernelCo2Three

theorem certificate13636 :
    Qg ≤ co2P ∧ Nat.card Qg = 729 ∧ (qCert2 ()).pts.size = 729 ∧
    (∀ k < 729, validA 2300 (qCert2 ()).pts[k]! = true) ∧
    (∀ x, x ∈ Qg ↔ ∃ k < 729, CFSG.Monster.B.Co2.permOfArr 2300 (qCert2 ()).pts[k]! = x) ∧
    (∀ i < 4, validA 2300 (dGens ())[i]! = true ∧ dGenP i ∈ co2P ∧ dGenP i ^ 3 = 1) ∧
    (∀ i < 4, ∀ j < 4, Commute (dGenP i) (dGenP j)) ∧
    (∀ k < 81, ∀ k' < 81, dEltP k = dEltP k' → k = k') ∧
    (∀ B : Subgroup (Equiv.Perm (Fin 2300)), (∀ b ∈ B, ∃ k < 81, b = dEltP k) →
      Nat.card B * 3 = 81 →
        Nat.card ↥(Subgroup.centralizer (B : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) ≤ 162) ∧
    (∀ c ∈ co2P, (∀ k < 81, Commute c (dEltP k)) → ∃ k < 81, c = dEltP k) ∧
    (∀ x ∈ co2P, orderOf x = 3 → ∃ h ∈ co2P, ∃ k < 81, h * x * h⁻¹ = dEltP k) :=
  ⟨kQg_le, kcard_Qg, qCert2_size, kqPts_valid, kmem_Qg_iff, kdGen_facts, kdGen_comm, kdElt_inj,
    kcard_cent_le, kcent_D, kfus⟩

end Certificates
