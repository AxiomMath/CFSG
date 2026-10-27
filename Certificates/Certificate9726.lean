
module

public import Certificates.Certificate9726Base

public import CFSG.Sporadic.Bridge.BTcData
public import CFSG.Monster.B.Pinned.Primes.FiveWords
import Certificates.Kernel.BabyMonster.TcFive.Glue

public section

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Sporadic.Bridge.B

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Sporadic.Bridge.B in
local notation "uT" => qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4

theorem certificate9726 : 
    (∀ i : Fin 4, hFive⁻¹ * qFive i * hFive =
      (List.ofFn fun j => qFive j ^ (tcHR.getD i []).getD j 0).prod * zFive ^ tcHC.getD i 0) ∧
    uT ^ 5 = 1 ∧ uT * qFive 0 = qFive 0 * uT ∧
    (∀ a b c : ℕ, a < 5 → b < 5 → c < 5 → (b ≠ 0 ∨ c ≠ 0) →
      zFive ^ a * qFive 0 ^ b * uT ^ c ≠ 1) ∧
    ∃ e : NativeSporadic.B, e * qFive 0 = qFive 0 * e ∧ e * uT = uT * e ∧
      ∃ a ∈ Subgroup.closure ({xFive, hFive, e} : Set NativeSporadic.B),
        ∃ b ∈ Subgroup.closure ({xFive, hFive, e} : Set NativeSporadic.B),
          ∃ G Gi : Matrix (Fin 4370) (Fin 4370) (ZMod 2), G * Gi = 1 ∧
            genA₁ * G = G * bMat a ∧ genA₂ * G = G * bMat b :=
  KernelBM.TcFive.fact9726

end Certificates
