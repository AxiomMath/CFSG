
module

public import Certificates.Certificate21205Base

public import CFSG.LargeExtraspecial.AS35QCoSp6Spec
import CFSG.Certificates.Kernel.C21205.CritSound
import CFSG.Certificates.Kernel.C21205.ProdSound
import Certificates.Kernel.C21205.SylowCheck
import Certificates.Kernel.C21205.CritCheck0
import Certificates.Kernel.C21205.CritCheck1
import Certificates.Kernel.C21205.ProdCheck

public section

namespace Certificates

open CFSG.KC.C21205 CFSG.KD.C21205C CFSG.LargeExtraspecial.AS35QCo
  CFSG.LargeExtraspecial.AS35QCo.Native

open CFSG.LargeExtraspecial.AS35QCo CFSG.LargeExtraspecial.AS35QCo.Native CFSG.Sporadic.Co2Smith in
theorem certificate21205 :
    (∀ τ : Sp62, τ * τ = 1 → τ ≠ 1 →
      ∃ k < 4, ∃ ρ : Sp62, Rep (repc k) ρ ∧ ∃ m : Sp62, τ = m * ρ * m⁻¹) ∧
    (∀ k : ℕ, (k = 2 ∨ k = 3) → ∀ ρ : Sp62, Rep (repc k) ρ →
      ∃ w : Sp62, ∀ j, 1 ≤ j → j ≤ 4 → (ρ * (w * ρ * w⁻¹)) ^ j ≠ 1) ∧
    (∀ k : ℕ, (k = 0 ∨ k = 1) → ∀ ρ : Sp62, Rep (repc k) ρ →
      ∀ y : Sp62, y ∈ Subgroup.centralizer ({ρ} : Set Sp62) → y ≠ 1 → y ≠ ρ →
        ((fun h : Sp62 => h * y * h⁻¹) ''
          (Subgroup.centralizer ({ρ} : Set Sp62) : Set Sp62)).ncard ≤ 6 →
        ∀ h₀ : Sp62, h₀ ∈ Subgroup.centralizer ({ρ} : Set Sp62) → h₀ * y * h₀⁻¹ = ρ * y →
          False) := by
    refine ⟨exists_conj_rep_of_sylowK CFSG.KD.C21205S.sylowK_ok, fun k hk ρ hρ => ?_,
      fun k hk ρ hρ y hy hy1 hyρ hsmall h₀ hh₀ hconj =>
        c21205_false_of_small_rep hk hρ hy hy1 hyρ hsmall hh₀ hconj⟩
    have h : prodK k = true := by
      rcases hk with rfl | rfl
      · exact ch21205p2
      · exact ch21205p3
    exact exists_bigOrder_rep_of_prodOK (prodOK_of_prodK h) hρ

end Certificates
