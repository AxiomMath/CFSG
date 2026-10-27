module

public import CFSG.Sporadic.Schreier.TitsAction
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
import Certificates.Kernel.TitsN12.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru
open scoped Pointwise

@[expose] def burnsideF4nC_N1 (v : Fin 2925) : Set (Equiv.Perm (Fin 1755)) :=
  {g | g ∈ titsH ∧ g * g = 1 ∧ g • titsLine 0 = titsLine v ∧ g • titsLine v = titsLine 0 ∧
    ∃ p : Fin 1755, octGraph.dist (Sum.inl 0) (Sum.inl p) = 8 ∧ g p = p}

@[expose] def burnsideF4nC_N2 (y : Fin 1755) : Set (Equiv.Perm (Fin 1755)) :=
  {g | g ∈ titsN ∧ g * g = 1 ∧ g 0 = y ∧ g y = 0}

end Certificates

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru in
open scoped Pointwise in
theorem certificate7470 : (∀ v : Fin 2925, (0 : Fin 1755) ∈ titsLine v → v ≠ 0 →
      (burnsideF4nC_N1 v).ncard = 16 ∧
        ∀ g ∈ burnsideF4nC_N1 v, ∀ g' ∈ burnsideF4nC_N1 v, ∃ u ∈ titsJ ⊓ titsK, u * g * u⁻¹ = g') ∧
    ∀ y : Fin 1755, y ∈ titsLine 0 → y ≠ 0 → (burnsideF4nC_N2 y).ncard = 64 :=
  ⟨fun v h0 hv => ⟨KernelTitsN12.card_N1 v h0 hv,
    fun _ hg _ hg' => KernelTitsN12.trans_N1 v h0 hv hg hg'⟩,
    fun y hy hy0 => KernelTitsN12.card_N2 y hy hy0⟩

end Certificates
