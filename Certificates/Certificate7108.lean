module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Beta4
import Certificates.Kernel.M23Aut.Assembly

public section

namespace Certificates

open MulAction CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Asc94 in
theorem certificate7108 :
    (Nat.card ↥(Gbar ⊓ M2bar) ≤ 1920 →
      ∀ γ : ↥(Gbar ⊓ M2bar) →* ↥NativeSporadic.M23, Function.Injective γ →
        (∀ h, γ h ∈ Gbar ⊓ M2bar) →
        (∀ h : ↥(Gbar ⊓ M2bar), (h : ↥NativeSporadic.M23) ∈ Lbar → γ h ∈ Lbar) →
        ∃ g ∈ Gbar ⊓ M2bar, (g : Equiv.Perm (Fin 23)) 19 = 19 ∧
          ∀ i : ↥(Gbar ⊓ M2bar),
            (i : ↥NativeSporadic.M23) ∈ quadStab ↥NativeSporadic.M23 (16 : Fin 23) 19 21 22 ⊓ Gbar →
              γ i = g * i * g⁻¹) ∧
    (Nat.card ↥Lbar = 960 → ∀ α : ↥Lbar ≃* ↥Lbar,
      (∀ f : ↥Lbar, (f : ↥NativeSporadic.M23) ∈
          fixingSubgroup ↥NativeSporadic.M23 (({16, 19, 21, 22} : Finset (Fin 23)) : Set (Fin 23)) →
        α f = f) →
      α = MulEquiv.refl _) :=
  ⟨CFSG.KD.M23Aut.autH_sound, CFSG.KD.M23Aut.autL_sound⟩

end Certificates
