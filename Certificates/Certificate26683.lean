module

public import CFSG.Sporadic.Co1Block.TwoBComp
import Certificates.Kernel.Sporadic.Co1Row26683.GlueS

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

public section

open CFSG.Sporadic.Co1Block CertificateChecks.KernelSpor.Co1Row26683

namespace Certificates

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block in
theorem certificate26683 :     ((d₂C twoBXY.1 : GA) : GL24) * ((d₂C twoBXY.1 : GA) : GL24) = 1 ∧
    ((d₂C twoBXY.2 : GA) : GL24) ^ 5 = 1 ∧
    (∃ (Z l : GL24) (hZ : Z ∈ GA ⊓ Subgroup.centralizer {A₁}),
      Z ∈ Subgroup.closure {((d₂C twoBXY.2 : GA) : GL24),
        ((d₂C twoBXY.1 : GA) : GL24) * ((d₂C twoBXY.2 : GA) : GL24) *
          ((d₂C twoBXY.1 : GA) : GL24)} ∧
      Z * Z = 1 ∧ Z ≠ 1 ∧ l ∈ GA ∧ l * A₁ * l⁻¹ = A₁ * Z ∧
      GA ≤ Subgroup.closure {((d₂C twoBXY.2 : GA) : GL24),
        ((d₂C twoBXY.1 : GA) : GL24) * ((d₂C twoBXY.2 : GA) : GL24) *
          ((d₂C twoBXY.1 : GA) : GL24),
        l * ((d₂C twoBXY.2 : GA) : GL24) * l⁻¹,
        l * (((d₂C twoBXY.1 : GA) : GL24) * ((d₂C twoBXY.2 : GA) : GL24) *
          ((d₂C twoBXY.1 : GA) : GL24)) * l⁻¹} ∧
      (∀ x ∈ GA, x * A₁ * x⁻¹ ≠ Z) ∧
      ∃ S : Subgroup (Equiv.Perm (Fin 1365)), S ≤ twoBD ∧ Nat.card S = 4096 ∧
        (∀ x ∈ S, x * triHom (liftC Z hZ) = triHom (liftC Z hZ) * x) ∧
        ∀ x ∈ S, x * x = 1 → x ≠ 1 → (∀ s ∈ S, x * s = s * x) →
          ∃ c ∈ twoBD, c * triHom (liftC Z hZ) * c⁻¹ = x) ∧
    (∃ c : C₁, triHom c ∉ twoBD) ∧
    ∀ y : Equiv.Perm (Fin 1365), (∀ d ∈ twoBD, y * d = d * y) → y = 1 := by
  intros
  exact ⟨xM_sq, yM_pow, ⟨zM, lM, zM_mem, zM_closure, zM_sq, zM_ne, lM_mem, lM_conj, gen_le,
    zM_not_conj, co1_d_K (prep_zeta (c := liftC zM zM_mem) rep_zM) zeta_mem⟩,
    co1_exists_not_mem_K, fun _ hy => co1_centralizer_trivial_K hy⟩

end Certificates
