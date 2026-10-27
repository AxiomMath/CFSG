module

public import CFSG.Sporadic.Co2Smith.CCFacts
public import CFSG.Sporadic.Co2Smith.HPCore

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem cE_eq_mul
    (e n : ℕ) : cE e n = ⟨sElt n, S0_le_Cz (sElt_mem_S0 n)⟩ * (qE e : Cz) := rfl

theorem rho_cE
    (e n : ℕ) : cfgCz.rho (cE e n) = ⟨sElt n, sElt_mem_S0 n⟩ := by
  rw [cE_eq_mul, map_mul, rho_S0, cfgCz.rho_E (qE e), mul_one]

theorem zCz_comm (g : Cz) : g * zCz = zCz * g :=
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

theorem cz_classes
    (hc : CCFacts) :
    (∀ y : Cz, y * y = 1 → y = 1 ∨ y = zCz ∨ ∃ i : Fin 9, ∃ h : Cz, h * y * h⁻¹ = cR i) ∧
      ∀ i : Fin 9, (conjSet (cR i)).ncard = Native.ccCls[(i : ℕ)]! :=
  ⟨hc.classes, hc.cls⟩

theorem cz_sqrt
    (hc : CCFacts) (i : Fin 9) :
    sqrtCnt zCz (cR i) = Native.ccSqZ[(i : ℕ)]! ∧
      sqrtCnt (cR i) (cR i) = Native.ccSqR[(i : ℕ)]! :=
  hc.sqrt i

end CFSG.Sporadic.Co2Smith
