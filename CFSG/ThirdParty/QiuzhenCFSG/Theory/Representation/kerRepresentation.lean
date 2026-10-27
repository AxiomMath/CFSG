module

public import Mathlib.RepresentationTheory.Irreducible

namespace CFSG
end CFSG
open CFSG

open MonoidHom Function

section kerLift'

namespace QuotientGroup

variable {G : Type*} [Group G] {H : Type*} [Monoid H] (φ : G →* H)

/-- The induced homomorphism from the quotient by the kernel of `φ`. -/
@[expose]
public def kerLift' : G ⧸ φ.ker →* H := lift _ φ fun _g => mem_ker.mp


public theorem kerLift'_injective : Injective (kerLift' φ) := fun a b =>
  Quotient.inductionOn₂' a b fun a b (h : φ a = φ b) =>
    Quotient.sound' <| by rw [leftRel_apply, mem_ker, map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]

end QuotientGroup

end kerLift'

section kerRepresentation

open QuotientGroup Representation

namespace CFSG.Theory.Representation

open _root_.Representation

variable {F G V : Type*} [CommSemiring F] [Group G] [AddCommMonoid V] [Module F V] (ρ : Representation F G V)

/-- The faithful quotient representation obtained by modding out the kernel of `ρ`. -/
@[expose]
public def kerRepresentation : Representation F (G ⧸ ker ρ) V :=
  kerLift' ρ

public theorem kerRepresentation_apply (g : G) : Theory.Representation.kerRepresentation ρ (mk' _ g) = ρ g := by rfl

public theorem kerRepresentation_faithful : Injective (kerRepresentation ρ) :=
  kerLift'_injective ρ

variable {F G V : Type*} [CommRing F] [Group G] [AddCommMonoid V] [Module F V] (ρ : Representation F G V)

/-- The subrepresentation lattice is unchanged after passing to the faithful kernel quotient. -/
public def kerRepresentationOrderIso : Subrepresentation (kerRepresentation ρ) ≃o Subrepresentation ρ := {
  toFun := fun φ => .mk (φ.toSubmodule) (fun g v hv => by
    have := φ.apply_mem_toSubmodule (mk' _ g)
    rw [kerRepresentation_apply] at this
    exact this hv)
  invFun := fun φ => .mk (φ.toSubmodule) (fun g v hv => by
    have := φ.apply_mem_toSubmodule g.out hv
    rw [← kerRepresentation_apply] at this
    simp only [QuotientGroup.mk'_apply, Quotient.out_eq] at this
    exact this)
  map_rel_iff' := by rfl
}

variable {F G V : Type*}  [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)

public theorem kerRepresentation_irreducible_iff : IsIrreducible (kerRepresentation ρ) ↔ IsIrreducible ρ :=
  OrderIso.isSimpleOrder_iff (kerRepresentationOrderIso ρ)

public instance kerRepresentation_irreducible [IsIrreducible ρ] : IsIrreducible (kerRepresentation ρ) := (kerRepresentation_irreducible_iff ρ).mpr inferInstance

end CFSG.Theory.Representation

end kerRepresentation
