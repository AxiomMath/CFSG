module

public import CFSG.Quasithin.Background.G11Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def subRep (N : Subgroup (GLV V)) : Representation (ZMod 2) N V where
  toFun n := ((n : GLV V) : V →ₗ[ZMod 2] V)
  map_one' := by
    ext
    rfl
  map_mul' a b := by
    ext
    rfl

theorem exists_invariant_isCompl_of_odd [Finite V] {N : Subgroup (GLV V)} (hN : ¬ 2 ∣ Nat.card N)
    {U : Submodule (ZMod 2) V} (hU : Invariant N U) :
    ∃ U' : Submodule (ZMod 2) V, Invariant N U' ∧ IsCompl U U' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinG : Finite (GLV V) := Finite.of_injective (fun g : GLV V => (g : V → V))
    DFunLike.coe_injective
  have : Finite N := inferInstance
  have : NeZero (Nat.card N : ZMod 2) :=
    ⟨fun h => hN ((ZMod.natCast_eq_zero_iff _ _).1 h)⟩
  obtain ⟨σ', hσ'⟩ := ComplementedLattice.exists_isCompl
    (⟨U, fun n _ hx => hU n n.2 _ hx⟩ : Subrepresentation (subRep N))
  refine ⟨σ'.toSubmodule, fun n hn u hu => σ'.apply_mem_toSubmodule ⟨n, hn⟩ hu, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hσ' ⊢
  exact ⟨congrArg Subrepresentation.toSubmodule hσ'.1, congrArg Subrepresentation.toSubmodule hσ'.2⟩

end CFSG.Quasithin.SzN31
