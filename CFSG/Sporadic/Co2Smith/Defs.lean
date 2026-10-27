module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Open

abbrev Sp62 : Type := StatedSp 3 (ZMod 2)

structure SmithLocal (H : Type*) [Group H] : Prop where
  card_pCore : Nat.card (CFSG.pCore 2 H) = 2 ^ 9
  pCore_noncomm : ∃ x ∈ CFSG.pCore 2 H, ∃ y ∈ CFSG.pCore 2 H, x * y ≠ y * x
  quotient_equiv : Nonempty (H ⧸ CFSG.pCore 2 H ≃* Sp62)
  sylow_five : ∀ P : Sylow 5 H, ∀ x ∈ CFSG.pCore 2 H, (∀ p ∈ P, p * x = x * p) →
    ∀ y ∈ CFSG.pCore 2 H, x * y = y * x

structure SmithHyp (G : Type*) [Group G] [Finite G] (z : G) : Prop where
  oddCore_eq_bot : CFSG.oddCore G = ⊥
  center_eq_bot : center G = ⊥
  orderOf_eq : orderOf z = 2
  centralizer : SmithLocal (centralizer ({z} : Set G))

@[expose] def selfInCentralizer {G : Type*} [Group G] (t : G) : centralizer ({t} : Set G) :=
  ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩

structure TimmesfeldCo2Hyp (G : Type*) [Group G] [Finite G] (t : G) : Prop where
  simple : IsSimpleGroup G
  noncomm : ∃ a b : G, a * b ≠ b * a
  orderOf_eq : orderOf t = 2
  extraspecial : timmesfeldIsExtraspecial (timmesfeldFStar (centralizer ({t} : Set G)))
  card : Nat.card (timmesfeldFStar (centralizer ({t} : Set G))) = 2 ^ 9
  quotient : timmesfeldQuotientIso (timmesfeldFStar (centralizer ({t} : Set G))) Sp62
  spin : ∃ g : centralizer ({t} : Set G), orderOf g = 5 ∧
    ∀ y ∈ timmesfeldFStar (centralizer ({t} : Set G)),
      (g * y * g⁻¹ = y ∨ g * y * g⁻¹ = y * selfInCentralizer t) →
        y = 1 ∨ y = selfInCentralizer t

end CFSG.Sporadic.Co2Smith
