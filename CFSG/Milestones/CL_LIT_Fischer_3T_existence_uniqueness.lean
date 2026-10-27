module

public import CFSG.Fischer.Assembly
public import CFSG.Sporadic.Fi23.Tr.Facts
public import CFSG.Sporadic.Fi22.InvCent
public import CFSG.Sporadic.Fi23.InvCover

public section

universe u v w

namespace CFSG.Open

open Matrix in
theorem _root_.CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness :
    ∀ k ∈ ({22, 23, 24} : Set ℕ),
      (∃ (G : Type) (_ : Group G) (_ : Finite G) (D : Set G),
        fischerEUIsCenterlessPair D ∧ fischerEUType k D ∧
        (∀ D' : Set G, fischerEUIsPair D' → D' = D) ∧
        ∀ d ∈ D, fischerEULocalStructure k d) ∧
      (∀ (G H : Type) [Group G] [Group H] [Finite G] [Finite H] (D : Set G) (E : Set H),
        fischerEUIsCenterlessPair D → fischerEUType k D →
        fischerEUIsCenterlessPair E → fischerEUType k E →
        ∃ φ : G ≃* H, φ '' D = E) :=
  CFSG.Fischer.open_of_facts
    (Sporadic.Fi23.fi23Facts (Sporadic.Fi22.fi22Facts Fischer.polarFacts Fischer.hyperovalFacts))

end CFSG.Open

namespace CFSG.Milestones

open Blueprint.Fischer

theorem cl_lit_fischer_3t_existence_uniqueness_full :
    ∀ k : Fin 3, Subgroup.center (Carrier k) = ⊥ ∧ IsSimpleGroup (commutator (Carrier k)) ∧
      ∃ D : Set (Carrier k), HasType k (Carrier k) D ∧
        (∀ E : Set (Carrier k), Pair (Carrier k) E → E = D) ∧ LocalStructure k D ∧
        ∀ (X : Type) [Group X] (E : Set X), Pair X E →
          Subgroup.center X = ⊥ → IsSimpleGroup (commutator X) → HasType k X E →
          ∃ iso : X ≃* Carrier k, iso '' E = D :=
  CFSG.Fischer.full_of_facts
    (Sporadic.Fi23.fi23Facts (Sporadic.Fi22.fi22Facts Fischer.polarFacts Fischer.hyperovalFacts))
    Sporadic.Fi22.card_fixed_involution_D Sporadic.Fi22.eq_of_commute_centralizer
    Sporadic.Fi23.d1_mem_localClass Sporadic.Fi23.involution_cover

end CFSG.Milestones
