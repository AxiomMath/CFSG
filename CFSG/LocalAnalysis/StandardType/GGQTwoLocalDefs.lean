module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.Models.Blueprint
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Models.Transport

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def DirectP3At (p : ℕ) (Bs L : Subgroup G) (x : G) (hx : x ∈ Bs) : Prop :=
  ∀ r ∈ ggInduced ⊤ Bs, GGIsReflection p r → r ⟨x, hx⟩ = ⟨x, hx⟩ → r ∈ ggAutomizer L Bs

@[expose] def ggCommSpace (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) : Subgroup ↥Bs :=
  Subgroup.closure {c | ∃ a ∈ A, ∃ b : ↥Bs, c = a b * b⁻¹}

@[expose] def PSUTrivialMultiplier (m : ℕ) : Prop :=
  ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ →
    LieModel (E ⧸ Subgroup.center E) .PSU m 2 1 → Nat.card (Subgroup.center E) = 1

structure QTwoLocalModel (m : ℕ) (Bs L : Subgroup G) (x : G) : Prop where
  elemAb : IsElemAbelian 3 Bs
  mem : x ∈ Bs
  card : Nat.card Bs = 3 ^ m
  weyl : GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) (ggAutomizer L Bs)
  fixes : ∀ a ∈ ggAutomizer L Bs, a ⟨x, mem⟩ = ⟨x, mem⟩
  fixed : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer L Bs, a b = b) → (b : G) ∈ Subgroup.zpowers x
  comm : Nat.card (ggCommSpace Bs (ggAutomizer L Bs)) = 3 ^ (m - 1)
  stab : Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, mem⟩ = ⟨x, mem⟩} ≤ 2 * m.factorial
  direct : DirectP3At 3 Bs L x mem

end CFSG.StandardType.QTwo

end
