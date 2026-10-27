module

public import CFSG.LocalAnalysis.StandardType.GGResLeaves
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGReflClassLargeInput' : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (n : ℕ), Module.finrank (ZMod p) V = n → 9 ≤ n →
    ∀ A : Subgroup (V ≃ₗ[ZMod p] V), ZS.AbsIrred p A →
      A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} →
      CFSG.Quasithin.SimsG4.IsImprimitiveOnV A ∨ p ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A ∨
        (¬ p ∣ n + 1 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 1)),
          ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod p] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
        (p ∣ n + 2 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 2)),
          ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod p] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)

@[expose] def GGResCentBoundInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime], ∀ hx : x ∈ Bs,
    Nat.card ↥((ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⊓
        MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)

@[expose] def GGIsGOFourMinusThree {G : Type} [Group G] {Bs : Subgroup G}
    (A : Subgroup (MulAut ↥Bs)) : Prop :=
  Nat.card Bs = 3 ^ 4 ∧ Nat.card A = 1440 ∧
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (ι : Additive ↥Bs ≃+ V)
      (Q : QuadraticForm (ZMod 3) V), (QuadraticMap.polarBilin Q).Nondegenerate ∧
      ∀ a ∈ A, ∀ v, Q (ggLin (p := 3) ι a v) = Q v

@[expose] def GGResGOFourShape {G : Type} [Group G] (p : ℕ) (Bs L K : Subgroup G) : Prop :=
  p = 3 ∧ (GGHasLabel ⟨.A, 5, 1⟩ (↥L ⧸ Subgroup.center ↥L) ∨
      GGHasLabel ⟨.A, 6, 1⟩ (↥L ⧸ Subgroup.center ↥L)) ∧
    GGIsGOFourMinusThree (ggAutomizer L Bs ⊔ ggAutomizer K Bs)

@[expose] def GGResFFGOFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → GGResGOFourShape p Bs L K → False

@[expose] def GGResCaseIQTwoRestInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
    GGResLeviDatum p Bs L J K ggSelI (ggTypRankLt 8) ∧ GGInnerDiagOnLabel GGLabQTwo p Bs L ∧
      ¬ GGResGOFourShape p Bs L K

theorem GGResCaseIQTwoInput.of_rest (h : GGResCaseIQTwoRestInput) (hFF : GGResFFGOFourInput) :
    GGResCaseIQTwoInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  by_cases hsh : GGResGOFourShape p Bs L K
  · exact (hFF G p B Bs x L D J y K hH hsh).elim
  · exact h G p B Bs x L D J y K hH hF hS hE ⟨hP.1, hP.2, hsh⟩

end CFSG.StandardType
