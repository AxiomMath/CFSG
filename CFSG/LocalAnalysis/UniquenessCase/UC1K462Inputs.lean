module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspPair
public import CFSG.GH74.Uniqueness.SU.SU5Q8D8
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp (InspPair)
open scoped MatrixGroups

namespace UC46

abbrev A5Q8D8 (G : Type) [Group G] : Prop :=
  CFSG.Quasithin.IsExt G (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
    (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)

structure Hyp45 (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] (V : Type)
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ρ : Representation (ZMod p) G V)
    (D : Subgroup G) : Prop where
  odd : 2 < p
  kgroup : CFSG.Open.IsKGroup G
  faithful : Function.Injective ρ
  irred : ρ.IsIrreducible
  card_three : Nat.card D = 3
  gen : Subgroup.normalClosure (D : Set G) = ⊤
  fix : fixV ρ D = ⊥

structure Hyp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] (V : Type)
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (ρ : Representation (ZMod p) G V)
    (D : Subgroup G) : Prop extends Hyp45 p G V ρ D where
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1
  perfect : commutator G = ⊤

end UC46

open UC46

@[expose] def K45Odd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (ρ : Representation (ZMod p) G V) (D : Subgroup G),
    Hyp p G V ρ D → CFSG.pPrimeCore 3 G ≤ Subgroup.center G ∨ A5Q8D8 G

@[expose] def QuasisimpleOfCentral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (ρ : Representation (ZMod p) G V) (D : Subgroup G),
    Hyp p G V ρ D → CFSG.pPrimeCore 3 G ≤ Subgroup.center G →
      CFSG.Open.IsQuasisimple G ∧ IsCyclic (Subgroup.center G) ∧
        ¬ 3 ∣ Nat.card (Subgroup.center G)

@[expose] def K46Quasisimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → CFSG.Open.IsQuasisimple G →
    CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1 →
      (∃ p f : ℕ, LieModel G .PSL 2 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel G .PSU 3 p f) ∨ IsSpor G .J1 ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ Nonempty (G ≃* SL(2, F)))

@[expose] def Insp2L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), LieModel G .PSL 2 2 n →
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ n - 1 →
      (∃ A : Subgroup G, Nat.card A = r) ∧
      ∀ A : Subgroup G, Nat.card A = r → ∃ U : Subgroup G, InspPair 2 A U

@[expose] def Insp2L3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    ((∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel G .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel G .PSU 3 p f)) →
    ∀ D : Subgroup G, Nat.card D = 3 → ∃ U : Subgroup G, InspPair 2 D U

@[expose] def Insp2J1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSpor G .J1 → ∀ D : Subgroup G, Nat.card D = 3 →
    ∃ U : Subgroup G, InspPair 2 D U

@[expose] def ZassenhausPerfect : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G], commutator G = ⊤ →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) G V), Function.Injective ρ →
      (∀ g : G, g ≠ 1 → ∀ v : V, ρ g v = v → v = 0) → Nat.card G ≠ 1 →
        Nonempty (G ≃* SL(2, ZMod 5))

end CFSG.LocalAnalysis.UniquenessCase.UCK
