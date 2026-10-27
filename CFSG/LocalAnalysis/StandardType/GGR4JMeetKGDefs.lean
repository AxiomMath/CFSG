module

public import CFSG.LocalAnalysis.StandardType.GGR4JCardDefs
public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.Assembly.LargeEvenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGF4OrderThreeLayer : Prop :=
  ∀ (H : Type) [Group H] [Finite H] [Group.IsPerfect H] (f : ℕ), 1 ≤ f →
    GGHasLabel ⟨.F4, 0, f⟩ (H ⧸ Subgroup.center H) →
    ∀ z : H, z ≠ 1 → z ^ 3 = 1 → ∀ J : Subgroup H,
      J = LargeEvenLayer (Subgroup.centralizer ({z} : Set H)) →
      IsComponentOf J (Subgroup.centralizer ({z} : Set H)) →
      GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J) ∧
        ∀ E : Subgroup H, E ≤ Subgroup.centralizer ({z} : Set H) → IsElemAbelian 3 E →
          Nat.card E ≤ 3 * Nat.card (E ⊓ J : Subgroup H)

@[expose] def GGE6OppOrderThreeLayer : Prop :=
  ∀ (H : Type) [Group H] [Finite H] [Group.IsPerfect H] (f : ℕ), 1 ≤ f →
    ((GGHasLabel ⟨.E6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f + 1) ∨
      (GGHasLabel ⟨.twE6, 0, f⟩ (H ⧸ Subgroup.center H) ∧ 3 ∣ 2 ^ f - 1)) →
    ∀ z : H, z ≠ 1 → z ^ 3 = 1 → ∀ J : Subgroup H,
      J = LargeEvenLayer (Subgroup.centralizer ({z} : Set H)) →
      IsComponentOf J (Subgroup.centralizer ({z} : Set H)) →
      (((3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
          (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
          GGHasLabel ⟨.twD, 4, f⟩ (J ⧸ Subgroup.center J)) ∧
        ∀ E : Subgroup H, E ≤ Subgroup.centralizer ({z} : Set H) → IsElemAbelian 3 E →
          Nat.card E ≤ 3 * Nat.card (E ⊓ J : Subgroup H)) ∨
      (f = 1 ∧ GGHasLabel ⟨.E6, 0, 1⟩ (H ⧸ Subgroup.center H) ∧
        GGHasLabel ⟨.A, 2, 2⟩ (J ⧸ Subgroup.center J))

@[expose] def GGR4AmbientLabel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → GGInnerDiagOn Bs L → Nat.card Bs = 3 ^ 5 →
    ∀ [Fact (Nat.Prime 3)] (Γ : Type) [Fintype Γ] [DecidableEq Γ] (C : Matrix Γ Γ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Γ → MulAut ↥Bs) (h : Γ → V) (α : Γ → Module.Dual (ZMod 3) V),
    GGExtDatum ι C φ h α →
    (∃ e : Fin 4 ≃ Γ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) →
    ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
    GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .F4 ∨ (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1))
      3 Bs L

@[expose] def GGR4RowFact (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  (∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r) ∧
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ g ∈ Subgroup.center L', Nat.Coprime 3 (orderOf g)

@[expose] def GGR4SurvivorRow : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .F4 ∨ (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)) →
    LargeEvenLabelAll lab fun R _ I _ => GGR4RowFact R I

@[expose] def GGR4AmbExcl (T : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → GGInnerDiagOn Bs L → Nat.card Bs = 3 ^ 5 →
    ∀ [Fact (Nat.Prime 3)] (Γ : Type) [Fintype Γ] [DecidableEq Γ] (C : Matrix Γ Γ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
      (φ : Γ → MulAut ↥Bs) (h : Γ → V) (α : Γ → Module.Dual (ZMod 3) V),
    GGExtDatum ι C φ h α →
    (∃ e : Fin 4 ≃ Γ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) →
    ggAutomizer L Bs = Subgroup.closure (Set.range φ) →
    GGInnerDiagOnLabel (fun _ lab => T lab) 3 Bs L → False

@[expose] def GGR4ClassBig (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .A ∨ lab.tag = .twA) ∧ 24 ≤ lab.rank + 1) ∨
    ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) ∧ 24 ≤ 2 * lab.rank)

@[expose] def GGR4ClassSmall (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨
    lab.tag = .twD) ∧ ¬ GGR4ClassBig lab

@[expose] def GGClassicalTwoLocalRankNine : Prop :=
  ∀ (H : Type) [Group H] [Finite H] [Group.IsPerfect H] (lab : LargeEvenLabel),
    LargeEvenInLambda2 lab → GGHasLabel lab (H ⧸ Subgroup.center H) →
    (((lab.tag = .A ∨ lab.tag = .twA) ∧ 24 ≤ lab.rank + 1) ∨
      ((lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) ∧ 24 ≤ 2 * lab.rank)) →
    9 ≤ LargeEvenTwoLocalRank 3 H

@[expose] def GGSmallThreeRank : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
      lab.tag = .G2der ∨ lab.tag = .twF4der) →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), (∀ a ∈ A, a ∈ I) → IsElemAbelian 3 A → Nat.card A ≤ 3 ^ 2

@[expose] def GGE78TwoLocalRankSix : Prop :=
  ∀ (H : Type) [Group H] [Finite H] [Group.IsPerfect H] (lab : LargeEvenLabel),
    LargeEvenInLambda2 lab → (lab.tag = .E7 ∨ lab.tag = .E8) →
    GGHasLabel lab (H ⧸ Subgroup.center H) → 6 ≤ LargeEvenTwoLocalRank 3 H

@[expose] def GGProjDegreeF4 : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (d : ℕ), ringChar K ≠ 3 →
    ∀ (A N : Subgroup (Matrix.GeneralLinearGroup (Fin d) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))),
      IsElemAbelian 3 A → Nat.card A = 3 ^ 4 →
      ∀ [Fact (Nat.Prime 3)] (Γ : Type) [Fintype Γ] [DecidableEq Γ] (C : Matrix Γ Γ ℤ)
        (V : Type) [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥A ≃+ V)
        (φ : Γ → MulAut ↥A) (h : Γ → V) (α : Γ → Module.Dual (ZMod 3) V),
      GGExtDatum ι C φ h α →
      (∃ e : Fin 4 ≃ Γ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
        (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) →
      ggAutomizer N A = Subgroup.closure (Set.range φ) → 24 ≤ d

@[expose] def ggClassDeg (lab : LargeEvenLabel) : ℕ :=
  match lab.tag with
  | .A | .twA => lab.rank + 1
  | .B | .C => 2 * lab.rank
  | .D => if lab.rank = 3 then 4 else 2 * lab.rank
  | .twD => if lab.rank = 2 then 2 else if lab.rank = 3 then 4 else 2 * lab.rank
  | _ => 0

@[expose] def GGClassicalProjEmbedAt (d : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  (∀ r : R, MulAut.conj r ∈ I) ∧
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharP K 2)
      (ε : ↥(Subgroup.closure I) →* (Matrix.GeneralLinearGroup (Fin d) K ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))),
      Function.Injective ε

@[expose] def GGClassLinUni (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA ∨ (lab.tag = .D ∧ lab.rank = 3) ∨
    (lab.tag = .twD ∧ (lab.rank = 2 ∨ lab.rank = 3))

end CFSG.StandardType

end
