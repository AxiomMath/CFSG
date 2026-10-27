module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.Open.FusionDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped commutatorElement

inductive Row : Type
  | D6
  | twD7
  | E7
  deriving DecidableEq

namespace Row

@[expose] def n : Row → ℕ
  | D6 => 6
  | twD7 => 7
  | E7 => 7

@[expose] def m (r : Row) : ℕ := r.n + 1

end Row

@[expose] def IsRow {G : Type} [Group G] (r : Row) (K : Subgroup G) : Prop :=
  LargeEvenMarking K (fun lab _ _ _ _ _ =>
    lab.n = 1 ∧ ((r = Row.D6 ∧ lab.tag = .D ∧ lab.rank = 6) ∨
      (r = Row.twD7 ∧ lab.tag = .twD ∧ lab.rank = 7) ∨
      (r = Row.E7 ∧ lab.tag = .E7 ∧ lab.rank = 0)))

@[expose] def HypSetup {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (m : ℕ) : Prop :=
  FS81HypA b₀ K ∧ IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E ∧ b₀ ∈ E ∧
    Nat.card E = 3 ^ m ∧ 7 ≤ m ∧ 2 ^ m * m.factorial < Nat.card (ggAutomizer ⊤ E)

@[expose] def CanonPosition {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G)
    (r : Row) : Prop :=
  IsRow r K ∧ Disjoint (Subgroup.zpowers b₀) (E ⊓ K) ∧ Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E ∧
    IsMaxElemAb3 K (E ⊓ K) ∧ Nat.card ↥(E ⊓ K) = 3 ^ r.n ∧
    Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K

@[expose] def StdAssumptions {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G)
    (r : Row) : Prop :=
  IsSimpleGroup G ∧ HypSetup b₀ K E r.m ∧ CanonPosition b₀ K E r

abbrev Coords (k : ℕ) : Type := Fin k → ZMod 3

structure Basis3 (G : Type) [Group G] (k : ℕ) where
  b : Fin k → G
  comm : ∀ i j, Commute (b i) (b j)
  ord : ∀ i, orderOf (b i) = 3
  indep : ∀ e : Coords k, (List.ofFn fun i => b i ^ (e i).val).prod = 1 → e = 0

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

@[expose] def vec (B : Basis3 G k) (e : Coords k) : G :=
  (List.ofFn fun i => B.b i ^ (e i).val).prod

@[expose] def span (B : Basis3 G k) : Subgroup G := Subgroup.closure (Set.range B.b)

@[expose] def line (B : Basis3 G k) (e : Coords k) : Subgroup G := Subgroup.zpowers (B.vec e)

@[expose] def Acts (B : Basis3 G k) (g : G) (A : Matrix (Fin k) (Fin k) (ZMod 3)) : Prop :=
  ∀ j, g * B.b j * g⁻¹ = B.vec (fun i => A i j)

@[expose] def realized (B : Basis3 G k) (H : Subgroup G) : Set (Matrix (Fin k) (Fin k) (ZMod 3)) :=
  {A | ∃ g ∈ H, B.Acts g A}

end Basis3

@[expose] def IsConjLine {G : Type} [Group G] (x : G) (Z : Subgroup G) : Prop :=
  ∃ g : G, Subgroup.zpowers (g * x * g⁻¹) = Z

@[expose] def IsConjLineIn {G : Type} [Group G] (S : Subgroup G) (x : G) (Z : Subgroup G) : Prop :=
  ∃ g ∈ Subgroup.normalizer (S : Set G), Subgroup.zpowers (g * x * g⁻¹) = Z

@[expose] def wt {k : ℕ} (e : Coords k) : ℕ := (Finset.univ.filter fun i => e i ≠ 0).card

@[expose] def Adapted {G : Type} [Group G] {n : ℕ} (B : Basis3 G (n + 1)) (b₀ : G)
    (K E : Subgroup G) : Prop :=
  B.span = E ∧ B.b 0 = b₀ ∧ ∀ i : Fin (n + 1), i ≠ 0 → B.b i ∈ K

@[expose] def spMat {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) :
    Matrix (Fin k) (Fin k) (ZMod 3) := fun i j => if i = σ j then s j else 0

@[expose] def IsSign {k : ℕ} (s : Fin k → ZMod 3) : Prop := ∀ i, s i = 1 ∨ s i = -1

@[expose] def spSet {k : ℕ}
    (p : Equiv.Perm (Fin k) → (Fin k → ZMod 3) → Prop) : Set (Matrix (Fin k) (Fin k) (ZMod 3)) :=
  {A | ∃ σ s, IsSign s ∧ p σ s ∧ A = spMat σ s}

@[expose] def monoFix0 (n : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) :=
  spSet fun σ s => σ 0 = 0 ∧ s 0 = 1

@[expose] def monoN0 (n : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) :=
  spSet fun σ _ => σ 0 = 0

@[expose] def evenFix0 (n : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) :=
  spSet fun σ s => σ 0 = 0 ∧ s 0 = 1 ∧ ∏ i : Fin n, s i.succ = 1

@[expose] def evenN0 (n : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) :=
  spSet fun σ s => σ 0 = 0 ∧ ∏ i : Fin n, s i.succ = 1

@[expose] def evenAll0 (n : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)) :=
  spSet fun σ s => σ 0 = 0 ∧ ∏ i : Fin (n + 1), s i = 1

@[expose] def LocalOrthI {G : Type} [Group G] {n : ℕ} (B : Basis3 G (n + 1)) (b₀ : G) : Prop :=
  B.realized (Subgroup.centralizer ({b₀} : Set G)) = monoFix0 n ∧
    (B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = monoFix0 n ∨
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = monoN0 n)

@[expose] def LocalOrthII {G : Type} [Group G] {n : ℕ} (B : Basis3 G (n + 1)) (b₀ : G) : Prop :=
  B.realized (Subgroup.centralizer ({b₀} : Set G)) = evenFix0 n ∧
    (B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenFix0 n ∨
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenN0 n ∨
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) = evenAll0 n)

@[expose] def LocalE7 {G : Type} [Group G] (B : Basis3 G 8) (b₀ : G) : Prop :=
  Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) = 2903040 ∧
    (B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) =
        B.realized (Subgroup.centralizer ({b₀} : Set G)) ∨
      Nat.card ↥(B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) = 2 * 2903040) ∧
    B.realized (Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G)) =
      spSet fun σ s => σ 0 = 0 ∧ s 0 = 1 ∧ σ 1 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1

@[expose] def LocalData {G : Type} [Group G] : (r : Row) → Basis3 G (r.n + 1) → G → Prop
  | Row.D6, B, b₀ => LocalOrthI B b₀ ∨ LocalOrthII B b₀
  | Row.twD7, B, b₀ => LocalOrthI B b₀ ∨ LocalOrthII B b₀
  | Row.E7, B, b₀ => LocalE7 B b₀

@[expose] def Fus42 {G : Type} [Group G] {k : ℕ} (B : Basis3 G k) (b₀ : G) : Prop :=
  ¬ (Subgroup.normalizer (B.span : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ∧
    ∀ g : G, g * b₀ * g⁻¹ ∈ B.span →
      ∃ x ∈ Subgroup.normalizer (B.span : Set G), g * b₀ * g⁻¹ = x * b₀ * x⁻¹

@[expose] def OddCoreTrivial {G : Type} [Group G] (E : Subgroup G) : Prop :=
  ∀ N : Subgroup ↥(ggAutomizer ⊤ E), N.Normal → Odd (Nat.card N) → N = ⊥

@[expose] def RecOutD6 {G : Type} [Group G] [Finite G] (B : Basis3 G 7) (b₀ : G) : Prop :=
  Nat.card ↥(ggAutomizer ⊤ B.span) = 2903040 ∧
    ∀ e : Coords 7, e ≠ 0 → (IsConjLine b₀ (B.line e) ↔
      ((wt e = 1 ∧ e 0 ≠ 0) ∨ (wt e = 2 ∧ e 0 = 0) ∨
        (wt e = 7 ∧ ∏ i : Fin 6, e i.succ = 1)))

@[expose] def RecOutTwD7 {G : Type} [Group G] [Finite G] (B : Basis3 G 8) (b₀ : G) : Prop :=
  Nat.card ↥(ggAutomizer ⊤ B.span) = 696729600 ∧
    (∀ e : Coords 8, e ≠ 0 → (IsConjLine b₀ (B.line e) ↔ (wt e = 1 ∨ wt e = 4 ∨ wt e = 7))) ∧
    (∀ e : Coords 8, e ≠ 0 → (IsConjLineIn B.span (b₀ * B.b 1) (B.line e) ↔
      (wt e = 2 ∨ (wt e = 8 ∧ ∏ i : Fin 8, e i = -1))))

@[expose] def RecOutE7 {G : Type} [Group G] [Finite G] (B : Basis3 G 8) (b₀ : G) : Prop :=
  Nat.card ↥(ggAutomizer ⊤ B.span) = 696729600 ∧
    (∀ e : Coords 8, e ≠ 0 → (IsConjLine b₀ (B.line e) ↔
      ((wt e = 1 ∧ (e 0 ≠ 0 ∨ e 1 ≠ 0)) ∨ (wt e = 2 ∧ e 0 = 0 ∧ e 1 = 0) ∨
        (wt e = 3 ∧ e 0 ≠ 0 ∧ e 1 ≠ 0) ∨
        (wt e = 7 ∧ e 0 = 0 ∧ ∏ i : Fin 6, e i.succ.succ = 1) ∨
        (wt e = 7 ∧ e 1 = 0 ∧ ∏ i : Fin 6, e i.succ.succ = -1)))) ∧
    (∀ e : Coords 8, e ≠ 0 → (IsConjLineIn B.span (b₀ * B.b 1) (B.line e) ↔
      2 * (e 0 ^ 2 + e 1 ^ 2) + ∑ i : Fin 6, e i.succ.succ ^ 2 = 1))

@[expose] def RecOut {G : Type} [Group G] [Finite G] : (r : Row) → Basis3 G (r.n + 1) → G → Prop
  | Row.D6, B, b₀ => RecOutD6 B b₀
  | Row.twD7, B, b₀ => RecOutTwD7 B b₀
  | Row.E7, B, b₀ => RecOutE7 B b₀

@[expose] def IsSylow2In {G : Type} [Group G] (S Y : Subgroup G) : Prop :=
  S ≤ Y ∧ IsPGroup 2 S ∧ ∀ T : Subgroup G, T ≤ Y → IsPGroup 2 T → S ≤ T → T = S

end CFSG.StandardType.FrameRoute.FS81
