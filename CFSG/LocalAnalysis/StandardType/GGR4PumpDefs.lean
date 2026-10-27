module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGPropFourOneTransfer
public import CFSG.LocalAnalysis.StandardType.GGStdSubExist
public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProofFork

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGR4JLabel (R : Type) [Group R] : Prop :=
  ∃ f : ℕ, GGHasLabel ⟨.C, 3, f⟩ R ∨ (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ R) ∨
    (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ R) ∨ GGHasLabel ⟨.twD, 4, f⟩ R

@[expose] def GGR4JInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsPmOne Bs → ∀ [Fact p.Prime], p = 3 →
      ∀ (Λ : Type) [Fintype Λ] [DecidableEq Λ] (C : Matrix Λ Λ ℤ) (b c : Λ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (φ' : Option Λ → MulAut ↥Bs) (h' : Option Λ → V) (α' : Option Λ → Module.Dual (ZMod p) V),
      GGExtDatum ι (ggAttachCartan C c) φ' h' α' →
      Submodule.span (ZMod p) (Set.range h') = ⊤ →
      (∃ e : Fin 4 ≃ Λ, ((∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
          (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∧
        ((b = e 0 ∧ c = e 1) ∨ (b = e 3 ∧ c = e 2))) →
      ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)) →
      ggAutomizer K Bs = Subgroup.closure
        ((fun i : Λ => φ' (some i)) '' {i | i ≠ b} ∪ {φ' none}) →
      ggAutomizer J Bs = Subgroup.closure (Set.range fun j : {j : Λ // j ≠ b} => φ' (some j)) ∧
        GGR4JLabel (J ⧸ Subgroup.center J)

@[expose] def GGCentreTwoKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∨ lab.tag = .F4) →
    LargeEvenLabelAll lab fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ g ∈ Subgroup.center L', ∃ k : ℕ, orderOf g = 2 ^ k


@[expose] def GGPumpCLabelKnown : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ≠ 1 → e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ (J : Subgroup L') (k f : ℕ), CFSG.Assembly.IsComponentOf J (ggFixSub e) → 3 ≤ k →
            GGHasLabel ⟨.C, k, f⟩ (J ⧸ Subgroup.center J) →
            ((lab.tag = .B ∨ lab.tag = .C) ∧ k < lab.rank ∧ lab.n = f) ∨
              (k = 3 ∧ lab.tag = .F4 ∧ lab.n = f)

@[expose] def GGTorusAutCardSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) (r N : ℕ) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      p ^ r ≤ Nat.card A ∧
        Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = N

@[expose] def GGTorusAutCardSCF4 (p f : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) (r N : ℕ) :
    Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      (∃ e ∈ A, ∃ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) ∧
        GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J)) →
      p ^ r ≤ Nat.card A ∧
        Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = N

@[expose] def GGPumpCAutKnown : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f : ℕ, 1 ≤ f → p ∣ (2 ^ f) ^ 2 - 1 →
    (∀ N : ℕ, 3 ≤ N → LargeEvenLabelAll ⟨.C, N, f⟩ fun R _ I _ =>
      GGTorusAutCardSC p R I N (2 ^ N * N.factorial)) ∧
    LargeEvenLabelAll ⟨.F4, 4, f⟩ fun R _ I _ => GGTorusAutCardSCF4 p f R I 4 1152

@[expose] def GGPumpCInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ f : ℕ, GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J) →
    p ∣ (2 ^ f) ^ 2 - 1 →
    ∀ z ∈ D, z ≠ 1 → ∀ X : Subgroup G,
      LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X → J ≤ X →
      LargeEvenPComponent p (X ⊓ Subgroup.centralizer ({x} : Set G)) J → GGInnerDiagOn Bs X →
      3 ≤ Nat.log p (Nat.card (Bs ⊓ J : Subgroup G)) →
      ¬ (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X →
      ∃ N : ℕ, 3 ≤ N ∧ p ^ (N + 1) ≤ Nat.card Bs ∧
        (Nat.card (ggAutomizer X Bs) = 2 ^ N * N.factorial ∨
          (N = 4 ∧ Nat.card (ggAutomizer X Bs) = 1152))

@[expose] def GGCentreTrivialTwKnown : Prop :=
  ∀ f : ℕ, 1 ≤ f →
    ((3 ∣ 2 ^ f - 1 → LargeEvenLabelAll ⟨.twA, 5, f⟩ fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Subgroup.center L' = ⊥) ∧
     (3 ∣ 2 ^ f + 1 → LargeEvenLabelAll ⟨.A, 5, f⟩ fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Subgroup.center L' = ⊥) ∧
     LargeEvenLabelAll ⟨.twD, 4, f⟩ fun R _ _ _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Subgroup.center L' = ⊥)

@[expose] def GGPumpTwInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → p = 3 → ∀ f : ℕ,
    ((3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (J ⧸ Subgroup.center J)) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (J ⧸ Subgroup.center J)) →
    ∀ z ∈ D, z ≠ 1 → ∀ X : Subgroup G,
      LargeEvenPComponent p (Subgroup.centralizer ({z} : Set G)) X → J ≤ X →
      LargeEvenPComponent p (X ⊓ Subgroup.centralizer ({x} : Set G)) J → GGInnerDiagOn Bs X →
      3 ≤ Nat.log p (Nat.card (Bs ⊓ J : Subgroup G)) →
      ¬ (⁅X, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X →
      ∃ N : ℕ, 3 ≤ N ∧ p ^ (N + 1) ≤ Nat.card Bs ∧
        (Nat.card (ggAutomizer X Bs) = 2 ^ N * N.factorial ∨
          (N = 4 ∧ Nat.card (ggAutomizer X Bs) = 1152))

end CFSG.StandardType
