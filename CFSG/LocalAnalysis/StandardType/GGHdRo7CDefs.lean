module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def C2SP (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (a : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod p), σ 0 = 0 ∧ c 0 = 1 ∧
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)

@[expose] def C2Full (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (a : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)

@[expose] def C2SignX (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (a : V ≃ₗ[ZMod p] V) : Prop :=
  a (b 0) = -b 0 ∧ ∀ i, i ≠ 0 → a (b i) = b i

@[expose] def C2Swap (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (a : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ (i : Fin (n + 1)) (ε : ZMod p), i ≠ 0 ∧ (ε = 1 ∨ ε = -1) ∧ a (b 0) = ε • b i ∧
    a (b i) = ε • b 0 ∧ ∀ j, j ≠ 0 → j ≠ i → a (b j) = b j

@[expose] def C2Transv (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Fact p.Prime]
    (a : V ≃ₗ[ZMod p] V) : Prop :=
  Module.finrank (ZMod p) (ggLinMove a) = 1 ∧ ∀ w, a (a w - w) = a w - w

structure C2LinData (p : ℕ) [Fact p.Prime] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (AL Q A : Subgroup (V ≃ₗ[ZMod p] V)) : Prop where
  hp : p = 3
  hn : 5 ≤ n
  hAL : ∀ a, a ∈ AL ↔ C2SP p b a
  hALA : AL ≤ A
  hQA : Q ≤ A
  hStab : ∀ a ∈ A, a (b 0) = b 0 → ∀ s, C2SP p b s → C2SP p b (a * s * a⁻¹)
  hNoT : ∀ a ∈ A, ¬ C2Transv p a
  hQgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ s ∈ S, s ∈ Q ∧ GGLinRefl s) ∧ Q = Subgroup.closure S ∧
    ∀ s ∈ S, ∀ t ∈ S,
      Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) s t
  hJ : ∃ a ∈ Q, a ∈ AL ∧ a ≠ 1
  hnle : ¬ Q ≤ AL

@[expose] def C2NormalizerLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (a : V ≃ₗ[ZMod p] V),
    (∀ s, C2SP p b s → C2SP p b (a * s * a⁻¹)) → a (b 0) = b 0 → C2SP p b a

@[expose] def C2ReflLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (A : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ a, C2SP p b a → a ∈ A) → (∀ a ∈ A, a (b 0) = b 0 → C2SP p b a) →
    (∀ a ∈ A, ¬ C2Transv p a) →
    ∀ r ∈ A, GGLinRefl r → C2SP p b r ∨ C2SignX p b r ∨ C2Swap p b r

@[expose] def C2JoinLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n → ∀ (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (AL Q : Subgroup (V ≃ₗ[ZMod p] V)) (S : Set (V ≃ₗ[ZMod p] V)),
    (∀ a, a ∈ AL ↔ C2SP p b a) →
    (∀ s ∈ S, s ∈ Q ∧ GGLinRefl s ∧ (C2SP p b s ∨ C2SignX p b s ∨ C2Swap p b s)) →
    Q = Subgroup.closure S → (∃ s ∈ S, C2Swap p b s) →
    ∃ F : Subgroup (V ≃ₗ[ZMod p] V), (∀ a, a ∈ F ↔ C2Full p b a) ∧ AL ⊔ Q = F ∧ ZS.LinWeyl p F

@[expose] def C2KContraLeaf : Prop :=
  C2NormalizerLeaf → C2ReflLeaf → ∀ (p : ℕ) [Fact p.Prime], p = 3 → ∀ (n : ℕ), 5 ≤ n →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (AK AL A : Subgroup (V ≃ₗ[ZMod p] V)) (c : ZMod p),
    (∀ a, a ∈ AK ↔ C2SP p b a) → AK ≤ A → AL ≤ A →
    (∀ a ∈ A, a (b 0) = b 0 → ∀ s, C2SP p b s → C2SP p b (a * s * a⁻¹)) →
    (∀ a ∈ A, ¬ C2Transv p a) →
    (∀ a ∈ AL, a (c • b 0 + b 1 + b 2) = c • b 0 + b 1 + b 2) →
    AL = Subgroup.closure {r | r ∈ AL ∧ GGLinRefl r} →
    2 ^ n * n.factorial ≤ Nat.card AL → False

@[expose] def XDatumGraphLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (Bs X : Subgroup G),
    GGResXDatum p Bs X → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (ι : Additive ↥Bs ≃+ V),
      ∃ S : Set (V ≃ₗ[ZMod p] V),
        (∀ s ∈ S, s ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ∧ GGLinRefl s) ∧
        (ggAutomizer X Bs).map (ggLin (p := p) ι) = Subgroup.closure S ∧
        ∀ s ∈ S, ∀ t ∈ S,
          Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) s t

@[expose] def NoTVLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (Bs : Subgroup G),
    GGNoTransvection p Bs → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (ι : Additive ↥Bs ≃+ V), ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), ¬ C2Transv p a

@[expose] def C2LModelLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowCorank2C p J L →
    ∃ (n : ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hx : x ∈ Bs),
      p = 3 ∧ 5 ≤ n ∧ ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = b 0 ∧
      ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ C2SP p b a

@[expose] def C2AJLeaf : Prop :=
  GGResXDichotomyInput → GGTBJInputR → GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowCorank2C p J L →
    ggAutomizer J Bs ≠ ⊥ ∧ ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs

@[expose] def C2KModelLeaf : Prop :=
  GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowCorank2C p J K →
    ∃ (n : ℕ) (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hy : y ∈ Bs) (hx : x ∈ Bs),
      p = 3 ∧ 5 ≤ n ∧ ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = b 0 ∧
      (∀ a, a ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) ↔ C2SP p b a) ∧
      ∃ c : ZMod p, ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = c • b 0 + b 1 + b 2

@[expose] def C2KStabLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
    ∀ [Fact p.Prime], GGResRowAt ggRowCorank2C p J K →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hy : y ∈ Bs), p = 3 → 5 ≤ n →
      ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = b 0 →
      (∀ a, a ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) ↔ C2SP p b a) →
      ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (b 0) = b 0 →
        ∀ s, C2SP p b s → C2SP p b (a * s * a⁻¹)

@[expose] def C2LOrderLeaf : Prop :=
  GGTCJKnown → GGResXDichotomyInput → GGTBJInputR → GGLabelRigidInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResRowAt ggRowCorank2C p J K →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hy : y ∈ Bs), p = 3 → 5 ≤ n →
      ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = b 0 →
      (∀ a, a ∈ (ggAutomizer K Bs).map (ggLin (p := p) ι) ↔ C2SP p b a) →
      2 ^ n * n.factorial ≤ Nat.card (ggAutomizer L Bs)

@[expose] def C2LFixGenLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGResXDatum p Bs L → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (ι : Additive ↥Bs ≃+ V) (hx : x ∈ Bs),
      (∀ a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι),
        a (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) = ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) ∧
      (ggAutomizer L Bs).map (ggLin (p := p) ι) = Subgroup.closure
        {r | r ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ∧ GGLinRefl r}

end CFSG.StandardType.HdRo7C
