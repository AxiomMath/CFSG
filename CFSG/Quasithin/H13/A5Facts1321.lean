module

public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

section Cond

variable {V : Type} [CommGroup V]

structure Cond1321 (G L : Subgroup (MulAut V)) (v : MulAut V) : Prop where
  mem : v ∈ G
  ne_one : v ≠ 1
  sq : v * v = 1
  eq_sup : G = L ⊔ Subgroup.zpowers v
  sylow : ∃ S : Subgroup (MulAut V), IsSylowTwoOf S L ∧ S ≤ Subgroup.centralizer {v}
  rank : rkIdx (fixV (Subgroup.zpowers v)) ≤ 2
  pair : ∀ g ∈ G, (∃ k : ℕ, (v * (g * v * g⁻¹)) ^ 2 ^ k = 1) ∨ (v * (g * v * g⁻¹)) ^ 3 = 1

end Cond

@[expose] def FactLieRows1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ ((∃ n, n ≠ 2 ∧ BinaryNaturalSL L ⊤ ⊥ 2 n) ∨ (∃ n, n ≠ 1 ∧ BinaryNaturalSL L ⊤ ⊥ 3 n) ∨
        (∃ n, 2 ≤ n ∧ BinaryNaturalSp4 L ⊤ ⊥ n) ∨ (∃ n, 2 ≤ n ∧ G2Natural L ⊤ ⊥ n) ∨
        (∃ m, 2 ≤ m ∧ BinaryOrthogonalFour L ⊤ ⊥ m) ∨ (∃ m, BinaryNaturalSU3 L ⊤ ⊥ m) ∨
        (∃ f, BinaryNaturalSz L ⊤ ⊥ f) ∨ (∃ m, 1 ≤ m ∧ BinaryNineTensor L ⊤ ⊥ m) ∨
        (∃ a, 1 ≤ a ∧ TwistedTensorSp4 L ⊤ ⊥ a))

@[expose] def FactM12Row1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), L ≤ G →
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) → M12Ten L ⊤ ⊥ →
      ∀ v ∈ G, orderOf v = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers v))

@[expose] def FactM22HatRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), L ≤ G →
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) → Mhat22Twelve L ⊤ ⊥ →
      ∀ v ∈ G, orderOf v = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers v))

@[expose] def FactJ2Row1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G L : Subgroup (MulAut V)), L ≤ G →
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) → IsSporadic .J2 ↥L → J2Twelve L ⊤ ⊥ →
      ∀ v ∈ G, orderOf v = 2 → 3 ≤ rkIdx (fixV (Subgroup.zpowers v))

@[expose] def FactA5Rows1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ (BinaryNaturalSL L ⊤ ⊥ 2 2 ∨ BinaryOrthogonalFour L ⊤ ⊥ 1)

@[expose] def FactSymRows1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      B42Case5 G A → ∃ π : ↥(alternatingGroup (Fin 7)) →* ↥L, Function.Surjective π

@[expose] def FactA7FourRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ B42Case7 G L A

@[expose] def FactTripleA6Row1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ B42Case8 G L A

@[expose] def FactLNatRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      B42Case9 G L → rkIdx (fixV (Subgroup.zpowers v)) = 1

@[expose] def FactL5TenRow1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)) (v : MulAut V), B4Hyp G L → Cond1321 G L v →
      ¬ B42Case11 G L A

@[expose] def Rows1321Remaining {V : Type} [CommGroup V] [Finite V]
    (G L A : Subgroup (MulAut V)) : Prop :=
  B42Case6 G L A ∨ BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1 ∨ B42Case9 G L ∨ B42Case10 G L A ∨
    G2Natural (ffJ G) ⊤ ⊥ 1 ∨ G2NaturalDerived L ⊤ ⊥ 1

@[expose] def FactRankRows1321 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ w : V, w ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut V)), B4Hyp G L → Rows1321Remaining G L A →
      IsSimpleGroup ↥L ∧ 2 ≤ CFSG.Open.pRank 3 L

@[expose] def FactA7Grp1321 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nontrivial K →
    (∃ π : ↥(alternatingGroup (Fin 7)) →* K, Function.Surjective π) →
    ∀ v : MulAut K, v ≠ 1 → v * v = 1 →
      (∀ g : K, (∃ k : ℕ, (v * (MulAut.conj g * v * (MulAut.conj g)⁻¹)) ^ 2 ^ k = 1) ∨
        (v * (MulAut.conj g * v * (MulAut.conj g)⁻¹)) ^ 3 = 1) →
      ∀ Y : Subgroup (MulAut K), Y ≤ Subgroup.centralizer {v} →
        (∀ k : K, v k = k → ∀ y ∈ Y, MulAut.conj k * y * (MulAut.conj k)⁻¹ ∈ Y) →
        Group.IsSolvable ↥Y → Y = oTwoRes Y → Y = ⊥

@[expose] def FactL3Grp1321 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nontrivial K →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ π : ↥(StatedSL 3 F) →* K, Function.Surjective π) →
    ∀ v : MulAut K, v ≠ 1 → v * v = 1 → (∃ S : Sylow 2 K, ∀ s ∈ S, v s = s) →
      ∀ Y : Subgroup (MulAut K), Y ≤ Subgroup.centralizer {v} → Y = oTwoRes Y → Y = ⊥

end CFSG.Quasithin.H13.A5
