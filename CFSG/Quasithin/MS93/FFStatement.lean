module

public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V]

structure FFHyp (X K : Subgroup (MulAut V)) : Prop where
  le : K ≤ X
  le_normalizer : X ≤ Subgroup.normalizer (K : Set (MulAut V))
  quasisimple : CFSG.IsQuasisimple ↥K
  sqtk : SQTKGroup ↥K
  rankTwo : IsRankTwoLie2Derived (↥K ⧸ Subgroup.center ↥K)
  cent : ∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → ∀ e : ℕ, c ^ 2 ^ e = 1 → c = 1
  two : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K
  gen : ∃ T : Subgroup (MulAut V), IsSylowTwoOf T K ∧ G6.submoduleClosure X (fixV T) = ⊤
  fix : fixV X = ⊥
  ff : IsFFModule X

@[expose] def FFCaseSL3 (K : Subgroup (MulAut V)) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ n ∧ Nat.card F = 2 ^ n ∧
    Nonempty (↥K ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∧
    IsPSL 3 2 n (↥K ⧸ Subgroup.center ↥K) ∧
    ((FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)).Realizes K ⊤ ⊥ ∨
      DirectSumOfCopies K ⊤ ⊥ (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 F)) 2)

@[expose] def FFCaseHatA6 (K : Subgroup (MulAut V)) : Prop :=
  TripleA6Six K ⊤ ⊥ ∧ IsHat ↥K ↥(alternatingGroup (Fin 6)) ∧ Nat.card V = 2 ^ 6 ∧
    XMod.IsIrrSec ↥K (⊥ : Subgroup V) ⊤

@[expose] def FFCaseSp4 (K : Subgroup (MulAut V)) : Prop :=
  (∃ n, 2 ≤ n ∧ BinaryNaturalSp4 K ⊤ ⊥ n) ∨ AlternatingNatural K ⊤ ⊥ 6

@[expose] def FFCaseG2 (X K : Subgroup (MulAut V)) : Prop :=
  (∃ n, 2 ≤ n ∧ G2Natural K ⊤ ⊥ n) ∨ (G2NaturalDerived K ⊤ ⊥ 1 ∧ X ≠ K ∧ G2Natural X ⊤ ⊥ 1)

@[expose] def FFExcludedType (Y : Type) [Group Y] : Prop :=
  (∃ e, Is3D4 2 e Y) ∨ (∃ e, Is2F4 e Y) ∨ IsTits Y ∨ (∃ e, IsPSU 4 2 e Y) ∨ (∃ e, IsPSU 5 2 e Y)

@[expose] def FFConclusion (X K : Subgroup (MulAut V)) : Prop :=
  commV K = ⊤ ∧ fixV K = ⊥ ∧
    (FFCaseSL3 K ∨ FFCaseHatA6 K ∨ FFCaseSp4 K ∨ FFCaseG2 X K) ∧
    ¬ FFExcludedType (↥K ⧸ Subgroup.center ↥K)

@[expose] def MS14AS : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X K : Subgroup (MulAut V), FFHyp X K → FFConclusion X K

end CFSG.Quasithin.MS93
