module

public import CFSG.Quasithin.Background.E6Gamma
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique
open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

section Cases

variable {G : Type} [Group G]

@[expose] def E68Case1 {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (T M U L : Subgroup G) :
    Prop :=
  ∃ n : ℕ,
    ((2 ≤ n ∧ StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 n) ∨
      (Odd n ∧ 3 ≤ n ∧ SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n) ∨
      (1 ≤ n ∧ StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n) ∨
      (2 ≤ n ∧ StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 n)) ∧
    IsPGroup 2 (Subgroup.center ↥L) ∧
    L ⊓ M = L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
      Set G) ∧
    IsCyclic (autI hV (L ⊓ M)) ∧ Nat.card (autI hV (L ⊓ M)) = 2 ^ n - 1 ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ E3.mQuot V U ∧
    (1 < n → ⁅V, L ⊓ M⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      ⁅V, L ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V ∧ E3.mQuot ⁅V, L ⊓ M⁆ ⊥ = n)

@[expose] def E68Case2 {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (T M U L : Subgroup G) :
    Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    ((2 ≤ n ∧ StatedClassicalModel ↥L .PSp 2 2 n) ∨
      (n = 1 ∧ Nonempty (↥L ≃* alternatingGroup (Fin 6)))) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ E3.mQuot V U ∧
    (1 < n → ⁅V, L ⊓ M⁆ ⊓ (V ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
      ⁅V, L ⊓ M⁆ ⊔ (V ⊓ Subgroup.centralizer (L : Set G)) = V) ∧
    ((L ⊓ M = L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
        Set G) ∧
      ((E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 2 * n ∧
          ∃ A : Subgroup G, U < A ∧ A < V ∧ E3.mQuot V A = n ∧
            ¬ L ⊓ Subgroup.centralizer (A : Set G) ≤ M) ∨
        (n = 1 ∧ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1))) ∨
     (L ⊓ Subgroup.normalizer (((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L : Subgroup G) :
        Set G) ≤ L ⊓ M ∧ L ⊓ M < L ∧
      (∀ K : Subgroup G, L ⊓ M ≤ K → K ≤ L → K = L ⊓ M ∨ K = L) ∧
      E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = n ∧
      (1 < n → IsCyclic (autI hV (L ⊓ M)) ∧ Nat.card (autI hV (L ⊓ M)) = 2 ^ n - 1)))

@[expose] def E68HypOrMax (M V U : Subgroup G) : Prop :=
  E3.mQuot V U = 1 ∨ ∀ W : Subgroup G, U < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M

@[expose] def E68Case3 (T M V U L : Subgroup G) : Prop :=
  StatedClassicalModel ↥L .PSL 4 2 1 ∧
    Nonempty ((↥(L ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) ⧸
      CFSG.pCore 2 ↥(L ⊔ (T ⊓ Subgroup.centralizer (V : Set G)))) ≃* Equiv.Perm (Fin 8)) ∧
    (E68HypOrMax M V U → U = V ⊓ Subgroup.centralizer (L : Set G)) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 ∧ E3.rParam V = 1

@[expose] def E68Case4 (M V U L : Subgroup G) : Prop :=
  (Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨
    (Nat.card (Subgroup.center ↥L) = 3 ∧
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 6))) ∨
    (Nat.card (Subgroup.center ↥L) = 3 ∧
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)))) ∧
    (∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ E3.mQuot V A = 1 ∧
      ¬ L ⊓ Subgroup.centralizer (A : Set G) ≤ M) ∧
    E3.rParam V = 1 ∧ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ 2

@[expose] def E68Case5 (M V U L : Subgroup G) : Prop :=
  ((∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧ StatedClassicalModel ↥L .PSL 2 p 1) ∨
    StatedClassicalModel ↥L .PSL 3 3 1 ∨ Nonempty (↥L ≃* NativeSporadic.Carrier .M11)) ∧
    (E68HypOrMax M V U → U = V ⊓ Subgroup.centralizer (L : Set G)) ∧
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 ∧ E3.rParam V = 1

end Cases

@[expose] def E68Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G) (hV : CFSG.Open.IsElemAbelian 2 V),
    HypE61 T M V → U ∈ gammaE64 V M → IsComponentIn L (Subgroup.centralizer (U : Set G)) →
    ¬ L ≤ M ∧ (E68Case1 hV T M U L ∨ E68Case2 hV T M U L ∨ E68Case3 T M V U L ∨
      E68Case4 M V U L ∨ E68Case5 M V U L)

end E6

end CFSG.Quasithin
