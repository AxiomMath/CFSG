module

public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Quasithin.Background.E6Gamma
public import CFSG.Quasithin.Background.E2Seventeen
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

@[expose] def Ch6InE63 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V : Subgroup G), E6.HypE61 T M V →
    ∀ hV : IsElemAbelian 2 V, 2 < mParam (autI hV M) →
      (mParam (autI hV M) : ℕ∞) ≤ rParam V ∧ sParam hV = mParam (autI hV M)

@[expose] def Ch6InE610Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G), E6.HypE61 T M V →
    U ∈ E6.gammaE64 V M → mQuot V U = 1 →
    (V ⊓ Subgroup.centralizer (T : Set G) ⊓ U ≠ ⊥ ∨
      QuasithinUnique.CharTwo (Subgroup.centralizer (U : Set G))) →
    ¬ omegaOneCenterOf (T ⊓ Subgroup.normalizer (U : Set G)) ≤ U

@[expose] def Ch6InE612 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G), E6.HypE61 T M V → U ≠ ⊥ → U ≤ V →
    M ⊓ Subgroup.centralizer (U : Set G) = M ⊓ Subgroup.centralizer (V : Set G) →
    ¬ Subgroup.centralizer (U : Set G) ≤ M →
      (∃ U₁ : Subgroup G, U ≤ U₁ ∧ U₁ ≤ V ∧ mQuot V U₁ = 1 ∧
        ¬ Subgroup.centralizer (U₁ : Set G) ≤ M) ∧ rParam V = 1

@[expose] def Ch6InE626 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V M H S : Subgroup G) (j : ℕ),
    quasithinIsSylowTwo T → V ≠ ⊥ → IsElemAbelian 2 V → V ≤ T →
    T ≤ Subgroup.normalizer (V : Set G) →
    Subgroup.normalizer (V : Set G) ≤ M → IsUniqueM (Subgroup.normalizer (ch6Q T V : Set G)) M →
    0 < j → E1.nParam H ≤ j → IsSylowIn 2 S H → ch6Q T V ≤ S → S ≤ T →
    (j : ℕ∞) < rParam V → thompsonJk j S ≤ S ⊓ Subgroup.centralizer (V : Set G) →
      H ≤ M ∧ Subgroup.normalizer (S : Set G) ≤ M

@[expose] def Ch6InH11 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)) (a : ℕ),
    (∀ v : V, v ^ 2 = 1) → 1 < a → L ≤ M → M ≤ Subgroup.normalizer (L : Set (MulAut V)) →
    BinaryOrthogonalFour L ⊤ ⊥ a →
    ∀ A : Subgroup (MulAut V), A ≤ M → A ≠ ⊥ → IsElemAbelian2 A →
      rk A + a ≤ rkIdx (fixV A) + 1 ∧
      (rk A + 2 ≤ rkIdx (fixV A) ∨
        (a = 2 ∧ ∃ t ∈ A, rkIdx (fixV (Subgroup.zpowers t)) = a)) ∧
      (A ≤ L → rk A + a ≤ rkIdx (fixV A))

@[expose] def StmtKuM22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H P : Subgroup G) (z : G), IsSimpleGroup G →
    quasithinIsSylowTwo T → T ≤ M → T ≤ H →
    IsElemAbelian 2 (pCoreOf 2 M) → Nat.card (pCoreOf 2 M) = 16 →
    M = Subgroup.normalizer (pCoreOf 2 M : Set G) →
    M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) = pCoreOf 2 M →
    (∃ φ : ↥M →* Equiv.Perm (Fin 5), Function.Surjective φ ∧ φ.ker = (pCoreOf 2 M).subgroupOf M) →
    IsNatModCh5 (oTwoUpper M) (pCoreOf 2 M) 2 →
    P ≤ H → H ≤ Subgroup.normalizer (P : Set G) → E2.IsExtraspecialPlus 2 P →
    (∃ φ : ↥H →* Equiv.Perm (Fin 3) × Multiplicative (ZMod 2), Function.Surjective φ ∧
      φ.ker = P.subgroupOf H) →
    H ⊓ Subgroup.centralizer (P : Set G) ≤ P →
    P ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers z →
    (∃ X : Subgroup G, IsSylowIn 3 X H ∧
      P ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z) →
    H = Subgroup.centralizer ({z} : Set G) →
    (∃ d : G, d⁻¹ * z * d ∈ P ∧ d⁻¹ * z * d ≠ z ∧
      IsElemAbelian 2 (P ⊓ CFSG.Quasithin.conjSubgroup P d) ∧
      Nat.card ↥(P ⊓ CFSG.Quasithin.conjSubgroup P d) = 4) →
    Nonempty (G ≃* NativeSporadic.M22)

end CFSG.Quasithin.H13
