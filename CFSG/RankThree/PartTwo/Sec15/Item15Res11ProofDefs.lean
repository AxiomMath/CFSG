module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1515HJEndFpfRLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Conf1515HJ A c L L →
    (∀ e ∈ A, e ≠ 1 → IsZCentral L e →
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) →
    ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
        delta A (lB A) (Subgroup.centralizer ({d} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))

@[expose] noncomputable def Step1515HJEndFpfRBoundOff : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Conf1515HJ A c L L →
    (∀ e ∈ A, e ≠ 1 → IsZCentral L e →
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) →
    ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    (∀ F ∈ omegaA A, ¬ F ≤ A ⊓ L) →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))

@[expose] def KS1515ONCent : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (M K X₀ T : Subgroup H) (y : H),
    ¬ 3 ∣ Nat.card M → K ≤ Subgroup.normalizer (M : Set H) →
    Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) CFSG.Blueprint.NativeSporadic.ON →
    inSubgroup (aschbacherSolvableCore 3) K ≤ M →
    X₀ ≤ M ⊔ K → X₀ ⊓ M = ⊥ → Group.IsPerfect ↥X₀ →
    Sec4.IsTripleCover ↥X₀ (alternatingGroup (Fin 6)) →
    (∃ z ∈ X₀, z ≠ 1 ∧ K ≤ Subgroup.centralizer ({z} : Set H)) →
    T ≤ M ⊔ K → T ⊓ M = ⊥ → IsPGroup 2 T → T ≤ Subgroup.centralizer (X₀ : Set H) →
    y ∈ Subgroup.normalizer (M : Set H) →
    y ∈ Subgroup.normalizer ((M ⊔ K : Subgroup H) : Set H) →
    y ∈ Subgroup.centralizer (X₀ : Set H) → y ^ 3 = 1 →
    y ∈ Subgroup.normalizer (T : Set H) → T = ⁅T, Subgroup.zpowers y⁆ → T = ⊥

@[expose] noncomputable def Step1515HJEndFpfA6A6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Conf1515HJ A c L L →
    (∀ e ∈ A, e ≠ 1 → IsZCentral L e →
      CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) →
    ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    ∀ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({d} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
      Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X : Subgroup G) : Set G) →
      (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 d ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
      IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X) →
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔ X →
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))

end CFSG.RankThree.PartTwo.Sec15
