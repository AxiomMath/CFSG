module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
public import CFSG.Quasithin.Vol2.Ch9L34Gam
public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

@[expose] def UIn (X : Type) [Group X] : Prop :=
  (∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b) ∧
    ∃ z g : X, orderOf z = 2 ∧ 6 ≤ orderOf (z * (g⁻¹ * z * g))

@[expose] def UOut (X : Type) [Group X] (M : Subgroup X) : Prop :=
  ∀ y : MulAut X, y * y = 1 → (∀ b ∈ M, y b = b) → ∃ x : X, y = MulAut.conj x

@[expose] def UOutAll (X : Type) [Group X] : Prop :=
  ∀ y : MulAut X, y * y = 1 → ∃ x : X, y = MulAut.conj x

theorem UOut.of_all {X : Type} [Group X] (h : UOutAll X) (M : Subgroup X) : UOut X M :=
  fun y hy _ => h y hy

@[expose] def NKLeafSz : Prop :=
  ∀ (e : ℕ) (X : Type) [Group X], IsSz e X → UIn X ∧ UOutAll X

@[expose] def NKLeafSzDvd : Prop :=
  ∀ (e : ℕ) (X : Type) [Group X], IsSz e X → 5 ∣ Nat.card X

@[expose] def NKLeafU3Even : Prop :=
  ∀ (n : ℕ), n % 4 = 0 → ∀ (X : Type) [Group X], IsPSU 3 2 n X →
    UIn X ∧ ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → UOut X (Subgroup.normalizer (S : Set X))

@[expose] def NKLeafU3Five : Prop :=
  ∀ (n : ℕ), n % 4 = 2 → ∀ (X : Type) [Group X] [Finite X], IsPSU 3 2 n X →
    2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X)

@[expose] def NKLeafL3TwoOdd : Prop :=
  ∀ (n : ℕ), Odd n → 3 ≤ n → ∀ (X : Type) [Group X], IsPSL 3 2 n X →
    UIn X ∧ ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → UOut X (Subgroup.normalizer (S : Set X))

@[expose] def NKLeafL2Odd : Prop :=
  ∀ (p e : ℕ), p.Prime → 3 < p → (e = 1 ∨ e = 2) → (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) →
    p ^ e ≠ 7 → p ^ e ≠ 25 → ∀ (X : Type) [Group X], IsPSL 2 p e X →
      UIn X ∧ ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
        UOut X (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X))

@[expose] def NKLeafL2TwentyFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPSL 2 5 2 X → 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X)

@[expose] def NKLeafL3Odd : Prop :=
  ∀ (p : ℕ), p.Prime → 7 ≤ p → p % 4 = 3 → ∀ (X : Type) [Group X], IsPSL 3 p 1 X →
    UIn X ∧ ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
      UOut X (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X))

@[expose] def NKLeafU3Odd : Prop :=
  ∀ (p : ℕ), p.Prime → 13 ≤ p → p % 4 = 1 → ∀ (X : Type) [Group X], IsPSU 3 p 1 X →
    UIn X ∧ ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
      UOut X (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X))

@[expose] def NKLeafU3FiveP : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPSU 3 5 1 X → 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X)

@[expose] def NKLeafL2Dvd3 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X], IsPSL 2 p 1 X → 3 ∣ Nat.card X

@[expose] def NKLiftCase1 (p : ℕ) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H K M : Subgroup G} {t : G},
    K ∈ cComp H → t ∈ H → kerIn M H = pCoreOf 2 H → cjSub t K ≠ K →
    IsSimpleGroup ↥(E2.star M H K) → (∃ a b : ↥(E2.star M H K), a * b ≠ b * a) →
    p ∣ Nat.card ↥(E2.star M H K) → CFSG.Open.pRank p H ≤ 1 → False

@[expose] def NKLiftCase2 (p : ℕ) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H K M : Subgroup G}, K ≤ H →
    (∀ x : G, x ∈ kerIn M H ↔
      x ∈ K ⊔ pCoreOf 2 H ∧ ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) →
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(E2.star M H K)) → CFSG.Open.pRank p H ≤ 1 → False

@[expose] def NKLeafL32 : Prop :=
  ∀ (X : Type) [Group X], IsPSL 3 2 1 X →
    (∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b) ∧
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
      UOut X (Subgroup.normalizer (S : Set X)) ∧
      UOut X (Subgroup.centralizer ((S ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X))

@[expose] def NKLeafSchurL32 : Prop :=
  ∀ (G L : Type) [Group G] [Finite G] [Group L], commutator G = ⊤ → IsPSL 3 2 1 L →
    ∀ π : G →* L, Function.Surjective π → (∀ z ∈ π.ker, ∀ g : G, g * z = z * g) →
      (∀ z ∈ π.ker, Odd (orderOf z)) → Function.Injective π

@[expose] def NKLeafSL3Rep : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], (Nat.card K = 2 ∨ Nat.card K = 4) →
    ∀ (n : ℕ) (N : Subgroup (GL (Fin n) K)), CFSG.RankThree.SubgroupLists.IsIrreducibleOn N →
      (∀ g ∈ N, orderOf g = 2 → L829N.IsTransvectionK g) →
      (∃ (L : Type) (_ : Group L), IsPSL 3 2 1 L ∧ Nonempty (↥N ≃* L)) →
      ∃ hn : n = 3, ∃ P : GL (Fin n) K, ∀ g : GL (Fin n) K, g ∈ N ↔
        ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det = 1 ∧
          ((P * g * P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (M.map (fun a : ZMod 2 => ((a.val : ℕ) : K))).submatrix (Fin.cast hn) (Fin.cast hn)

end CFSG.Quasithin.H13.L829NK
