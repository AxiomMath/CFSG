module

public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] noncomputable def Item1715 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      (omegaA A = {Subgroup.zpowers c} ∧ Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
          Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
          ((∃ (q : ℕ) (_ : Fact q.Prime), 3 < q ∧
              Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) q 1) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
            Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))) ∨
        (A ⊔ L ≤ Y₀ ∧
          Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∧
          Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) ∧
          WStarS4 A ∧ TransOmegaThree A c)

@[expose] def Item1718 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ∀ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
        w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) →
          Y₁.map (MulAut.conj w).toMonoidHom ≠ Y₁

@[expose] def Item1719 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      A ⊓ L ≠ A ⊓ Subgroup.centralizer (P : Set G)

@[expose] noncomputable def Item1721 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)

@[expose] def Item1722 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y₁ : Set G)

@[expose] def Item1725 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17WQ G A c L Y₀ Y₁ S p P w Q →
      ∀ X ∈ invariantPiSubgroups Q (Subgroup.zpowers w ⊔ A) (piOf p),
        X = (X ⊓ yI Y₁ w 1) ⊔ (X ⊓ yI Y₁ w 2) ⊔ (X ⊓ yI Y₁ w 3) ∧
          (∀ i : ℕ, 1 ≤ i → i ≤ 3 →
            X ⊓ yI Y₁ w i = (X ⊓ yI Y₁ w 3).map (MulAut.conj (w ^ i)).toMonoidHom) ∧
          (IsMulCommutative ↥X → Nat.card ↥X = Nat.card ↥(X ⊓ yI Y₁ w 1) ^ 3)

@[expose] def Item1726 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G) (s : G), Sec17S G A c L Y₀ Y₁ S p P w Q s →
      omegaOneZ p Q = omegaOneAt p Q ∧ CFSG.Assembly.IsElemAbelian p (omegaOneZ p Q) ∧
        Nat.card ↥(omegaOneZ p Q) = p ^ 6

@[expose] def Item1727 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G) (s d r : G),
    Sec17Data G A c L Y₀ Y₁ S p P w Q s d r → Q ⊓ Subgroup.centralizer ({d} : Set G) = ⊥

@[expose] def Item1728Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G) (s d r : G),
    Sec17Data G A c L Y₀ Y₁ S p P w Q s d r →
      omegaOneZ p Q = (omegaOneZ p Q ⊓ Subgroup.centralizer {c * d}) ⊔
          (omegaOneZ p Q ⊓ Subgroup.centralizer {c * d⁻¹}) ∧
        (omegaOneZ p Q ⊓ Subgroup.centralizer {c * d}) ⊓
            (omegaOneZ p Q ⊓ Subgroup.centralizer {c * d⁻¹}) = ⊥ ∧
        Nat.card ↥(omegaOneZ p Q ⊓ Subgroup.centralizer {c * d}) = p ^ 3

end CFSG.RankThree.PartTwo.Sec17
