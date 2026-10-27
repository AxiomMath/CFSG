module

public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec4.LThreePiOn
public import CFSG.RankThree.PartTwo.Sec21.Notation
public import CFSG.RankThree.PartTwo.Sec8.Groups
public import CFSG.RankThree.PartTwo.Sec12.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def lBarA (c : G) (L A : Subgroup G) :
    Subgroup (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
  ((L ⊔ A).subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map (QuotientGroup.mk' _)

@[expose] def Item131 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      (Sec8.IsZ3LThreePi (lBarA c L A) ∧
          (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
            Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
      (Sec8.IsZ3PGLThreePi (lBarA c L A) ∧
          Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧
          ∃ x ∈ A, Sec4.InducesTypeOn L x 3) ∨
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
          Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M22) ∧
          Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2)) ∨
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∧
          Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      (Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2) ∧
          Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      ((Sec4.IsSLThreePiTwo (lBarA c L A) ∨
          (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
            (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
              Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
              Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L)
                CFSG.Blueprint.NativeSporadic.M22))) ∧
        (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) →
          Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
        ∀ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) →
          CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
          ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) →
          ¬ IsCyclic (E ⊓ L : Subgroup G) →
            E ∈ partTwoF G ∧ (E ∉ partTwoT G →
              Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
              (∃ K ∈ thetaComponentsAt 3 c, A ≤ L ⊔ K ∧
                Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
              ∃ e ∈ E ⊓ L, e ∉ Subgroup.zpowers c ∧
                omegaA E = orbitIn A (Subgroup.zpowers e) ∧
                ∃ I : Subgroup G, lA E e = {I} ∧
                  Nonempty (I ⧸ CFSG.pCore 2 I ≃* CFSG.Blueprint.NativeSporadic.J2)))

@[expose] def Item132 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A →
    ∀ a ∈ A, a ≠ 1 → ∀ X ∈ thetaComponentsAt 3 a,
      A = Subgroup.zpowers a ⊔ (A ⊓ X) → a ∉ A ⊓ X →
      Sec21.IsIrreducibleOn (Sec4.autIn (X ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ X)) →
        (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G) ∧
          CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
          wStar A = oThreeWStar A ⊔
            Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A ∧
          omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) ∧
          omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers a) ∧
          (omegaA A).ncard = 9 ∧
          Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
          (IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22))) ∨
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) ∨
        (Sec21.IsIrreducibleOn (wStar A) ∧
          Nonempty (Subgroup.closure {σ : MulAut A | σ ∈ wStar A ∧ ∃ k : ℕ, σ ^ 3 ^ k = 1} ≃*
            alternatingGroup (Fin 4)) ∧
          ∃ φ : wStar A →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4), Function.Injective φ)

@[expose] def Item133 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∨
      ((Nonempty (wStar A ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (wStar A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
        (omegaA A).ncard = 3 ∧
        (∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
          F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom) ∧
        ∃ t ∈ Subgroup.normalizer (A : Set G), t * c * t⁻¹ = c⁻¹ ∧
          ∃ (ht : t ∈ Subgroup.normalizer (L : Set G))
            (e : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7))
            (τ : Equiv.Perm (Fin 7)), τ.IsSwap ∧ ∀ y : L ⧸ aschbacherSolvableCore 3 L,
              ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨t, ht⟩) y) :
                  Equiv.Perm (Fin 7))) = τ * (e y : Equiv.Perm (Fin 7)) * τ⁻¹) ∨
      (Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) ∧
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
        CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
        wStar A = oThreeWStar A ⊔
          Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A ∧
        omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) ∧
        (omegaA A).ncard = 9 ∧
        Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
        (IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22))) ∨
      Sec8.IsZ3PGLThreePi (lBarA c L A) ∨
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)

@[expose] def Item137 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
        ∃ E : Subgroup G, E ≤ (A ⊔ L) ⊓ Subgroup.normalizer (A : Set G) ∧
          CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
          Nonempty (Sec4.autIn L E ≃* GL (Fin 2) (ZMod 3)) ∧ ¬ HypS E ∧ ¬ HypT E

end CFSG.RankThree.PartTwo.Sec13
