module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

structure Cx1291 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) : Prop where
  hyp : Hyp1281One G T L V n
  n45 : n = 4 ∨ n = 5
  select : n = 4 → ¬ ∃ K : Subgroup G, quasithinIsMaximalLocal T K ∧
    quasithinIsFaithfulLocal T K ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

@[expose] def Lemma12_9_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n → n = 4 →
    ¬ ∃ K : Subgroup G, quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K ∧
      (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* NativeSporadic.M24) ∨
        Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* NativeSporadic.J4))

@[expose] def IsHatA7 (Q : Type) [Group Q] : Prop :=
  CFSG.IsQuasisimple Q ∧ Nat.card (Subgroup.center Q) = 3 ∧
    Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 7))

@[expose] def IsSL27OverE49 (Q : Type) [Group Q] : Prop :=
  ∃ E : Subgroup Q, IsElemAbelian 7 E ∧ Nat.card E = 49 ∧
    Subgroup.centralizer (E : Set Q) = E ∧
    ∃ _ : E.Normal, Nonempty (Q ⧸ E ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7))

@[expose] def Lemma12_9_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ (i : ℕ) (Vi : Subgroup G), IsTSub T V Vi i →
      ((n = 5 ∧ 1 ≤ i ∧ i < 5) ∨ (n = 4 ∧ (i = 1 ∨ i = 3))) →
      ∃ Ki : Subgroup G, li128 n i L Vi ≤ Ki ∧
        quasithinIsCComponent Ki (Subgroup.normalizer (Vi : Set G)) ∧
        Subgroup.normalizer (Vi : Set G) ≤ Subgroup.normalizer (Ki : Set G) ∧
        (li128 n i L Vi = Ki ∨
          (i = 1 ∧
            (Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
              Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* NativeSporadic.M24) ∨
              Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* NativeSporadic.J4))) ∨
          (i = 1 ∧ n = 4 ∧
            (Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
              Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* alternatingGroup (Fin 7)) ∨
              IsHatA7 (↥Ki ⧸ CFSG.pCore 2 ↥Ki) ∨
              Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* NativeSporadic.M23) ∨
              Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* NativeSporadic.HS) ∨
              Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* NativeSporadic.He) ∨
              Nonempty (↥Ki ⧸ CFSG.pCore 2 ↥Ki ≃* NativeSporadic.Ru) ∨
              IsSL27OverE49 (↥Ki ⧸ CFSG.pCore 2 ↥Ki))))

@[expose] def Lemma12_9_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 → IsMulCommutative ↥(u128 V V₁)

@[expose] def Lemma12_9_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ K₁ : Subgroup G, IsTSub T V V₁ 1 → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) →
      (centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (V₁ : Set G)) K₁ ≤
          Subgroup.normalizer (L : Set G) ∧ IsHzOne T L V₁ (K₁ ⊔ T)) ∧
      (Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
        Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) ∧
      (n = 4 → Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        ∃ φ : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
          (((lOne L V₁).subgroupOf K₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))).map
              φ.toMonoidHom = Subgroup.centralizer ({transvection15} : Set _))

@[expose] def Lemma12_9_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ V₂ K₁ : Subgroup G, IsTSub T V V₁ 1 → IsTSub T V V₂ 2 → V₁ ≤ V₂ → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) →
      ⁅V₂, pCoreOf 2 K₁⁆ ≠ ⊥ ∧
      (Subgroup.normalizer (V₂ : Set G) ≤ Subgroup.normalizer
          (conjClosure (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
            (Subgroup.normalizer (V₂ : Set G)) : Set G) ∧
        Nonempty (↥(conjClosure (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
            (Subgroup.normalizer (V₂ : Set G))) ⧸
          CFSG.pCore 2 ↥(conjClosure (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
            (Subgroup.normalizer (V₂ : Set G))) ≃* Equiv.Perm (Fin 3)) ∧
        pCoreOf 2 (conjClosure (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
            (Subgroup.normalizer (V₂ : Set G))) =
          conjClosure (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
            (Subgroup.normalizer (V₂ : Set G)) ⊓ Subgroup.centralizer (V₂ : Set G) ∧
        conjClosure (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
            (Subgroup.normalizer (V₂ : Set G)) ⊔ T = p128 T L V) ∧
      CFSG.Open.pRank 3 (Subgroup.centralizer (V₂ : Set G)) ≤ 1

@[expose] def Lemma12_9_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ (i : ℕ) (Vi : Subgroup G), 1 < i → i < n → IsTSub T V Vi i →
      Subgroup.normalizer (Vi : Set G) ≤
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)

@[expose] def Lemma12_9_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    (∀ g : G, g ∉ Subgroup.normalizer (L : Set G) →
      Nat.card ↥(V ⊓ CFSG.conjugate V g) ≤ 2) ∧
    ∀ g : G, V ⊓ CFSG.conjugate V g ≠ ⊥ → ⁅V, CFSG.conjugate V g⁆ = ⊥

@[expose] def Lemma12_9_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ≤
        Subgroup.centralizer (V : Set G) ∧
      Subgroup.normalizer
          ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (L : Set G)) ∧
    ∀ g : G, CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G) ≤ T →
      (CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G)).relIndex (CFSG.conjugate V g) = 2 →
        ⁅CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G), V⁆ ≠ ⊥ →
          CFSG.conjugate V g ⊓ Subgroup.normalizer (L : Set G) ⊓
            Subgroup.centralizer (V : Set G) = ⊥

@[expose] def Final1291 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ), Cx1291 G T L V n →
    ∀ V₁ K₁ : Subgroup G, IsTSub T V V₁ 1 → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) →
      ∃ H : Subgroup G, T ≤ H ∧ H ≤ K₁ ⊔ T ∧ ¬ H ≤ Subgroup.normalizer (L : Set G) ∧
        Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3))

end CFSG.Quasithin.H13
