module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Big
public import CFSG.Quasithin.Background.CosetGraphCriticalPair

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

section Data

variable (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ)

@[expose] def NoSumBigData : Prop :=
  Hyp4_2_3 G T M L Mm I ∧ InM I H ∧ Conf4212 G T M L I H K ∧ (m = 3 ∨ m = 4) ∧ m ≤ k ∧ k ≤ 4 ∧
    IsPSL m 2 1 (ModO2 (perfectCore (L ⊓ H))) ∧
    IsSumOfNaturalModules (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆ ⊥
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I))
      (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k

@[expose] def ChoiceCh : Prop :=
  NoSumBigData G T M L Mm I H K m k ∧
    ∀ H' K' : Subgroup G, NoSumBigData G T M L Mm I H' K' m k →
      Nat.card (ModO2 K') ≤ Nat.card (ModO2 K)

end Data

theorem conf4212NoSumBig_iff : Conf4212NoSumBig ↔
    ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
      ¬ NoSumBigData G T M L Mm I H K m k := by
  constructor
  · rintro h G _ _ T M L Mm I H K m k ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact h G T M L Mm I H K h1 h2 h3 m k h4 h5 h6 h7 h8
  · intro h G _ _ T M L Mm I H K h1 h2 h3 m k h4 h5 h6 h7 h8
    exact h G T M L Mm I H K m k ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

abbrev vV {G : Type} [Group G] (T L : Subgroup G) : Subgroup G := ⁅reducedAggregate (L ⊔ T), L⁆

theorem lemma_3_24_two {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}
    (hd : NoSumBigData G T M L Mm I H K m k) :
    ∃ H' K' : Subgroup G, ChoiceCh G T M L Mm I H' K' m k := by
  obtain ⟨⟨H', K'⟩, hp, hmax⟩ := Set.exists_max_image
    {p : Subgroup G × Subgroup G | NoSumBigData G T M L Mm I p.1 p.2 m k}
    (fun p => Nat.card (ModO2 p.2)) (Set.toFinite _) ⟨(H, K), hd⟩
  exact ⟨H', K', hp, fun H'' K'' h => hmax (H'', K'') h⟩

abbrev rPlus {G : Type} [Group G] (T M L : Subgroup G) : Subgroup G :=
  T ⊓ centralizerSection M L (pCoreOf 2 L)

abbrev uZero {G : Type} [Group G] (I K : Subgroup G) : Subgroup G :=
  ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I)), K⁆

abbrev gammaZero {G : Type} [Group G] (T M L I : Subgroup G) : Subgroup G :=
  centralizerSection M L (pCoreOf 2 L) ⊓ Subgroup.normalizer ((pCoreOf 2 I : Subgroup G) : Set G) ⊓
    Subgroup.centralizer (vV T L : Set G)

abbrev graph322 {G : Type} [Group G] (T M L I K : Subgroup G) :=
  amalgamGraph (K ⊔ pCoreOf 2 I) (gammaZero T M L I)

@[expose] def typeOne {G : Type} [Group G] (T M L I K : Subgroup G) :
    (G ⧸ (K ⊔ pCoreOf 2 I)) ⊕ (G ⧸ gammaZero T M L I) → Prop :=
  fun v => v.isLeft ∧ (graph322 T M L I K).Reachable (.inl ((1 : G) : G ⧸ (K ⊔ pCoreOf 2 I))) v

@[expose] def Lemma324One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k →
      NoSumBigData G T M L Mm (I ⊓ Subgroup.normalizer (vV T L : Set G)) H K m k ∧
        pCoreOf 2 (I ⊓ Subgroup.normalizer (vV T L : Set G)) = pCoreOf 2 I

@[expose] def Lemma31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k →
      pCoreOf 2 I < rPlus T M L ∧ rPlus T M L ≤ Subgroup.centralizer (vV T L : Set G)

@[expose] def Lemma32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k →
      H ≤ Subgroup.normalizer (K : Set G) ∧ pCoreOf 2 K ≠ ⊥ ∧
        ∃ n : ℕ, ((n = 4 ∧ m = 3) ∨ (n = 5 ∧ m = 3) ∨ (n = 5 ∧ m = 4)) ∧
          IsPSL n 2 1 (ModO2 K)

@[expose] def UZeroNeBot : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k → uZero I K ≠ ⊥

@[expose] def Lemma323' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k → ∀ z : G,
      z ∈ Subgroup.normalizer (vV T L : Set G) →
        (∀ l ∈ L, ⁅z, l⁆ ∈ Subgroup.centralizer (vV T L : Set G)) →
          ∃ e : ℕ, Odd e ∧ z ^ e ∈ Subgroup.centralizer (vV T L : Set G)

@[expose] def AmalgamData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    ChoiceCh G T M L Mm I H K m k → I ≤ Subgroup.normalizer (vV T L : Set G) →
      (K ⊔ pCoreOf 2 I) ⊓ gammaZero T M L I = pCoreOf 2 I ∧ pCoreOf 2 I < gammaZero T M L I ∧
        I ≤ Subgroup.normalizer (gammaZero T M L I : Set G) ∧
        uZero I K ≤ pCoreOf 2 (K ⊔ pCoreOf 2 I)

@[expose] def KRInfGammaZero : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    ChoiceCh G T M L Mm I H K m k → I ≤ Subgroup.normalizer (vV T L : Set G) →
      (K ⊔ pCoreOf 2 I) ⊓ gammaZero T M L I = pCoreOf 2 I

@[expose] def lowerBlock2 {n m : ℕ} (h : n = m + 2) (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun a b => g ⟨m + a.val, by omega⟩ ⟨m + b.val, by omega⟩

@[expose] def Lemma35KR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    NoSumBigData G T M L Mm I H K m k →
      ∃ (n j : ℕ) (α : ↥K →* GL (Fin n) (ZMod 2))
        (β : ↥(uZero I K) →* Multiplicative (Fin j → Fin n → ZMod 2)),
        (n = m + 1 ∨ (n = 5 ∧ m = 3)) ∧ α.ker = CFSG.pCore 2 ↥K ∧
        (∀ (x : ↥K) (u v : ↥(uZero I K)), (v : G) = x * u * (x : G)⁻¹ → ∀ i : Fin j,
          Multiplicative.toAdd (β v) i =
            ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
              (Multiplicative.toAdd (β u) i)) ∧
        (∀ a : Fin n, a.val < m → ∃ v : ↥(uZero I K), (v : G) ∈ vV T L ∧
          ∃ i : Fin j, Multiplicative.toAdd (β v) i = Pi.single a 1) ∧
        (∀ h : n = m + 2, ∃ τ : Matrix (Fin 2) (Fin 2) (ZMod 2), τ ≠ 1 ∧ τ * τ = 1 ∧
          (∀ x : ↥K, (x : G) ∈ pCoreOf 2 I →
            lowerBlock2 h ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 ∨
              lowerBlock2 h ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = τ) ∧
          ∃ x : ↥K, (x : G) ∈ pCoreOf 2 I ∧
            lowerBlock2 h ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = τ)

@[expose] def OddKGamma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    ChoiceCh G T M L Mm I H K m k → I ≤ Subgroup.normalizer (vV T L : Set G) →
      ∀ x ∈ K ⊓ gammaZero T M L I, Odd (orderOf x) → x = 1

@[expose] def LocalFlip : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    ChoiceCh G T M L Mm I H K m k → I ≤ Subgroup.normalizer (vV T L : Set G) →
      ∀ g : G, g ∈ (K ⊔ pCoreOf 2 I) ⊔ gammaZero T M L I →
        (∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I) → (∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) →
          (∃ u ∈ uZero I K, g⁻¹ * u * g ∉
            kerA (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) → False

@[expose] def FlipCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    ChoiceCh G T M L Mm I H K m k → I ≤ Subgroup.normalizer (vV T L : Set G) →
      ∀ g : G, g ∈ (K ⊔ pCoreOf 2 I) ⊔ gammaZero T M L I →
        (∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I) → (∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) →
          (∃ u ∈ uZero I K, g⁻¹ * u * g ∉
            kerA (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) →
            (∀ v ∈ vV T L, g * v * g⁻¹ ∈ vV T L) ∧
              (∀ l ∈ L, ∀ l' ∈ L, ⁅g * l' * g⁻¹, l⁆ ∈ Subgroup.centralizer (vV T L : Set G))

@[expose] def NotCriticalPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    ChoiceCh G T M L Mm I H K m k → I ≤ Subgroup.normalizer (vV T L : Set G) →
      ∀ δ ε : (G ⧸ (K ⊔ pCoreOf 2 I)) ⊕ (G ⧸ gammaZero T M L I),
        ¬ IsCriticalPair (graph322 T M L I K)
          (zAt (K ⊔ pCoreOf 2 I) (gammaZero T M L I) (uZero I K)) (typeOne T M L I K) δ ε

@[expose] def Lemma37 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    ChoiceCh G T M L Mm I H K m k → ∀ X : Subgroup G, I ≤ X → K ≤ X → pCoreOf 2 X ≠ ⊥ → X ≤ H

@[expose] def NotLeKernelAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k : ℕ),
    ChoiceCh G T M L Mm I H K m k → I ≤ Subgroup.normalizer (vV T L : Set G) →
      ¬ ∀ δ ε, typeOne T M L I K δ → (graph322 T M L I K).Reachable δ ε →
        zAt (K ⊔ pCoreOf 2 I) (gammaZero T M L I) (uZero I K) δ ≤
          kernelAt (graph322 T M L I K) ε

end CFSG.Quasithin.H13.Ch4.NSB
