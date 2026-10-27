module

public import CFSG.Quasithin.Background.G2L2Seven
public import CFSG.Quasithin.Background.G2A5CoreWrap
public import CFSG.Quasithin.Background.G25Direct
public import CFSG.Quasithin.Background.G2Omega4PlusFive
import CFSG.Quasithin.Background.RonanG24
import CFSG.Quasithin.Background.RonanG25Main

public section

namespace CFSG.ASVolI.ChG

@[expose] def IsQ8Squared {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  Nat.card P = 32 ∧ ∃ A B : Subgroup G, A ≤ P ∧ B ≤ P ∧ A ⊔ B = P ∧ ⁅A, B⁆ = ⊥ ∧
    Nonempty (↥A ≃* QuaternionGroup 2) ∧ Nonempty (↥B ≃* QuaternionGroup 2)

section Chief

variable {G : Type} [Group G]

structure IsOpCompSeries (X P : Subgroup G) (k : ℕ) (Ps : ℕ → Subgroup G) : Prop where
  zero : Ps 0 = ⊥
  top : Ps k = P
  mono : ∀ i < k, Ps i ≤ Ps (i + 1)
  strict : ∀ i < k, Ps i < Ps (i + 1)
  inv : ∀ i ≤ k, ∀ x ∈ X, ∀ y ∈ Ps i, x * y * x⁻¹ ∈ Ps i
  normal : ∀ i < k, ∀ y ∈ Ps (i + 1), ∀ z ∈ Ps i, y * z * y⁻¹ ∈ Ps i
  simple : ∀ i < k, ∀ Q : Subgroup G, Ps i ≤ Q → Q ≤ Ps (i + 1) →
    (∀ x ∈ X, ∀ y ∈ Q, x * y * x⁻¹ ∈ Q) → (∀ y ∈ Ps (i + 1), ∀ z ∈ Q, y * z * y⁻¹ ∈ Q) →
      Q = Ps i ∨ Q = Ps (i + 1)

@[expose] def FactorCentral (X A B : Subgroup G) : Prop :=
  ∀ x ∈ X, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ A

@[expose] def FactorNatural (F : Type) [Field F] (X A B : Subgroup G) : Prop :=
  ∃ (φ : ↥B →* Multiplicative (Fin 2 → F)) (β : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F),
    Function.Surjective φ ∧ (∀ y : ↥B, φ y = 1 ↔ (y : G) ∈ A) ∧
    (∀ (x : ↥X) (y y' : ↥B), (x : G) * (y : G) * (x : G)⁻¹ = (y' : G) →
      Multiplicative.toAdd (φ y') =
        ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (φ y))) ∧
    (Nat.card F = 2 → β ≠ 1) ∧
    (2 < Nat.card F → ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : ↥X,
      ((β x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F))

open Classical in
@[expose] def HasChiefCounts (F : Type) [Field F] (X P : Subgroup G) (a b : ℕ) : Prop :=
  ∃ (k : ℕ) (Ps : ℕ → Subgroup G), IsOpCompSeries X P k Ps ∧
    (Finset.univ.filter (fun i : Fin k => FactorNatural F X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)))).card = a ∧
    (Finset.univ.filter (fun i : Fin k =>
      ¬ FactorCentral X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)) ∧
        ¬ FactorNatural F X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)))).card = b ∧
    ∀ i : Fin k, ¬ FactorCentral X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)) →
      ¬ FactorNatural F X (Ps (i : ℕ)) (Ps ((i : ℕ) + 1)) →
        Nat.card ↥(Ps ((i : ℕ) + 1)) = Nat.card F * Nat.card ↥(Ps (i : ℕ))

@[expose] def FactorTwo (A B : Subgroup G) : Prop :=
  ∃ dimension : ℕ, 0 < dimension ∧ Nat.card ↥B = 2 ^ dimension * Nat.card ↥A

open Classical in
@[expose] def HasOrdinaryTwoChiefCounts (F : Type) [Field F] (X : Subgroup G)
    (naturalCount additionalCount : ℕ) : Prop :=
  ∃ (length : ℕ) (terms : ℕ → Subgroup G), IsOpCompSeries X X length terms ∧
    (Finset.univ.filter (fun index : Fin length =>
      FactorTwo (terms (index : ℕ)) (terms ((index : ℕ) + 1)) ∧
        FactorNatural F X (terms (index : ℕ)) (terms ((index : ℕ) + 1)))).card = naturalCount ∧
    (Finset.univ.filter (fun index : Fin length =>
      FactorTwo (terms (index : ℕ)) (terms ((index : ℕ) + 1)) ∧
        ¬ FactorCentral X (terms (index : ℕ)) (terms ((index : ℕ) + 1)) ∧
        ¬ FactorNatural F X (terms (index : ℕ)) (terms ((index : ℕ) + 1)))).card = additionalCount ∧
    ∀ index : Fin length,
      FactorTwo (terms (index : ℕ)) (terms ((index : ℕ) + 1)) →
      ¬ FactorCentral X (terms (index : ℕ)) (terms ((index : ℕ) + 1)) →
      ¬ FactorNatural F X (terms (index : ℕ)) (terms ((index : ℕ) + 1)) →
        Nat.card ↥(terms ((index : ℕ) + 1)) = Nat.card F * Nat.card ↥(terms (index : ℕ))

end Chief

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

@[expose] def G_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V V₁ L T H : Subgroup G), AlmostSpecialHyp V V₁ L T H →
    (tildeOf V₁ V ≤ tildeOf V₁ (conjClosure V H) ∧
      tildeOf V₁ (conjClosure V H) ≤ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H))) ∧
    frattiniOf (conjClosure V H) ≤ V₁ ∧
    (conjClosure V H ≤ T ∧ T ≤ Subgroup.normalizer (conjClosure V H : Set G)) ∧
    IsTwoReducedIn (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H))

theorem as_G_2_2 : G_2_2 := by
  intro G _ _ V V₁ L T H h
  exact ⟨h.G22_one, h.G22_two, h.G22_three, h.G22_four⟩

@[expose] def G_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (V V₁ L T H : Subgroup G),
    AlmostSpecialL2Hyp n V V₁ L T H →
    ∀ g ∈ L, g ∉ Subgroup.normalizer (V₁ : Set G) →
    ∀ U I S W : Subgroup G, U = conjClosure V H → I = U ⊔ rconj U g → S = pCoreOf 2 I →
      W = U ⊓ S →
      (Nonempty (↥(starImg L T (L ⊔ U)) ≃* SL(2, GaloisField 2 n)) ∧
        IsSylowTwoOf (starImg L T U) (starImg L T (L ⊔ U))) ∧
      I = L ⊔ U ∧
      (S = W ⊔ rconj W g ∧ (S : Set G) = (W : Set G) * (rconj W g : Set G)) ∧
      (V ≤ U ⊓ rconj U g ∧ U ⊓ rconj U g ≤ S ∧ V ≤ centerOf S ∧
        I ≤ Subgroup.normalizer (V : Set G) ∧
        I ≤ Subgroup.normalizer ((U ⊓ rconj U g : Subgroup G) : Set G) ∧
        I ≤ Subgroup.normalizer (S : Set G)) ∧
      (⁅U ⊓ rconj U g, I⁆ ≤ V ∧ IsElemAbelian 2 (U ⊓ rconj U g)) ∧
      ∃ s : ℕ, (IsSumOfNaturalSL2ModulesOver (GaloisField 2 n) s I S S (U ⊓ rconj U g) ∧
        W ⊓ rconj W g = U ⊓ rconj U g ∧ S = W ⊔ rconj W g ∧
        ∀ x ∈ S, x ∈ W ↔ ∀ u ∈ U, ⁅u, x⁆ ∈ U ⊓ rconj U g) ∧
        Nat.card ↥U = 2 ^ (n * (s + 3)) * V.relIndex (U ⊓ rconj U g)

theorem as_G_2_3 : G_2_3 := by
  intro G _ _ n V V₁ L T H hyp g hg hgN U I S W hU hI hS hW
  subst hU hI hS hW
  obtain ⟨D⟩ := hyp.natural.nonempty_data
  let St : L2Setting n V V₁ L T H := ⟨hyp, D⟩
  obtain ⟨s, β, φ, hβs, hβk, hφs, hφk, hφe, hcard, hC, hdisj, hsup⟩ :=
    St.sum_natural rfl hg hgN rfl rfl rfl CFSG.Quasithin.G1.theorem_G_1_3_two
  have hUW := St.card_U_eq rfl hg hgN rfl rfl rfl
  have hS₂ := card_eq_mul_relIndex_of_le (hyp.G23_four hg hgN).1
  have hV := St.card_V
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hyp.n_pos.ne'
  refine ⟨hyp.G23_one, hyp.G23_two hg hgN, hyp.G23_three rfl hg hgN rfl rfl rfl,
    hyp.G23_four hg hgN, hyp.G23_five hg hgN, s,
    ⟨⟨β, φ, hβs, hβk, hφs, hφk, hφe⟩, hdisj, hsup, hC⟩, ?_⟩
  rw [hUW, hcard, hS₂, hV, hF]
  ring

@[expose] def G_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V V₁ L T H : Subgroup G),
    AlmostSpecialA5Hyp V V₁ L T H →
    ∀ g ∈ L, g ∉ Subgroup.normalizer (V₁ : Set G) →
    ∀ U I S W : Subgroup G, U = conjClosure V H → I = U ⊔ rconj U g → S = pCoreOf 2 I →
      W = U ⊓ S →
      (starImg L T U = pCoreOf 2 (starImg L T (lOne L V₁)) ∧
        IsSylowTwoOf (starImg L T U) (starImg L T L)) ∧
      I = L ⊔ U ∧
      (S = W ⊔ rconj W g ∧ (S : Set G) = (W : Set G) * (rconj W g : Set G)) ∧
      (conjClosure V₁ L ≤ conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
        conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤ S ∧ conjClosure V₁ L ≤ centerOf S ∧
        I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) ∧
        I ≤ Subgroup.normalizer ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) ∧
        I ≤ Subgroup.normalizer (S : Set G)) ∧
      ⁅conjClosure V₁ L ⊔ (U ⊓ rconj U g), I⁆ ≤ conjClosure V₁ L ∧
      (∃ s : ℕ, (IsSumOfNaturalSL2ModulesOver (GaloisField 2 2) s I S S
          (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ∧
        (W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ⊓
            (rconj W g ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) =
          conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
        S = (W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ⊔
            (rconj W g ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ∧
        ∀ x ∈ S, x ∈ W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ↔
          ∀ u ∈ U, ⁅u, x⁆ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ∧
        Nat.card ↥U = 2 ^ (2 * s + 5) *
          (conjClosure V₁ L).relIndex (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ∧
      (⁅tildeOf V₁ U, tildeOf V₁ (lOne L V₁)⁆ = tildeOf V₁ U →
        pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 H →
        I = L ∧ (IsShort2 L ∧ IsAltType L 5) ∧ S = conjClosure V₁ L ∧
          U = pCoreOf 2 (lOne L V₁) ∧ ChG.IsQ8Squared U)

theorem as_G_2_4 : G_2_4 := by
  intro G _ _ V V₁ L T H hyp g hg hgN U I S W hU hI hS hW
  obtain ⟨-, h6₁, h6₂, h6₃⟩ := hyp.toCore.G24_six' hU hg hgN hI hS hW
  obtain ⟨s, hs, h7⟩ := hyp.toCore.G24_seven' hU hg hgN hI hS hW
  refine ⟨?_, ?_, hyp.G24_three hU hg hgN hI hS hW, hyp.G24_four hU hg hgN hI hS,
    hyp.G24_five hU hg hgN hI, ⟨s, ⟨hs, h6₁, h6₂, h6₃⟩, h7⟩, fun hc hO2 => ?_⟩
  · subst hU
    exact hyp.G24_one
  · subst hU hI
    exact hyp.G24_two hg hgN
  · subst hU hI hS
    exact RonanG24.G24_eight hyp hg hgN hc hO2

@[expose] def G_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ) (V V₁ L T H : Subgroup G),
    AlmostSpecialL3Hyp n V V₁ L T H →
    ∀ (g h : G) (hg : g ∈ L) (hh : h ∈ L),
    (V = V₁ ⊔ rconj V₁ g ⊔ rconj V₁ h ∧ V₁ ⊓ rconj V₁ g = ⊥ ∧
      (V₁ ⊔ rconj V₁ g) ⊓ rconj V₁ h = ⊥) →
    ∀ U I S W : Subgroup G, U = conjClosure V H → I = U ⊔ rconj U g ⊔ rconj U h →
      S = pCoreOf 2 I → W = U ⊓ S →
      (starImg L T U = pCoreOf 2 (starImg L T (L ⊓ Subgroup.normalizer (V₁ : Set G))) ∧
        IsElemAbelian 2 (starImg L T U) ∧ Nat.card ↥(starImg L T U) = 2 ^ (2 * n) ∧
        ⁅V, U⁆ = V₁) ∧
      I = L ⊔ U ∧
      (S = W ⊔ rconj W g ⊔ rconj W h ∧
        (S : Set G) = (W : Set G) * (rconj W g : Set G) * (rconj W h : Set G)) ∧
      (V ≤ U ⊓ rconj U g ⊓ rconj U h ∧
        U ⊓ rconj U g ⊓ rconj U h ≤ sThree W g h ∧ sThree W g h ≤ S ∧ V ≤ centerOf S ∧
        I ≤ Subgroup.normalizer (V : Set G) ∧
        I ≤ Subgroup.normalizer ((U ⊓ rconj U g ⊓ rconj U h : Subgroup G) : Set G) ∧
        I ≤ Subgroup.normalizer ((sThree W g h : Subgroup G) : Set G) ∧
        I ≤ Subgroup.normalizer (S : Set G)) ∧
      ⁅U ⊓ rconj U g ⊓ rconj U h, I⁆ ≤ V ∧
      (S = W ⊔ rconj W g ⊔ rconj W h ∧
        (W ⊔ sThree W g h) ⊓ (rconj W g ⊔ sThree W g h) = sThree W g h ∧
        (W ⊔ sThree W g h) ⊓ (rconj W h ⊔ sThree W g h) = sThree W g h ∧
        (rconj W g ⊔ sThree W g h) ⊓ (rconj W h ⊔ sThree W g h) = sThree W g h ∧
        ((W ⊔ sThree W g h) ⊔ (rconj W g ⊔ sThree W g h)) ⊓ (rconj W h ⊔ sThree W g h) =
          sThree W g h ∧
        (W ⊓ rconj W g) ⊓ (W ⊓ rconj W h) = U ⊓ rconj U g ⊓ rconj U h ∧
        (W ⊓ rconj W g) ⊓ (rconj W g ⊓ rconj W h) = U ⊓ rconj U g ⊓ rconj U h ∧
        (W ⊓ rconj W h) ⊓ (rconj W g ⊓ rconj W h) = U ⊓ rconj U g ⊓ rconj U h ∧
        ((W ⊓ rconj W g) ⊔ (W ⊓ rconj W h)) ⊓ (rconj W g ⊓ rconj W h) =
          U ⊓ rconj U g ⊓ rconj U h) ∧
      ∀ D : NatData3 n L (pCoreOf 2 (L ⊔ T)) V V₁,
        ∃ (r s : ℕ) (φ₇ : ↥S →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n))
          (φ₆ : ↥(sThree W g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)),
          IsSumOfSL3ModulesVia r L S (sThree W g h) D.θ φ₇ ∧
          (∀ x : ↥S, (x : G) ∈ W ⊔ sThree W g h ↔
            ∀ l : Fin r, ∃ c : GaloisField 2 n,
              Multiplicative.toAdd (φ₇ x) l = c • vE (GaloisField 2 n) 0) ∧
          (∀ x : ↥S, (x : G) ∈ rconj W g ⊔ sThree W g h ↔
            ∀ l : Fin r, ∃ c : GaloisField 2 n,
              Multiplicative.toAdd (φ₇ x) l = c • (D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0)) ∧
          (∀ x : ↥S, (x : G) ∈ rconj W h ⊔ sThree W g h ↔
            ∀ l : Fin r, ∃ c : GaloisField 2 n,
              Multiplicative.toAdd (φ₇ x) l = c • (D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0)) ∧
          IsSumOfSL3ModulesVia s L (sThree W g h) (U ⊓ rconj U g ⊓ rconj U h)
            ((dualHom (GaloisField 2 n) 3).comp D.θ) φ₆ ∧
          (∀ x : ↥(sThree W g h), (x : G) ∈ W ⊓ rconj W g ↔
            ∀ l : Fin s, Multiplicative.toAdd (φ₆ x) l ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧
              Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ∧
          (∀ x : ↥(sThree W g h), (x : G) ∈ W ⊓ rconj W h ↔
            ∀ l : Fin s, Multiplicative.toAdd (φ₆ x) l ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧
              Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ∧
          (∀ x : ↥(sThree W g h), (x : G) ∈ rconj W g ⊓ rconj W h ↔
            ∀ l : Fin s,
              Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) = 0 ∧
              Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) = 0) ∧
          Nat.card ↥U = 2 ^ (n * (2 * s + r + 5)) * V.relIndex (U ⊓ rconj U g ⊓ rconj U h) ∧
          ChG.HasOrdinaryTwoChiefCounts (GaloisField 2 n) (lOne L V₁)
            (r + s + 2) (if 1 < n then r + s + 1 else 0) ∧
          ChG.HasChiefCounts (GaloisField 2 n) (lOne L V₁) U (s + 2) (if 1 < n then r + 1 else 0) ∧
          ChG.HasChiefCounts (GaloisField 2 n) (lOne L V₁) (S ⊔ U) (r + s + 2)
            (if 1 < n then r + s + 1 else 0)

private theorem chG_series {G : Type} [Group G] {X P : Subgroup G} {k : ℕ} {Ps : ℕ → Subgroup G}
    (h : CFSG.Quasithin.RonanG25.IsOpCompSeries X P k Ps) : ChG.IsOpCompSeries X P k Ps :=
  ⟨h.zero, h.top, h.mono, h.strict, h.inv, h.normal, h.simple⟩

private theorem chG_hasChiefCounts {G : Type} [Group G] {F : Type} [Field F] {X P : Subgroup G}
    {a b : ℕ} (h : CFSG.Quasithin.RonanG25.HasChiefCounts F X P a b) :
    ChG.HasChiefCounts F X P a b := by
  obtain ⟨k, Ps, hs, h1, h2, h3⟩ := h
  exact ⟨k, Ps, chG_series hs, h1, h2, h3⟩

private theorem chG_hasOrdinaryTwoChiefCounts {G : Type} [Group G] {F : Type} [Field F]
    {X : Subgroup G} {a b : ℕ} (h : CFSG.Quasithin.RonanG25.HasOrdinaryTwoChiefCounts F X a b) :
    ChG.HasOrdinaryTwoChiefCounts F X a b := by
  obtain ⟨k, Ps, hs, h1, h2, h3⟩ := h
  exact ⟨k, Ps, chG_series hs, h1, h2, h3⟩

theorem as_G_2_5 : G_2_5 := by
  intro G _ _ n V V₁ L T H hyp g h hg hh hVd U I S W hU hI hS hW
  obtain ⟨hV, -, -⟩ := hVd
  have hn : 0 < n := hyp.n_pos
  have h1 := hyp.G25_one
  have h2 := hyp.G25_two hg hh hV
  have h3 := hyp.G25_three hU hg hh hV hI hS hW
  have h4 := hyp.G25_four hU hg hh hV hI hS hW
  have h4i := hyp.G25_four_inv hU hg hh hV hI hS hW
  have h5 := hyp.G25_five hU hg hh hV hI
  have hd := hyp.G25_direct hU hg hh hV hI hS hW
  have h678 := fun D => hyp.G25_six_seven_eight hU hg hh hV hI hS hW D
  have hI' : I = L ⊔ U := by subst hU; exact hI.trans h2
  subst hU
  subst hS
  subst hW
  subst hI'
  obtain ⟨h4a, h4b, h4c, h4d, h4e, h4f, h4g⟩ := h4
  have hsub : CFSG.Quasithin.RonanG25.SubFacts V L H g h :=
    ⟨h4a, h4b, h4c, h4d, h4e, h4f, h4i, h4g, h5, hd.2.2.2.2.2.1⟩
  refine ⟨h1, rfl, h3, ⟨h4a, h4b, h4c, h4d, h4e, h4f, h4i, h4g⟩, h5, hd, fun D => ?_⟩
  obtain ⟨r, s, φ₇, φ₆, h7, h7W, h7Wg, h7Wh, h6, h6g, h6h, h6gh, hcard⟩ := h678 D
  have hsum : CFSG.Quasithin.RonanG25.SumFacts D g h hg hh r s φ₇ φ₆ :=
    ⟨h7, h7W, h6, h6g, h6h, h6gh⟩
  refine ⟨r, s, φ₇, φ₆, h7, h7W, h7Wg, h7Wh, h6, h6g, h6h, h6gh, hcard, ?_, ?_, ?_⟩
  · exact chG_hasOrdinaryTwoChiefCounts
      (CFSG.Quasithin.RonanG25.counts_L₁ ⟨hyp, D⟩ hn hg hh hsub hsum)
  · exact chG_hasChiefCounts (CFSG.Quasithin.RonanG25.counts_U ⟨hyp, D⟩ hn hg hh hV hsub hsum)
  · exact chG_hasChiefCounts (CFSG.Quasithin.RonanG25.counts_SU ⟨hyp, D⟩ hn hg hh hsub hsum)

@[expose] def G_2_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V V₁ L T H : Subgroup G),
    AlmostSpecialOm4Hyp V V₁ L T H →
    ∀ g ∈ L, ¬ rconj V₁ g ≤ V →
    ∀ U I S S₂ W : Subgroup G, U = conjClosure V H → I = U ⊔ rconj U g → S = pCoreOf 2 I →
      S₂ = conjClosure V₁ L ⊔ (U ⊓ rconj U g) → W = U ⊓ S →
      I = L ⊔ U ∧
      (S = W ⊔ rconj W g ∧ (S : Set G) = (W : Set G) * (rconj W g : Set G)) ∧
      (conjClosure V₁ L ≤ S₂ ∧ S₂ ≤ S ∧ conjClosure V₁ L ≤ centerOf S ∧
        I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) ∧
        I ≤ Subgroup.normalizer (S₂ : Set G) ∧ I ≤ Subgroup.normalizer (S : Set G)) ∧
      ⁅S₂, I⁆ ≤ conjClosure V₁ L ∧
      ∃ (M₁ M₂ Sa Sb : Subgroup G) (s₁ s₂ : ℕ),
        S ≤ M₁ ∧ S ≤ M₂ ∧ M₁ ≤ I ∧ M₂ ≤ I ∧ M₁ ⊔ M₂ = I ∧ M₁ ⊓ M₂ = S ∧ ⁅M₁, M₂⁆ ≤ S ∧
        S₂ ≤ Sa ∧ Sa ≤ S ∧ S₂ ≤ Sb ∧ Sb ≤ S ∧ Sa ⊔ Sb = S ∧ Sa ⊓ Sb = S₂ ∧ ⁅Sa, Sb⁆ ≤ S₂ ∧
        Sa = ⁅S, M₁⁆ ⊔ S₂ ∧ Sb = ⁅S, M₂⁆ ⊔ S₂ ∧
        (∀ s ∈ S, s ∈ Sa ↔ ∀ m ∈ M₂, ⁅m, s⁆ ∈ S₂) ∧
        (∀ s ∈ S, s ∈ Sb ↔ ∀ m ∈ M₁, ⁅m, s⁆ ∈ S₂) ∧
        IsSumOfNaturalSL2ModulesOver (ZMod 2) s₁ M₁ Sa S S₂ ∧
        IsSumOfNaturalSL2ModulesOver (ZMod 2) s₂ M₂ Sb S S₂

theorem as_G_2_6 : G_2_6 := by
  intro G _ _ V V₁ L T H hyp g hg hgV U I S S₂ W hU hI hS hS₂ hW
  have h1 : I = L ⊔ U := by
    rw [hI, hU]
    exact hyp.G26_one hg hgV
  obtain ⟨M₁, M₂, Sa, Sb, a1, a2, a3, a4, a5, a6, a7, b1, b2, b3, b4, b5, b6, b7, c1, c2, c3, c4,
    ⟨s₁, hA⟩, ⟨s₂, hB⟩⟩ := hyp.G26_five hU hg hgV hI hS hS₂
  refine ⟨h1, hyp.G26_two hU hg hgV hI hS hW, ?_, ?_, M₁, M₂, Sa, Sb, s₁, s₂, a1, a2, a3, a4, a5,
    a6, a7, b1, b2, b3, b4, b5, b6, b7, c1, c2, c3, c4, hA, hB⟩
  · subst hS hS₂
    exact hyp.G26_three hU hg hgV hI
  · subst hS₂
    exact hyp.G26_four hU hg hgV hI

end CFSG.ASVolI
