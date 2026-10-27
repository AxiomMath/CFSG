module

public import CFSG.Quasithin.EmptyFaithful.S153D27

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input27List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15325L T Mc M V₁ V₂ Yp I L t → B56QuasisimpleList ↥(Star153 T I L)

@[expose] def Input27Normal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15327 T Mc M V₁ V₂ Yp I L t → B56QuasisimpleList ↥(Star153 T I L) →
      I ≤ Subgroup.normalizer (L : Set G)

@[expose] def Input27Trichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15327 T Mc M V₁ V₂ Yp I L t → B56QuasisimpleList ↥(Star153 T I L) →
      I ≤ Subgroup.normalizer (L : Set G) →
        (CFSG.Open.pRank 3 L = 1 ∧
          ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
              Nonempty (↥(Star153 T I L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K))) ∨
            (∃ m : ℕ, Odd m ∧ IsSL3 (2 ^ m) ↥(Star153 T I L)))) ∨
        L = thetaOf I ∨ (∃ n : ℕ, Even n ∧ IsSL3 (2 ^ n) ↥(Star153 T I L))

@[expose] def Input27Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15327 T Mc M V₁ V₂ Yp I L t → I ≤ Subgroup.normalizer (L : Set G) →
      CFSG.Open.pRank 3 L = 1 →
      ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(Star153 T I L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K))) ∨
        (∃ m : ℕ, Odd m ∧ IsSL3 (2 ^ m) ↥(Star153 T I L))) → Yp ≤ L

@[expose] def Input27Center : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15327 T Mc M V₁ V₂ Yp I L t → I ≤ Subgroup.normalizer (L : Set G) →
      ((∃ n : ℕ, Even n ∧ IsSL3 (2 ^ n) ↥(Star153 T I L)) ∨
        IsHat ↥(Star153 T I L) (alternatingGroup (Fin 6))) → False

theorem le_thetaOf_of_facts {G : Type} [Group G] [Finite G] {T M V₁ Yp I : Subgroup G}
    (hF : Facts153 T M V₁ Yp I) : Yp ≤ thetaOf I := by
  rw [hF.theta]
  exact Subgroup.closure_mono fun x hx => ⟨hx.1.2, hx.2⟩

theorem input15327_of_narrow (hL : Input27List) (h1 : Input27Normal)
    (h2 : Input27Trichotomy) (h3 : Input27Inner) (h4 : Input27Center) : Input15327 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  have hlist := hL G T Mc M V₁ V₂ Yp I L t c.toCtx15325L
  have hnorm := h1 G T Mc M V₁ V₂ Yp I L t c hlist
  have hno3 : ¬ ∃ n : ℕ, Even n ∧ IsSL3 (2 ^ n) ↥(Star153 T I L) :=
    fun h => h4 G T Mc M V₁ V₂ Yp I L t c hnorm (Or.inl h)
  have hnoHat : ¬ IsHat ↥(Star153 T I L) (alternatingGroup (Fin 6)) :=
    fun h => h4 G T Mc M V₁ V₂ Yp I L t c hnorm (Or.inr h)
  have hYp : Yp ≤ L := by
    rcases h2 G T Mc M V₁ V₂ Yp I L t c hlist hnorm with ⟨hr, hi⟩ | hθ | hS
    · exact h3 G T Mc M V₁ V₂ Yp I L t c hnorm hr hi
    · exact (le_thetaOf_of_facts c.facts.toFacts153).trans hθ.ge
    · exact (hno3 hS).elim
  exact ⟨hnorm, hYp, hno3, hnoHat⟩

end CFSG.Quasithin
