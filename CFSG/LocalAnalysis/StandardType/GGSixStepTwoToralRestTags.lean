module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Witness

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggStepTwoWitness_of_inf_ne_bot {Bs D G₀ R : Subgroup G} (hDBs : D ≤ Bs) (h : D ⊓ R ≠ ⊥) :
    ∃ a ∈ Bs ⊓ R, a ≠ 1 ∧ ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := (D ⊓ R).ne_bot_iff_exists_ne_one.mp h
  have ha' := Subgroup.mem_inf.mp ha
  refine ⟨a, Subgroup.mem_inf.mpr ⟨hDBs ha'.1, ha'.2⟩, fun h1 => ha1 (Subtype.ext h1), 1,
    Subgroup.mem_inf.mpr ⟨one_mem _, one_mem _⟩, ?_⟩
  simpa using ha'.1

theorem ggStepTwo_inf_ne_bot_of_card_le_mul {p : ℕ} (hp : p.Prime) {Bs D R : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hDBs : D ≤ Bs) (hDcard : Nat.card D = p ^ 2)
    (hidx : Nat.card Bs ≤ p * Nat.card ↥(Bs ⊓ R)) : D ⊓ R ≠ ⊥ := by
  intro hbot
  have hDS : D ⊓ (Bs ⊓ R) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left D inf_le_right).trans hbot.le)
  have hcomm : ∀ a ∈ D, ∀ c ∈ Bs ⊓ R, a * c = c * a := fun a ha c hc => by
    have := hBs.1
    exact congrArg Subtype.val (mul_comm' (⟨a, hDBs ha⟩ : Bs) ⟨c, hc.1⟩)
  have hle := ggCard_mul_card_le_of_commute hDBs inf_le_left hcomm hDS
  rw [hDcard] at hle
  have hpos : 0 < Nat.card ↥(Bs ⊓ R) := Nat.card_pos
  have h3 : p ^ 2 ≤ p := Nat.le_of_mul_le_mul_right (hle.trans hidx) hpos
  have hp1 := hp.one_lt
  nlinarith

theorem ggStepTwoWitness_of_card_le_mul {p : ℕ} (hp : p.Prime) {Bs D G₀ R : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hDBs : D ≤ Bs) (hDcard : Nat.card D = p ^ 2)
    (hidx : Nat.card Bs ≤ p * Nat.card ↥(Bs ⊓ R)) :
    ∃ a ∈ Bs ⊓ R, a ≠ 1 ∧ ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D :=
  ggStepTwoWitness_of_inf_ne_bot hDBs (ggStepTwo_inf_ne_bot_of_card_le_mul hp hBs hDBs hDcard hidx)

end Witness

section Inputs

theorem ggStepTwoToralWitnessOn_of_placeholder {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedF4 ∨ t = .Tits) :
    GGStepTwoToralWitnessOn t := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  have hrk := hctx.2.2.2.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggStepTwoToralWitnessOn_G2 : GGStepTwoToralWitnessOn .G2 :=
  ggStepTwoToralWitnessOn_of_placeholder (Or.inl rfl)

theorem ggStepTwoToralWitnessOn_trialityD4 : GGStepTwoToralWitnessOn .trialityD4 :=
  ggStepTwoToralWitnessOn_of_placeholder (Or.inr (Or.inl rfl))

theorem ggStepTwoToralWitnessOn_twistedB2 : GGStepTwoToralWitnessOn .twistedB2 :=
  ggStepTwoToralWitnessOn_of_placeholder (Or.inr (Or.inr (Or.inl rfl)))

theorem ggStepTwoToralWitnessOn_twistedF4 : GGStepTwoToralWitnessOn .twistedF4 :=
  ggStepTwoToralWitnessOn_of_placeholder (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem ggStepTwoToralWitnessOn_Tits : GGStepTwoToralWitnessOn .Tits :=
  ggStepTwoToralWitnessOn_of_placeholder (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem ggStepTwoToralWitnessRestInput_of_exc (hF4 : GGStepTwoToralWitnessOn .F4)
    (hE6 : GGStepTwoToralWitnessOn .E6) (hE7 : GGStepTwoToralWitnessOn .E7)
    (hE8 : GGStepTwoToralWitnessOn .E8) (hTwE6 : GGStepTwoToralWitnessOn .twistedE6) :
    GGStepTwoToralWitnessRestInput :=
  ⟨hF4, hE6, hE7, hE8, hTwE6, ggStepTwoToralWitnessOn_G2, ggStepTwoToralWitnessOn_trialityD4,
    ggStepTwoToralWitnessOn_twistedB2, ggStepTwoToralWitnessOn_twistedF4,
    ggStepTwoToralWitnessOn_Tits⟩

@[expose] def ggExcWeylOrder : StatedLieTag → ℕ
  | .F4 => 1152
  | .E6 => 51840
  | .twistedE6 => 51840
  | .E7 => 2903040
  | .E8 => 696729600
  | _ => 1

@[expose] def GGStepTwoExcIndexOn (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ p ∣ ggExcWeylOrder t →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        Nat.card Bs ≤ p * Nat.card ↥(Bs ⊓ (Subgroup.zpowers b ⊔ L₁))

@[expose] def GGStepTwoToralWitnessSmallOn (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    p ∣ ggExcWeylOrder t →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥ →
          ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
            ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D

theorem ggStepTwoToralWitnessOn_of_index_small {t : StatedLieTag} (hI : GGStepTwoExcIndexOn t)
    (hS : GGStepTwoToralWitnessSmallOn t) : GGStepTwoToralWitnessOn t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 _ b L₁ hpair
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hDBs : D ≤ Bs := hctx.2.2.1.1.1.trans hctx.2.1.1
  have hDcard : Nat.card D = p ^ 2 := hctx.2.2.1.1.2.2.1
  by_cases hW : p ∣ ggExcWeylOrder t
  · by_cases hDR : D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥
    · exact hS G p B Bs x L D J n f ψ hctx s1 hW b L₁ hpair hDR
    · exact ggStepTwoWitness_of_inf_ne_bot hDBs hDR
  · exact ggStepTwoWitness_of_card_le_mul hp hctx.2.1.2.1 hDBs hDcard
      (hI G p B Bs x L D J n f ψ hctx s1 hW b L₁ hpair)

@[expose] def GGStepTwoToralExcInputs : Prop :=
  (GGStepTwoExcIndexOn .F4 ∧ GGStepTwoToralWitnessSmallOn .F4) ∧
    (GGStepTwoExcIndexOn .E6 ∧ GGStepTwoToralWitnessSmallOn .E6) ∧
    (GGStepTwoExcIndexOn .E7 ∧ GGStepTwoToralWitnessSmallOn .E7) ∧
    (GGStepTwoExcIndexOn .E8 ∧ GGStepTwoToralWitnessSmallOn .E8) ∧
    (GGStepTwoExcIndexOn .twistedE6 ∧ GGStepTwoToralWitnessSmallOn .twistedE6)

theorem ggStepTwoToralWitnessRestInput_of_excInputs (h : GGStepTwoToralExcInputs) :
    GGStepTwoToralWitnessRestInput := by
  obtain ⟨⟨iF, sF⟩, ⟨i6, s6⟩, ⟨i7, s7⟩, ⟨i8, s8⟩, ⟨iT, sT⟩⟩ := h
  exact ggStepTwoToralWitnessRestInput_of_exc (ggStepTwoToralWitnessOn_of_index_small iF sF)
    (ggStepTwoToralWitnessOn_of_index_small i6 s6) (ggStepTwoToralWitnessOn_of_index_small i7 s7)
    (ggStepTwoToralWitnessOn_of_index_small i8 s8) (ggStepTwoToralWitnessOn_of_index_small iT sT)

end Inputs

end CFSG.StandardType
