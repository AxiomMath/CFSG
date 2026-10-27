module

public import CFSG.RankThree.PartOne.F106.QD32Exc
public import CFSG.RankThree.PartOne.F106.QD32Center
public import CFSG.RankThree.PartOne.F106.FiveRank

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.N143
open scoped commutatorElement

@[expose] def NoQD32AtThree : Prop :=
  ∀ (T : Type) [Group T],
    ((∃ f, StatedClassicalModel T .PSL 3 2 f) ∨ (∃ f, StatedClassicalModel T .PSU 3 2 f) ∨
      StatedClassicalModel T .PSU 6 2 1) →
    ∀ E R : Subgroup T, IsElementaryAbelian 3 E → InducesQD32 E R → False

@[expose] def NoQD32F4 : Prop :=
  ∀ (T : Type) [Group T], UntwistedChevalleyModel T .F4 2 →
    ∀ E R : Subgroup T, IsElementaryAbelian 3 E → InducesQD32 E R → False

@[expose] def NoQD32NonabelianRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ),
    StatedLieAdmissible t n 2 f → LieModel X t n 2 f → SmallEvenParams t n f →
    (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .twistedB2 ∨
      t = .F4) →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 5 → (t = .F4 → q = 3) → ∀ α : MulAut X, α ^ 5 = 1 →
      ∀ Y R : Subgroup X, (∀ y ∈ Y, y ^ q = 1) →
      (∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) → (∃ a ∈ Y, ∃ b ∈ Y, a * b ≠ b * a) →
      IsPGroup 2 R → R ≤ Subgroup.normalizer (Y : Set X) → (∀ y ∈ Y, α y ∈ Y) →
      (∀ r ∈ R, α r ∈ R) → (∃ r ∈ R, α r * r⁻¹ ∉ Subgroup.centralizer (Y : Set X)) →
      ∀ ψ : ↥R →* QD32, Function.Surjective ψ →
        (∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ Subgroup.centralizer (Y : Set X)) →
        (∀ r ∈ R, (∀ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Y : Set X)) →
          r ∈ Subgroup.centralizer (Y : Set X)) → False

theorem qd32_abelian_false_of_small
    (hThree : NoQD32AtThree) (hF4 : NoQD32F4) {X : Type} [Group X] [Finite X]
    (hEven : EvenLieTypeSmall X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    {E R : Subgroup X} (hE : IsElementaryAbelian q E) (h : InducesQD32 E R) : False := by
  obtain ⟨t, n, f, hadm, hLie, hsmall⟩ := hEven
  rcases hLie with ⟨ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, rfl, hmod⟩
  ·
    cases t
    case PSL =>
      by_cases h33 : q = 3 ∧ n = 3
      · obtain ⟨rfl, rfl⟩ := h33
        exact hThree X (Or.inl ⟨f, hmod⟩) E R hE h
      · exact false_psl_qd32 hsmall hmod hq hq2 hq5 h33 hE h
    case PSU =>
      by_cases h33 : q = 3 ∧ (n = 3 ∨ n = 6)
      · obtain ⟨rfl, hn36⟩ := h33
        rcases hn36 with rfl | rfl
        · exact hThree X (Or.inr (Or.inl ⟨f, hmod⟩)) E R hE h
        · have hf1 : f = 1 := by
            rcases hsmall with h6 | h6
            · omega
            · exact h6.2
          subst hf1
          exact hThree X (Or.inr (Or.inr hmod)) E R hE h
      · exact false_psu_qd32 hsmall hmod hq hq2 hq5 h33 hE h
    case PSp =>
      by_cases h4 : n ≤ 4
      · exact false_psp_qd32 h4 hmod hq hq2 hE h
      · exact absurd hsmall h4
    case POmegaOdd => exact absurd rfl hmod.1.2.2.2
    case POmegaPlus =>
      by_cases h4 : n ≤ 4
      · exact false_pomegaPlus_qd32 h4 hmod hq hq2 hE h
      · exact absurd hsmall h4
    case POmegaMinus =>
      by_cases h4 : n ≤ 4
      · exact false_pomegaMinus_qd32 h4 hmod hq hq2 hE h
      · exact absurd hsmall h4
    all_goals exact hmod.2.elim
  ·
    cases t
    case G2 => exact false_G2_qd32 hmod hq hq2 hE h
    case trialityD4 => exact false_triality_qd32 hmod hq hq2 hE h
    case F4 =>
      have hf1 : f = 1 := hsmall
      subst hf1
      by_cases hq3 : q = 3
      · subst hq3
        exact hF4 X (by simpa using hmod.2) E R hE h
      · exact false_F4_qd32 (by simpa using hmod.2) hq hq2 hq3 hE h
    case E6 => exact hsmall.elim
    case E7 => exact hsmall.elim
    case E8 => exact hsmall.elim
    case twistedE6 => exact hsmall.elim
    all_goals exact absurd ht (by decide)
  ·
    cases t
    case twistedG2 => exact absurd hmod.1.2.2.2.1 (by norm_num)
    case twistedF4 => exact false_ree_qd32 hmod hq hq2 hE h
    case Tits => exact false_tits_qd32 hmod hq hq2 hE h
    all_goals exact absurd ht (by decide)
  ·
    exact false_suzuki_qd32 hmod hq hq2 hE h

theorem qd32_nonabelian_false_of_small
    (hRest : NoQD32NonabelianRest) {X : Type} [Group X] [Finite X] (hEven : EvenLieTypeSmall X)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5) (α : MulAut X) (hα : α ^ 5 = 1)
    {Y R : Subgroup X} (hYexp : ∀ y ∈ Y, y ^ q = 1)
    (hYcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) (hYnab : ∃ a ∈ Y, ∃ b ∈ Y, a * b ≠ b * a)
    (hR2 : IsPGroup 2 R) (hRN : R ≤ Subgroup.normalizer (Y : Set X)) (hαY : ∀ y ∈ Y, α y ∈ Y)
    (hαR : ∀ r ∈ R, α r ∈ R) (hαnt : ∃ r ∈ R, α r * r⁻¹ ∉ Subgroup.centralizer (Y : Set X))
    (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ Subgroup.centralizer (Y : Set X))
    (hB : ∀ r ∈ R, (∀ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Y : Set X)) →
      r ∈ Subgroup.centralizer (Y : Set X))
    (h4 : q ^ 4 ≤ Nat.card Y) : False := by
  obtain ⟨t, n, f, hadm, hLie, hsmall⟩ := hEven
  have hrest : (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨
      t = .twistedB2 ∨ t = .F4) → (t = .F4 → q = 3) → False := fun ht hq3 =>
    hRest X t n f hadm hLie hsmall ht q hq hq2 hq5 hq3 α hα Y R hYexp hYcl hYnab hR2 hRN hαY hαR
      hαnt ψ hψs hψc hB
  rcases hLie with ⟨ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, ht, hmod⟩ | ⟨hn0, rfl, hmod⟩
  ·
    cases t
    case PSL => exact hrest (Or.inl rfl) (fun h => absurd h (by decide))
    case PSU => exact hrest (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide))
    case PSp => exact hrest (Or.inr (Or.inr (Or.inl rfl))) (fun h => absurd h (by decide))
    case POmegaOdd => exact absurd rfl hmod.1.2.2.2
    case POmegaPlus =>
      exact hrest (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun h => absurd h (by decide))
    case POmegaMinus =>
      exact hrest (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (fun h => absurd h (by decide))
    all_goals exact hmod.2.elim
  ·
    cases t
    case G2 => exact false_G2_of_card hmod hq hq2 hYexp h4
    case trialityD4 => exact false_triality_of_card hmod hq hq2 hYexp h4
    case F4 =>
      have hf1 : f = 1 := hsmall
      subst hf1
      by_cases hq3 : q = 3
      · exact hrest (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) (fun _ => hq3)
      · exact false_F4_of_card (by simpa using hmod.2) hq hq2 hq3 hYexp h4
    case E6 => exact hsmall.elim
    case E7 => exact hsmall.elim
    case E8 => exact hsmall.elim
    case twistedE6 => exact hsmall.elim
    all_goals exact absurd ht (by decide)
  ·
    cases t
    case twistedG2 => exact absurd hmod.1.2.2.2.1 (by norm_num)
    case twistedF4 => exact false_ree_of_card hmod hq hq2 hYexp h4
    case Tits => exact false_tits_of_card hmod hq hq2 hYexp h4
    all_goals exact absurd ht (by decide)
  ·
    exact hrest (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (fun h => absurd h
      (by decide))

theorem evenLieNoQD32_of_converse
    (hConv : EvenListConverse) (hThree : NoQD32AtThree) (hF4 : NoQD32F4)
    (hRest : NoQD32NonabelianRest) : EvenLieNoQD32 := by
  intro X _ _ hs hnonab hEven hList q hq hq2 hq5 α hα Y R hYexp hYcl hR2 hRN hαY hαR hαnt ψ hψs hψc
  have hEvenS := hConv X hs hnonab hEven hList
  by_cases hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a
  · have hE : IsElementaryAbelian q Y :=
      { is_comm := ⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
          Subtype.ext (by simpa using hYexp y y.2) }
    exact qd32_abelian_false_of_small hThree hF4 hEvenS hq hq2 hq5 hE ⟨hRN, ψ, hψs, hψc⟩
  · push Not at hab
    rcases qd32_center_dichotomy hq hq2 hYexp hR2 hRN ψ hψs hψc with hA | hBr
    · exact qd32_abelian_false_of_small hThree hF4 hEvenS hq hq2 hq5
        (isElementaryAbelian_centerOf hYexp) (inducesQD32_centerOf hRN ψ hψs hψc hA)
    · exact qd32_nonabelian_false_of_small hRest hEvenS hq hq2 hq5 α hα hYexp hYcl hab hR2 hRN hαY
        hαR hαnt ψ hψs hψc (fun r hr h => hBr ⟨r, hr⟩ h)
        (card_ge_pow_four_of_faithful_quotient hq hq2 hYexp hYcl hRN ψ hψs hψc hBr)

end CFSG.RankThree.PartOne.F106
