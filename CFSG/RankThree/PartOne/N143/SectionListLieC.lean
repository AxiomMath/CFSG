module

public import CFSG.RankThree.PartOne.N143.SectionListProof
public import CFSG.RankThree.PartOne.N143.SecRankHard
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup
open CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Assembly.LowTwoRank CFSG.Models
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem seven_le_dvd_genericOrders_cases {ℓ : ℕ} (h7 : 7 ≤ ℓ) {t : StatedLieTag} {n p f : ℕ}
    (h : ℓ ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2) :
    (t = .PSL ∧ ℓ ∣ n ∧ ℓ ∣ p ^ f - 1) ∨ (t = .PSU ∧ ℓ ∣ n ∧ ℓ ∣ p ^ f + 1) := by
  have small : ∀ m : ℕ, 0 < m → m ≤ 6 → ℓ ∣ m → False := fun m hm hm6 hd => by
    have := Nat.le_of_dvd hm hd
    omega
  have g2 : ∀ m : ℕ, ¬ ℓ ∣ Nat.gcd 2 m * 1 := fun m hm => by
    rw [mul_one] at hm
    exact small 2 (by norm_num) (by norm_num) (Nat.dvd_trans hm (Nat.gcd_dvd_left 2 m))
  have g3 : ∀ m : ℕ, ¬ ℓ ∣ Nat.gcd 3 m * 1 := fun m hm => by
    rw [mul_one] at hm
    exact small 3 (by norm_num) (by norm_num) (Nat.dvd_trans hm (Nat.gcd_dvd_left 3 m))
  have g4 : ∀ m : ℕ, ¬ ℓ ∣ Nat.gcd 4 m * 1 := fun m hm => by
    rw [mul_one] at hm
    exact small 4 (by norm_num) (by norm_num) (Nat.dvd_trans hm (Nat.gcd_dvd_left 4 m))
  cases t <;> simp only [genericOrders] at h
  · rw [mul_one] at h
    exact Or.inl ⟨rfl, Nat.dvd_trans h (Nat.gcd_dvd_left _ _),
      Nat.dvd_trans h (Nat.gcd_dvd_right _ _)⟩
  · rw [mul_one] at h
    exact Or.inr ⟨rfl, Nat.dvd_trans h (Nat.gcd_dvd_left _ _),
      Nat.dvd_trans h (Nat.gcd_dvd_right _ _)⟩
  · exact (g2 _ h).elim
  · exact (small 2 (by norm_num) (by norm_num) (by simpa using h)).elim
  · split_ifs at h
    · exact (small 1 (by norm_num) (by norm_num) (by simpa using h)).elim
    · exact (small 4 (by norm_num) (by norm_num) (by simpa using h)).elim
    · exact (g4 _ h).elim
  · exact (g4 _ h).elim
  · exact (small 1 (by norm_num) (by norm_num) (by simpa using h)).elim
  · exact (small 1 (by norm_num) (by norm_num) (by simpa using h)).elim
  · exact (g3 _ h).elim
  · exact (g2 _ h).elim
  · exact (small 1 (by norm_num) (by norm_num) (by simpa using h)).elim
  · exact (g3 _ h).elim
  all_goals exact (small 1 (by norm_num) (by norm_num) (by simpa using h)).elim

theorem seven_le_not_dvd_exceptionalOrders {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) {t : StatedLieTag}
    {n p f : ℕ} (h : ℓ ∣ (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) : False := by
  have key : ∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 9 ∨ m = 16) → ¬ ℓ ∣ m := by
    rintro m (rfl | rfl | rfl | rfl | rfl | rfl) hd
    · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    · have : ℓ ∣ 3 := hℓ.dvd_of_dvd_pow (n := 2) (by simpa using hd)
      exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
    · have : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow (n := 4) (by simpa using hd)
      exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  revert h
  unfold exceptionalOrders
  split <;> intro h <;> exact key _ (by decide) h

theorem seven_le_dvd_tableOrder_cases {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) {t : StatedLieTag}
    {n p f : ℕ} (h : ℓ ∣ tableOrder t n p f) :
    (t = .PSL ∧ ℓ ∣ n ∧ ℓ ∣ p ^ f - 1) ∨ (t = .PSU ∧ ℓ ∣ n ∧ ℓ ∣ p ^ f + 1) := by
  rw [tableOrder] at h
  rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
  · exact seven_le_dvd_genericOrders_cases h7 h
  · exact (seven_le_not_dvd_exceptionalOrders hℓ h7 h).elim

@[expose] def PrimeCoverLieIndex (ℓ : ℕ) : LieTypeIndex → Prop
  | .A r q => ℓ ∣ r + 1 ∧ ℓ ∣ q.card - 1
  | .twistedA r q => ℓ ∣ r + 1 ∧ ℓ ∣ q.card + 1
  | _ => False

theorem primeCoverLie_of_griess (hGA : GriessMultipliersAllModels) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    (d : ValidLieTypeIndex) {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (e : J ⧸ center J ≃* (CFSGIndex.lie d).Group) (hdvd : ℓ ∣ Nat.card (center J)) :
    PrimeCoverLieIndex ℓ d.1 := by
  have key : ∀ {t : StatedLieTag} {n p f : ℕ}, LieModel (CFSGIndex.lie d).Group t n p f →
      ℓ ∣ tableOrder t n p f := fun hm =>
    Nat.dvd_trans hdvd (card_center_dvd_tableOrder hGA hq e hm)
  have cases2 : ∀ {t : StatedLieTag} {n p f : ℕ}, LieModel (CFSGIndex.lie d).Group t n p f →
      (t = .PSL ∧ ℓ ∣ n ∧ ℓ ∣ p ^ f - 1) ∨ (t = .PSU ∧ ℓ ∣ n ∧ ℓ ∣ p ^ f + 1) :=
    fun hm => seven_le_dvd_tableOrder_cases hℓ h7 (key hm)
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    rcases cases2 (lieModel_typeA r q hv) with ⟨-, h1, h2⟩ | ⟨h, -⟩
    · exact ⟨h1, by simpa only [PrimePower.card_def] using h2⟩
    · exact absurd h (by decide)
  | twistedA r q =>
    have hm := lieModel_of_statedClassicalModel
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _))
    rcases cases2 hm with ⟨h, -⟩ | ⟨-, h1, h2⟩
    · exact absurd h (by decide)
    · exact ⟨h1, by simpa only [PrimePower.card_def] using h2⟩
  | B r q =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · have hm := lieModel_of_statedClassicalModel
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _))
      rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
    · by_cases hp : q.p = 2
      · have hm := lieModel_of_statedClassicalModel
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3
            (MulEquiv.refl _))
        rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
      · have hm := lieModel_of_statedClassicalModel
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3
            (MulEquiv.refl _))
        rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | C r q =>
    have hm := lieModel_of_statedClassicalModel
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _))
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | D r q =>
    have hm := lieModel_of_statedClassicalModel
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _))
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | twistedD r q =>
    have hm := lieModel_of_statedClassicalModel
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _))
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | E6 q =>
    have hm := lieModel_of_namesTag (t := .E6) ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | E7 q =>
    have hm := lieModel_of_namesTag (t := .E7) ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | E8 q =>
    have hm := lieModel_of_namesTag (t := .E8) ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | F4 q =>
    have hm := lieModel_of_namesTag (t := .F4) ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | G2 q =>
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    have hm := lieModel_of_namesTag (t := .G2) ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | twistedE6 q =>
    have hm := lieModel_of_namesTag (t := .twistedE6) ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | trialityD4 q =>
    have hm := lieModel_of_namesTag (t := .trialityD4) ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | suzuki m =>
    have hm1 : 1 ≤ m := hrange
    have hm := lieModel_of_namesTag (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      ⟨.suzuki m, hv⟩ ⟨rfl, rfl⟩ ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | reeG2 m =>
    have hm1 : 1 ≤ m := hrange
    have hm := lieModel_of_namesTag (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨.reeG2 m, hv⟩ ⟨rfl, rfl⟩ ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    have hm := lieModel_of_namesTag (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨.reeF4 m, hv⟩ ⟨rfl, rfl⟩ ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  | tits =>
    have hm := lieModel_of_namesTag (t := .Tits) (p := 2) (f := 1) ⟨.tits, hv⟩ ⟨rfl, rfl⟩
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩
    rcases cases2 hm with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

@[expose] def IsListedLieIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ =>
      (r = 1 ∧ q.p ≠ 2 ∧ 5 ≤ q.card) ∨ (r = 2 ∧ q.p ≠ 2 ∧ q.exponent ≤ 3) ∨
      (r = 3 ∧ q.p ≠ 2 ∧ q.exponent = 1) ∨ ((r = 1 ∨ r = 2) ∧ q.p = 2) ∨ (r = 3 ∧ q.p = 2) ∨
      ((r = 4 ∨ r = 5 ∨ r = 6) ∧ q.p = 2 ∧ q.exponent = 1)
  | .lie ⟨.twistedA r q, _⟩ =>
      (r = 2 ∧ q.p ≠ 2 ∧ q.exponent ≤ 3) ∨ (r = 3 ∧ q.p ≠ 2 ∧ q.exponent = 1) ∨
      ((r = 2 ∨ r = 3 ∨ r = 4) ∧ q.p = 2) ∨ (r = 5 ∧ q.p = 2 ∧ q.exponent = 1)
  | .lie ⟨.B r q, _⟩ =>
      (r = 2 ∧ q.p ≠ 2 ∧ q.exponent = 1) ∨ (r = 2 ∧ q.p = 2) ∨ (r = 3 ∧ q.p = 2) ∨
      (r = 4 ∧ q.p = 2 ∧ q.exponent = 1)
  | .lie ⟨.D r q, _⟩ => r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  | .lie ⟨.twistedD r q, _⟩ => r = 4 ∧ q.p = 2
  | .lie ⟨.F4 q, _⟩ => q.p = 2 ∧ q.exponent = 1
  | .lie ⟨.G2 q, _⟩ => (q.p ≠ 2 ∧ q.exponent = 1) ∨ q.p = 2
  | .lie ⟨.trialityD4 q, _⟩ => q.p = 2
  | .lie ⟨.suzuki _, _⟩ => True
  | .lie ⟨.reeG2 m, _⟩ => m = 1
  | .lie ⟨.reeF4 _, _⟩ => True
  | .lie ⟨.tits, _⟩ => True
  | _ => False

theorem IsListedLieIndex.theoremThreeList {i : CFSGIndex} (h : IsListedLieIndex i) {G : Type}
    [Group G] (e : G ≃* i.Group) : Census3.TheoremThreeList G := by
  cases i with
  | cyclic p hp => exact h.elim
  | alternating n hn => exact h.elim
  | sporadic s => exact h.elim
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      rcases h with ⟨rfl, hp, h5⟩ | ⟨rfl, hp, hf⟩ | ⟨rfl, hp, hf⟩ | ⟨hr, hp⟩ | ⟨rfl, hp⟩ |
        ⟨hr, hp, hf⟩
      · exact Census3.TheoremThreeList.of_A1_odd hv hp h5 e
      · exact Census3.TheoremThreeList.of_A2_odd hv hp hf e
      · exact Census3.TheoremThreeList.of_A3_prime hv hp hf e
      · rcases hr with rfl | rfl
        · exact Census3.TheoremThreeList.of_A1_even hv hp e
        · exact Census3.TheoremThreeList.of_A2_even hv hp e
      · exact Census3.TheoremThreeList.of_A3_even hv hp e
      · rcases hr with rfl | rfl | rfl
        · exact Census3.TheoremThreeList.of_A4_two hv hp hf e
        · exact Census3.TheoremThreeList.of_A5_two hv hp hf e
        · exact Census3.TheoremThreeList.of_A6_two hv hp hf e
    | twistedA r q =>
      rcases h with ⟨rfl, hp, hf⟩ | ⟨rfl, hp, hf⟩ | ⟨hr, hp⟩ | ⟨rfl, hp, hf⟩
      · exact Census3.TheoremThreeList.of_twistedA2_odd hv hp hf e
      · exact Census3.TheoremThreeList.of_twistedA3_prime hv hp hf e
      · rcases hr with rfl | rfl | rfl
        · exact Census3.TheoremThreeList.of_twistedA2_even hv hp e
        · exact Census3.TheoremThreeList.of_twistedA3_even hv hp e
        · exact Census3.TheoremThreeList.of_twistedA4_even hv hp e
      · exact Census3.TheoremThreeList.of_twistedA5_two hv hp hf e
    | B r q =>
      rcases h with ⟨rfl, hp, hf⟩ | ⟨rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨rfl, hp, hf⟩
      · exact Census3.TheoremThreeList.of_B2_prime hv hp hf e
      · exact Census3.TheoremThreeList.of_B2_even hv hp e
      · exact Census3.TheoremThreeList.of_B3_even hv hp e
      · exact Census3.TheoremThreeList.of_B4_two hv hp hf e
    | C r q => exact h.elim
    | D r q =>
      obtain ⟨rfl, hp, hf⟩ := h
      exact Census3.TheoremThreeList.of_D4_two hv hp hf e
    | twistedD r q =>
      obtain ⟨rfl, hp⟩ := h
      exact Census3.TheoremThreeList.of_twistedD4_even hv hp e
    | E6 q => exact h.elim
    | E7 q => exact h.elim
    | E8 q => exact h.elim
    | F4 q =>
      obtain ⟨hp, hf⟩ := h
      exact Census3.TheoremThreeList.of_F4_two hv hp hf e
    | G2 q =>
      rcases h with ⟨hp, hf⟩ | hp
      · exact Census3.TheoremThreeList.of_G2_prime hv hp hf e
      · exact Census3.TheoremThreeList.of_G2_even hv hp e
    | twistedE6 q => exact h.elim
    | trialityD4 q => exact Census3.TheoremThreeList.of_trialityD4_even hv h e
    | suzuki m => exact Census3.TheoremThreeList.of_suzuki hv e
    | reeG2 m =>
      obtain rfl : m = 1 := h
      exact Census3.TheoremThreeList.of_reeG2_one hv e
    | reeF4 m => exact Census3.TheoremThreeList.of_reeF4 hv e
    | tits => exact Census3.TheoremThreeList.of_tits hv e

theorem not_dvd_center_of_listed (hGA : GriessMultipliersAllModels) {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
    {i : CFSGIndex} (hi : IsListedLieIndex i) {J : Type} [Group J] [Finite J]
    (hq : IsQuasisimple J) (e : J ⧸ center J ≃* i.Group) : ¬ ℓ ∣ Nat.card (center J) := by
  intro hdvd
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim
  | lie d =>
    have hc := primeCoverLie_of_griess hGA hℓ h7 d hq e hdvd
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      obtain ⟨h1, h2⟩ := hc
      have key : r ≤ 6 ∧ (r = 6 → q.card = 2) := by
        rcases hi with ⟨rfl, hp, h5⟩ | ⟨rfl, hp, hf⟩ | ⟨rfl, hp, hf⟩ | ⟨hr, hp⟩ | ⟨rfl, hp⟩ |
          ⟨hr, hp, hf⟩
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, by omega⟩
        · refine ⟨by omega, fun h6 => ?_⟩
          simp [PrimePower.card_def, hp, hf]
      have hle := Nat.le_of_dvd (by omega) h1
      have h6 : r = 6 := by omega
      have hq2 := key.2 h6
      rw [hq2] at h2
      exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    | twistedA r q =>
      obtain ⟨h1, -⟩ := hc
      have key : r ≤ 5 := by
        rcases hi with ⟨rfl, hp, hf⟩ | ⟨rfl, hp, hf⟩ | ⟨hr, hp⟩ | ⟨rfl, hp, hf⟩ <;> omega
      have hle := Nat.le_of_dvd (by omega) h1
      omega
    | B r q => exact hc.elim
    | C r q => exact hc.elim
    | D r q => exact hc.elim
    | twistedD r q => exact hc.elim
    | E6 q => exact hc.elim
    | E7 q => exact hc.elim
    | E8 q => exact hc.elim
    | F4 q => exact hc.elim
    | G2 q => exact hc.elim
    | twistedE6 q => exact hc.elim
    | trialityD4 q => exact hc.elim
    | suzuki m => exact hc.elim
    | reeG2 m => exact hc.elim
    | reeF4 m => exact hc.elim
    | tits => exact hc.elim

@[expose] def IsLieUnlistedRestIndex (i : CFSGIndex) : Prop :=
  IsLieIndex i ∧ ¬ IsListedLieIndex i ∧ ¬ IsHardLowTwoIndex i

theorem lowTwoRankSectionListFor_lie_of_parts (hGA : GriessMultipliersAllModels)
    (hH : NoLowTwoRankSectionFor IsHardLowTwoIndex)
    (hR : NoLowTwoRankSectionFor IsLieUnlistedRestIndex) : LowTwoRankSectionListFor IsLieIndex := by
  intro L _ _ hK he H M _ _ hM π hπ hU ⟨i, hi, ⟨e⟩⟩
  by_cases hh : IsHardLowTwoIndex i
  · exact (hH L hK he H M hM π hπ hU ⟨i, hh, ⟨e⟩⟩).elim
  by_cases hl : IsListedLieIndex i
  · exact ⟨hl.theoremThreeList e, fun ℓ hℓ h7 => not_dvd_center_of_listed hGA hℓ h7 hl hM e⟩
  · exact (hR L hK he H M hM π hπ hU ⟨i, ⟨hi, hl, hh⟩, ⟨e⟩⟩).elim

end CFSG.RankThree.PartOne.N143
