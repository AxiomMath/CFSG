module

public import CFSG.RankThree.PartOne.N143.SectionListLieC
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly TauCeti Subgroup CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Assembly.LowTwoRank CFSG.Models
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem five_dvd_genericOrders_cases {t : StatedLieTag} {n p f : ℕ}
    (h : 5 ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2) :
    (t = .PSL ∧ 5 ∣ n ∧ 5 ∣ p ^ f - 1) ∨ (t = .PSU ∧ 5 ∣ n ∧ 5 ∣ p ^ f + 1) := by
  have small : ∀ m : ℕ, 0 < m → m ≤ 4 → 5 ∣ m → False := fun m hm hm4 hd => by
    have := Nat.le_of_dvd hm hd
    omega
  have g2 : ∀ m : ℕ, ¬ 5 ∣ Nat.gcd 2 m * 1 := fun m hm => by
    rw [mul_one] at hm
    exact small 2 (by norm_num) (by norm_num) (Nat.dvd_trans hm (Nat.gcd_dvd_left 2 m))
  have g3 : ∀ m : ℕ, ¬ 5 ∣ Nat.gcd 3 m * 1 := fun m hm => by
    rw [mul_one] at hm
    exact small 3 (by norm_num) (by norm_num) (Nat.dvd_trans hm (Nat.gcd_dvd_left 3 m))
  have g4 : ∀ m : ℕ, ¬ 5 ∣ Nat.gcd 4 m * 1 := fun m hm => by
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
  · exact (small 2 (by norm_num) (by norm_num) (by simp at h)).elim
  · split_ifs at h
    · exact (small 1 (by norm_num) (by norm_num) (by simp at h)).elim
    · exact (small 4 (by norm_num) (by norm_num) (by simp at h)).elim
    · exact (g4 _ h).elim
  · exact (g4 _ h).elim
  · exact (small 1 (by norm_num) (by norm_num) (by simp at h)).elim
  · exact (small 1 (by norm_num) (by norm_num) (by simp at h)).elim
  · exact (g3 _ h).elim
  · exact (g2 _ h).elim
  · exact (small 1 (by norm_num) (by norm_num) (by simp at h)).elim
  · exact (g3 _ h).elim
  all_goals exact (small 1 (by norm_num) (by norm_num) (by simp at h)).elim

theorem five_not_dvd_exceptionalOrders {t : StatedLieTag}
    {n p f : ℕ} (h : 5 ∣ (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) :
    False := by
  have key : ∀ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 9 ∨ m = 16) → ¬ 5 ∣ m := by
    rintro m (rfl | rfl | rfl | rfl | rfl | rfl) hd
    · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    · omega
    · omega
  revert h
  unfold exceptionalOrders
  split <;> intro h <;> exact key _ (by decide) h

theorem five_dvd_tableOrder_cases {t : StatedLieTag}
    {n p f : ℕ} (h : 5 ∣ tableOrder t n p f) :
    (t = .PSL ∧ 5 ∣ n ∧ 5 ∣ p ^ f - 1) ∨ (t = .PSU ∧ 5 ∣ n ∧ 5 ∣ p ^ f + 1) := by
  rw [tableOrder] at h
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
  · exact five_dvd_genericOrders_cases h
  · exact (five_not_dvd_exceptionalOrders h).elim


theorem primeCoverLie_five (hGA : GriessMultipliersAllModels)
    (d : ValidLieTypeIndex) {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (e : J ⧸ center J ≃* (CFSGIndex.lie d).Group) (hdvd : 5 ∣ Nat.card (center J)) :
    PrimeCoverLieIndex 5 d.1 := by
  have key : ∀ {t : StatedLieTag} {n p f : ℕ}, LieModel (CFSGIndex.lie d).Group t n p f →
      5 ∣ tableOrder t n p f := fun hm =>
    Nat.dvd_trans hdvd (card_center_dvd_tableOrder hGA hq e hm)
  have cases2 : ∀ {t : StatedLieTag} {n p f : ℕ}, LieModel (CFSGIndex.lie d).Group t n p f →
      (t = .PSL ∧ 5 ∣ n ∧ 5 ∣ p ^ f - 1) ∨ (t = .PSU ∧ 5 ∣ n ∧ 5 ∣ p ^ f + 1) :=
    fun hm => five_dvd_tableOrder_cases (key hm)
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


end CFSG.RankThree.PartOne.K133B
