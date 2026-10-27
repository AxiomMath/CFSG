module

public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeSmall
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46
public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverSporadic
public import CFSG.RankThree.PartOne.Census3.SporadicCertificates
public import CFSG.RankThree.PartOne.Census3.Sporadic
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Bridge.M24Surj
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.Bridge.J2
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.McL
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.RankThree.PartTwo.Census.Exceptional.Main
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 TauCeti
open CFSG.RankThree.PartOne.Census3
open CFSG.Assembly.LowTwoRank CFSG.Models
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.GH74.Generic (card_center_dvd_hopfMultiplier centralQuotientMap
  centralQuotientMap_surjective centralQuotientMap_ker card_eq_card_mul_card_ker)

@[expose] def TripleCoverSporadicRankFour (s : SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsThreeCenterCover G (CFSGIndex.sporadic s).Group →
    4 ≤ CFSG.twoLocalOddRank G

structure TripleCoverSporadicResidual : Prop where
  ly : TripleCoverSporadicRankFour .Ly
  co3 : TripleCoverSporadicRankFour .Co3
  co2 : TripleCoverSporadicRankFour .Co2
  hn : TripleCoverSporadicRankFour .HN
  th : TripleCoverSporadicRankFour .Th

theorem tripleCoverAlternating : TripleCoverAlternating := by
  intro n G _ _ hn ⟨hq, h3, ⟨e⟩⟩
  have hdvd := card_center_dvd_hopfMultiplier hq e
  rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn).2] at hdvd
  by_contra h67
  rw [ite_eq_right_iff.mpr fun h => absurd h h67] at hdvd
  have := Nat.dvd_trans h3 hdvd
  omega

theorem three_dvd_genericOrders_cases {t : StatedLieTag} {n p f : ℕ}
    (h : 3 ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2) :
    (t = .PSL ∧ 3 ∣ n ∧ 3 ∣ p ^ f - 1) ∨ (t = .PSU ∧ 3 ∣ n ∧ 3 ∣ p ^ f + 1) ∨
      (t = .E6 ∧ 3 ∣ p ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ p ^ f + 1) := by
  have h2 : ∀ m : ℕ, ¬ 3 ∣ Nat.gcd 2 m * 1 := fun m hm => by
    rw [mul_one] at hm
    exact absurd (Nat.dvd_trans hm (Nat.gcd_dvd_left 2 m)) (by norm_num)
  have h4 : ∀ m : ℕ, ¬ 3 ∣ Nat.gcd 4 m * 1 := fun m hm => by
    rw [mul_one] at hm
    exact absurd (Nat.dvd_trans hm (Nat.gcd_dvd_left 4 m)) (by norm_num)
  cases t <;> simp only [genericOrders] at h
  · rw [mul_one] at h
    exact Or.inl ⟨rfl, Nat.dvd_trans h (Nat.gcd_dvd_left _ _),
      Nat.dvd_trans h (Nat.gcd_dvd_right _ _)⟩
  · rw [mul_one] at h
    exact Or.inr (Or.inl ⟨rfl, Nat.dvd_trans h (Nat.gcd_dvd_left _ _),
      Nat.dvd_trans h (Nat.gcd_dvd_right _ _)⟩)
  · exact (h2 _ h).elim
  · omega
  · split_ifs at h
    · omega
    · omega
    · exact (h4 _ h).elim
  · exact (h4 _ h).elim
  · omega
  · omega
  · rw [mul_one] at h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, Nat.dvd_trans h (Nat.gcd_dvd_right _ _)⟩))
  · exact (h2 _ h).elim
  · omega
  · rw [mul_one] at h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, Nat.dvd_trans h (Nat.gcd_dvd_right _ _)⟩))
  all_goals omega

theorem three_dvd_exceptionalOrders_cases {t : StatedLieTag} {n p f : ℕ}
    (h : 3 ∣ (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) :
    (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  revert h
  unfold exceptionalOrders
  split <;> simp_all

theorem three_dvd_tableOrder_cases {t : StatedLieTag} {n p f : ℕ} (h : 3 ∣ tableOrder t n p f) :
    (t = .PSL ∧ 3 ∣ n ∧ 3 ∣ p ^ f - 1) ∨ (t = .PSU ∧ 3 ∣ n ∧ 3 ∣ p ^ f + 1) ∨
      (t = .E6 ∧ 3 ∣ p ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ p ^ f + 1) ∨
      (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  rw [tableOrder] at h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases three_dvd_genericOrders_cases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (three_dvd_exceptionalOrders_cases h))))

theorem lieModel_of_statedClassicalModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel X t n p f) : LieModel X t n p f :=
  ⟨h.1, Or.inl h⟩

theorem lieModel_typeA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    LieModel (CFSGIndex.lie ⟨.A r q, hv⟩).Group .PSL (r + 1) q.p q.exponent :=
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA r q hv

theorem lieModel_of_namesTag {t : StatedLieTag} {p f : ℕ} (d : ValidLieTypeIndex)
    (hd : NamesTag d.1 t p f) (h : StatedLieAdmissible t 0 p f) :
    LieModel (CFSGIndex.lie d).Group t 0 p f :=
  lieModel_lie h d hd

theorem tripleCoverLie_of_griess (hGA : GriessMultipliersAllModels) : TripleCoverLie := by
  intro d G _ _ ⟨hq, h3, ⟨e⟩⟩
  have key : ∀ {t : StatedLieTag} {n p f : ℕ}, LieModel (CFSGIndex.lie d).Group t n p f →
      3 ∣ tableOrder t n p f := fun hm =>
    Nat.dvd_trans h3 (card_center_dvd_tableOrder hGA hq e hm)
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hdup := (LieTypeIndex.valid_iff _).1 hv
  cases d with
  | A r q =>
    rcases three_dvd_tableOrder_cases (key (lieModel_typeA r q hv)) with
      ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hn, hp, hf⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨h1, by simpa only [PrimePower.card_def] using h2⟩
    all_goals first
      | exact absurd h (by decide)
      | (exfalso
         apply hdup.2
         simp only [LieTypeIndex.isDuplicateRepresentative_iff, PrimePower.card_def, hp, hf]
         omega)
  | twistedA r q =>
    have hm := lieModel_of_statedClassicalModel
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _))
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hn, hp, hf⟩
    · exact absurd h (by decide)
    · exact Or.inl ⟨h1, by simpa only [PrimePower.card_def] using h2⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact Or.inr ⟨by omega, by simp only [PrimePower.card_def, hp, hf]; norm_num⟩
  | B r q =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · have hm := lieModel_of_statedClassicalModel
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _))
      rcases three_dvd_tableOrder_cases (key hm) with
        ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        exact absurd h (by decide)
    · by_cases hp : q.p = 2
      · have hm := lieModel_of_statedClassicalModel
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3
            (MulEquiv.refl _))
        rcases three_dvd_tableOrder_cases (key hm) with
          ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
          exact absurd h (by decide)
      · have hm := lieModel_of_statedClassicalModel
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3
            (MulEquiv.refl _))
        rcases three_dvd_tableOrder_cases (key hm) with
          ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hn, hp3, hf⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact ⟨hn, by simp only [PrimePower.card_def, hp3, hf]; norm_num⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
  | C r q =>
    have hm := lieModel_of_statedClassicalModel
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv (MulEquiv.refl _))
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | D r q =>
    have hm := lieModel_of_statedClassicalModel
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv (MulEquiv.refl _))
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | twistedD r q =>
    have hm := lieModel_of_statedClassicalModel
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv (MulEquiv.refl _))
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | E6 q =>
    have hm := lieModel_of_namesTag (t := .E6) ⟨.E6 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simpa only [TripleCoverLieIndex, PrimePower.card_def] using h1
    all_goals exact absurd h (by decide)
  | E7 q =>
    have hm := lieModel_of_namesTag (t := .E7) ⟨.E7 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | E8 q =>
    have hm := lieModel_of_namesTag (t := .E8) ⟨.E8 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | F4 q =>
    have hm := lieModel_of_namesTag (t := .F4) ⟨.F4 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | G2 q =>
    have h3q : 3 ≤ q.p ^ q.exponent := by simpa only [PrimePower.card_def] using hrange
    have hm := lieModel_of_namesTag (t := .G2) ⟨.G2 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl, h3q⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hp, hf⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · show q.card = 3
      simp only [PrimePower.card_def, hp, hf]
      norm_num
    · exact absurd h (by decide)
  | twistedE6 q =>
    have hm := lieModel_of_namesTag (t := .twistedE6) ⟨.twistedE6 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simpa only [TripleCoverLieIndex, PrimePower.card_def] using h1
    all_goals exact absurd h (by decide)
  | trialityD4 q =>
    have hm := lieModel_of_namesTag (t := .trialityD4) ⟨.trialityD4 q, hv⟩ ⟨rfl, rfl⟩
      ⟨q.prime_p, q.exponent_pos, rfl⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | suzuki m =>
    have hm1 : 1 ≤ m := hrange
    have hm := lieModel_of_namesTag (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      ⟨.suzuki m, hv⟩ ⟨rfl, rfl⟩ ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | reeG2 m =>
    have hm1 : 1 ≤ m := hrange
    have hm := lieModel_of_namesTag (t := .twistedG2) (p := 3) (f := 2 * m + 1)
      ⟨.reeG2 m, hv⟩ ⟨rfl, rfl⟩ ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    have hm := lieModel_of_namesTag (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨.reeF4 m, hv⟩ ⟨rfl, rfl⟩ ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)
  | tits =>
    have hm := lieModel_of_namesTag (t := .Tits) (p := 2) (f := 1) ⟨.tits, hv⟩ ⟨rfl, rfl⟩
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩
    rcases three_dvd_tableOrder_cases (key hm) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      exact absurd h (by decide)

theorem not_isThreeCenterCover_of_odd {G S T : Type} [Group G] [Finite G] [Group S] [Group T]
    (b : T ≃* S)
    (H : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* T),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    ¬ IsThreeCenterCover G S := by
  rintro ⟨hq, h3, ⟨e⟩⟩
  have : Group.IsPerfect G := hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.center G)) := Sylow.nonempty
  set T₂ : Subgroup G := (P : Subgroup (Subgroup.center G)).map (Subgroup.center G).subtype
    with hT₂
  have hTZ : T₂ ≤ Subgroup.center G := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have : T₂.Normal := Subgroup.normal_of_le_center hTZ
  set φ : G →* T := centralQuotientMap (e.trans b.symm) with hφ
  have hφs : Function.Surjective φ := centralQuotientMap_surjective _
  have hφk : φ.ker = Subgroup.center G := centralQuotientMap_ker _
  set π : G ⧸ T₂ →* T := QuotientGroup.lift T₂ φ (hφk ▸ hTZ) with hπ
  have hπs : Function.Surjective π := by
    intro t
    obtain ⟨g, rfl⟩ := hφs t
    exact ⟨(g : G ⧸ T₂), rfl⟩
  have hπk : π.ker = (Subgroup.center G).map (QuotientGroup.mk' T₂) := by
    rw [hπ, QuotientGroup.ker_lift, hφk]
  have hπc : π.ker ≤ Subgroup.center (G ⧸ T₂) := by
    rw [hπk]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective T₂ y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  have : Finite T := Finite.of_surjective φ hφs
  have h1 : Nat.card G = Nat.card T * Nat.card (Subgroup.center G) := by
    rw [card_eq_card_mul_card_ker φ hφs, hφk]
  have h2 : Nat.card G = Nat.card (G ⧸ T₂) * Nat.card T₂ :=
    T₂.card_eq_card_quotient_mul_card_subgroup
  have h4 : Nat.card (G ⧸ T₂) = Nat.card T * Nat.card π.ker := card_eq_card_mul_card_ker π hπs
  have h5 : Nat.card T₂ = Nat.card P := Subgroup.card_map_of_injective
    (Subgroup.center G).subtype_injective
  set a := (Nat.card (Subgroup.center G)).factorization 2 with ha
  have h6 : Nat.card P = 2 ^ a := Sylow.card_eq_multiplicity P
  have hZ : Nat.card (Subgroup.center G) = Nat.card π.ker * 2 ^ a := by
    have e1 := h1.symm.trans h2
    rw [h4, h5, h6, mul_assoc] at e1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos e1
  have hodd : Odd (Nat.card π.ker) := by
    have hc := Nat.coprime_ordCompl Nat.prime_two (Nat.card_pos (α := Subgroup.center G)).ne'
    have e2 : Nat.card (Subgroup.center G) / 2 ^ a = Nat.card π.ker := by
      rw [hZ, Nat.mul_div_cancel _ (pow_pos two_pos _)]
    rw [e2] at hc
    exact Nat.coprime_two_left.mp hc
  have h3k : 3 ∣ Nat.card π.ker := by
    rw [hZ] at h3
    exact (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right h3
  have hbot := H (G ⧸ T₂) π hπs hπc hodd
  rw [hbot, Subgroup.card_bot] at h3k
  omega

theorem J1_perfect_odd_cover_trivial {E : Type} [Group E]
    [Finite E] [Group.IsPerfect E] (π : E →* Blueprint.NativeSporadic.J1)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have : Finite Blueprint.NativeSporadic.J1 := Finite.of_surjective π hπ
  refine CFSG.SectionRank.ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC hodd
    fun r hr hr2 hsq _ _ => ?_
  exfalso
  rw [CFSG.Sporadic.J1.card_J1] at hsq
  by_cases h3 : r = 3
  · subst h3
    exact absurd hsq (by norm_num)
  · exact (CFSG.SectionRank.small_sporadic_order_conditions (Or.inr (Or.inr (Or.inr rfl)))).2
      r hr hr2 h3 hsq

section NoTripleCover

theorem not_isThreeCenterCover_sporadic {G : Type} [Group G] [Finite G] {s : SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .HS ∨ s = .He ∨
      s = .Ru ∨ s = .J4) :
    ¬ IsThreeCenterCover G (CFSGIndex.sporadic s).Group := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
    exact not_isThreeCenterCover_of_odd b fun _ _ _ _ π hπ hC hodd =>
      CFSG.QuasithinUnique.Ch1.M11_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    exact not_isThreeCenterCover_of_odd b fun _ _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
    exact not_isThreeCenterCover_of_odd b fun _ _ _ _ π hπ hC hodd =>
      CFSG.QuasithinUnique.Ch1.M23_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
    exact not_isThreeCenterCover_of_odd b fun _ _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.M24_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
    exact @not_isThreeCenterCover_of_odd G _ Blueprint.NativeSporadic.J1 _ _ _ Units.instGroup b
      fun _ _ _ _ π hπ hC hodd =>
        J1_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
    exact @not_isThreeCenterCover_of_odd G _ Blueprint.NativeSporadic.J2 _ _ _ Units.instGroup b
      fun _ _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.J2_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
    exact @not_isThreeCenterCover_of_odd G _ Blueprint.NativeSporadic.HS _ _ _ Units.instGroup b
      fun _ _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.HS_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
    exact @not_isThreeCenterCover_of_odd G _ Blueprint.NativeSporadic.He _ _ _ Units.instGroup b
      fun _ _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.He_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
    exact @not_isThreeCenterCover_of_odd G _ Blueprint.NativeSporadic.Ru _ _ _ Units.instGroup b
      fun _ _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.Ru_perfect_odd_cover_trivial π hπ hC hodd
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
    exact @not_isThreeCenterCover_of_odd G _ Blueprint.NativeSporadic.J4 _ _ _ Units.instGroup b
      fun _ _ _ _ π hπ hC hodd =>
        CFSG.SectionRank.J4_perfect_odd_cover_trivial CFSG.SectionRank.j4OrderHyp π hπ hC
          hodd

end NoTripleCover

section Sporadic43

theorem item43_sporadic (hres : TripleCoverSporadicResidual) {G : Type} [Group G] [Finite G]
    (hG : SectionFourHyp G) (hS : SectionFourHyp (G ⧸ Subgroup.center G))
    (hnonab : ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a) [IsSimpleGroup (G ⧸ Subgroup.center G)]
    {s : SporadicName} (e : G ⧸ Subgroup.center G ≃* (CFSGIndex.sporadic s).Group)
    (htc : IsThreeCenterCover G (CFSGIndex.sporadic s).Group) :
    Nonempty (G ⧸ Subgroup.center G ≃* Blueprint.NativeSporadic.M22) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (G ⧸ Subgroup.center G ≃* Blueprint.NativeSporadic.ON) := by
  have hex : ∀ {j : CFSGIndex}, ExcludedIndex j → (G ⧸ Subgroup.center G ≃* j.Group) → False :=
    fun hj e' => SectionFourHyp.false_of_four_le_twoLocalOddRank hS (hj _ ‹_› hnonab e')
  have hexG : 4 ≤ CFSG.twoLocalOddRank G → False :=
    SectionFourHyp.false_of_four_le_twoLocalOddRank hG
  have hnot : (s = .M11 ∨ s = .M12 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .HS ∨
      s = .He ∨ s = .Ru ∨ s = .J4) → False := fun hs => not_isThreeCenterCover_sporadic hs htc
  cases s with
  | M22 =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    exact Or.inl ⟨e.trans b.symm⟩
  | J3 =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
    exact Or.inr (Or.inl ⟨e.trans b.symm⟩)
  | McL =>
    have : IsSimpleGroup SporadicName.McL.Group := e.symm.isSimpleGroup
    obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL
    exact Or.inr (Or.inr (Or.inl ⟨e.trans b⟩))
  | ONan =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    exact Or.inr (Or.inr (Or.inr ⟨e.trans b.symm⟩))
  | Suz => exact (hexG (tripleCoverSuzRankFour G htc)).elim
  | Ly => exact (hexG (hres.ly G htc)).elim
  | Co3 => exact (hexG (hres.co3 G htc)).elim
  | Co2 => exact (hexG (hres.co2 G htc)).elim
  | HN => exact (hexG (hres.hn G htc)).elim
  | Th => exact (hexG (hres.th G htc)).elim
  | Co1 => exact (hex excludedIndex_Co1 e).elim
  | Fi22 => exact (hex excludedIndex_Fi22 e).elim
  | Fi23 => exact (hex excludedIndex_Fi23 e).elim
  | Fi24Prime => exact (hex excludedIndex_Fi24Prime e).elim
  | B => exact (hex PartOne.CTP.rankFourBabyMonster e).elim
  | M => exact (hex excludedIndex_M e).elim
  | M11 => exact (hnot (by simp)).elim
  | M12 => exact (hnot (by simp)).elim
  | M23 => exact (hnot (by simp)).elim
  | M24 => exact (hnot (by simp)).elim
  | J1 => exact (hnot (by simp)).elim
  | J2 => exact (hnot (by simp)).elim
  | HS => exact (hnot (by simp)).elim
  | He => exact (hnot (by simp)).elim
  | Ru => exact (hnot (by simp)).elim
  | J4 => exact (hnot (by simp)).elim

end Sporadic43

section Item43

theorem rank3II_4_3_of_narrow (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hres : TripleCoverSporadicResidual) : Item4_3 := by
  intro G _ _ hG hq h3
  have hS : SectionFourHyp (G ⧸ Subgroup.center G) := sectionFourHyp_quotient_center h41 hG hq
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have hnonab : ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := hq.2.2
  obtain ⟨i, ⟨e⟩⟩ := exists_index_of_sectionFourHyp hS
  have htc : IsThreeCenterCover G i.Group := ⟨hq, h3, ⟨e⟩⟩
  have hex : ∀ {j : CFSGIndex}, ExcludedIndex j → (G ⧸ Subgroup.center G ≃* j.Group) → False :=
    fun hj e' => SectionFourHyp.false_of_four_le_twoLocalOddRank hS (hj _ this hnonab e')
  have hexG : 4 ≤ CFSG.twoLocalOddRank G → False :=
    SectionFourHyp.false_of_four_le_twoLocalOddRank hG
  have hspin := PartOne.CTP.spinRankFour
  have hexc := CFSG.RankThree.PartTwo.Census.Exceptional.exceptionalRankFour
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hc : ∀ x y : (CFSGIndex.cyclic p hp).Group, x * y = y * x := fun x y => mul_comm x y
    exact hab (e.injective (by rw [map_mul, map_mul]; exact hc _ _))
  | alternating n hn =>
    rcases tripleCoverAlternating n G hn htc with rfl | rfl
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | sporadic s =>
    rcases item43_sporadic hres hG hS hnonab e htc with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  | lie d =>
    obtain ⟨d, hv⟩ := d
    have hd := tripleCoverLie_of_griess hGA ⟨d, hv⟩ G htc
    cases d with
    | A r q =>
      obtain ⟨h3r, h3q⟩ := hd
      have hr1 : 1 ≤ r :=
        ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
      rcases (show r = 2 ∨ 5 ≤ r by omega) with rfl | hr5
      · exact Or.inl ⟨q.p, q.exponent, ⟨q.prime_p⟩, q.exponent_pos, isoLThreePi_of_A2 hv h3q e⟩
      · refine (hex (excludedIndex_A_of_five_le r q hv hr5 ?_) e).elim
        by_contra hq
        push Not at hq
        have hc : q.card = 2 := by
          rw [PrimePower.card_def, hq.1, show q.exponent = 1 by have := q.exponent_pos; omega]
          norm_num
        rw [hc] at h3q
        omega
    | twistedA r q =>
      have hr2 : 2 ≤ r :=
        LieTypeIndex.two_le_of_twistedA_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1
      rcases hd with ⟨h3r, h3q⟩ | ⟨rfl, hq3⟩
      · rcases (show r = 2 ∨ 5 ≤ r by omega) with rfl | hr5
        · exact Or.inl ⟨q.p, q.exponent, ⟨q.prime_p⟩, q.exponent_pos,
            isoLThreePi_of_twistedA2 hv h3q e⟩
        · by_cases h62 : r = 5 ∧ q.p = 2 ∧ q.exponent = 1
          · exact (hexG (tripleCoverU62RankFour q (h62.1 ▸ hv) h62.2.1 h62.2.2 G (by
              obtain ⟨rfl, -, -⟩ := h62
              exact htc))).elim
          · exact (hex (excludedIndex_twistedA_of_five_le r q hv hr5 h62) e).elim
      · obtain ⟨hp3, hf1⟩ := eq_three_of_card_eq_three hq3
        obtain ⟨p, f, hp, hf⟩ := q
        obtain rfl : p = 3 := hp3
        obtain rfl : f = 1 := hf1
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨e.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 3 _ hv)⟩))))
    | B r q =>
      obtain ⟨rfl, hq3⟩ := hd
      obtain ⟨hp3, -⟩ := eq_three_of_card_eq_three hq3
      exact (hex (excludedIndex_of_four_le (hspin.typeB 3 q hv le_rfl (fun h => by omega)
        (fun h => by omega))) e).elim
    | G2 q =>
      obtain ⟨hp3, hf1⟩ := eq_three_of_card_eq_three hd
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e
          (chevalleyExceptionalModel_G2_three q hv hp3 hf1)))))
    | E6 q => exact (hex (excludedIndex_of_four_le (hexc.e6 q hv)) e).elim
    | twistedE6 q => exact (hex (excludedIndex_of_four_le (hexc.twistedE6 q hv)) e).elim
    | C r q => exact hd.elim
    | D r q => exact hd.elim
    | twistedD r q => exact hd.elim
    | E7 q => exact hd.elim
    | E8 q => exact hd.elim
    | F4 q => exact hd.elim
    | trialityD4 q => exact hd.elim
    | suzuki m => exact hd.elim
    | reeG2 m => exact hd.elim
    | reeF4 m => exact hd.elim
    | tits => exact hd.elim

end Item43

section Item46

theorem rank3II_4_6_of_narrow (h41 : Item4_1) (hGA : GriessMultipliersAllModels)
    (hres : TripleCoverSporadicResidual) (hcen : CoverCenterThreeRest) : Item4_6 :=
  rank3II_4_6_of h41 rank3II_4_2 (rank3II_4_3_of_narrow h41 hGA hres)
    (Inputs46.of_open coverSLThree46 (coverCenterThree_of_rest hcen) nineCoverU43RankFour
      (RankThree46Open.of_sporadic rankThree46Sporadic))

end Item46

end CFSG.RankThree.PartTwo.Sec4.Census
