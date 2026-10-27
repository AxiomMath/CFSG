module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a
public import CFSG.Quasithin.Background.D216Restrict
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16c34_card_mulAut_dvd_168 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk W ≤ 3) : Nat.card (MulAut W) ∣ 168 := by
  have hcardW : Nat.card W = 2 ^ rk W :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  have h2 : ∀ e : W, e * e = 1 := fun e => by rw [← pow_two]; exact hW e
  have hAut : Nat.card (MulAut W) = ∏ i : Fin (rk W), (2 ^ rk W - 2 ^ (i : ℕ)) :=
    CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two h2 (rk W) hcardW
  rw [hAut]
  generalize rk W = n at hrk ⊢
  interval_cases n <;> decide

theorem s16c34_pRank_le_one {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hrk : rk W ≤ 3) {X : Subgroup (MulAut W)} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥X) ≤ 1 := by
  have hdvdX : Nat.card X ∣ 168 :=
    (Subgroup.card_subgroup_dvd_card X).trans (s16c34_card_mulAut_dvd_168 hW hrk)
  have hcop : Nat.Coprime (p ^ 2) 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow 2 3
  have hnot : ¬ p ^ 2 ∣ 21 := by
    rintro h
    have hpp : p ∣ p ^ 2 := by rw [pow_two]; exact dvd_mul_right p p
    have hp_dvd : p ∣ 21 := hpp.trans h
    have hp_le : p ≤ 21 := Nat.le_of_dvd (by norm_num) hp_dvd
    have hp2' : 2 ≤ p := hp.two_le
    interval_cases p <;> norm_num at h
  by_contra hgt
  push Not at hgt
  have hp2dvd : p ^ 2 ∣ Nat.card X := by
    have hpp := CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp
      (⊤ : Subgroup ↥X)
    rw [Subgroup.card_top] at hpp
    exact (pow_dvd_pow p (by omega : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥X))).trans hpp
  have h168 : p ^ 2 ∣ 8 * 21 := by
    rw [show (8 : ℕ) * 21 = 168 by norm_num]
    exact hp2dvd.trans hdvdX
  exact hnot (hcop.dvd_of_dvd_mul_left h168)

theorem s16c34_inducesTransvection_of_involution {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk W ≤ 3) {a : MulAut W} (ha : orderOf a = 2) :
    InducesTransvection a (⊤ : Subgroup W) := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hna : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha
    exact absurd ha (by norm_num)
  refine ⟨fun u => Iff.rfl, ?_⟩
  have hle : commSub (⊤ : Subgroup W) (Subgroup.zpowers a) ≤
      (⊤ : Subgroup W) ⊓ fixV (Subgroup.zpowers a) :=
    commSub_zpowers_le_inf_fixV hW ha2 (fun _ _ _ _ => Subgroup.mem_top _)
  have hsum := rk_commSub_add_rk_inf_fixV (g := a) (W := (⊤ : Subgroup W))
    (fun _ _ _ _ => Subgroup.mem_top _)
  have h1 := rk_mono hle
  have h0 : rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers a)) ≠ 0 := by
    intro h0
    have hbot := (rk_eq_zero_iff hW).1 h0
    have hfix := commSub_eq_bot_iff.1 hbot
    apply hna
    ext w
    exact (mem_fixV_zpowers_iff_apply.1 (hfix (Subgroup.mem_top w)))
  rw [rk_top] at hsum
  omega

theorem s16c34_inducesTransvection_of_resHom {W : Type} [CommGroup W] {U : Subgroup W}
    {φ : MulAut W} (hφ : φ ∈ stabSub U)
    (h : InducesTransvection (resHom U ⟨φ, hφ⟩) (⊤ : Subgroup ↥U)) :
    InducesTransvection φ U := by
  refine ⟨hφ, ?_⟩
  have h1 := commSub_eq_map_commV (U := U) (A := Subgroup.zpowers φ)
    ((Subgroup.zpowers_le).2 hφ)
  rw [s15_Three_autSub_zpowers hφ] at h1
  have h2 := h.2
  rw [← commV_eq_commSub] at h2
  rw [h1]
  unfold rk at h2 ⊢
  rwa [Subgroup.card_map_of_injective U.subtype_injective]

theorem s16c34_not_quasisimple_of_odd_card_dvd_168 {X : Type*} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (hd : Nat.card X ∣ 168) (hodd : Odd (Nat.card X)) :
    False := by
  haveI : Nontrivial X := by
    obtain ⟨-, hs⟩ := hq
    haveI := hs.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  have hcop8 : Nat.Coprime (Nat.card X) 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact (Nat.coprime_two_right.mpr hodd).pow_right 3
  have hd21 : Nat.card X ∣ 3 ^ 1 * 7 ^ 1 := by
    have hdvd' : Nat.card X ∣ 8 * 21 := by
      rwa [show (8 : ℕ) * 21 = 168 by norm_num]
    simpa using hcop8.dvd_of_dvd_mul_left hdvd'
  have hsolv : Group.IsSolvable X :=
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_three
      (by norm_num : Nat.Prime 7) hd21
  exact Group.IsPerfect.not_isSolvable X hsolv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
