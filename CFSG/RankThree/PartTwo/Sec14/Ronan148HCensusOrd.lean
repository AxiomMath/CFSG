module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusTools
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.Models.PGLOrders
public import CFSG.CGT.PushingUpLit.CGT6.SixFourOrders
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL52

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem N_factor : (1382446517760 : ℕ) = 2 ^ 9 * 3 ^ 5 * 5 * 7 ^ 3 * 11 * 19 * 31 := by norm_num

theorem prime_of_dvd_N {p : ℕ} (hp : p.Prime) (h : p ∣ 1382446517760) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 ∨ p = 31 := by
  rw [N_factor] at h
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
            · exact Or.inl (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl (hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h)))
          · exact Or.inr (Or.inr (Or.inl (hq 5 (by norm_num) h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) (hp.dvd_of_dvd_pow h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 11 (by norm_num) h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 19 (by norm_num) h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hq 31 (by norm_num) h))))))

theorem pow_dvd_N {p k : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p ^ k ∣ 1382446517760) :
    k ≤ 1 ∨ (p = 7 ∧ k ≤ 3) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Or.inl (Nat.zero_le 1)
  have hpN : p ∣ 1382446517760 := (dvd_pow_self p hk.ne').trans h
  rcases prime_of_dvd_N hp hpN with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · by_contra hc
    push Not at hc
    have : 5 ^ 2 ∣ 1382446517760 := (pow_dvd_pow 5 (by omega)).trans h
    norm_num at this
  · by_contra hc
    push Not at hc
    have : 7 ^ 4 ∣ 1382446517760 := (pow_dvd_pow 7 (by omega)).trans h
    norm_num at this
  · by_contra hc
    push Not at hc
    have : 11 ^ 2 ∣ 1382446517760 := (pow_dvd_pow 11 (by omega)).trans h
    norm_num at this
  · by_contra hc
    push Not at hc
    have : 19 ^ 2 ∣ 1382446517760 := (pow_dvd_pow 19 (by omega)).trans h
    norm_num at this
  · by_contra hc
    push Not at hc
    have : 31 ^ 2 ∣ 1382446517760 := (pow_dvd_pow 31 (by omega)).trans h
    norm_num at this

theorem three_pow_dvd_N {k : ℕ} (h : 3 ^ k ∣ 1382446517760) : k ≤ 5 := by
  by_contra hc
  push Not at hc
  have : 3 ^ 6 ∣ 1382446517760 := (pow_dvd_pow 3 (by omega)).trans h
  norm_num at this

theorem two_pow_dvd_N {k : ℕ} (h : 2 ^ k ∣ 1382446517760) : k ≤ 9 := by
  by_contra hc
  push Not at hc
  have : 2 ^ 10 ∣ 1382446517760 := (pow_dvd_pow 2 (by omega)).trans h
  norm_num at this

theorem coprime_pow_of_dvd {p k g m : ℕ} (hp : p.Prime) (hg : g ∣ m) (hpm : ¬ p ∣ m) :
    Nat.Coprime (p ^ k) g :=
  Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpm (h.trans hg))

theorem not_dvd_four {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : ¬ p ∣ 4 := fun h => by
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h)
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem eq_seven_of_cube_dvd {p e : ℕ} (hp : p.Prime) (hp3 : 3 < p) (he : 1 ≤ e)
    (h : (p ^ e) ^ 3 ∣ 1382446517760) : p = 7 ∧ e = 1 := by
  rw [← pow_mul] at h
  rcases pow_dvd_N hp hp3 h with h1 | ⟨h7, h3⟩
  · omega
  · exact ⟨h7, by omega⟩

theorem card_of_isExtOf_three {T S : Type} [Group T] [Group S] [Finite T]
    (h : IsExtOf T S (Multiplicative (ZMod 3))) : Nat.card T = Nat.card S * 3 := by
  obtain ⟨K, hKn, ⟨eK⟩, ⟨eS⟩⟩ := h
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, Nat.card_congr eS.toEquiv,
    Nat.card_congr eK.toEquiv, h3]

@[expose] def CardRow (Φ : (T : Type) → [Group T] → Prop) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Φ T → Nat.card T ∣ 1382446517760 → False

theorem cardRow_iso (S : Type) [Group S] (h : Nat.card S ∣ 1382446517760 → False) :
    CardRow (fun T _ => Nonempty (T ≃* S)) :=
  fun T _ _ ⟨e⟩ hT => h (by rw [← Nat.card_congr e.toEquiv]; exact hT)

section Card

theorem olRow_of_card (Φ : (T : Type) → [Group T] → Prop)
    (h : ∀ (T : Type) [Group T] [Finite T], Φ T → Nat.card T ∣ 1382446517760 → False) :
    OLRow Φ := by
  intro X _ _ P L Q hcfg hΦ
  apply h L hΦ
  rw [← card_X hcfg.triple]
  exact Subgroup.card_subgroup_dvd_card L

theorem cardRow_three_Sp (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    CardRow (fun T _ => Nonempty (T ≃* projSp 2 (GaloisField p 1))) :=
  cardRow_iso _ fun hT => by
    have hp : p.Prime := Fact.out
    have hK : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
    have h2 : (2 : GaloisField p 1) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : GaloisField p 1) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff (GaloisField p 1) p] at h'
      have := Nat.le_of_dvd (by norm_num) h'
      omega
    have hc := Sec11.KSListsProof.card_projSp_two_mul (GaloisField p 1) h2
    rw [hK] at hc
    have h4 : p ^ 4 ∣ Nat.card (projSp 2 (GaloisField p 1)) := by
      have h' : p ^ 4 ∣ Nat.card (projSp 2 (GaloisField p 1)) * 2 := by
        rw [hc]; exact dvd_mul_right _ _
      exact (coprime_pow_of_dvd hp (dvd_refl 2) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h; omega)).dvd_of_dvd_mul_right h'
    rcases pow_dvd_N hp hp3 (h4.trans hT) with h | ⟨-, h⟩ <;> omega

theorem olRow_three_Sp (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    OLRow (fun T _ => Nonempty (T ≃* projSp 2 (GaloisField p 1))) :=
  olRow_of_card _ (cardRow_three_Sp p hp3)

theorem cardRow_three_SL (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    CardRow (fun T _ => Nonempty (T ≃* projSL 4 (GaloisField p 1))) :=
  cardRow_iso _ fun hT => by
    have hp : p.Prime := Fact.out
    have hK : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
    have hc := Sec11.KSListsProof.card_projSL_four_mul (GaloisField p 1)
    rw [hK] at hc
    have h6 : p ^ 6 ∣ Nat.card (projSL 4 (GaloisField p 1)) := by
      have h' : p ^ 6 ∣ Nat.card (projSL 4 (GaloisField p 1)) * Nat.gcd 4 (p - 1) := by
        rw [hc]; exact dvd_mul_right _ _
      exact (coprime_pow_of_dvd hp (Nat.gcd_dvd_left 4 (p - 1)) (not_dvd_four hp hp3)).dvd_of_dvd_mul_right h'
    rcases pow_dvd_N hp hp3 (h6.trans hT) with h | ⟨-, h⟩ <;> omega

theorem olRow_three_SL (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    OLRow (fun T _ => Nonempty (T ≃* projSL 4 (GaloisField p 1))) :=
  olRow_of_card _ (cardRow_three_SL p hp3)

theorem cardRow_three_SU (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    CardRow (fun T _ => Nonempty (T ≃* projSU 4 p 1)) :=
  cardRow_iso _ fun hT => by
    have hp : p.Prime := Fact.out
    have hc := Sec11.KSListsProof.card_projSU_four_mul p 1 le_rfl
    rw [pow_one] at hc
    have h6 : p ^ 6 ∣ Nat.card (projSU 4 p 1) := by
      have h' : p ^ 6 ∣ Nat.card (projSU 4 p 1) * Nat.gcd 4 (p + 1) := by
        rw [hc]; exact dvd_mul_right _ _
      exact (coprime_pow_of_dvd hp (Nat.gcd_dvd_left 4 (p + 1)) (not_dvd_four hp hp3)).dvd_of_dvd_mul_right h'
    rcases pow_dvd_N hp hp3 (h6.trans hT) with h | ⟨-, h⟩ <;> omega

theorem olRow_three_SU (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    OLRow (fun T _ => Nonempty (T ≃* projSU 4 p 1)) :=
  olRow_of_card _ (cardRow_three_SU p hp3)

theorem cardRow_two_SU (p e : ℕ) [Fact p.Prime] (hp3 : 3 < p) (he : 1 ≤ e) :
    CardRow (fun T _ => Nonempty (T ≃* projSU 3 p e)) :=
  cardRow_iso _ fun hT => by
    have hp : p.Prime := Fact.out
    have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e + 1)) := by
      rw [← pow_mul]
      exact coprime_pow_of_dvd hp (Nat.gcd_dvd_left 3 _) (fun h => by
        have := Nat.le_of_dvd (by norm_num) h; omega)
    have h3 : (p ^ e) ^ 3 ∣ Nat.card (projSU 3 p e) := by
      have h' : (p ^ e) ^ 3 ∣ Nat.card (projSU 3 p e) * Nat.gcd 3 (p ^ e + 1) := by
        rw [hc]; exact dvd_mul_right _ _
      exact hcop.dvd_of_dvd_mul_right h'
    obtain ⟨rfl, rfl⟩ := eq_seven_of_cube_dvd hp hp3 he (h3.trans hT)
    norm_num at hc
    have h43 : 43 ∣ Nat.card (projSU 3 7 1) := by rw [hc]; norm_num
    have := h43.trans hT
    norm_num at this

theorem olRow_two_SU (p e : ℕ) [Fact p.Prime] (hp3 : 3 < p) (he : 1 ≤ e) :
    OLRow (fun T _ => Nonempty (T ≃* projSU 3 p e)) :=
  olRow_of_card _ (cardRow_two_SU p e hp3 he)

theorem cardRow_seven_SL52 : CardRow (fun T _ => Nonempty (T ≃* projSL 5 (GaloisField 2 1))) :=
  cardRow_iso _ fun hT => by
    have hc : Nat.card (projSL 5 (GaloisField 2 1)) = 9999360 := by
      rw [← Nat.card_congr (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.slEquivProjSL
        (by norm_num : 1 ≤ 5)).toEquiv]
      exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L52.card_SL5
    rw [hc] at hT
    norm_num at hT

theorem olRow_seven_SL52 : OLRow (fun T _ => Nonempty (T ≃* projSL 5 (GaloisField 2 1))) :=
  olRow_of_card _ (cardRow_seven_SL52)

theorem cardRow_seven_SU54 : CardRow (fun T _ => Nonempty (T ≃* projSU 5 2 2)) :=
  cardRow_iso _ fun hT => by
    rw [CFSG.PGLModel.card_projSU_five_four] at hT
    norm_num at hT

theorem olRow_seven_SU54 : OLRow (fun T _ => Nonempty (T ≃* projSU 5 2 2)) :=
  olRow_of_card _ (cardRow_seven_SU54)

theorem cardRow_eight_SL3 (e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    CardRow (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField 3 e))) :=
  cardRow_iso _ fun hT => by
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 3 e)
    rw [GaloisField.card 3 e (by omega)] at hc
    interval_cases e
    · norm_num at hc
      rw [hc] at hT
      norm_num at hT
    · norm_num at hc
      rw [hc] at hT
      norm_num at hT

theorem olRow_eight_SL3 (e : ℕ) (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    OLRow (fun T _ => Nonempty (T ≃* projSL 3 (GaloisField 3 e))) :=
  olRow_of_card _ (cardRow_eight_SL3 e he1 he2)

theorem cardRow_eight_SU3_nine : CardRow (fun T _ => Nonempty (T ≃* projSU 3 3 2)) :=
  cardRow_iso _ fun hT => by
    have hc := KFacts.KS14.card_projSU_three_mul_gcd 3 2 (by norm_num)
    norm_num at hc
    rw [hc] at hT
    norm_num at hT

theorem olRow_eight_SU3_nine : OLRow (fun T _ => Nonempty (T ≃* projSU 3 3 2)) :=
  olRow_of_card _ (cardRow_eight_SU3_nine)

theorem cardRow_eight_SL43 : CardRow (fun T _ => Nonempty (T ≃* projSL 4 (GaloisField 3 1))) :=
  cardRow_iso _ fun hT => by
    have hc := Sec11.KSListsProof.card_projSL_four_mul (GaloisField 3 1)
    rw [GaloisField.card 3 1 one_ne_zero] at hc
    norm_num at hc
    have hc' : Nat.card (projSL 4 (GaloisField 3 1)) = 6065280 := by omega
    rw [hc'] at hT
    norm_num at hT

theorem olRow_eight_SL43 : OLRow (fun T _ => Nonempty (T ≃* projSL 4 (GaloisField 3 1))) :=
  olRow_of_card _ (cardRow_eight_SL43)

section M23

theorem cardRow_spor_M23 :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M23)) :=
  cardRow_iso _ fun hT => by
    change Nat.card ↥Blueprint.NativeSporadic.M23 ∣ _ at hT
    rw [CFSG.CGT.PushingUpLit.CGT6.card_nativeM23] at hT
    norm_num at hT

theorem olRow_spor_M23 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M23)) :=
  olRow_of_card _ cardRow_spor_M23

end M23

theorem cardRow_spor_M24 :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M24)) :=
  cardRow_iso _ fun hT => by
    rw [show Blueprint.NativeSporadic.Carrier .M24 = Blueprint.NativeSporadic.M24 from rfl,
      CFSG.Sporadic.Mathieu.card_M24] at hT
    norm_num at hT

theorem olRow_spor_M24 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M24)) :=
  olRow_of_card _ cardRow_spor_M24

theorem cardRow_spor_J2 :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .J2)) :=
  cardRow_iso _ fun hT => by
    rw [show Blueprint.NativeSporadic.Carrier .J2 = Blueprint.NativeSporadic.J2 from rfl,
      CFSG.Sporadic.J2.card_J2] at hT
    norm_num at hT

theorem olRow_spor_J2 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .J2)) :=
  olRow_of_card _ cardRow_spor_J2

theorem cardRow_spor_J3 :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .J3)) :=
  cardRow_iso _ fun hT => by
    rw [show Blueprint.NativeSporadic.Carrier .J3 = Blueprint.NativeSporadic.J3 from rfl,
      CFSG.Sporadic.J3.card_J3] at hT
    norm_num at hT

theorem olRow_spor_J3 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .J3)) :=
  olRow_of_card _ cardRow_spor_J3

theorem cardRow_spor_J4 :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .J4)) :=
  cardRow_iso _ fun hT => by
    rw [show Blueprint.NativeSporadic.Carrier .J4 = Blueprint.NativeSporadic.J4 from rfl,
      CFSG.Sporadic.J4.card_J4] at hT
    norm_num at hT

theorem olRow_spor_J4 :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .J4)) :=
  olRow_of_card _ cardRow_spor_J4

theorem cardRow_spor_McL :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .McL)) :=
  cardRow_iso _ fun hT => by
    rw [show Blueprint.NativeSporadic.Carrier .McL = Blueprint.NativeSporadic.McL from rfl,
      CFSG.Sporadic.McL.card_McL] at hT
    norm_num at hT

theorem olRow_spor_McL :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .McL)) :=
  olRow_of_card _ cardRow_spor_McL

theorem cardRow_spor_HS :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .HS)) :=
  cardRow_iso _ fun hT => by
    rw [show Blueprint.NativeSporadic.Carrier .HS = Blueprint.NativeSporadic.HS from rfl,
      CFSG.Sporadic.HS.card_HS] at hT
    norm_num at hT

theorem olRow_spor_HS :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .HS)) :=
  olRow_of_card _ cardRow_spor_HS

theorem cardRow_spor_He :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .He)) :=
  cardRow_iso _ fun hT => by
    rw [show Blueprint.NativeSporadic.Carrier .He = Blueprint.NativeSporadic.He from rfl,
      CFSG.Sporadic.He.card_He] at hT
    norm_num at hT

theorem olRow_spor_He :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .He)) :=
  olRow_of_card _ cardRow_spor_He

theorem cardRow_spor_Ru :
    CardRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .Ru)) :=
  cardRow_iso _ fun hT => by
    rw [show Blueprint.NativeSporadic.Carrier .Ru = Blueprint.NativeSporadic.Ru from rfl,
      CFSG.Sporadic.Ru.card_Ru] at hT
    norm_num at hT

theorem olRow_spor_Ru :
    OLRow (fun T _ => Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .Ru)) :=
  olRow_of_card _ cardRow_spor_Ru

theorem cardRow_cover_J3 :
    CardRow (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier .J3) (Multiplicative (ZMod 3))) :=
  fun T _ _ hT hd => by
    rw [card_of_isExtOf_three hT,
      show Blueprint.NativeSporadic.Carrier .J3 = Blueprint.NativeSporadic.J3 from rfl,
      CFSG.Sporadic.J3.card_J3] at hd
    norm_num at hd

theorem olRow_cover_J3 :
    OLRow (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier .J3) (Multiplicative (ZMod 3))) :=
  olRow_of_card _ cardRow_cover_J3

theorem cardRow_cover_McL :
    CardRow (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier .McL) (Multiplicative (ZMod 3))) :=
  fun T _ _ hT hd => by
    rw [card_of_isExtOf_three hT,
      show Blueprint.NativeSporadic.Carrier .McL = Blueprint.NativeSporadic.McL from rfl,
      CFSG.Sporadic.McL.card_McL] at hd
    norm_num at hd

theorem olRow_cover_McL :
    OLRow (fun T _ => IsExtOf T (Blueprint.NativeSporadic.Carrier .McL) (Multiplicative (ZMod 3))) :=
  olRow_of_card _ cardRow_cover_McL

end Card

section G2

theorem cardRow_three_G2 (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    CardRow (fun T _ => Blueprint.ChevalleyExceptionalModel T .G2 p 1) := by
  intro T _ _ hT hd
  have hp : p.Prime := Fact.out
  have hc := CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two
    (t := .G2) (by omega) hT
  simp only [pow_one] at hc
  have h6 : p ^ 6 ∣ Nat.card T := by
    rw [hc, CFSG.Open.ordG2, mul_assoc]; exact dvd_mul_right _ _
  rcases pow_dvd_N hp hp3 (h6.trans hd) with h | ⟨-, h⟩ <;> omega

theorem olRow_three_G2 (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) :
    OLRow (fun T _ => Blueprint.ChevalleyExceptionalModel T .G2 p 1) :=
  olRow_of_card _ (cardRow_three_G2 p hp3)

theorem cardRow_eight_cover : CardRow (fun T _ => Nat.card (Subgroup.center T) ≤ 3 ∧
    (Blueprint.ChevalleyExceptionalModel (T ⧸ Subgroup.center T) .G2 3 1 ∨
      Nonempty (T ⧸ Subgroup.center T ≃* projSU 4 3 1))) := by
  intro T _ _ ⟨_, hT⟩ hd
  have h6 : 3 ^ 6 ∣ Nat.card (T ⧸ Subgroup.center T) := by
    rcases hT with hT | hT
    · have hc := CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two
        (t := .G2) (by norm_num) hT
      rw [hc, CFSG.Open.ordG2, mul_assoc]
      exact dvd_mul_right _ _
    · obtain ⟨e⟩ := hT
      rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSU_four_three]
      norm_num
  have h6' : 3 ^ 6 ∣ Nat.card T := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center T)]
    exact h6.mul_right _
  have := three_pow_dvd_N (h6'.trans hd)
  omega

theorem olRow_eight_cover : OLRow (fun T _ => Nat.card (Subgroup.center T) ≤ 3 ∧
    (Blueprint.ChevalleyExceptionalModel (T ⧸ Subgroup.center T) .G2 3 1 ∨
      Nonempty (T ⧸ Subgroup.center T ≃* projSU 4 3 1))) :=
  olRow_of_card _ (cardRow_eight_cover)

end G2

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
