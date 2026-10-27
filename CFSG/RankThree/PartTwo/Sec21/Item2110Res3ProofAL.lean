module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res3ProofCent
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.J4
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.RankThree.PartTwo.Sec8.Item83ProofDistinct

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def KF2110ALInID4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
    (∃ n : ℕ, 0 < n ∧ Even n ∧ ChevalleyExceptionalModel (lBar L) .trialityD4 2 n) →
    Nonempty (starOf A L ≃* DihedralGroup 6) →
    ∀ d ∈ A, d ≠ 1 → IsCentral218 L d → A ⊓ L ≤ iOf218 L d

namespace Item2110Res3Proof

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_dvd_card {P I L : Subgroup G} (hPL : P ≤ L) (hIL : I ≤ L)
    (hPN : P ≤ normalizer (I : Set G)) (hP3 : IsPGroup 3 P) {k : ℕ} (hk : 3 ^ k ∣ Nat.card I)
    (hk1 : ¬ 3 ^ (k + 1) ∣ Nat.card L) : P ≤ I := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hle
  have hprod := Sec6.card_sup_mul_card_inf hPN
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hP3
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (hP3.to_le (inf_le_left : P ⊓ I ≤ P))
  have hdvd : Nat.card (P ⊓ I : Subgroup G) ∣ Nat.card P := card_dvd_of_le inf_le_left
  have hne : Nat.card (P ⊓ I : Subgroup G) ≠ Nat.card P := by
    intro h
    apply hle
    have := eq_of_le_of_card_ge (inf_le_left : P ⊓ I ≤ P) h.symm.le
    rw [← this]
    exact inf_le_right
  rw [hi, hj] at hdvd hne
  have hij : i < j := by
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd
    rcases this.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ rfl) hne
  have hsup : Nat.card (P ⊔ I : Subgroup G) = 3 ^ (j - i) * Nat.card I := by
    rw [hi, hj] at hprod
    have h3i : 0 < 3 ^ i := by positivity
    apply Nat.eq_of_mul_eq_mul_right h3i
    rw [hprod, mul_assoc, mul_comm (Nat.card I), ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel hij.le]
  have hk1' : 3 ^ (k + 1) ∣ Nat.card (P ⊔ I : Subgroup G) := by
    rw [hsup, pow_succ, mul_comm (3 ^ k)]
    exact mul_dvd_mul (dvd_pow_self 3 (by omega)) hk
  exact hk1 (hk1'.trans (card_dvd_of_le (sup_le hPL hIL)))

theorem not_dvd_card_of_lBar {L : Subgroup G} {k : ℕ}
    (h : ¬ 3 ^ (k + 1) ∣ Nat.card (lBar L)) : ¬ 3 ^ (k + 1) ∣ Nat.card L := by
  intro hdvd
  apply h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)] at hdvd
  have hcop : Nat.Coprime (3 ^ (k + 1)) (Nat.card (aschbacherSolvableCore 3 ↥L)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      three_not_dvd_card_aschbacherSolvableCore)
  exact hcop.dvd_of_dvd_mul_right hdvd

omit [Finite G] in
theorem card_lBar_dvd (I : Subgroup G) : Nat.card (lBar I) ∣ Nat.card I := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥I)]
  exact dvd_mul_right _ _

omit [Finite G] in
theorem le_normalizer_iOf218 (L : Subgroup G) (d : G) :
    L ⊓ centralizer ({d} : Set G) ≤ normalizer (iOf218 L d : Set G) := by
  set X := L ⊓ centralizer ({d} : Set G)
  have h1 := le_normalizer_map (H := layer ↥X) X.subtype
  have htop : normalizer ((layer ↥X : Subgroup ↥X) : Set ↥X) = ⊤ := by
    have := LocalCores.layer_characteristic (G := ↥X)
    exact normalizer_eq_top_iff.mpr inferInstance
  rw [htop, ← MonoidHom.range_eq_map, range_subtype] at h1
  exact h1

theorem card_SL3 {n : ℕ} (hn : n ≠ 0) :
    Nat.card (SL3 n) = (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := Fintype.ofFinite (GaloisField 2 n)
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  have h1 := Matrix.card_SL_mul_card_units (n := Fin 3) (R := GaloisField 2 n)
  rw [Matrix.card_GL_field, Nat.card_units, Fin.prod_univ_three] at h1
  rw [← Nat.card_eq_fintype_card, hK] at h1
  set Q := 2 ^ n with hQ
  have hQ2 : 2 ≤ Q := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h1
  have hpos : 0 < Q - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hpos
  change Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) * (Q - 1) = _
  rw [h1]
  have e1 : Q ^ 3 - Q = Q * (Q ^ 2 - 1) := by
    rw [Nat.mul_sub, mul_one]
    ring_nf
  have e2 : Q ^ 3 - Q ^ 2 = Q ^ 2 * (Q - 1) := by
    rw [Nat.mul_sub, mul_one]
    ring_nf
  rw [e1, e2]
  ring

theorem ordG2_eq {Q : ℕ} (hQ : 1 ≤ Q) :
    CFSG.Open.ordG2 Q = Q ^ 3 * (Q ^ 3 + 1) * (Q ^ 3 * (Q ^ 3 - 1) * (Q ^ 2 - 1)) := by
  have h6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ
  have h3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ
  have h2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  rw [CFSG.Open.ordG2]
  zify [h6, h3, h2]
  ring

theorem not_dvd_ordG2 {n : ℕ} (hev : Even n) {k m : ℕ} (hm : ¬ 3 ∣ m)
    (hN : (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1) = 3 ^ k * m) :
    ¬ 3 ^ (k + 1) ∣ CFSG.Open.ordG2 (2 ^ n) := by
  have hQ : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [ordG2_eq hQ, hN]
  obtain ⟨r, hr⟩ := hev
  have hQ3 : (2 ^ n) % 3 = 1 := by
    rw [hr, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hQ3' : (2 ^ n) ^ 3 % 3 = 1 := by
    rw [Nat.pow_mod, hQ3]
  have hM : ¬ 3 ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1) := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, hQ3']
    norm_num
  intro hdvd
  rw [pow_succ, show (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1) * (3 ^ k * m) =
    3 ^ k * ((2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1) * m) by ring] at hdvd
  have h3 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 3 ^ k)).mp hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact hM h
  · exact hm h

theorem item2110ALInI_of
    (h211 : Item211) (h219 : Item219) (hD4 : KF2110ALInID4) :
    Item2110ALInI := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hcases⟩ := h219 G A E U c L hpair hL d hdA hd1 hdcen
  have hAe := hpair.mem_S.1.1
  have hAp : IsPGroup 3 A := fun z => ⟨1, Subtype.ext (by simpa using hAe.2 z z.2)⟩
  set I := iOf218 L d with hI
  have hALX : A ⊓ L ≤ L ⊓ centralizer ({d} : Set G) := by
    intro a ⟨haA, haL⟩
    refine ⟨haL, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨d, hdA⟩)
  have hPN : A ⊓ L ≤ normalizer (I : Set G) := hALX.trans (le_normalizer_iOf218 L d)
  have hIL : I ≤ L := (map_subtype_le _).trans inf_le_left
  have hP3 : IsPGroup 3 (A ⊓ L : Subgroup G) := hAp.to_le inf_le_left
  have key : ∀ k : ℕ, 3 ^ k ∣ Nat.card I → ¬ 3 ^ (k + 1) ∣ Nat.card L → A ⊓ L ≤ I :=
    fun k hk hk1 => le_of_dvd_card inf_le_right hIL hPN hP3 hk hk1
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  rcases hcases with ⟨⟨eHe⟩, hT⟩ | ⟨hM | hJ | hR, hT⟩ | ⟨⟨eJ4⟩, hc6, ⟨e⟩⟩ |
      ⟨n, hn, hev, hG | hD, ⟨eI⟩⟩
  ·
    refine key 3 ?_ ?_
    · rw [Item2113Proof.card_of_isTripleCover hT, nat_card_alternatingGroup, Nat.card_fin]
      decide
    · rw [Nat.card_congr eHe.toEquiv, CFSG.Sporadic.He.card_He]
      norm_num
  ·
    refine key 3 ((show 3 ^ 3 ∣ Nat.card (lBar I) by
      rw [Item2113Proof.card_of_isTripleCover hT, hA6]; norm_num).trans (card_lBar_dvd I))
      (not_dvd_card_of_lBar ?_)
    obtain ⟨e⟩ := hM
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  ·
    refine key 3 ((show 3 ^ 3 ∣ Nat.card (lBar I) by
      rw [Item2113Proof.card_of_isTripleCover hT, hA6]; norm_num).trans (card_lBar_dvd I))
      (not_dvd_card_of_lBar ?_)
    obtain ⟨e⟩ := hJ
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
    norm_num
  ·
    refine key 3 ((show 3 ^ 3 ∣ Nat.card (lBar I) by
      rw [Item2113Proof.card_of_isTripleCover hT, hA6]; norm_num).trans (card_lBar_dvd I))
      (not_dvd_card_of_lBar ?_)
    obtain ⟨e⟩ := hR
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ru.card_Ru]
    norm_num
  ·
    refine key 3 ?_ ?_
    · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥I), hc6,
        Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
      norm_num
    · rw [Nat.card_congr eJ4.toEquiv, CFSG.Sporadic.J4.card_J4]
      norm_num
  ·
    have hn0 : n ≠ 0 := by omega
    have hNpos : (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 - 1) * ((2 ^ n) ^ 2 - 1) ≠ 0 := by
      rw [← card_SL3 hn0]
      exact Nat.card_pos.ne'
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hNpos 3 (by norm_num)
    have hIcard : Nat.card (lBar I) = 3 ^ k * m := by
      rw [Nat.card_congr eI.toEquiv, card_SL3 hn0, hkm]
    refine key k ((show 3 ^ k ∣ Nat.card (lBar I) by
      rw [hIcard]; exact dvd_mul_right _ _).trans (card_lBar_dvd I)) (not_dvd_card_of_lBar ?_)
    have hc : Nat.card (lBar L) = CFSG.Open.ordG2 (2 ^ n) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG
    rw [hc]
    exact not_dvd_ordG2 hev hm hkm
  ·
    have hc : Nat.card (lBar L) = CFSG.Open.ordTrialityD4 (2 ^ n) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD
    have hv := Item218Proof.padicValNat_ordTrialityD4 (m := n) (by omega)
    rw [← hc] at hv
    have hval : ∀ {a r : ℕ}, Odd r → Nat.card (lBar L) = 2 ^ a * r → a ≠ n * 12 → False := by
      intro a r hr hX ha
      rw [hX, Sec8.Item83Proof.padicValNat_two_pow_mul_odd hr] at hv
      exact ha hv
    have hS : Nonempty (starOf A L ≃* DihedralGroup 6) := by
      rcases Item2113Res2Proof.starOf_cases_of_isList218 h211 hpair hL with
        ⟨he | he | he | he, -⟩ | ⟨-, hS⟩ | ⟨he, -⟩
      · obtain ⟨e⟩ := he
        exact (hval (a := 10) (r := 239085) (by decide)
          (by rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]; norm_num)
          (by omega)).elim
      · obtain ⟨e⟩ := he
        exact (hval (a := 10) (r := 3935925) (by decide)
          (by rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.He.card_He]; norm_num)
          (by omega)).elim
      · obtain ⟨e⟩ := he
        exact (hval (a := 14) (r := 8906625) (by decide)
          (by rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ru.card_Ru]; norm_num)
          (by omega)).elim
      · obtain ⟨e⟩ := he
        exact (hval (a := 21) (r := 41377816699065) (by decide)
          (by rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J4.card_J4]; norm_num)
          (by omega)).elim
      · exact hS
      · obtain ⟨e⟩ := he
        exact (hval (a := 7) (r := 4725) (by decide)
          (by rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]; norm_num)
          (by omega)).elim
    exact hD4 G A E U c L hpair ⟨n, hn, hev, hD⟩ hS d hdA hd1 hdcen

end Item2110Res3Proof

end CFSG.RankThree.PartTwo.Sec21
