module

public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.Quasithin.Vol2.F134Orders
import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson

public section

namespace CFSG.Quasithin.F134

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.P134
open scoped MatrixGroups

theorem nonempty_mulEquiv_psl2 {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (h : StatedClassicalModel X .PSL 2 p f) : Nonempty (X ≃* PSL(2, GaloisField p f)) :=
  CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd h

theorem false_of_card_nine_of_center {X Y : Type*} [Group X] [Group Y] {Q : Subgroup X}
    (hQ : Nat.card Q = 9) (e : Q ≃* Y) (hY : Subgroup.center Y = ⊥) : False := by
  have : IsMulCommutative Q := isMulCommutative_of_card_nine hQ
  have hc : Subgroup.center Q = ⊥ := CFSG.Quasithin.F420.center_eq_bot_of_mulEquiv' e hY
  have htop : (⊤ : Subgroup Q) = ⊥ := Subgroup.center_eq_top.symm.trans hc
  have h1 : Nat.card Q = 1 := by
    rw [← Subgroup.card_top (G := Q), htop, Subgroup.card_bot]
  omega

theorem card_alternating_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem card_alternating_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem noElemNine_psl2
    {p f : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3) (hf : 1 ≤ f) :
    NoElemNine PSL(2, GaloisField p f) := by
  intro H hH hexp
  have hp9 : ∀ m : ℕ, p ^ m ∣ 9 → m = 0 := by
    intro m hm
    by_contra hm0
    have h1 : p ∣ 3 ^ 2 := (dvd_pow_self p hm0).trans (by simpa using hm)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1
      (hp.out.dvd_of_dvd_pow h1))
  rcases F6.dicksonPSL2_holds p f hf H with
      ⟨-, m, -, hm⟩ | ⟨hc, -⟩ | ⟨z, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, -, hPc, hQc, hQt, -, -⟩ | ⟨m, -, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩
  · have := hp9 m (by rw [← hm, hH])
    subst this
    rw [hH] at hm
    norm_num at hm
  · exact not_isCyclic_of_card_nine hH hexp hc
  · have := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card, hH] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_alternating_four, hH] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_perm_four, hH] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [card_alternating_five, hH] at this
    omega
  · have hHt : Nat.card H = t * p ^ m := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hQt, hPc]
    have hm0 := hp9 m (by rw [← hH, hHt]; exact Dvd.intro_left _ rfl)
    subst hm0
    have hPbot : P = ⊥ := Subgroup.card_eq_one.mp (by rw [hPc, pow_zero])
    subst hPbot
    have := hQc
    exact not_isCyclic_of_card_nine hH hexp
      (isCyclic_of_surjective (QuotientGroup.quotientBot.toMonoidHom)
        QuotientGroup.quotientBot.surjective)
  · exact false_of_card_nine_of_center hH e
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField p m))
  · exact false_of_card_nine_of_center hH e
      (CFSG.GorensteinWalter.pgl2_center_eq_bot (GaloisField p m))

theorem noElemNine_of_statedPSL_two
    {X : Type} [Group X] {p f : ℕ} (hp3 : p ≠ 3)
    (h : StatedClassicalModel X .PSL 2 p f) : NoElemNine X := by
  have : Fact p.Prime := ⟨h.1.1⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2 h
  exact NoElemNine.of_mulEquiv e (noElemNine_psl2 hp3 h.1.2.1)

theorem even_of_three_dvd_two_pow_sub_one {n : ℕ} (h : 3 ∣ 2 ^ n - 1) : Even n := by
  rcases Nat.even_or_odd n with hn | ⟨k, rfl⟩
  · exact hn
  · exfalso
    have hmod : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h1 : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
    have h0 := Nat.mod_eq_zero_of_dvd h
    generalize 2 ^ (2 * k + 1) = x at hmod h1 h0
    omega

theorem exists_prime_dvd_four_pow_sub_one {m : ℕ} (hm : 2 ≤ m) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ m * (2 ^ (2 * m) - 1) ∧ r ≠ 2 ∧ r ≠ 3 := by
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hfac : 2 ^ (2 * m) - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
    rw [mul_comm 2 m, pow_mul, sq_sub_one_eq]
  have hodd1 : ¬ 2 ∣ 2 ^ m - 1 := by
    intro h
    have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hodd2 : ¬ 2 ∣ 2 ^ m + 1 := by
    intro h
    have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hdvd1 : 2 ^ m - 1 ∣ 2 ^ m * (2 ^ (2 * m) - 1) :=
    Dvd.dvd.mul_left (hfac ▸ Dvd.intro _ rfl) _
  have hdvd2 : 2 ^ m + 1 ∣ 2 ^ m * (2 ^ (2 * m) - 1) :=
    Dvd.dvd.mul_left (hfac ▸ Dvd.intro_left _ rfl) _
  by_cases h3 : Nat.minFac (2 ^ m - 1) = 3
  · refine ⟨Nat.minFac (2 ^ m + 1), Nat.minFac_prime (by omega),
      (Nat.minFac_dvd _).trans hdvd2, fun h => hodd2 ?_, fun h => ?_⟩
    · have := Nat.minFac_dvd (2 ^ m + 1)
      rwa [h] at this
    have ha : 3 ∣ 2 ^ m - 1 := by
      have := Nat.minFac_dvd (2 ^ m - 1)
      rwa [h3] at this
    have hb : 3 ∣ 2 ^ m + 1 := by
      have := Nat.minFac_dvd (2 ^ m + 1)
      rwa [h] at this
    have := Nat.dvd_sub hb ha
    rw [show 2 ^ m + 1 - (2 ^ m - 1) = 2 by omega] at this
    omega
  · refine ⟨Nat.minFac (2 ^ m - 1), Nat.minFac_prime (by omega),
      (Nat.minFac_dvd _).trans hdvd1, fun h => hodd1 ?_, h3⟩
    have := Nat.minFac_dvd (2 ^ m - 1)
    rwa [h] at this

theorem card_psl2_two {m : ℕ} (hm : m ≠ 0) :
    Nat.card PSL(2, GaloisField 2 m) = 2 ^ m * (2 ^ (2 * m) - 1) :=
  CFSG.Quasithin.H13.NQCore.card_psl2_two_pow hm

theorem even_of_psl2_two
    {n : ℕ} (hn : 2 ≤ n) (H : Subgroup PSL(2, GaloisField 2 n))
    (h2 : 2 ^ n ∣ Nat.card H) (h3 : 3 ∣ Nat.card H)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = 3) : Even n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have h2' : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
  have h4 : 4 ∣ Nat.card H := (pow_dvd_pow 2 hn).trans h2
  have hev : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have hodd : ∀ z : ℕ, (z ∣ (2 ^ n + 1) / Nat.gcd 2 (2 ^ n - 1) ∨
      z ∣ (2 ^ n - 1) / Nat.gcd 2 (2 ^ n - 1)) → ¬ 2 ∣ z := by
    rintro z hz h2z
    rw [hgcd, Nat.div_one, Nat.div_one] at hz
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rcases hz with hz | hz
    · have := h2z.trans hz
      omega
    · have := h2z.trans hz
      omega
  have h5 : ¬ 5 ∣ Nat.card H := fun h => by
    rcases hprime 5 (by norm_num) h with h | h <;> omega
  rcases F6.dicksonPSL2_holds 2 n (by omega) H with
      ⟨-, m, -, hm⟩ | ⟨-, hz⟩ | ⟨z, hz, ⟨e⟩⟩ | ⟨hA4, -⟩ | ⟨h16, -⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, -, hPc, -, hQt, -, htq⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact absurd (hm ▸ h3) (not_three_dvd_two_pow m)
  · exact absurd ((dvd_pow_self 2 (by omega : n ≠ 0)).trans h2) (hodd _ hz)
  · have hc := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at hc
    rw [hc] at h4
    exact (hodd z hz (by omega)).elim
  · exact hA4.resolve_left (by norm_num)
  · exfalso
    have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have h2' : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
    have : 2 ∣ 2 ^ (2 * n) - 1 := (by norm_num : 2 ∣ 16).trans h16
    omega
  · exact absurd (by rw [Nat.card_congr e.toEquiv, card_alternating_five]; norm_num) h5
  · have hHt : Nat.card H = t * 2 ^ m := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hQt, hPc]
    rw [hHt] at h3
    have ht3 : 3 ∣ t := ((Nat.Prime.dvd_mul Nat.prime_three).1 h3).resolve_right
      (not_three_dvd_two_pow m)
    rw [hgcd, Nat.div_one] at htq
    exact even_of_three_dvd_two_pow_sub_one (ht3.trans htq)
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hm
      omega
    have hc := Nat.card_congr e.toEquiv
    rw [card_psl2_two hm0] at hc
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · have : m = 1 := by omega
      subst this
      rw [hc] at h4
      norm_num at h4
    · obtain ⟨r, hr, hrd, hr2, hr3⟩ := exists_prime_dvd_four_pow_sub_one hm2
      rcases hprime r hr (hc ▸ hrd) with h | h
      · exact absurd h hr2
      · exact absurd h hr3
  · exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hm
      omega
    have hc := Nat.card_congr e.toEquiv
    have hK : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
    rw [CFSG.GorensteinWalter.pgl2_card_formula, hK, ← pow_mul, mul_comm m 2] at hc
    rw [hc] at h2
    have hcop : Nat.Coprime (2 ^ n) (2 ^ (2 * m) - 1) := by
      refine Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr ?_))
      have h1 : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
      have h2' : 2 ∣ 2 ^ (2 * m) := dvd_pow_self 2 (by omega)
      omega
    have hle : n ≤ m :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hcop.dvd_of_dvd_mul_right h2)
    have := Nat.le_of_dvd (by omega) hm
    omega

theorem even_of_le_statedPSL_two_two
    {A : Type} [Group A] [Finite A] {L B U : Subgroup A} {n : ℕ}
    {y : A} (hL : StatedClassicalModel ↥L .PSL 2 2 n) (hUB : U ≤ B) (hBL : B ≤ L)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3) (hy : y ∈ B)
    (hy3 : orderOf y = 3) : Even n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hn1, -, h22, -⟩, -⟩ := id hL
  have hn : 2 ≤ n := by
    by_contra h
    have : n = 1 := by omega
    subst this
    exact h22 (by norm_num)
  have hcardL := CFSG.Quasithin.F420.card_of_statedPSL_two_two hL
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2 hL
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hU.2.1
  have hidx := (U.subgroupOf L).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv, hk, hcardL] at hidx
  have hcop : Nat.Coprime (2 ^ n) (U.subgroupOf L).index :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by
      have := hU.2.2
      omega)))
  have h2U : 2 ^ n ∣ Nat.card U := by
    rw [hk]
    exact hcop.dvd_of_dvd_mul_right (hidx ▸ Dvd.intro _ rfl)
  let H : Subgroup PSL(2, GaloisField 2 n) := (B.subgroupOf L).map e.toMonoidHom
  have hH : Nat.card H = Nat.card B := by
    rw [← Nat.card_congr ((B.subgroupOf L).equivMapOfInjective _ e.injective).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  refine even_of_psl2_two hn H ?_ ?_ ?_
  · rw [hH]
    exact h2U.trans (Subgroup.card_dvd_of_le hUB)
  · rw [hH, ← hy3]
    exact Subgroup.orderOf_dvd_natCard B hy
  · rw [hH]
    exact hB

end CFSG.Quasithin.F134
