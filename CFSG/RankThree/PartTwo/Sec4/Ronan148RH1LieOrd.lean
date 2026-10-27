module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Type
public import CFSG.HardMathSupport.Dickson.Bal207.OrthShapeIdx
public import CFSG.HardMathSupport.Dickson.Bal207.G28Shape
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Core

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG.Open Finset
open CFSG.HardMathSupport.Solomon.Coordinator (lieOrderBridge_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula add_one_dvd_sq_sub_one)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow IsL2EightIndex)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux (IsSmallTwistedIdx)
open CFSG.HardMathSupport.Dickson.Bal207 (SpCompType SpCompIdx ExcU62Type ExcU62CompIdx
  OrthCompType OrthCompIdx G28CompType)

section Orders

theorem two_pow_dvd_of_dvd_mul_odd {a m g : ℕ} (hg : Odd g) (h : 2 ^ a ∣ m * g) : 2 ^ a ∣ m :=
  (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hg)).dvd_of_dvd_mul_right h

theorem le_two_of_two_pow_dvd_sixty {a : ℕ} (h : 2 ^ a ∣ 60) : a ≤ 2 := by
  by_contra ha
  push Not at ha
  have h8 : 2 ^ 3 ∣ 2 ^ a := pow_dvd_pow 2 ha
  have := h8.trans h
  norm_num at this

theorem two_pow_dvd_pow_of_even {q : ℕ} (hq : Even q) (N : ℕ) : 2 ^ N ∣ q ^ N :=
  pow_dvd_pow_of_dvd (even_iff_two_dvd.mp hq) N

theorem odd_sub_one_of_even {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) : Odd (q - 1) := by
  obtain ⟨k, rfl⟩ := hq
  exact ⟨k - 1, by omega⟩

theorem orderBC_ne_sixty {n q : ℕ} (hn : 2 ≤ n) (hq : Even q) (hq2 : 2 ≤ q) : orderBC n q ≠ 60 := by
  intro h
  have hg : Nat.gcd 2 (q - 1) = 1 := Nat.coprime_two_left.mpr (odd_sub_one_of_even hq hq2)
  unfold orderBC at h
  rw [hg, Nat.div_one] at h
  have h1 : q ^ (n * n) ∣ 60 := h ▸ Dvd.intro _ rfl
  have h2 := le_two_of_two_pow_dvd_sixty ((two_pow_dvd_pow_of_even hq _).trans h1)
  nlinarith

theorem orderTwistedA_ne_sixty {n q : ℕ} (hn : 2 ≤ n) (hq : Even q) (hq2 : 2 ≤ q) :
    orderTwistedA n q ≠ 60 := by
  intro h
  have hmem : 2 ∈ Icc 2 (n + 1) := by simp; omega
  have hfac : q + 1 ∣ (fun i => if Even i then q ^ i - 1 else q ^ i + 1) 2 := by
    show q + 1 ∣ (if Even 2 then q ^ 2 - 1 else q ^ 2 + 1)
    simpa using add_one_dvd_sq_sub_one q (by omega)
  have hGd : Nat.gcd (n + 1) (q + 1) ∣ q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) :=
    Dvd.dvd.mul_left (((Nat.gcd_dvd_right _ _).trans hfac).trans
      (Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) hmem)) _
  have hmul : Nat.gcd (n + 1) (q + 1) * orderTwistedA n q = q ^ (n * (n + 1) / 2) *
      ∏ i ∈ Icc 2 (n + 1), (if Even i then q ^ i - 1 else q ^ i + 1) := Nat.mul_div_cancel' hGd
  rw [h] at hmul
  have hodd : Odd (Nat.gcd (n + 1) (q + 1)) :=
    Odd.of_dvd_nat (by obtain ⟨k, rfl⟩ := hq; exact ⟨k, by ring⟩) (Nat.gcd_dvd_right _ _)
  have h1 : q ^ (n * (n + 1) / 2) ∣ 60 * Nat.gcd (n + 1) (q + 1) := by
    rw [show 60 * Nat.gcd (n + 1) (q + 1) = Nat.gcd (n + 1) (q + 1) * 60 from mul_comm _ _, hmul]
    exact Dvd.intro _ rfl
  have h2 := le_two_of_two_pow_dvd_sixty
    (two_pow_dvd_of_dvd_mul_odd hodd ((two_pow_dvd_pow_of_even hq _).trans h1))
  have h3 : 3 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
  omega

theorem orderD_ne_sixty {n q : ℕ} (hn : 3 ≤ n) (hq : Even q) (hq2 : 2 ≤ q) : orderD n q ≠ 60 := by
  intro h
  have hodd : Odd (q ^ n - 1) := by
    have hqn : Even (q ^ n) := (Nat.even_pow' (by omega)).mpr hq
    have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    obtain ⟨k, hk⟩ := hqn
    exact ⟨k - 1, by omega⟩
  have hg : Nat.gcd 4 (q ^ n - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) |>.symm.symm
  unfold orderD at h
  rw [hg, Nat.div_one] at h
  have h1 : q ^ (n * (n - 1)) ∣ 60 := by
    rw [← h, mul_assoc]
    exact Dvd.intro _ rfl
  have h2 := le_two_of_two_pow_dvd_sixty ((two_pow_dvd_pow_of_even hq _).trans h1)
  have h3 : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  omega

theorem orderTwistedD_ne_sixty {n q : ℕ} (hn : 3 ≤ n) (hq : Even q) (hq2 : 2 ≤ q) :
    orderTwistedD n q ≠ 60 := by
  intro h
  have hodd : Odd (q ^ n + 1) := by
    have hqn : Even (q ^ n) := (Nat.even_pow' (by omega)).mpr hq
    exact hqn.add_one
  have hg : Nat.gcd 4 (q ^ n + 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) |>.symm.symm
  unfold orderTwistedD at h
  rw [hg, Nat.div_one] at h
  have h1 : q ^ (n * (n - 1)) ∣ 60 := by
    rw [← h, mul_assoc]
    exact Dvd.intro _ rfl
  have h2 := le_two_of_two_pow_dvd_sixty ((two_pow_dvd_pow_of_even hq _).trans h1)
  have h3 : 3 * 2 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  omega

theorem card_of_isTwoPow {q : TauCeti.PrimePower} {k : ℕ} (h : IsTwoPow q k) : q.card = 2 ^ k := by
  rw [TauCeti.PrimePower.card_def, h.1, h.2]

theorem even_card_of_isTwoPow {q : TauCeti.PrimePower} {k : ℕ} (h : IsTwoPow q k) (hk : 1 ≤ k) :
    Even q.card ∧ 2 ≤ q.card := by
  rw [card_of_isTwoPow h]
  refine ⟨(Nat.even_pow' (by omega)).mpr even_two, ?_⟩
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem even_card_of_two_or_eight {q : TauCeti.PrimePower} (h : IsTwoPow q 1 ∨ IsTwoPow q 3) :
    Even q.card ∧ 2 ≤ q.card := by
  rcases h with h | h
  · exact even_card_of_isTwoPow h le_rfl
  · exact even_card_of_isTwoPow h (by norm_num)

theorem orderA_one_eight_ne_sixty {q : TauCeti.PrimePower} (h : IsTwoPow q 3) :
    orderA 1 q.card ≠ 60 := by
  rw [card_of_isTwoPow h]
  decide

end Orders

section Catalogue


theorem not_isA5Type_of_lie {Q : Type} [Group Q] {d : TauCeti.ValidLieTypeIndex}
    (e : Q ≃* (TauCeti.CFSGIndex.lie d).Group) (hd : lieOrderFormula d.1 ≠ 60) : ¬ IsA5Type Q := by
  intro hA5
  have h60 := hA5.card
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [h60]; norm_num)
  exact hd ((lieOrderBridge_holds d Q ⟨e⟩).symm.trans h60)

theorem not_isA5Type_of_alt6 {Q : Type} [Group Q] (e : Q ≃* alternatingGroup (Fin 6)) :
    ¬ IsA5Type Q := by
  intro hA5
  have h := hA5.card
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin] at h
  revert h
  decide

theorem not_isA5Type_of_spCompType : ∀ (Q : Type) [Group Q], SpCompType Q → ¬ IsA5Type Q := by
  intro Q _ h
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  · exact not_isA5Type_of_alt6 e
  · refine not_isA5Type_of_lie e ?_
    cases d with
    | B s q =>
      obtain ⟨hq, hs, -⟩ := hd
      obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
      exact orderBC_ne_sixty hs hev h2
    | A r q =>
      obtain ⟨rfl, hq⟩ := hd
      exact orderA_one_eight_ne_sixty hq
    | twistedA r q =>
      obtain ⟨hq, hr, -⟩ := hd
      obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
      exact orderTwistedA_ne_sixty hr hev h2
    | _ => exact hd.elim

theorem not_isA5Type_of_excU62Type : ∀ (Q : Type) [Group Q], ExcU62Type Q → ¬ IsA5Type Q := by
  intro Q _ ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  refine not_isA5Type_of_lie e ?_
  cases d with
  | twistedA r q =>
    obtain ⟨hr, hq⟩ := hd
    obtain ⟨hev, h2⟩ := even_card_of_isTwoPow hq le_rfl
    exact orderTwistedA_ne_sixty (by omega) hev h2
  | A r q =>
    obtain ⟨rfl, hq⟩ := hd
    exact orderA_one_eight_ne_sixty hq
  | _ => exact hd.elim

theorem orderTwistedA_two_three_ne_sixty {q : TauCeti.PrimePower} (hp : q.p = 3)
    (he : q.exponent = 1) : orderTwistedA 2 q.card ≠ 60 := by
  rw [TauCeti.PrimePower.card_def, hp, he]
  decide

theorem not_isA5Type_of_orthCompType : ∀ (Q : Type) [Group Q], OrthCompType Q → ¬ IsA5Type Q := by
  intro Q _ ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  refine not_isA5Type_of_lie e ?_
  cases d with
  | D s q =>
    obtain ⟨hq, -, hs⟩ := hd
    obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
    exact orderD_ne_sixty (by omega) hev h2
  | twistedD s q =>
    obtain ⟨hq, -, hs⟩ := hd
    obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
    exact orderTwistedD_ne_sixty (by omega) hev h2
  | twistedA r q =>
    rcases hd with ⟨hq, hr, -⟩ | ⟨rfl, hp, he⟩
    · obtain ⟨hev, h2⟩ := even_card_of_two_or_eight hq
      exact orderTwistedA_ne_sixty hr hev h2
    · exact orderTwistedA_two_three_ne_sixty hp he
  | A r q =>
    obtain ⟨rfl, hq⟩ := hd
    exact orderA_one_eight_ne_sixty hq
  | _ => exact hd.elim

theorem not_isA5Type_of_g28CompType : ∀ (Q : Type) [Group Q], G28CompType Q → ¬ IsA5Type Q := by
  intro Q _ ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  refine not_isA5Type_of_lie e ?_
  rcases hd with hd | hd
  · cases d with
    | twistedA r q =>
      obtain ⟨rfl, ⟨hp, he⟩ | hq⟩ := hd
      · exact orderTwistedA_two_three_ne_sixty hp he
      · obtain ⟨hev, h2⟩ := even_card_of_isTwoPow hq (by norm_num)
        exact orderTwistedA_ne_sixty le_rfl hev h2
    | _ => exact hd.elim
  · cases d with
    | A r q =>
      obtain ⟨rfl, hq⟩ := hd
      exact orderA_one_eight_ne_sixty hq
    | _ => exact hd.elim

end Catalogue

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
