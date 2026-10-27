module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

theorem mul_sub_one_add_one_lt_pow {Q r : ℕ} (hQ : 2 ≤ Q) (hr : 2 ≤ r) :
    r * (Q - 1) + 1 < Q ^ r := by
  induction r, hr using Nat.le_induction with
  | base =>
    have : 2 * (Q - 1) + 1 = 2 * Q - 1 := by omega
    rw [this, sq]
    have : 2 * Q ≤ Q * Q := Nat.mul_le_mul_right Q hQ
    omega
  | succ r hr ih =>
    have h1 : (r + 1) * (Q - 1) + 1 = (r * (Q - 1) + 1) + (Q - 1) := by ring
    have h2 : Q ^ (r + 1) = Q ^ r * Q := pow_succ Q r
    have h3 : 1 ≤ Q ^ r := Nat.one_le_pow _ _ (by omega)
    have h4 : Q ^ r * Q = Q ^ r + Q ^ r * (Q - 1) := by
      rw [Nat.mul_sub_one]
      have : Q ^ r ≤ Q ^ r * Q := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have h5 : Q - 1 ≤ Q ^ r * (Q - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega

theorem eq_one_of_three_mul_dvd {Q r k m : ℕ} (hQ : 2 ≤ Q) (hr : 1 ≤ r) (hm : ¬ 3 ∣ m)
    (hq : Q ^ r - 1 = 3 ^ k * m) (hdvd : 3 * m ∣ Q - 1) : r = 1 := by
  by_contra hr1
  have hr2 : 2 ≤ r := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h1 : 1 < Q ^ r := Nat.one_lt_pow (by omega) (by omega)
    rw [mul_zero] at hq
    omega
  have hQ1 : Q - 1 ≠ 0 := by omega
  have hmQ : m ∣ Q - 1 := dvd_trans (dvd_mul_left m 3) hdvd
  have h3Q : 3 ∣ Q - 1 := dvd_trans (dvd_mul_right 3 m) hdvd
  have hQdvd : Q - 1 ∣ Q ^ r - 1 := by
    simpa [one_pow] using Nat.sub_dvd_pow_sub_pow (x := Q) (y := 1) (n := r)
  obtain ⟨j, hj⟩ := hmQ
  have hj3 : j ∣ 3 ^ k := by
    rw [hq, hj, mul_comm m j] at hQdvd
    exact (Nat.mul_dvd_mul_iff_right (Nat.pos_of_ne_zero hm0)).mp hQdvd
  obtain ⟨v, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hj3
  have hval : padicValNat 3 (Q ^ r - 1 ^ r) = padicValNat 3 (Q - 1) + padicValNat 3 r := by
    refine padicValNat.pow_sub_pow (by decide : Odd 3) (by omega) (by simpa using h3Q) ?_
      (by omega)
    intro h3
    have : 3 ∣ Q - (Q - 1) := Nat.dvd_sub h3 h3Q
    rw [show Q - (Q - 1) = 1 by omega] at this
    exact absurd this (by norm_num)
  have hvm : padicValNat 3 m = 0 := padicValNat.eq_zero_of_not_dvd hm
  have hk : padicValNat 3 (3 ^ k * m) = k := by
    rw [padicValNat.mul (by positivity) hm0, padicValNat.prime_pow, hvm, add_zero]
  have hv : padicValNat 3 (m * 3 ^ v) = v := by
    rw [padicValNat.mul hm0 (by positivity), padicValNat.prime_pow, hvm, zero_add]
  rw [one_pow, hq, hk, hj, hv] at hval
  have hpow : 3 ^ padicValNat 3 r ≤ r := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have heq : Q ^ r - 1 = 3 ^ padicValNat 3 r * (Q - 1) := by
    rw [hq, hj, hval, pow_add]
    ring
  have hle : Q ^ r - 1 ≤ r * (Q - 1) := by
    rw [heq]
    exact Nat.mul_le_mul_right _ hpow
  have hlt := mul_sub_one_add_one_lt_pow hQ hr2
  omega

variable {F : Type*} [Field F]

@[expose] def muM (F : Type*) [Field F] : Set F :=
  {x | x ^ ordCompl[3] (Nat.card F - 1) = 1}

theorem mem_muM {x : F} : x ∈ muM F ↔ x ^ ordCompl[3] (Nat.card F - 1) = 1 := Iff.rfl

theorem muM_mul {x y : F} (hx : x ∈ muM F) (hy : y ∈ muM F) : x * y ∈ muM F := by
  rw [mem_muM] at *
  rw [mul_pow, hx, hy, one_mul]

theorem muM_inv {x : F} (hx : x ∈ muM F) : x⁻¹ ∈ muM F := by
  rw [mem_muM] at *
  rw [inv_pow, hx, inv_one]

theorem one_mem_muM : (1 : F) ∈ muM F := by
  rw [mem_muM, one_pow]

theorem ne_zero_of_mem_muM [Finite F] {x : F} (hx : x ∈ muM F) : x ≠ 0 := by
  rintro rfl
  rw [mem_muM, zero_pow] at hx
  · exact zero_ne_one hx
  · have : 1 < Nat.card F := Finite.one_lt_card
    exact (Nat.ordCompl_pos 3 (by omega)).ne'

theorem subring_closure_muM_eq_top [Finite F] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    Subring.closure (muM F ∪ {ω}) = ⊤ := by
  classical
  have := Fintype.ofFinite F
  set q := Nat.card F with hqdef
  have hq1 : 1 < q := Finite.one_lt_card
  set m := ordCompl[3] (q - 1) with hmdef
  set k := (q - 1).factorization 3 with hkdef
  have hqkm : 3 ^ k * m = q - 1 := Nat.ordProj_mul_ordCompl_eq_self (q - 1) 3
  have hm3 : ¬ 3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three (by omega)
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  set A := Subring.closure (muM F ∪ {ω}) with hA
  have hinv : ∀ x ∈ A, x⁻¹ ∈ A := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact A.zero_mem
    · have h1 : x ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
      have h2 : x⁻¹ = x ^ (Fintype.card F - 2) := by
        have hc : 2 ≤ Fintype.card F := by
          rw [← Nat.card_eq_fintype_card]
          omega
        rw [inv_eq_of_mul_eq_one_right]
        rw [← pow_succ', show Fintype.card F - 2 + 1 = Fintype.card F - 1 by omega, h1]
      rw [h2]
      exact A.pow_mem hx _
  set F₀ : Subfield F :=
    { A with
      inv_mem' := fun {x} hx => hinv x hx } with hF₀
  have hmemF₀ : ∀ x, x ∈ F₀ ↔ x ∈ A := fun x => Iff.rfl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgo : orderOf g = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  have hk0 : 3 ^ k ≠ 0 := by positivity
  have hgk : orderOf (g ^ 3 ^ k) = m := by
    rw [orderOf_pow_of_dvd hk0 (by rw [hgo, ← hqkm]; exact dvd_mul_right _ _), hgo, ← hqkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  set ωu : Fˣ := Units.mk0 ω hω0 with hωu
  have hωu3 : orderOf ωu = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hω3, Units.val_one])
    · intro h
      apply hω1
      have := congrArg Units.val h
      rwa [Units.val_mk0, Units.val_one] at this
  have hcop : Nat.Coprime m 3 :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3))
  have hη : orderOf (g ^ 3 ^ k * ωu) = 3 * m := by
    rw [(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hgk, hωu3]; exact hcop),
      hgk, hωu3, mul_comm]
  have hgkM : ((g ^ 3 ^ k : Fˣ) : F) ∈ muM F := by
    rw [mem_muM, ← hqdef, ← hmdef, ← Units.val_pow_eq_pow_val, ← hgk, pow_orderOf_eq_one,
      Units.val_one]
  have hηA : ((g ^ 3 ^ k * ωu : Fˣ) : F) ∈ F₀ := by
    rw [hmemF₀, Units.val_mul]
    refine A.mul_mem (Subring.subset_closure (Or.inl hgkM)) ?_
    rw [hωu, Units.val_mk0]
    exact Subring.subset_closure (Or.inr rfl)
  have := Fintype.ofFinite F₀
  set Q := Fintype.card F₀ with hQdef
  have hdvd : 3 * m ∣ Q - 1 := by
    rw [← hη]
    refine orderOf_dvd_of_pow_eq_one (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨_, hηA⟩ : F₀) (by
      intro h
      have := congrArg Subtype.val h
      simp at this)
    have := congrArg Subtype.val h1
    simpa using this
  obtain ⟨r, hr⟩ := VectorSpace.card_fintype F₀ F
  have hQ2 : 2 ≤ Q := by
    have : 1 < Fintype.card F₀ := Fintype.one_lt_card
    omega
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, pow_zero, ← Nat.card_eq_fintype_card] at hr
      omega
    · exact h
  have hqQ : Q ^ r - 1 = 3 ^ k * m := by
    rw [hqkm, hqdef, Nat.card_eq_fintype_card, hr]
  have hr' := eq_one_of_three_mul_dvd hQ2 hr1 hm3 hqQ hdvd
  rw [hr', pow_one] at hr
  have hcardA : Nat.card A.toAddSubgroup = Nat.card F := by
    have e : Nat.card A.toAddSubgroup = Nat.card F₀ :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => (hmemF₀ x).symm)
    rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hr]
  have htop := AddSubgroup.eq_top_of_card_eq A.toAddSubgroup hcardA
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ A.toAddSubgroup := htop ▸ AddSubgroup.mem_top x
  exact hx

theorem addSubgroup_eq_top_of_muM [Finite F] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {R : AddSubgroup F} (h1 : (1 : F) ∈ R) (hS : ∀ ζ ∈ muM F, ∀ r ∈ R, ζ * r ∈ R)
    (hωR : ∀ r ∈ R, ω * r ∈ R) : R = ⊤ := by
  set R' : Subring F :=
    { carrier := {t | ∀ r ∈ R, t * r ∈ R}
      mul_mem' := fun {a b} ha hb r hr => by
        rw [mul_assoc]
        exact ha _ (hb r hr)
      one_mem' := fun r hr => by rwa [one_mul]
      add_mem' := fun {a b} ha hb r hr => by
        rw [add_mul]
        exact R.add_mem (ha r hr) (hb r hr)
      zero_mem' := fun r _ => by
        rw [zero_mul]
        exact R.zero_mem
      neg_mem' := fun {a} ha r hr => by
        rw [neg_mul]
        exact R.neg_mem (ha r hr) } with hR'
  have hle : Subring.closure (muM F ∪ {ω}) ≤ R' := by
    rw [Subring.closure_le]
    rintro t (ht | rfl)
    · exact hS t ht
    · exact hωR
  rw [subring_closure_muM_eq_top hω hω1] at hle
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ R' := hle (Subring.mem_top x)
  have := hx 1 h1
  rwa [mul_one] at this

end CFSG.RankThree.PartTwo.Sec14.L3PGL
