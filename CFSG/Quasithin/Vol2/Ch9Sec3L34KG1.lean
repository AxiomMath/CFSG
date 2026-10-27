module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34
public import CFSG.Quasithin.Vol2.Ch11L2Q5cL34
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch9.L34

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

variable {X : Type} [Group X]

theorem lieModel_of_isPSL (hX : IsPSL 3 2 2 X) : LieModel X .PSL 3 2 2 :=
  Or.inl ⟨by decide, hX⟩

theorem eq_one_of_commute_of_two (hX : IsPSL 3 2 2 X) {b s : X} (hb : orderOf b = 3) {m : ℕ}
    (hs : s ^ 2 ^ m = 1) (hc : b * s = s * b) : s = 1 := by
  by_contra hs1
  have hdvd : orderOf s ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hs
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hs1 (orderOf_eq_one_iff.mp (by simpa using hj))
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have ht : orderOf (s ^ 2 ^ i) = 2 := by
    rw [orderOf_pow' s (pow_ne_zero _ two_ne_zero), hj, pow_succ]
    have h1 : (2 ^ i * 2).gcd (2 ^ i) = 2 ^ i := Nat.gcd_eq_right (dvd_mul_right _ _)
    rw [h1, Nat.mul_div_cancel_left _ (by positivity)]
  exact Vol2.Ch11.SecB.mul_ne_mul_of_isPSL_three_two_two hX hb ht
    ((Commute.pow_right (show Commute b s from hc) _).eq)

theorem card_eq_of_isPSL (hX : IsPSL 3 2 2 X) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) : Nat.card S = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel (lieModel_of_isPSL hX)
  have hcard : Nat.card X = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    exact RankThree.PartTwo.KFacts.L34.card_projectiveSL hk
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h := Sylow.card_eq_multiplicity (hS.toSylow hSi)
  rw [hcard, CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_two
    (show 20160 = 2 ^ 6 * 315 by norm_num) (by norm_num)] at h
  simpa using h

theorem eq_one_of_fix [Finite X] (hX : IsPSL 3 2 2 X) {α : MulAut X} (hα : α * α = 1)
    {S : Subgroup X} (hS : Nat.card S = 64) (hαS : ∀ x ∈ S, α x = x) {b : X}
    (hb : orderOf b = 3) (hαb : α b = b) : α = 1 := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel (lieModel_of_isPSL hX)
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  set α' := MulAut.congr e α with hα'def
  have hα' : α' * α' = 1 := by rw [hα'def, ← map_mul, hα, map_one]
  let σ : k ≃+* k := RingEquiv.ofBijective (frobenius k 2)
    ⟨(frobenius k 2).injective, Finite.surjective_of_injective (frobenius k 2).injective⟩
  have hσ : ∀ a, σ a = a ^ 2 := fun a => frobenius_def 2 a
  have hfix : ∀ x : X, α x = x → α' (e x) = e x := by
    intro x hx
    show e (α (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hx]
  have hb' : orderOf (e b) = 3 := by rw [MulEquiv.orderOf_eq]; exact hb
  rcases RankThree.PartTwo.KFacts.L34.involution_cases_card hk hσ hα' with
    ⟨x, hx⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  ·
    have hx2 : x * x = 1 := by
      apply RankThree.PartTwo.KFacts.L34.conj_injective hk
      rw [map_mul, hx, hα', map_one]
    have hxb : e b * x = x * e b := by
      have h1 : MulAut.conj x (e b) = e b := by rw [hx]; exact hfix b hαb
      rw [MulAut.conj_apply] at h1
      calc e b * x = x * e b * x⁻¹ * x := by rw [h1]
        _ = x * e b := by group
    have hx1 : x = 1 := by
      by_contra hne
      have hox : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hne
      exact RankThree.PartTwo.KFacts.L34.mul_ne_mul_of_orderOf hk hb' hox hxb
    have h1 : α' = 1 := by rw [← hx, hx1, map_one]
    have h2 : α = MulAut.congr e.symm α' := by
      rw [hα'def]
      ext y
      simp
    rw [h2, h1, map_one]
  all_goals
    exfalso
    have hS' : (S.map e.toMonoidHom) ≤ GL3TwoFixedModel.autFixed α' := by
      rintro _ ⟨x, hx, rfl⟩
      exact hfix x (hαS x hx)
    have hb'' : Subgroup.zpowers (e b) ≤ GL3TwoFixedModel.autFixed α' := by
      rw [Subgroup.zpowers_le]
      exact hfix b hαb
    have h64 : 64 ∣ Nat.card (GL3TwoFixedModel.autFixed α') := by
      have := Subgroup.card_dvd_of_le hS'
      rwa [Subgroup.card_map_of_injective e.injective, hS] at this
    have h3 : 3 ∣ Nat.card (GL3TwoFixedModel.autFixed α') := by
      have := Subgroup.card_dvd_of_le hb''
      rwa [Nat.card_zpowers, hb'] at this
    have h192 : 192 ∣ Nat.card (GL3TwoFixedModel.autFixed α') :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h3
    rw [h] at h192
    norm_num at h192

end CFSG.Quasithin.H13.Ch9.L34
