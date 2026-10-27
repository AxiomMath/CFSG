module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap

public section

namespace CFSG.GroupTheory

open Subgroup

variable {A : Type*} [Group A]

theorem mulAut_eq_one_of_card_lt_of_pow_eq_one [Finite A] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card A < p) (α : MulAut A) (hα : α ^ p = 1) : α = 1 := by
  have hcard_aut : Nat.card (MulAut A) ∣ (Nat.card A).factorial := by
    have hinj : Function.Injective (MulAut.toPerm A) := by
      intro f g h
      ext x
      exact congrFun (congrArg (fun e : Equiv.Perm A => (e : A → A)) h) x
    have hrange := (MulAut.toPerm A).range.card_subgroup_dvd_card
    rw [Nat.card_perm] at hrange
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at hrange
  have horder_dvd_fact : orderOf α ∣ (Nat.card A).factorial :=
    (orderOf_dvd_natCard α).trans hcard_aut
  have horder_dvd_p : orderOf α ∣ p := orderOf_dvd_of_pow_eq_one hα
  rcases (Nat.dvd_prime hp).1 horder_dvd_p with h1 | hp_eq
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    have hp_dvd_fact : p ∣ (Nat.card A).factorial := hp_eq ▸ horder_dvd_fact
    rw [hp.dvd_factorial] at hp_dvd_fact
    omega

@[expose]
noncomputable def MulAut.restrictNormal (α : MulAut A) (N : Subgroup A)
    (hN : N.map α.toMonoidHom = N) : MulAut N :=
  (α.subgroupMap N).trans (MulEquiv.subgroupCongr hN)

@[simp]
theorem MulAut.restrictNormal_apply (α : MulAut A) (N : Subgroup A)
    (hN : N.map α.toMonoidHom = N) (n : N) :
    ((MulAut.restrictNormal α N hN n : N) : A) = α n := rfl

@[expose]
noncomputable def MulAut.quotientNormal (α : MulAut A) (N : Subgroup A) [N.Normal]
    (hN : N.map α.toMonoidHom = N) : MulAut (A ⧸ N) :=
  QuotientGroup.congr N N α hN

@[simp]
theorem MulAut.quotientNormal_mk (α : MulAut A) (N : Subgroup A) [N.Normal]
    (hN : N.map α.toMonoidHom = N) (a : A) :
    MulAut.quotientNormal α N hN (a : A ⧸ N) = (α a : A ⧸ N) :=
  QuotientGroup.congr_mk N N α hN a

theorem MulAut.quotientNormal_pow (α : MulAut A) (N : Subgroup A) [N.Normal]
    (hN : N.map α.toMonoidHom = N) {p : ℕ} (hα : α ^ p = 1) :
    (MulAut.quotientNormal α N hN) ^ p = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H a =>
      have hpow : ∀ k : ℕ,
          ((MulAut.quotientNormal α N hN) ^ k) (a : A ⧸ N) = ((α ^ k) a : A ⧸ N) := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
            rw [pow_succ', MulAut.mul_apply, ih, MulAut.quotientNormal_mk,
              pow_succ', MulAut.mul_apply]
      rw [hpow p, hα]
      rfl

theorem MulAut.restrictNormal_pow (α : MulAut A) (N : Subgroup A)
    (hN : N.map α.toMonoidHom = N) {p : ℕ} (hα : α ^ p = 1) :
    (MulAut.restrictNormal α N hN) ^ p = 1 := by
  refine MulEquiv.ext fun n => ?_
  apply Subtype.ext
  simp only [MulAut.one_apply]
  have hpow : ∀ k : ℕ, ∀ n : N,
      (((MulAut.restrictNormal α N hN) ^ k) n : A) = (α ^ k) n := by
    intro k
    induction k with
    | zero => intro n; rfl
    | succ k ih =>
        intro n
        rw [pow_succ', MulAut.mul_apply]
        change (α (((MulAut.restrictNormal α N hN) ^ k) n) : A) = (α ^ (k + 1)) n
        rw [ih n, pow_succ', MulAut.mul_apply]
  rw [hpow p n, hα]
  rfl

theorem mulAut_eq_one_of_normal_card_lt_of_quotient_card_lt [Finite A] (N : Subgroup A)
    [N.Normal] {p : ℕ} (hp : p.Prime) (hNlt : Nat.card N < p)
    (hQlt : Nat.card (A ⧸ N) < p) (α : MulAut A) (hα : α ^ p = 1)
    (hNα : ∀ n ∈ N, α n ∈ N) : α = 1 := by
  have hNmap : N.map α.toMonoidHom = N := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact hNα n hn
    · rw [Subgroup.card_map_of_injective (α : A ≃* A).injective]
  have hNltp : Nat.card N < p := hNlt
  have hQltp : Nat.card (A ⧸ N) < p := hQlt
  have hcop : p.Coprime (Nat.card N) := by
    rw [hp.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt Nat.card_pos hNltp
  have hfixN : ∀ n ∈ N, α n = n := by
    intro n hn
    have hNpow : (MulAut.restrictNormal α N hNmap) ^ p = 1 :=
      MulAut.restrictNormal_pow α N hNmap hα
    have hNid : MulAut.restrictNormal α N hNmap = 1 :=
      mulAut_eq_one_of_card_lt_of_pow_eq_one hp hNltp _ hNpow
    have h := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : A)) hNid
    simpa [MulAut.restrictNormal_apply] using h
  have hdisp : ∀ a : A, a⁻¹ * α a ∈ N := by
    intro a
    have hQpow : (MulAut.quotientNormal α N hNmap) ^ p = 1 :=
      MulAut.quotientNormal_pow α N hNmap hα
    have hQid : MulAut.quotientNormal α N hNmap = 1 :=
      mulAut_eq_one_of_card_lt_of_pow_eq_one hp hQltp _ hQpow
    have h := congrArg (fun f : MulAut (A ⧸ N) => f (a : A ⧸ N)) hQid
    rw [MulAut.quotientNormal_mk, MulAut.one_apply] at h
    have hq : ((a⁻¹ * α a : A) : A ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h]
      simp
    exact (QuotientGroup.eq_one_iff (a⁻¹ * α a)).1 hq
  exact CFSG.SectionRank.Ccomm.coprime_automorphism_trivial_normal_factors N α
    hp.pos hα hcop hfixN hdisp

theorem mulAut_eq_one_of_normal_card_four_of_quotient_card_four_of_pow_seven
    [Finite A] (N : Subgroup A) [N.Normal] (hNcard : Nat.card N = 4)
    (hQcard : Nat.card (A ⧸ N) = 4) (α : MulAut A) (hα : α ^ 7 = 1)
    (hNα : ∀ n ∈ N, α n ∈ N) : α = 1 :=
  mulAut_eq_one_of_normal_card_lt_of_quotient_card_lt N (by norm_num)
    (by omega) (by omega) α hα hNα

theorem mulAut_eq_one_of_normal_card_four_of_card_sixteen_of_pow_seven
    [Finite A] (N : Subgroup A) [N.Normal] (hAcard : Nat.card A = 16)
    (hNcard : Nat.card N = 4) (α : MulAut A) (hα : α ^ 7 = 1)
    (hNα : ∀ n ∈ N, α n ∈ N) : α = 1 := by
  have hQcard : Nat.card (A ⧸ N) = 4 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hAcard, hNcard] at h
    have h' : Nat.card (A ⧸ N) * 4 = 4 * 4 := by
      simpa using h.symm
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  exact mulAut_eq_one_of_normal_card_four_of_quotient_card_four_of_pow_seven N
    hNcard hQcard α hα hNα

theorem not_exists_mulAut_orderOf_eq_seven_of_normal_card_four_of_card_sixteen
    [Finite A] (N : Subgroup A) [N.Normal] (hAcard : Nat.card A = 16)
    (hNcard : Nat.card N = 4) :
    ¬ ∃ α : MulAut A, orderOf α = 7 ∧ ∀ n ∈ N, α n ∈ N := by
  rintro ⟨α, hord, hNα⟩
  have hα : α ^ 7 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one α
  have hα1 : α = 1 :=
    mulAut_eq_one_of_normal_card_four_of_card_sixteen_of_pow_seven N hAcard hNcard
      α hα hNα
  have horder1 : orderOf α = 1 := by rw [hα1, orderOf_one]
  omega

end CFSG.GroupTheory

end
