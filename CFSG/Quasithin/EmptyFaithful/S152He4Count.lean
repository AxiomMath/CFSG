module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.He4

open Subgroup

variable {Γ : Type*} [Group Γ]

@[expose] def NoInvCommNine (Γ : Type*) [Group Γ] : Prop :=
  ∀ P : Subgroup Γ, Nat.card P = 9 → ∀ t : Γ, t * t = 1 → (∀ p ∈ P, p * t = t * p) → t = 1

@[expose, instance_reducible] def conjAct (P R : Subgroup Γ) (hn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) :
    MulAction P R where
  smul p r := ⟨p * r * p⁻¹, hn p p.2 r r.2⟩
  one_smul r := Subtype.ext (by
    change ((1 : P) : Γ) * (r : Γ) * ((1 : P) : Γ)⁻¹ = r
    simp)
  mul_smul p q r := Subtype.ext (by
    change ((p * q : P) : Γ) * (r : Γ) * ((p * q : P) : Γ)⁻¹ =
      (p : Γ) * ((q : Γ) * (r : Γ) * (q : Γ)⁻¹) * (p : Γ)⁻¹
    simp [mul_assoc])

theorem card_modEq_centralizer (P R : Subgroup Γ) [Finite R] (hP : IsPGroup 3 P)
    (hn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) :
    Nat.card R ≡ Nat.card {r : R // ∀ p ∈ P, p * (r : Γ) * p⁻¹ = r} [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulAction P R := conjAct P R hn
  have h := hP.card_modEq_card_fixedPoints R
  have e : Nat.card (MulAction.fixedPoints P R) =
      Nat.card {r : R // ∀ p ∈ P, p * (r : Γ) * p⁻¹ = r} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hr p hp
      exact congrArg Subtype.val (hr ⟨p, hp⟩)
    · intro hr p
      exact Subtype.ext (hr p p.2)
  rw [e] at h
  exact h


theorem card_modEq_one_of_noInv (P R : Subgroup Γ) [Finite R] (hP : IsPGroup 3 P)
    (hR : IsPGroup 2 R) (hn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R)
    (hinv : ∀ t ∈ R, t * t = 1 → (∀ p ∈ P, p * t = t * p) → t = 1) :
    Nat.card R ≡ 1 [MOD 3] := by
  have h := card_modEq_centralizer P R hP hn
  have key : ∀ r : {r : R // ∀ p ∈ P, p * (r : Γ) * p⁻¹ = r}, (r.1 : Γ) = 1 := by
    intro r
    by_contra hne
    have hx : (r.1 : Γ) ∈ R := r.1.2
    have hfix : ∀ p ∈ P, p * (r.1 : Γ) = (r.1 : Γ) * p := by
      intro p hp
      have := r.2 p hp
      calc p * (r.1 : Γ) = p * (r.1 : Γ) * p⁻¹ * p := by group
        _ = (r.1 : Γ) * p := by rw [this]
    obtain ⟨k, hk⟩ := hR r.1
    have hk' : (r.1 : Γ) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hord : orderOf (r.1 : Γ) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.1 (by simpa using hio))
    have h2 : 2 ∣ orderOf (r.1 : Γ) := by
      rw [hio]
      exact dvd_pow_self 2 hi0
    have hu := orderOf_pow_orderOf_div (x := (r.1 : Γ)) (n := 2)
      (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨2 ^ k, by positivity, hk'⟩)).ne' h2
    set u : Γ := (r.1 : Γ) ^ (orderOf (r.1 : Γ) / 2) with hudef
    have huR : u ∈ R := R.pow_mem hx _
    have huu : u * u = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu, pow_two] at this
      exact this
    have hcomm : ∀ p ∈ P, p * u = u * p := by
      intro p hp
      exact ((Commute.pow_right (show Commute p (r.1 : Γ) from hfix p hp) _)).eq
    have := hinv u huR huu hcomm
    rw [this] at hu
    simp at hu
  have hcard : Nat.card {r : R // ∀ p ∈ P, p * (r : Γ) * p⁻¹ = r} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, fun p _ => by simp⟩⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [key a, key b]
  rw [hcard] at h
  exact h


section Lam

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem eq_of_mul_self_eq_one_of_card_four (R : Subgroup Λ) (hR : Nat.card R = 4) {r : Λ}
    (hr : r ∈ R) (hr2 : r * r ≠ 1) {v : Λ} (hv : v ∈ R) (hvv : v * v = 1) (hv1 : v ≠ 1) :
    v = r * r := by
  have hdvd : orderOf r ∣ 4 := hR ▸ Subgroup.orderOf_dvd_natCard R hr
  have hne1 : orderOf r ≠ 1 := fun h => hr2 (by rw [orderOf_eq_one_iff.1 h]; simp)
  have hne2 : orderOf r ≠ 2 := fun h => hr2 (by
    have := pow_orderOf_eq_one r
    rwa [h, pow_two] at this)
  have h4 : orderOf r = 4 := by
    have hle : orderOf r ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf r := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
    interval_cases h : orderOf r
    · exact absurd rfl hne1
    · exact absurd rfl hne2
    · exact absurd hdvd (by norm_num)
    · rfl
  have hzp : Subgroup.zpowers r = R := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · exact (Subgroup.zpowers_le).2 hr
    · rw [hR, Nat.card_zpowers, h4]
  have hv' : v ∈ Subgroup.zpowers r := hzp ▸ hv
  obtain ⟨j, hjv⟩ := Subgroup.mem_zpowers_iff.1 hv'
  have hvv' : r ^ j * r ^ j = 1 := by rw [hjv]; exact hvv
  have h2j : (orderOf r : ℤ) ∣ 2 * j :=
    orderOf_dvd_iff_zpow_eq_one.2 (by rw [two_mul, zpow_add]; exact hvv')
  obtain ⟨c, hc⟩ := h2j
  have hj : j = 2 * c := by rw [h4] at hc; push_cast at hc; omega
  have hu2 : (r * r) * (r * r) = 1 := by
    have h41 : r ^ 4 = 1 := by
      have := pow_orderOf_eq_one r
      rwa [h4] at this
    calc (r * r) * (r * r) = r ^ 2 * r ^ 2 := by rw [pow_two]
      _ = r ^ 4 := by rw [← pow_add]
      _ = 1 := h41
  have hvc : v = (r * r) ^ c := by rw [← hjv, hj, zpow_mul, zpow_two]
  rcases Int.even_or_odd' c with ⟨l, hl | hl⟩
  · exfalso
    apply hv1
    rw [hvc, hl, zpow_mul, zpow_two, hu2, one_zpow]
  · rw [hvc, hl, zpow_add, zpow_mul, zpow_two, hu2, one_zpow, one_mul, zpow_one]


omit [Finite Λ] in
theorem le_normalizer_of_conj_mem {P R : Subgroup Λ} (hn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) :
    P ≤ Subgroup.normalizer (R : Set Λ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hn g hg h hh, fun hh => ?_⟩
  have := hn g⁻¹ (P.inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem lam_B (hinv : NoInvCommNine Λ) (P R : Subgroup Λ) (hP : Nat.card P = 9)
    (hR2 : IsPGroup 2 R) (hn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) (j : ℕ)
    (hj : Nat.card R = 2 ^ (2 * j + 1)) : False := by
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  have hmod := card_modEq_one_of_noInv P R hP3 hR2 hn (fun t _ ht hc => hinv P hP t ht hc)
  rw [hj] at hmod
  have h2 : 2 ^ (2 * j + 1) % 3 = 2 := by
    have h4 : (2 ^ 2) ^ j % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [pow_succ, pow_mul, Nat.mul_mod, h4]
  unfold Nat.ModEq at hmod
  omega

structure SmallFacts (Λ : Type*) [Group Λ] : Prop where
  card : ∃ m, Nat.card Λ = 16 * m ∧ Odd m
  syl : ∀ S : Subgroup Λ, Nat.card S = 16 → Subgroup.normalizer (S : Set Λ) ≤ S
  four : ∀ F : Subgroup Λ, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
    ¬ 9 ∣ Nat.card (Subgroup.normalizer (F : Set Λ))
  inv : NoInvCommNine Λ

theorem lam_A (hΛ : SmallFacts Λ) (P R : Subgroup Λ) (hP : Nat.card P = 9) (hR2 : IsPGroup 2 R)
    (hRne : R ≠ ⊥) (hn : ∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) : False := by
  obtain ⟨m, hm, hodd⟩ := hΛ.card
  have hinv := hΛ.inv
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  have hmod := card_modEq_one_of_noInv P R hP3 hR2 hn (fun t _ ht hc => hinv P hP t ht hc)
  obtain ⟨a, ha⟩ := hR2.exists_card_eq
  have hdvd : 2 ^ a ∣ 16 * m := by
    rw [← ha, ← hm]
    exact Subgroup.card_subgroup_dvd_card R
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  have hd16 : 2 ^ a ∣ 16 := hcop.dvd_of_dvd_mul_right hdvd
  have ha4 : a ≤ 4 := by
    have h1 : 2 ^ a ≤ 16 := Nat.le_of_dvd (by norm_num) hd16
    by_contra hlt
    have hlt' : 5 ≤ a := by omega
    have : 2 ^ 5 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hlt'

    omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hRne
    rw [← Subgroup.card_eq_one]
    simpa using ha
  have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha0
  rw [ha] at hmod
  have hPN : P ≤ Subgroup.normalizer (R : Set Λ) := le_normalizer_of_conj_mem hn
  interval_cases a
  · exact absurd hmod (by decide)
  ·
    have hR4 : Nat.card R = 4 := by rw [ha]; norm_num
    by_cases hexp : ∀ f ∈ R, f * f = 1
    · exact hΛ.four R hR4 hexp (hP ▸ Subgroup.card_dvd_of_le hPN)
    · obtain ⟨r, hr, hr2⟩ : ∃ r ∈ R, r * r ≠ 1 := by
        by_contra h
        exact hexp fun f hf => by_contra fun hne => h ⟨f, hf, hne⟩
      have huR : r * r ∈ R := R.mul_mem hr hr
      have huu : (r * r) * (r * r) = 1 := by
        have hdvd4 : orderOf r ∣ 4 := hR4 ▸ Subgroup.orderOf_dvd_natCard R hr
        have h41 : r ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd4
        calc (r * r) * (r * r) = r ^ 2 * r ^ 2 := by rw [pow_two]
          _ = r ^ 4 := by rw [← pow_add]
          _ = 1 := h41
      have hcomm : ∀ p ∈ P, p * (r * r) = (r * r) * p := by
        intro p hp
        have hv : p * (r * r) * p⁻¹ ∈ R := hn p hp _ huR
        have hvv : (p * (r * r) * p⁻¹) * (p * (r * r) * p⁻¹) = 1 := by
          calc (p * (r * r) * p⁻¹) * (p * (r * r) * p⁻¹)
              = p * ((r * r) * (r * r)) * p⁻¹ := by group
            _ = 1 := by rw [huu]; group
        have hv1 : p * (r * r) * p⁻¹ ≠ 1 := by
          intro h
          apply hr2
          have : p * (r * r) * p⁻¹ = 1 := h
          have h' : r * r = 1 := by
            have := congrArg (fun x => p⁻¹ * x * p) this
            simpa [mul_assoc] using this
          exact h'
        have heq := eq_of_mul_self_eq_one_of_card_four R hR4 hr hr2 hv hvv hv1
        calc p * (r * r) = p * (r * r) * p⁻¹ * p := by group
          _ = (r * r) * p := by rw [heq]
      have := hinv P hP (r * r) huu hcomm
      exact hr2 this
  · exact absurd hmod (by decide)
  ·
    have hR16 : Nat.card R = 16 := by rw [ha]; norm_num
    have hPR : P ≤ R := fun g hg => hΛ.syl R hR16 (hPN hg)
    have := Subgroup.card_dvd_of_le hPR
    rw [hP, hR16] at this
    omega

end Lam

end CFSG.Quasithin.He4
