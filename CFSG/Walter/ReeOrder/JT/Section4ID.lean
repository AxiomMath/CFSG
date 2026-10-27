module

public import CFSG.Walter.ReeOrder.JT.Section4IB
public import CFSG.Walter.ReeOrder.JT.Section7W
public import CFSG.Walter.ReeOrder.JT.Section7ZA

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem commute_of_card_nine_of_isPGroup {C : Subgroup X} (hC : Nat.card C = 9) {r : ℕ}
    [hr : Fact r.Prime] (hr6 : Nat.Coprime r 6) {y : X} (hy : IsPGroup r (Subgroup.zpowers y))
    (hyC : y ∈ Subgroup.normalizer (C : Set X)) : ∀ c ∈ C, y * c = c * y := by
  classical
  have hYC : Subgroup.zpowers y ≤ Subgroup.normalizer (C : Set X) := (Subgroup.zpowers_le).mpr hyC
  let := conjAct (Subgroup.zpowers y) C hYC
  have hmod := hy.card_modEq_card_fixedPoints C
  set F := FixedPoints.subgroup (Subgroup.zpowers y) C with hFdef
  have hFcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) C) = Nat.card F := rfl
  rw [hC, hFcard] at hmod
  have hFdvd : Nat.card F ∣ 9 := hC ▸ Subgroup.card_subgroup_dvd_card F
  have hF9 : Nat.card F = 9 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hFdvd
    obtain ⟨k, hk, hFk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hFdvd
    have hr2 : r ≠ 2 := fun h2 => by
      rw [h2] at hr6
      norm_num at hr6
    have hr3 : r ≠ 3 := fun h3 => by
      rw [h3] at hr6
      norm_num at hr6
    interval_cases k
    · exfalso
      rw [hFk, pow_zero] at hmod
      have := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
      have h8 : r ∣ 8 := by simpa using this
      have := (Nat.Prime.dvd_of_dvd_pow hr.out (show r ∣ 2 ^ 3 by simpa using h8))
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.out Nat.prime_two).mp this)
    · exfalso
      rw [hFk, pow_one] at hmod
      have := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
      have h6 : r ∣ 6 := by simpa using this
      have := Nat.Coprime.eq_one_of_dvd hr6 h6
      exact hr.out.one_lt.ne this.symm
    · rw [hFk]; norm_num
  have htop : F = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hF9, hC]
  intro c hc
  have hcF : (⟨c, hc⟩ : C) ∈ F := htop ▸ Subgroup.mem_top _
  have h1 := (FixedPoints.mem_subgroup _ _ _).mp hcF ⟨y, Subgroup.mem_zpowers y⟩
  have h2 : y * c * y⁻¹ = c := congrArg Subtype.val h1
  calc y * c = y * c * y⁻¹ * y := by group
    _ = c * y := by rw [h2]

theorem le_centralizer_of_card_nine {C : Subgroup X} (hC : Nat.card C = 9) {R : Subgroup X}
    (hR6 : Nat.Coprime (Nat.card R) 6) (hRC : R ≤ Subgroup.normalizer (C : Set X)) :
    R ≤ Subgroup.centralizer (C : Set X) := by
  classical
  suffices key : ∀ n : ℕ, ∀ y ∈ R, orderOf y = n → y ∈ Subgroup.centralizer (C : Set X) from
    fun y hy => key _ y hy rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hyR hyn
  by_cases hn1 : n = 1
  · rw [hn1] at hyn
    rw [orderOf_eq_one_iff.mp hyn]
    exact Subgroup.one_mem _
  have hn0 : n ≠ 0 := by rw [← hyn]; exact (orderOf_pos y).ne'
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd hn1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 r hr.ne_one
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hab
    exact hb (hab ▸ hrn)
  have hyo : orderOf y ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hyR
  have hr6 : Nat.Coprime r 6 := Nat.Coprime.coprime_dvd_left (hrn.trans (hyn ▸ hyo)) hR6
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hab
    exact hn0 hab
  have h1 : y ^ b ∈ Subgroup.centralizer (C : Set X) := by
    have hyb : orderOf (y ^ b) = r ^ a := by
      rw [orderOf_pow_of_dvd hb0 (hyn ▸ ⟨r ^ a, by rw [hab, mul_comm]⟩), hyn, hab]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)
    have hp : IsPGroup r (Subgroup.zpowers (y ^ b)) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hyb] : Nat.card (Subgroup.zpowers (y ^ b)) = r ^ a)
    have := commute_of_card_nine_of_isPGroup hC hr6 hp (Subgroup.pow_mem _ (hRC hyR) b)
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (this c hc).symm
  have h2 : y ^ r ^ a ∈ Subgroup.centralizer (C : Set X) := by
    have hyb : orderOf (y ^ r ^ a) = b := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) (hyn ▸ ⟨b, hab⟩), hyn, hab]
      exact Nat.mul_div_cancel_left _ (pow_pos hr.pos a)
    refine ih b ?_ _ (R.pow_mem hyR _) hyb
    rw [hab]
    have : 1 < r ^ a := Nat.one_lt_pow ha hr.one_lt
    have hb0' : 0 < b := Nat.pos_of_ne_zero hb0
    nlinarith
  exact mem_of_pow_mem_of_coprime h1 h2
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hr).mpr hb)).symm

theorem commute_of_inv_of_inv {K Y : Subgroup X} {w : X} (hw : w * w = 1)
    (hKY : K ≤ Subgroup.normalizer (Y : Set X)) (hKodd : Odd (Nat.card K))
    (hYodd : Odd (Nat.card Y)) (hcop : Nat.Coprime (Nat.card K) (Nat.card Y))
    (hwK : ∀ k ∈ K, w * k * w⁻¹ = k⁻¹) (hwY : ∀ y ∈ Y, w * y * w⁻¹ = y⁻¹) :
    ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k := by
  have hdisj : Disjoint K Y := Subgroup.disjoint_of_coprime_natCard hcop
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hmem : ∀ z, z ∈ K ⊔ Y ↔ ∃ k ∈ K, ∃ y ∈ Y, k * y = z := by
    intro z
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKY]
    exact Iff.rfl
  have hwN : w ∈ Subgroup.normalizer ((K ⊔ Y : Subgroup X) : Set X) := by
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨k, hk, y, hy, rfl⟩ := (hmem z).mp hz
    rw [show w * (k * y) * w⁻¹ = (w * k * w⁻¹) * (w * y * w⁻¹) by group, hwK k hk, hwY y hy]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.inv_mem hk))
      (Subgroup.mem_sup_right (Y.inv_mem hy))
  have hodd2 : ∀ {H : Subgroup X}, Odd (Nat.card H) → ∀ x ∈ H, x * x = 1 → x = 1 := by
    intro H hH x hx hxx
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx)
    have hodd := Odd.of_dvd_nat hH (Subgroup.orderOf_dvd_natCard H hx)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hfix : ∀ z ∈ K ⊔ Y, w * z * w⁻¹ = z → z = 1 := by
    intro z hz hwz
    obtain ⟨k, hk, y, hy, rfl⟩ := (hmem z).mp hz
    rw [show w * (k * y) * w⁻¹ = (w * k * w⁻¹) * (w * y * w⁻¹) by group, hwK k hk, hwY y hy]
      at hwz
    have hk2 : k * k ∈ Y := by
      have h1 : k * k = y⁻¹ * y⁻¹ := by
        calc k * k = k * (k * y) * y⁻¹ := by group
          _ = k * (k⁻¹ * y⁻¹) * y⁻¹ := by rw [hwz]
          _ = y⁻¹ * y⁻¹ := by group
      rw [h1]
      exact Y.mul_mem (Y.inv_mem hy) (Y.inv_mem hy)
    have hk1 : k = 1 := hodd2 hKodd k hk
      (Subgroup.disjoint_def.mp hdisj (K.mul_mem hk hk) hk2)
    subst hk1
    rw [one_mul, inv_one, one_mul] at hwz
    rw [one_mul]
    exact hodd2 hYodd y hy (by
      calc y * y = y * y⁻¹ := by rw [hwz]
        _ = 1 := mul_inv_cancel y)
  have hcomm := commute_of_fpf_involution hw hwN hfix
  intro k hk y hy
  exact hcomm k (Subgroup.mem_sup_left hk) y (Subgroup.mem_sup_right hy)

theorem exists_hall_complement {M : Subgroup X} {n : ℕ}
    (hsyl : ∀ r : ℕ, r.Prime → r ∣ n → ∃ (_ : Fact r.Prime) (S : Sylow r M),
      Subgroup.normalizer ((S : Subgroup M) : Set M) ≤
        Subgroup.centralizer ((S : Subgroup M) : Set M)) :
    ∃ M₁ : Subgroup X, M₁ ≤ M ∧ (∀ x ∈ M₁, Nat.Coprime (orderOf x) n) ∧
      (∀ x ∈ M, Nat.Coprime (orderOf x) n → x ∈ M₁) ∧
      ∀ g ∈ Subgroup.normalizer (M : Set X), g ∈ Subgroup.normalizer (M₁ : Set X) := by
  classical
  set E : Set X := {x | x ∈ M ∧ Nat.Coprime (orderOf x) n} with hEdef
  refine ⟨Subgroup.closure E, ?_, ?_, fun x hx hxn => Subgroup.subset_closure ⟨hx, hxn⟩, ?_⟩
  · rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  · intro x hx
    refine Nat.coprime_of_dvd fun r hr hrx hrn => ?_
    obtain ⟨_, S, hS⟩ := hsyl r hr hrn
    obtain ⟨K, -, hKr, hKmem, -⟩ := exists_normal_complement_of_le_centralizer S hS
    have hle : Subgroup.closure E ≤ K.map M.subtype := by
      rw [Subgroup.closure_le]
      intro z hz
      refine ⟨⟨z, hz.1⟩, hKmem _ ?_, rfl⟩
      rw [Subgroup.orderOf_mk]
      exact Nat.Coprime.coprime_dvd_right hrn hz.2
    obtain ⟨⟨z, hzM⟩, hzK, rfl⟩ := hle hx
    have h1 : orderOf (⟨z, hzM⟩ : M) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hzK
    rw [Subgroup.orderOf_mk] at h1
    exact hKr (hrx.trans h1)
  · intro g hg
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hz.2
    | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb =>
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha

end General

namespace Setup

variable {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2) (hS : SuzukiFourGroupTheorem)
  (h3Q : ¬ 3 ∣ Nat.card s.Q)
include hp hS h3Q

theorem not_nine_dvd_card_normalizer_Q :
    ¬ 9 ∣ Nat.card (Subgroup.normalizer (s.Q : Set G)) := by
  intro h9
  have hc := s.card_normalizer_Q hp hS
  have h3 : ¬ 3 ∣ Nat.card s.Q := h3Q
  rcases hc with h | h <;> rw [h] at h9
  · have : 3 ∣ 8 * Nat.card s.Q := by
      have : 9 ∣ 3 * (8 * Nat.card s.Q) := by convert h9 using 1; ring
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp (by simpa [mul_comm] using this)
    exact h3 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 8) this))
  · have : 3 ∣ 40 * Nat.card s.Q := by
      have : 9 ∣ 3 * (40 * Nat.card s.Q) := by convert h9 using 1; ring
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp (by simpa [mul_comm] using this)
    exact h3 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 40) this))

theorem commute_of_mem_normalizer_Q
    {μ : G} (hμ : μ ∈ Subgroup.normalizer (s.Q : Set G))
    (hμ3 : orderOf μ = 3) {y : G} (hyN : y ∈ Subgroup.normalizer (s.Q : Set G))
    (hyμ : y * μ = μ * y) (hyodd : Odd (orderOf y)) :
    ∀ z ∈ s.Q, z * μ = μ * z → y * z = z * y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQc : ∀ a ∈ s.Q, ∀ b ∈ s.Q, a * b = b * a := by
    have := s.isCyclic_Q hp
    intro a ha b hb
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := s.Q)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  intro z hzQ hzμ
  set H := Subgroup.centralizer ({z} : Set G) with hHdef
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hn0 hab
  have h1 : y ^ 3 ^ a ∈ H := by
    have hyo : orderOf (y ^ 3 ^ a) = b := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) ⟨b, hab⟩, hab]
      exact Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)
    have hodd : Odd b := Odd.of_dvd_nat hyodd ⟨3 ^ a, by rw [hab, mul_comm]⟩
    have h6 : Nat.Coprime b 6 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_right (Nat.Coprime.symm (Nat.coprime_two_left.mpr hodd))
        (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb))
    have hmem := s.mem_Q_of_commute hp hS h3Q hμ hμ3 (Subgroup.pow_mem _ hyN _)
      (((Commute.pow_left (hyμ : Commute y μ) _)).eq) (hyo ▸ h6)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hQc _ hzQ _ hmem).symm
  have h2 : y ^ b ∈ H := by
    have hyo : orderOf (y ^ b) = 3 ^ a := by
      rw [orderOf_pow_of_dvd hb0 ⟨3 ^ a, by rw [hab, mul_comm]⟩, hab]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)
    have hc : Commute (y ^ b) μ := Commute.pow_left (hyμ : Commute y μ) b
    have hN : Subgroup.zpowers (y ^ b) ≤ Subgroup.normalizer (Subgroup.zpowers μ : Set G) :=
      (Subgroup.zpowers_le).mpr (mem_normalizer_zpowers_of_commute hc.eq)
    have hP : IsPGroup 3 (Subgroup.zpowers (y ^ b) ⊔ Subgroup.zpowers μ :
        Subgroup G) := by
      have h3a : IsPGroup 3 (Subgroup.zpowers (y ^ b)) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hyo])
      have h3μ : IsPGroup 3 (Subgroup.zpowers μ) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hμ3, pow_one] :
          Nat.card (Subgroup.zpowers μ) = 3 ^ 1)
      exact h3a.to_sup_of_normal_right' h3μ hN
    have hPN : Subgroup.zpowers (y ^ b) ⊔ Subgroup.zpowers μ ≤
        Subgroup.normalizer (s.Q : Set G) :=
      sup_le ((Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ hyN _))
        ((Subgroup.zpowers_le).mpr hμ)
    have hle : Nat.card (Subgroup.zpowers (y ^ b) ⊔ Subgroup.zpowers μ : Subgroup G) ≤ 3 := by
      obtain ⟨k, hk⟩ := hP.exists_card_eq
      have hdvd := Subgroup.card_dvd_of_le hPN
      rw [hk] at hdvd ⊢
      have hk1 : k ≤ 1 := by
        by_contra hk1
        exact s.not_nine_dvd_card_normalizer_Q hp hS h3Q
          ((show (9 : ℕ) = 3 ^ 2 by norm_num) ▸ (pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hdvd)
      interval_cases k <;> norm_num
    have heq : Subgroup.zpowers (y ^ b) ⊔ Subgroup.zpowers μ = Subgroup.zpowers μ :=
      (Subgroup.eq_of_le_of_card_ge le_sup_right (by
        rw [Nat.card_zpowers, hμ3]; exact hle)).symm
    have hyb : y ^ b ∈ Subgroup.zpowers μ := heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyb
    rw [← hk, Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.zpow_left (hzμ.symm : Commute μ z) k)).eq
  have hy := mem_of_pow_mem_of_coprime h2 h1
    (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.mp hy)

end Setup

end CFSG.Walter.JT
