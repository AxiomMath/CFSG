module

public import CFSG.RankThree.PartOne.S11d.Sec109Common
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S12.Sec125Moved

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_theta_self (p : ℕ) (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore p) K : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (theta_le_and_normal p K).1).mp
    (theta_le_and_normal p K).2

omit [Finite G] in
theorem thetaQuotientCentralizer_le (p : ℕ) (A K : Subgroup G) :
    thetaQuotientCentralizer p A K ≤ A := inf_le_left

theorem centralizes_of_commutator_mem_theta {p : ℕ} (hp : p.Prime) {K X : Subgroup G}
    (hq : CFSG.IsQuasisimple K) (hX : X ≤ Subgroup.normalizer (K : Set G))
    (h : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) K) :
    ∀ x ∈ X, ∀ k ∈ K, x * k = k * x := by
  have hθZ : inSubgroup (aschbacherSolvableCore p) K ≤ (Subgroup.center K).map K.subtype :=
    Subgroup.map_mono (theta_le_center_of_quasisimple hp hq)
  have hle : ⁅K, X⁆ ≤ inSubgroup (aschbacherSolvableCore p) K := by
    rw [Subgroup.commutator_le]
    intro k hk x hx
    have e : ⁅k, x⁆ = (x * k * x⁻¹ * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (inSubgroup (aschbacherSolvableCore p) K).inv_mem (h x hx k hk)
  by_cases hbot : ⁅K, X⁆ = ⊥
  · intro x hx k hk
    have h1 : ⁅k, x⁆ ∈ ⁅K, X⁆ := Subgroup.commutator_mem_commutator hk hx
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  · exfalso
    have hKK : ⁅K, X⁆ = K := Sec125.commutator_eq_of_ne_bot hq hX hbot
    have hKZ : K ≤ (Subgroup.center K).map K.subtype :=
      calc K = ⁅K, X⁆ := hKK.symm
        _ ≤ inSubgroup (aschbacherSolvableCore p) K := hle
        _ ≤ (Subgroup.center K).map K.subtype := hθZ
    have hcomm : ⁅K, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      obtain ⟨z, hz, hzk⟩ := hKZ hk
      have := Subgroup.mem_center_iff.mp hz ⟨k', hk'⟩
      have h2 := congrArg Subtype.val this
      rw [← hzk]
      exact h2
    have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
    exact Sec125.ne_bot_of_isQuasisimple hq (hperf ▸ hcomm)

structure Branch (p : ℕ) (A : Subgroup G) (c : G) (L B : Subgroup G) (n : ℕ) (b : G)
    (S K K' : Subgroup G) (a' : G) : Prop where
  config : Sec109.Config p A c L B n
  witness : Sec109.Witness A c B b S
  K_mem : K ∈ sectionTenAt p (sectionTenZero p A) b
  S_le : S ≤ K
  K'_mem : K' ∈ sectionTenAt p (sectionTenZeroStar p A) a'
  a'_mem : a' ∈ A
  a'_notMem : a' ∉ B
  rel : sectionTenRel p K K'

namespace Branch

variable {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ} {b : G} {S K K' : Subgroup G}
  {a' : G} (H : Branch p A c L B n b S K K' a')

include H

theorem prime : p.Prime := H.config.prime

theorem p_eq : p = 7 := H.config.p_eq

theorem three_lt : 3 < p := sectionTenSetup_three_lt H.config.setup

theorem hev : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq H.config.setup).le

theorem b_mem_A : b ∈ A := H.config.B_le_A H.witness.b_mem

theorem b_pow : b ^ p = 1 := H.config.pow_p_eq_one H.b_mem_A

theorem K_le_centralizer : K ≤ Subgroup.centralizer ({b} : Set G) :=
  (mem_thetaComponentsAt_iff.mp H.K_mem.2).1

theorem K'_le_centralizer : K' ≤ Subgroup.centralizer ({a'} : Set G) :=
  (mem_thetaComponentsAt_iff.mp H.K'_mem.2).1

theorem commute_b_of_mem_K {k : G} (hk : k ∈ K) : k * b = b * k :=
  mem_centralizer_singleton_iff.mp (H.K_le_centralizer hk)

theorem A_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G) :=
  selected_prime_elements_normalize_theta_components.2 G H.hev p H.prime H.three_lt A
    H.config.A_elem K H.K_mem.1.1

theorem A_le_normalizer_theta :
    A ≤ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore p) K : Subgroup G) : Set G) :=
  le_normalizer_theta_of_le_normalizer H.prime H.A_le_normalizer_K

theorem theta_K_eq : inSubgroup (aschbacherSolvableCore p) K =
    K ⊓ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) :=
  theta_eq_inf_of_mem_thetaComponentsAt H.prime H.K_mem.2

theorem b_mem_D : b ∈ thetaQuotientCentralizer p A K := by
  rw [mem_thetaQuotientCentralizer_iff]
  refine ⟨H.b_mem_A, ?_, fun k hk => ?_⟩
  · exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun k hk => H.commute_b_of_mem_K hk)
  · have : b * k * b⁻¹ * k⁻¹ = 1 := by
      rw [← H.commute_b_of_mem_K hk]
      group
    rw [this]
    exact Subgroup.one_mem _

theorem a'_mem_D : a' ∈ thetaQuotientCentralizer p A K := by
  rw [mem_thetaQuotientCentralizer_iff]
  refine ⟨H.a'_mem, H.A_le_normalizer_K H.a'_mem, fun k hk => ?_⟩
  set θ := inSubgroup (aschbacherSolvableCore p) K with hθ
  have hk' : k ∈ ((K ⊓ K' : Subgroup G) : Set G) * (θ : Set G) := by
    rw [← sectionTenRel_iff.mp H.rel]
    exact hk
  obtain ⟨m, hm, t, ht, rfl⟩ := hk'
  have hma : m * a' = a' * m :=
    mem_centralizer_singleton_iff.mp (H.K'_le_centralizer (Subgroup.mem_inf.mp hm).2)
  have h1 : a' * t * a'⁻¹ ∈ θ :=
    (Subgroup.mem_normalizer_iff.mp (H.A_le_normalizer_theta H.a'_mem) t).mp ht
  have h2 : a' * t * a'⁻¹ * t⁻¹ ∈ θ := θ.mul_mem h1 (θ.inv_mem ht)
  have h3 : m * (a' * t * a'⁻¹ * t⁻¹) * m⁻¹ ∈ θ :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_theta_self p K (Subgroup.mem_inf.mp hm).1)
      _).mp h2
  have e : a' * (m * t) * a'⁻¹ * (m * t)⁻¹ = m * (a' * t * a'⁻¹ * t⁻¹) * m⁻¹ := by
    calc a' * (m * t) * a'⁻¹ * (m * t)⁻¹ = (a' * m) * t * a'⁻¹ * t⁻¹ * m⁻¹ := by group
      _ = (m * a') * t * a'⁻¹ * t⁻¹ * m⁻¹ := by rw [← hma]
      _ = m * (a' * t * a'⁻¹ * t⁻¹) * m⁻¹ := by group
  rw [e]
  exact h3

theorem c_notMem_D : c ∉ thetaQuotientCentralizer p A K := by
  intro hcD
  have hSθ : S ≤ inSubgroup (aschbacherSolvableCore p) K := by
    calc S = ⁅S, Subgroup.zpowers c⁆ := H.witness.S_comm
      _ ≤ inSubgroup (aschbacherSolvableCore p) K := by
        rw [Subgroup.commutator_le]
        intro s hs g hg
        have hgD : g ∈ thetaQuotientCentralizer p A K := (Subgroup.zpowers_le.mpr hcD) hg
        have h := (mem_thetaQuotientCentralizer_iff.mp hgD).2.2 s (H.S_le hs)
        have e : ⁅s, g⁆ = (g * s * g⁻¹ * s⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact (inSubgroup (aschbacherSolvableCore p) K).inv_mem h
  have hSb : S ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) :=
    hSθ.trans (by rw [H.theta_K_eq]; exact inf_le_right)
  have hvan := vanishing_centralizes_invariant_two_subgroups H.prime
    (sectionTenSetup_vanishing H.config.setup) H.config.A_elem H.config.A_card H.b_mem_A
    H.witness.b_ne_one hSb H.witness.S_two H.witness.S_norm
  have hle : ⁅S, Subgroup.zpowers c⁆ ≤ ⁅S, A⁆ :=
    Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr H.config.c_mem)
  apply H.witness.S_ne_bot
  rw [eq_bot_iff]
  calc S = ⁅S, Subgroup.zpowers c⁆ := H.witness.S_comm
    _ ≤ ⁅S, A⁆ := hle
    _ = ⊥ := hvan
    _ ≤ ⊥ := le_rfl

theorem card_A : Nat.card A = 7 ^ 3 := by
  have := H.config.A_card
  rwa [H.p_eq] at this

theorem orderOf_b : orderOf b = 7 := by
  have : Fact p.Prime := ⟨H.prime⟩
  have := orderOf_eq_prime H.b_pow H.witness.b_ne_one
  rwa [H.p_eq] at this

end Branch

theorem card_eq_and_le_sup {A D : Subgroup G} {b a' c : G} (hA : Nat.card A = 7 ^ 3)
    (hDA : D ≤ A) (hb : b ∈ D) (hbord : orderOf b = 7) (ha' : a' ∈ D)
    (ha'b : a' ∉ Subgroup.zpowers b) (hcA : c ∈ A) (hc : c ∉ D) :
    Nat.card D = 49 ∧ A ≤ D ⊔ Subgroup.zpowers c := by
  have hdvd : Nat.card D ∣ 7 ^ 3 := hA ▸ Subgroup.card_dvd_of_le hDA
  obtain ⟨k, hk, hkD⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hdvd
  have hbD : Subgroup.zpowers b ≤ D := Subgroup.zpowers_le.mpr hb
  have hcb : Nat.card (Subgroup.zpowers b) = 7 := by rw [Nat.card_zpowers, hbord]
  have hD7 : 7 < Nat.card D := by
    by_contra hle
    push Not at hle
    have h := Subgroup.eq_of_le_of_card_ge hbD (by rw [hcb]; exact hle)
    apply ha'b
    rw [h]
    exact ha'
  have hDA' : Nat.card D ≠ 7 ^ 3 := by
    intro h
    have h' := Subgroup.eq_of_le_of_card_ge hDA (by rw [h, hA])
    apply hc
    rw [h']
    exact hcA
  have hcard : Nat.card D = 49 := by
    interval_cases k
    · simp only [pow_zero] at hkD
      omega
    · simp only [pow_one] at hkD
      omega
    · simpa using hkD
    · exact absurd hkD hDA'
  refine ⟨hcard, ?_⟩
  have hWA : D ⊔ Subgroup.zpowers c ≤ A := sup_le hDA (Subgroup.zpowers_le.mpr hcA)
  have hDW : D ≤ D ⊔ Subgroup.zpowers c := le_sup_left
  have hdvd' : Nat.card ↥(D ⊔ Subgroup.zpowers c) ∣ 7 ^ 3 := hA ▸ Subgroup.card_dvd_of_le hWA
  obtain ⟨k', hk', hkW⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hdvd'
  have h49 : 49 ∣ Nat.card ↥(D ⊔ Subgroup.zpowers c) := hcard ▸ Subgroup.card_dvd_of_le hDW
  have hWD : D ⊔ Subgroup.zpowers c ≠ D := fun h => hc (by
    rw [← h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hk3 : k' = 3 := by
    interval_cases k'
    · simp only [pow_zero] at hkW
      omega
    · simp only [pow_one] at hkW
      omega
    · exfalso
      apply hWD
      refine (Subgroup.eq_of_le_of_card_ge hDW ?_).symm
      rw [hcard, hkW]
      norm_num
    · rfl
  have hcardA : Nat.card A ≤ Nat.card ↥(D ⊔ Subgroup.zpowers c) := by rw [hA, hkW, hk3]
  exact (Subgroup.eq_of_le_of_card_ge hWA hcardA).ge

namespace Branch

variable {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ} {b : G} {S K K' : Subgroup G}
  {a' : G} (H : Branch p A c L B n b S K K' a')

include H

theorem a'_notMem_zpowers_b : a' ∉ Subgroup.zpowers b := fun h =>
  H.a'_notMem ((Subgroup.zpowers_le.mpr H.witness.b_mem) h)

theorem card_D : Nat.card (thetaQuotientCentralizer p A K) = 49 :=
  (card_eq_and_le_sup H.card_A (thetaQuotientCentralizer_le p A K) H.b_mem_D H.orderOf_b
    H.a'_mem_D H.a'_notMem_zpowers_b H.config.c_mem H.c_notMem_D).1

theorem A_le_D_sup : A ≤ thetaQuotientCentralizer p A K ⊔ Subgroup.zpowers c :=
  (card_eq_and_le_sup H.card_A (thetaQuotientCentralizer_le p A K) H.b_mem_D H.orderOf_b
    H.a'_mem_D H.a'_notMem_zpowers_b H.config.c_mem H.c_notMem_D).2

theorem D_centralizes (hq : CFSG.IsQuasisimple K) :
    ∀ d ∈ thetaQuotientCentralizer p A K, ∀ k ∈ K, d * k = k * d :=
  centralizes_of_commutator_mem_theta H.prime hq
    (fun _ hd => (mem_thetaQuotientCentralizer_iff.mp hd).2.1)
    (fun _ hd k hk => (mem_thetaQuotientCentralizer_iff.mp hd).2.2 k hk)

theorem commute_A_of_mem_K (hq : CFSG.IsQuasisimple K) {y : G} (hy : y ∈ K)
    (hyc : y * c = c * y) : ∀ a ∈ A, y * a = a * y := by
  have hle : A ≤ Subgroup.centralizer ({y} : Set G) := by
    refine H.A_le_D_sup.trans (sup_le (fun d hd => ?_) ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact H.D_centralizes hq d hd y hy
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hyc.symm
  intro a ha
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha)).symm

end Branch

end CFSG.RankThree.PartOne.MB3
