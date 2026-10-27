module

public import CFSG.Quasithin.EmptyFaithful.Insp9Cases1
public import CFSG.Quasithin.EmptyFaithful.Insp9Psl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Insp9

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem case1_false (h : Data D₁ D₂ J N) (hc : pCoreOf 2 D₁ = ⊥) : False := by
  have := le_pCoreOf_of_le_normalizer 2 h.le h.norm h.pgrp
  rw [hc] at this
  exact h.J_ne_bot (le_bot_iff.mp this)

theorem eq_one_of_two_pow_of_orderOf_dvd_three {G : Type*} [Group G] {x : G}
    (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1) (h3 : orderOf x ∣ 3) : x = 1 := by
  obtain ⟨k, hk⟩ := h2
  have h1 : orderOf x ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) h3
  have hcop : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
  rw [hcop] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem Data.N_eq_top_of_hat (h : Data D₁ D₂ J N) {n : ℕ} (hH : F6.IsHatAlt n D) : N = ⊤ := by
  have hq : CFSG.IsQuasisimple D := isQuasisimple_of_open hH.1
  have := h.normal
  rcases qs_normal_le_center_or_top hq N with hc | hN
  · exfalso
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.J_ne_bot
    apply hx
    have hxc : (x : D) ∈ Subgroup.center D := hc (h.J_le_N x.2)
    have h3 : orderOf (⟨(x : D), hxc⟩ : Subgroup.center D) ∣ 3 := by
      have := orderOf_dvd_natCard (⟨(x : D), hxc⟩ : Subgroup.center D)
      rwa [hH.2.1] at this
    have h3' : orderOf (x : D) ∣ 3 := by
      have := h3
      rw [← Subgroup.orderOf_coe] at this
      simpa using this
    obtain ⟨k, hk⟩ := h.pgrp x
    have hk' : (x : D) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subtype.ext (eq_one_of_two_pow_of_orderOf_dvd_three ⟨k, hk'⟩ h3')
  · exact hN

theorem map_center_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    have := hx g'
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_mul, this]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    have := hy (e g)
    apply e.injective
    simpa using this

theorem isHatAlt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : F6.IsHatAlt n X) : F6.IsHatAlt n Y := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  have hq' : CFSG.Open.IsQuasisimple Y :=
    open_of_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_of_open hq))
  refine ⟨hq', ?_, ?_⟩
  · rw [← hc]
    rw [← map_center_mulEquiv e, Subgroup.card_map_of_injective e.injective]
  · exact ⟨(QuotientGroup.congr (Subgroup.center Y) (Subgroup.center X) e.symm
      (map_center_mulEquiv e.symm)).trans f⟩

noncomputable def topEquivOfEq (hN : N = ⊤) : ↥N ≃* D :=
  (MulEquiv.subgroupCongr hN).trans Subgroup.topEquiv

theorem case6hat (h : Data D₁ D₂ J N) (hH : F6.IsHatAlt 6 D) : InspGoal D N := by
  have hN := h.N_eq_top_of_hat hH
  right
  refine ⟨?_, by rw [hN]; exact le_top⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (isHatAlt_of_mulEquiv (topEquivOfEq hN).symm hH))))))

theorem case7alt (h : Data D₁ D₂ J N) (e : D ≃* alternatingGroup (Fin 7)) : InspGoal D N := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup D := e.isSimpleGroup
  have hN := h.N_eq_top_of_simple hs
  right
  refine ⟨?_, by rw [hN]; exact le_top⟩
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(topEquivOfEq hN).trans e⟩)))

omit [Finite D] in
theorem card_hatAlt {n : ℕ} (hH : F6.IsHatAlt n D) (hn : 2 ≤ n) :
    Nat.card D = 3 * (n.factorial / 2) := by
  obtain ⟨-, hc, ⟨f⟩⟩ := hH
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center D)
  rw [Nat.card_congr f.toEquiv, hc, card_alternatingGroup1527d n hn] at h1
  omega

theorem case7hat_false (h : Data D₁ D₂ J N) (hH : F6.IsHatAlt 7 D) (hs : B56Setting D N)
    (hT : Nat.card ↥(D₁ ⊓ D₂) = 8) : False := by
  have hN := h.N_eq_top_of_hat hH
  have hq : CFSG.IsQuasisimple ↥N := by
    have := isQuasisimple_of_open hH.1
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (topEquivOfEq hN).symm this
  have hql := hs.ql_of_quasisimple hq
  have hcard : Nat.card ↥N = 7560 := by
    rw [Nat.card_congr (topEquivOfEq hN).toEquiv, card_hatAlt hH (by norm_num)]
    simp [Nat.factorial]
  have h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N := by
    rw [Nat.card_congr (topEquivOfEq hN).toEquiv]
    exact fun hd => h.not_two_pow_dvd (k := 3) (by simpa using hT) (m := 4) (by norm_num)
      ((Nat.pow_dvd_pow 2 (by norm_num : 4 ≤ 8)).trans hd)
  have hord := b56QL_card_le7 hql h8
  rw [hcard] at hord
  revert hord
  decide +kernel

omit [Finite D] in
theorem not_comm_of_simple_two_mul [Finite D] (hs : IsSimpleGroup D) {q : ℕ} (hq : 5 ≤ q)
    (hodd : q % 2 = 1) (hcard : 2 * Nat.card D = q * (q ^ 2 - 1)) :
    ∃ a b : D, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative D := ⟨⟨fun a b => hcomm a b⟩⟩
  have hr : (Nat.card D).Prime := hs.prime_card
  obtain ⟨m, hm⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  have hm2 : 2 ≤ m := by omega
  have h1 : (2 * m + 1) ^ 2 - 1 = 4 * m ^ 2 + 4 * m := by
    have : (2 * m + 1) ^ 2 = (4 * m ^ 2 + 4 * m) + 1 := by ring
    omega
  rw [hm, h1] at hcard
  have hr2 : Nat.card D = 2 * (m * (m + 1) * (2 * m + 1)) := by nlinarith
  rw [hr2] at hr
  have hne : m * (m + 1) * (2 * m + 1) ≠ 1 := by
    have : 1 < m * (m + 1) * (2 * m + 1) := by nlinarith
    omega
  exact Nat.not_prime_mul (by norm_num) hne hr

theorem case6l2 (h : Data D₁ D₂ J N) (hs : B56Setting D N) {p e : ℕ} (hL2 : F6.IsL2 p e D)
    (hmod : p ^ e % 16 = 7 ∨ p ^ e % 16 = 9) (hT : Nat.card ↥(D₁ ⊓ D₂) = 8) : InspGoal D N := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have he : 1 ≤ e := hL2.1.2.1
    have : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    omega
  have hsimple := isSimpleGroup_psl_two hL2
  have hcard := two_mul_card_psl_two_pow hp2 hL2
  obtain ⟨q, hq⟩ : ∃ q, q = p ^ e := ⟨_, rfl⟩
  rw [← hq] at hcard hmod
  have hq5 : 5 ≤ q := by omega
  have hnc := not_comm_of_simple_two_mul hsimple hq5 (by omega) hcard
  have hN := h.N_eq_top_of_simple hsimple
  have hqs := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hqsN : CFSG.IsQuasisimple ↥N :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (topEquivOfEq hN).symm hqs
  have hql := hs.ql_of_quasisimple hqsN
  have h8 : ¬ 2 ^ 8 ∣ Nat.card ↥N := by
    rw [Nat.card_congr (topEquivOfEq hN).toEquiv]
    exact fun hd => h.not_two_pow_dvd (k := 3) (by simpa using hT) (m := 4) (by norm_num)
      ((Nat.pow_dvd_pow 2 (by norm_num : 4 ≤ 8)).trans hd)
  rcases inspList_or_bad hql h8 with hgood | hbad
  · exact Or.inr ⟨hgood, by rw [hN]; exact le_top⟩
  · exfalso
    rw [Nat.card_congr (topEquivOfEq hN).toEquiv] at hbad
    have hmem : q * (q ^ 2 - 1) ∈ badQL.image (2 * ·) := Finset.mem_image.mpr ⟨_, hbad, hcard⟩
    have hbound : ∀ x ∈ badQL.image (2 * ·), x ≤ 4194048 := by
      unfold badQL; decide +kernel
    have hle := hbound _ hmem
    have hq200 : q < 200 := by
      by_contra hcon
      have h1 : 200 ≤ q := by omega
      have h2 : 40000 ≤ q ^ 2 := by nlinarith
      have h3 : 39999 ≤ q ^ 2 - 1 := by omega
      have := Nat.mul_le_mul h1 h3
      omega
    have hdec : ∀ r ∈ Finset.range 200, (r % 16 = 7 ∨ r % 16 = 9) →
        r * (r ^ 2 - 1) ∉ badQL.image (2 * ·) := by
      unfold badQL; decide +kernel
    exact hdec q (Finset.mem_range.mpr hq200) hmod hmem

end Insp9

end CFSG.Quasithin
