module

public import CFSG.RankThree.PartOne.S12.Sec15Lemmas

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace Sec159Aut

theorem orderOf_perm_four_le (σ : Equiv.Perm (Fin 4)) : orderOf σ ≤ 4 := by
  have h : ∀ τ : Equiv.Perm (Fin 4), τ ^ 4 = 1 ∨ τ ^ 3 = 1 := by decide +kernel
  rcases h σ with h4 | h3
  · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)).trans (by norm_num)

theorem card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

variable {G : Type} [Group G]

theorem fixes_of_mem_torusImage {E X : Subgroup G} {b : G} (hbE : b ∈ E)
    (hbX : ∀ y ∈ X, b * y = y * b) {φ : MulAut E} (hφ : φ ∈ torusImage E X) :
    φ ⟨b, hbE⟩ = ⟨b, hbE⟩ := by
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hφ
  have hnX : (n : G) ∈ X := Subgroup.mem_subgroupOf.1 hn
  apply Subtype.ext
  show (n : G) * b * (n : G)⁻¹ = b
  rw [← hbX n hnX]
  group

theorem torusImage_bound {p : ℕ} (hp : p.Prime) {E X : Subgroup G} [Finite G]
    (hEexp : ∀ e ∈ E, e ^ p = 1) {b : G} (hbE : b ∈ E) (hb1 : b ≠ 1)
    (hbX : ∀ y ∈ X, b * y = y * b) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hW4 : Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4))) :
    Nat.card ↥(torusImage E X) ∣ 24 ∧ ∀ g ∈ torusImage E X, orderOf g ≤ 4 := by
  classical
  obtain ⟨-, -, -, hsup, hinf, hscal⟩ := hW
  obtain ⟨e₄⟩ := hW4
  set Wt : Subgroup (MulAut E) := torusWeyl E with hWt
  set Zq : Subgroup ↥Wt := Subgroup.center ↥Wt with hZq
  set Zc : Subgroup (MulAut E) := Zq.map Wt.subtype with hZc
  set T : Subgroup (MulAut E) := torusImage E X with hT
  have hTle : T ≤ Wt := Subgroup.map_le_range _ _
  have hW0le : W₀ ≤ Wt := hsup ▸ le_sup_right
  have hfix : ∀ φ ∈ T, φ ⟨b, hbE⟩ = ⟨b, hbE⟩ := fun φ hφ => fixes_of_mem_torusImage hbE hbX hφ
  have hbord : orderOf b = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime (hEexp b hbE) hb1
  have hTZ : ∀ φ ∈ T, φ ∈ Zc → φ = 1 := by
    intro φ hφT hφZ
    obtain ⟨z, hz, rfl⟩ := hφZ
    obtain ⟨k, hk⟩ := hscal z hz
    have h2 : (z : MulAut ↥E) ⟨b, hbE⟩ = ⟨b, hbE⟩ := hfix _ hφT
    have hbk : b ^ k = b := by
      have h1 := hk ⟨b, hbE⟩
      rw [h2] at h1
      have h4 := congrArg Subtype.val h1
      simpa using h4.symm
    have hpk : (p : ℤ) ∣ k - 1 := by
      rw [← hbord, orderOf_dvd_iff_zpow_eq_one, zpow_sub, hbk]
      simp
    obtain ⟨m, hm⟩ := hpk
    have hk' : k = 1 + p * m := by linarith
    apply MulEquiv.ext
    intro e
    show (z : MulAut ↥E) e = e
    have hep : e ^ (p : ℤ) = 1 := by
      rw [zpow_natCast]; exact Subtype.ext (hEexp e e.2)
    rw [hk e, hk', zpow_add, zpow_one, zpow_mul, hep]
    simp
  set W0 : Subgroup ↥Wt := W₀.subgroupOf Wt with hW0
  set TQ : Subgroup ↥Wt := T.subgroupOf Wt with hTQ
  have hsupQ : Zq ⊔ W0 = ⊤ := by
    rw [eq_top_iff]
    intro q _
    have hq : q.1 ∈ (Zq ⊔ W0).map Wt.subtype := by
      rw [Subgroup.map_sup, ← hZc, hW0, Subgroup.subgroupOf_map_subtype, inf_of_le_left hW0le,
        ← hsup]
      exact q.2
    obtain ⟨q', hq', hq'q⟩ := hq
    have : q' = q := Subtype.ext hq'q
    exact this ▸ hq'
  have hinfQ : ∀ w : ↥Wt, w ∈ Zq → w ∈ W0 → w = 1 := by
    intro w hwZ hwW
    have h1 : w.1 ∈ Zc ⊓ W₀ := ⟨⟨w, hwZ, rfl⟩, Subgroup.mem_subgroupOf.1 hwW⟩
    rw [hinf, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hinj0 : Function.Injective ((QuotientGroup.mk' Zq).comp W0.subtype) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hw1 : (w : ↥Wt) ∈ Zq := (QuotientGroup.eq_one_iff (w : ↥Wt)).1 hw
    exact Subtype.ext (hinfQ w hw1 w.2)
  have hsurj0 : Function.Surjective ((QuotientGroup.mk' Zq).comp W0.subtype) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H q =>
      have hq : q ∈ Zq ⊔ W0 := hsupQ ▸ Subgroup.mem_top q
      obtain ⟨z, hz, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hq
      refine ⟨⟨w, hw⟩, ?_⟩
      have hz1 : (QuotientGroup.mk' Zq) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
      show (QuotientGroup.mk' Zq) w = (QuotientGroup.mk' Zq) (z * w)
      rw [map_mul, hz1, one_mul]
  let e₀ : ↥W0 ≃* (↥Wt ⧸ Zq) := MulEquiv.ofBijective _ ⟨hinj0, hsurj0⟩
  let ρT : ↥TQ →* (↥Wt ⧸ Zq) := (QuotientGroup.mk' Zq).comp TQ.subtype
  have hρT : Function.Injective ρT := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have ht1 : (t : ↥Wt) ∈ Zq := (QuotientGroup.eq_one_iff (t : ↥Wt)).1 ht
    have h1 : ((t : ↥Wt) : MulAut ↥E) = 1 :=
      hTZ _ (Subgroup.mem_subgroupOf.1 t.2) ⟨t, ht1, rfl⟩
    exact Subtype.ext (Subtype.ext h1)
  let F : ↥TQ →* Equiv.Perm (Fin 4) :=
    e₄.toMonoidHom.comp ((Subgroup.subgroupOfEquivOfLe hW0le).toMonoidHom.comp
      (e₀.symm.toMonoidHom.comp ρT))
  have hF : Function.Injective F := by
    refine e₄.injective.comp ((Subgroup.subgroupOfEquivOfLe hW0le).injective.comp
      (e₀.symm.injective.comp hρT))
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.card_dvd_of_injective F hF
    rw [card_perm_four] at h1
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
  · intro g hg
    let t : ↥TQ := ⟨⟨g, hTle hg⟩, Subgroup.mem_subgroupOf.2 hg⟩
    have h1 : orderOf g = orderOf t := by
      have e1 : orderOf ((t : ↥Wt) : MulAut ↥E) = orderOf (t : ↥Wt) := Subgroup.orderOf_coe _
      have e2 : orderOf (t : ↥Wt) = orderOf t := Subgroup.orderOf_coe _
      rw [← e2, ← e1]
    rw [h1, ← orderOf_injective F hF t]
    exact orderOf_perm_four_le _

theorem weyl_hom {p : ℕ} {E : Subgroup G} [Finite G] {W₀ : Subgroup (MulAut E)}
    (hW : Weyl154 p E W₀) (hW4 : Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4))) :
    ∃ Φ : ↥(torusWeyl E) →* Equiv.Perm (Fin 4),
      ∀ w : ↥(torusWeyl E), Φ w = 1 ↔ w ∈ Subgroup.center ↥(torusWeyl E) := by
  classical
  obtain ⟨-, -, -, hsup, hinf, -⟩ := hW
  obtain ⟨e₄⟩ := hW4
  set Wt : Subgroup (MulAut E) := torusWeyl E with hWt
  set Zq : Subgroup ↥Wt := Subgroup.center ↥Wt with hZq
  set Zc : Subgroup (MulAut E) := Zq.map Wt.subtype with hZc
  have hW0le : W₀ ≤ Wt := hsup ▸ le_sup_right
  set W0 : Subgroup ↥Wt := W₀.subgroupOf Wt with hW0
  have hsupQ : Zq ⊔ W0 = ⊤ := by
    rw [eq_top_iff]
    intro q _
    have hq : q.1 ∈ (Zq ⊔ W0).map Wt.subtype := by
      rw [Subgroup.map_sup, ← hZc, hW0, Subgroup.subgroupOf_map_subtype, inf_of_le_left hW0le,
        ← hsup]
      exact q.2
    obtain ⟨q', hq', hq'q⟩ := hq
    have : q' = q := Subtype.ext hq'q
    exact this ▸ hq'
  have hinfQ : ∀ w : ↥Wt, w ∈ Zq → w ∈ W0 → w = 1 := by
    intro w hwZ hwW
    have h1 : w.1 ∈ Zc ⊓ W₀ := ⟨⟨w, hwZ, rfl⟩, Subgroup.mem_subgroupOf.1 hwW⟩
    rw [hinf, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hinj0 : Function.Injective ((QuotientGroup.mk' Zq).comp W0.subtype) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hw1 : (w : ↥Wt) ∈ Zq := (QuotientGroup.eq_one_iff (w : ↥Wt)).1 hw
    exact Subtype.ext (hinfQ w hw1 w.2)
  have hsurj0 : Function.Surjective ((QuotientGroup.mk' Zq).comp W0.subtype) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H q =>
      have hq : q ∈ Zq ⊔ W0 := hsupQ ▸ Subgroup.mem_top q
      obtain ⟨z, hz, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hq
      refine ⟨⟨w, hw⟩, ?_⟩
      have hz1 : (QuotientGroup.mk' Zq) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
      show (QuotientGroup.mk' Zq) w = (QuotientGroup.mk' Zq) (z * w)
      rw [map_mul, hz1, one_mul]
  let e₀ : ↥W0 ≃* (↥Wt ⧸ Zq) := MulEquiv.ofBijective _ ⟨hinj0, hsurj0⟩
  let Φ : ↥Wt →* Equiv.Perm (Fin 4) :=
    e₄.toMonoidHom.comp ((Subgroup.subgroupOfEquivOfLe hW0le).toMonoidHom.comp
      (e₀.symm.toMonoidHom.comp (QuotientGroup.mk' Zq)))
  refine ⟨Φ, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · have h1 : (Subgroup.subgroupOfEquivOfLe hW0le) (e₀.symm (QuotientGroup.mk' Zq w)) = 1 :=
      e₄.injective (by simpa [Φ] using hw)
    have h2 : e₀.symm (QuotientGroup.mk' Zq w) = 1 :=
      (Subgroup.subgroupOfEquivOfLe hW0le).injective (by simpa using h1)
    have h3 : QuotientGroup.mk' Zq w = 1 := by
      have := congrArg e₀ h2
      simpa using this
    exact (QuotientGroup.eq_one_iff w).1 h3
  · have h1 : QuotientGroup.mk' Zq w = 1 := (QuotientGroup.eq_one_iff w).2 hw
    have h2 : Φ w = e₄ ((Subgroup.subgroupOfEquivOfLe hW0le) (e₀.symm (QuotientGroup.mk' Zq w))) := rfl
    rw [h2, h1]
    simp

theorem centralizes_of_pPower {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E : Subgroup G} [Finite G]
    (hEexp : ∀ e ∈ E, e ^ p = 1) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hW4 : Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4))) {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) {k : ℕ} (hgk : g ^ (p ^ k) = 1) :
    ∀ e ∈ E, g * e = e * g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Φ, hΦ⟩ := weyl_hom hW hW4
  obtain ⟨-, -, -, -, -, hscal⟩ := hW
  set φ : MulAut ↥E := E.normalizerMonoidHom ⟨g, hg⟩ with hφ
  have hφW : φ ∈ torusWeyl E := ⟨⟨g, hg⟩, rfl⟩
  have hφk : φ ^ (p ^ k) = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨g, hg⟩ : ↥(Subgroup.normalizer (E : Set G))) ^ (p ^ k) = 1 := Subtype.ext hgk
    rw [this, map_one]
  set w : ↥(torusWeyl E) := ⟨φ, hφW⟩ with hw
  have hwk : w ^ (p ^ k) = 1 := Subtype.ext hφk
  have hΦw : Φ w = 1 := by
    have h1 : (Φ w) ^ (p ^ k) = 1 := by rw [← map_pow, hwk, map_one]
    have h2 : orderOf (Φ w) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h2
    have h3 : orderOf (Φ w) ≤ 4 := orderOf_perm_four_le _
    have hj0 : j = 0 := by
      by_contra hj0
      have h5 : p ^ 1 ≤ p ^ j := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.2 hj0)
      rw [pow_one] at h5
      rw [hj] at h3
      omega
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.1 hj
  have hwc : w ∈ Subgroup.center ↥(torusWeyl E) := (hΦ w).1 hΦw
  obtain ⟨m, hm⟩ := hscal w hwc
  have hpowφ : ∀ (n : ℕ) (x : ↥E), (φ ^ n) x = x ^ (m ^ n) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      have h1 : (φ ^ (n + 1)) x = (φ ^ n) (φ x) := by rw [pow_succ]; rfl
      have h2 : φ x = x ^ m := hm x
      rw [h1, h2, map_zpow, ih, ← zpow_mul, pow_succ, mul_comm]
  intro e he
  by_cases he1 : e = 1
  · rw [he1]; simp
  · set x : ↥E := ⟨e, he⟩ with hx
    have hx1 : x ≠ 1 := fun h => he1 (congrArg Subtype.val h)
    have hxord : orderOf x = p := orderOf_eq_prime (Subtype.ext (hEexp e he)) hx1
    have hfix : x ^ (m ^ (p ^ k)) = x := by rw [← hpowφ, hφk]; rfl
    have hdvd' : (orderOf x : ℤ) ∣ m ^ (p ^ k) - 1 := by
      rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, hfix]
      simp
    have hdvd : (p : ℤ) ∣ m ^ (p ^ k) - 1 := by rwa [hxord] at hdvd'
    have h1 : ((m ^ (p ^ k) - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
    push_cast at h1
    rw [ZMod.pow_card_pow] at h1
    have hm1 : (p : ℤ) ∣ m - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact h1
    have hxm : x ^ m = x := by
      have hm1' : (orderOf x : ℤ) ∣ m - 1 := by rwa [hxord]
      have := (orderOf_dvd_iff_zpow_eq_one.1 hm1')
      rw [zpow_sub, zpow_one, mul_inv_eq_one] at this
      exact this
    have hφx : φ x = x := by rw [hm x, hxm]
    have h2 := congrArg Subtype.val hφx
    have h3 : g * e * g⁻¹ = e := h2
    calc g * e = g * e * g⁻¹ * g := by group
      _ = e * g := by rw [h3]

end Sec159Aut

end CFSG.RankThree.PartOne
