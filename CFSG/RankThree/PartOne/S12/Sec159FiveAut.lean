module

public import CFSG.RankThree.PartOne.S12.Sec159Aut

public section

namespace CFSG.RankThree.PartOne

open CFSG

namespace Sec159Aut

variable {G : Type} [Group G]

theorem torusImage_bound_gen {p : ℕ} (hp : p.Prime) {E X : Subgroup G} [Finite G]
    (hEexp : ∀ e ∈ E, e ^ p = 1) {b : G} (hbE : b ∈ E) (hb1 : b ≠ 1)
    (hbX : ∀ y ∈ X, b * y = y * b) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    {ι : Type} [Group ι] {m B : ℕ} (hW4 : Nonempty (↥W₀ ≃* ι)) (hcard : Nat.card ι ∣ m)
    (hord : ∀ σ : ι, orderOf σ ≤ B) :
    Nat.card ↥(torusImage E X) ∣ m ∧ ∀ g ∈ torusImage E X, orderOf g ≤ B := by
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
  let F : ↥TQ →* ι :=
    e₄.toMonoidHom.comp ((Subgroup.subgroupOfEquivOfLe hW0le).toMonoidHom.comp
      (e₀.symm.toMonoidHom.comp ρT))
  have hF : Function.Injective F := by
    refine e₄.injective.comp ((Subgroup.subgroupOfEquivOfLe hW0le).injective.comp
      (e₀.symm.injective.comp hρT))
  refine ⟨?_, ?_⟩
  · have h1 := Subgroup.card_dvd_of_injective F hF
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact h1.trans hcard
  · intro g hg
    let t : ↥TQ := ⟨⟨g, hTle hg⟩, Subgroup.mem_subgroupOf.2 hg⟩
    have h1 : orderOf g = orderOf t := by
      have e1 : orderOf ((t : ↥Wt) : MulAut ↥E) = orderOf (t : ↥Wt) := Subgroup.orderOf_coe _
      have e2 : orderOf (t : ↥Wt) = orderOf t := Subgroup.orderOf_coe _
      rw [← e2, ← e1]
    rw [h1, ← orderOf_injective F hF t]
    exact hord _

theorem orderOf_perm_five_le (σ : Equiv.Perm (Fin 5)) : orderOf σ ≤ 6 := by
  have h : ∀ τ : Equiv.Perm (Fin 5), τ ^ 4 = 1 ∨ τ ^ 3 = 1 ∨ τ ^ 5 = 1 ∨ τ ^ 6 = 1 := by
    decide +kernel
  rcases h σ with h4 | h3 | h5 | h6
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)).trans (by norm_num)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3)).trans (by norm_num)
  · exact (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h5)).trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h6)

theorem card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem torusImage_bound120 {p : ℕ} (hp : p.Prime) {E X : Subgroup G} [Finite G]
    (hEexp : ∀ e ∈ E, e ^ p = 1) {b : G} (hbE : b ∈ E) (hb1 : b ≠ 1)
    (hbX : ∀ y ∈ X, b * y = y * b) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hW45 : Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∨ Nonempty (↥W₀ ≃* Equiv.Perm (Fin 5))) :
    Nat.card ↥(torusImage E X) ∣ 120 ∧ ∀ g ∈ torusImage E X, orderOf g ≤ 6 := by
  rcases hW45 with h4 | h5
  · have := torusImage_bound_gen hp hEexp hbE hb1 hbX hW h4 (m := 24) (B := 4)
      (by rw [card_perm_four]) orderOf_perm_four_le
    exact ⟨this.1.trans (by norm_num), fun g hg => (this.2 g hg).trans (by norm_num)⟩
  · exact torusImage_bound_gen hp hEexp hbE hb1 hbX hW h5 (m := 120) (B := 6)
      (by rw [card_perm_five]) orderOf_perm_five_le

end Sec159Aut

end CFSG.RankThree.PartOne
