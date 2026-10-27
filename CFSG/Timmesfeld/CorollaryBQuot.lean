module

public import CFSG.Timmesfeld.CorollaryBOpp
public import CFSG.Timmesfeld.CorollaryBClass
public import CFSG.Timmesfeld.Bridge.RootSetsSolv
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.Timmesfeld.CorB

open Subgroup

section Quotient

variable {G : Type*} [Group G] {D : Set G}
  (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
  (hgen : closure D = ⊤) (hsq : ∀ d ∈ D, ∀ e ∈ D, Commute d e → d ≠ e → d * e ∈ D)
  (hopp : ∃ d ∈ D, ∃ e ∈ D, ¬ Commute d e ∧ Odd (orderOf (d * e)))

local notation "π" => QuotientGroup.mk' (center G)

include hclass hopp in
theorem not_mem_center {d : G} (hd : d ∈ D) : d ∉ center G := by
  intro hc
  obtain ⟨d₀, rfl⟩ := hclass
  have key : ∀ e ∈ {g | IsConj d₀ g}, e = d := by
    intro e he
    obtain ⟨c, rfl⟩ := isConj_iff.mp ((isConj_comm.mp hd).trans he)
    rw [mem_center_iff.mp hc c, mul_inv_cancel_right]
  obtain ⟨a, ha, b, hb, hab, -⟩ := hopp
  exact hab (by rw [key a ha, key b hb])

include hclass hD hsq hopp in
theorem eq_of_mk_eq {d e : G} (hd : d ∈ D) (he : e ∈ D) (hde : π d = π e) : d = e := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hde
  set c := d⁻¹ * e with hc
  have hec : e = d * c := by rw [hc, mul_inv_cancel_left]
  by_contra hne
  have hcomm : Commute d e := by
    rw [hec]
    exact (Commute.refl d).mul_right ((mem_center_iff.mp hde d))
  have hmem := hsq d hd e he hcomm hne
  rw [hec, ← mul_assoc, hD.mul_self_eq_one hd, one_mul] at hmem
  exact not_mem_center hclass hopp hmem hde

include hclass hD hopp in
theorem commute_of_commute_mk {d e : G} (hd : d ∈ D) (he : e ∈ D) (hde : Commute (π d) (π e)) :
    Commute d e := by
  have hd2 := hD.mul_self_eq_one hd
  have he2 := hD.mul_self_eq_one he
  have hsq2 : (d * e) ^ 2 ∈ center G := by
    have h1 : π ((d * e) ^ 2) = 1 := by
      rw [map_pow, map_mul, ← (commute_iff_mul_sq_eq_one (by rw [← map_mul, hd2, map_one])
        (by rw [← map_mul, he2, map_one])).mp hde]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rcases hD.orderOf_mul hd he with h2 | h4 | hodd
  · exact (commute_iff_mul_sq_eq_one hd2 he2).mpr (by rw [← h2, pow_orderOf_eq_one])
  · exact absurd hsq2 (not_mem_center hclass hopp (hD.sq_mem hd he h4))
  ·
    obtain ⟨k, hk⟩ := hodd
    have hpow : ((d * e) ^ 2) ^ (k + 1) = d * e := by
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
        pow_orderOf_eq_one, one_mul]
    have hc : d * e ∈ center G := hpow ▸ pow_mem hsq2 (k + 1)
    have hde' : d * (d * e) = d * e * d := mem_center_iff.mp hc d
    have : e = d * e * d := by rw [← hde', ← mul_assoc, hd2, one_mul]
    change d * e = e * d
    calc d * e = d * (d * e * d) := by rw [← this]
      _ = e * d := by rw [← mul_assoc, ← mul_assoc, hd2, one_mul]

include hclass hD hgen hsq hopp in
theorem center_quotient_eq_bot : center (G ⧸ center G) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center G) y
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine mem_center_of_forall_commute hgen fun d hd => ?_
  have hxd : x * d * x⁻¹ ∈ D := by
    obtain ⟨d₀, rfl⟩ := hclass
    exact hd.trans (isConj_iff.mpr ⟨x, rfl⟩)
  have heq : π (x * d * x⁻¹) = π d := by
    rw [map_mul, map_mul, map_inv, (mem_center_iff.mp hy (π d)).symm, mul_inv_cancel_right]
  have := eq_of_mk_eq hclass hD hsq hopp hxd hd heq
  change x * d = d * x
  calc x * d = x * d * x⁻¹ * x := by group
    _ = d * x := by rw [this]

include hclass hD hsq hopp in
theorem mul_mem_mk {d e : G} (hd : d ∈ D) (he : e ∈ D) (hde : Commute (π d) (π e))
    (hne : π d ≠ π e) : π d * π e ∈ π '' D :=
  ⟨d * e, hsq d hd e he (commute_of_commute_mk hclass hD hopp hd he hde)
    (fun h => hne (by rw [h])), map_mul _ _ _⟩

include hclass hD hgen hsq hopp in
theorem hyp_quotient_center [Finite G] (hpair : ∃ d ∈ D, ∃ e ∈ D, d ≠ e ∧ Commute d e)
    (h4 : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    Hyp (G ⧸ center G) (π '' D) := by
  have hZ := center_quotient_eq_bot hclass hD hgen hsq hopp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hclass' : ∃ d₀ : G ⧸ center G, π '' D = {g | IsConj d₀ g} := by
    obtain ⟨d₀, rfl⟩ := hclass
    refine ⟨π d₀, ?_⟩
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := isConj_iff.mp hx
      exact isConj_iff.mpr ⟨π c, by rw [map_mul, map_mul, map_inv]⟩
    · intro hy
      obtain ⟨c, rfl⟩ := isConj_iff.mp hy
      obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (center G) c
      exact ⟨c' * d₀ * c'⁻¹, isConj_iff.mpr ⟨c', rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
  have hinv : ∀ d ∈ D, π d ≠ 1 := fun d hd h1 => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact not_mem_center hclass hopp hd h1
  have hord2 : ∀ d ∈ D, orderOf (π d) = 2 := fun d hd =>
    orderOf_eq_prime (by rw [← map_pow, pow_two, hD.mul_self_eq_one hd, map_one]) (hinv d hd)
  have hdvd : ∀ d e : G, orderOf (π d * π e) ∣ orderOf (d * e) := fun d e => by
    rw [← map_mul]
    exact orderOf_map_dvd _ _
  have hroot : IsRootInvolutionSet (π '' D) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩
      exact hord2 d hd
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
      have hdv := hdvd d e
      rcases hD.orderOf_mul hd he with h | h | h
      · rw [h] at hdv
        rcases (Nat.dvd_prime Nat.prime_two).mp hdv with h1 | h1
        · exact Or.inr (Or.inr (by rw [h1]; exact odd_one))
        · exact Or.inl h1
      · rw [h] at hdv
        have hle := Nat.le_of_dvd (by norm_num) hdv
        interval_cases hk : orderOf (π d * π e)
        · exact absurd hdv (by norm_num)
        · exact Or.inr (Or.inr odd_one)
        · exact Or.inl rfl
        · exact absurd hdv (by norm_num)
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Odd.of_dvd_nat h hdv))
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ h4'
      have hdv := hdvd d e
      rw [h4'] at hdv
      have h4 : orderOf (d * e) = 4 := by
        rcases hD.orderOf_mul hd he with h | h | h
        · rw [h] at hdv
          exact absurd hdv (by norm_num)
        · exact h
        · exact absurd (Odd.of_dvd_nat h hdv) (by decide)
      exact ⟨(d * e) ^ 2, hD.sq_mem hd he h4, by rw [map_pow, map_mul]⟩
  have hgen' : closure (π '' D) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  refine ⟨inferInstance, hclass', hroot, hgen', ?_, ?_, ?_⟩
  ·
    intro N hN hodd
    obtain ⟨d, hd, e, he, hne, hde⟩ := hpair
    have hle := Bridge.le_center_of_odd_card hclass' hroot hgen' (u₁ := π d) (u₂ := π e)
      ⟨d, hd, rfl⟩ ⟨e, he, rfl⟩ (fun h => hne (eq_of_mk_eq hclass hD hsq hopp hd he h))
      (hde.map π) ⟨d * e, hsq d hd e he hde hne, map_mul _ _ _⟩ hN hodd
    rw [hZ] at hle
    exact le_bot_iff.mp hle
  ·
    intro N hN h2
    have hnot : ∀ d ∈ D, π d ∉ N := by
      intro d hd hdN
      obtain ⟨a, ha, b, hb, hab, hodd⟩ := id hopp
      have haN : π a ∈ N := by
        obtain ⟨d₀, rfl⟩ := hclass
        obtain ⟨c, rfl⟩ := isConj_iff.mp ((isConj_comm.mp hd).trans ha)
        rw [map_mul, map_mul, map_inv]
        exact hN.conj_mem _ hdN _
      have hbN : π b ∈ N := by
        obtain ⟨d₀, rfl⟩ := hclass
        obtain ⟨c, rfl⟩ := isConj_iff.mp ((isConj_comm.mp hd).trans hb)
        rw [map_mul, map_mul, map_inv]
        exact hN.conj_mem _ hdN _
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨_, N.mul_mem haN hbN⟩
      rw [Subgroup.orderOf_mk] at hk
      have hodd' : Odd (orderOf (π a * π b)) := Odd.of_dvd_nat hodd (hdvd a b)
      have hk0 : k = 0 := by
        by_contra hk0
        rw [hk] at hodd'
        exact (Nat.not_even_iff_odd.mpr hodd') ((Nat.even_pow' hk0).mpr even_two)
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      have hab' : π a = π b := by
        rw [eq_inv_of_mul_eq_one_left hk, ← map_inv, hD.inv_eq hb]
      exact hab (eq_of_mk_eq hclass hD hsq hopp ha hb hab' ▸ Commute.refl a)
    have hcomm : ∀ n ∈ N, ∀ d ∈ D, Commute n (π d) := by
      intro n hn d hd
      obtain ⟨d₀, rfl⟩ := hclass
      set e := n⁻¹ * d * n⁻¹⁻¹
      obtain ⟨e', rfl⟩ := QuotientGroup.mk'_surjective (center G) n
      have he' : e' ⁻¹ * d * e'⁻¹⁻¹ ∈ {g | IsConj d₀ g} := hd.trans (isConj_iff.mpr ⟨e'⁻¹, rfl⟩)
      have hmemN : π d * π (e'⁻¹ * d * e'⁻¹⁻¹) ∈ N := by
        rw [map_mul, map_mul, map_inv, inv_inv]
        have h1 : π d * (π e')⁻¹ * (π d)⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hn) _
        have hdi : (π d)⁻¹ = π d := by rw [← map_inv, hD.inv_eq hd]
        rw [hdi] at h1
        rw [show π d * ((π e')⁻¹ * π d * π e') = π d * (π e')⁻¹ * π d * π e' by group]
        exact N.mul_mem h1 hn
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨_, hmemN⟩
      rw [Subgroup.orderOf_mk] at hk
      by_cases h1 : π d * π (e'⁻¹ * d * e'⁻¹⁻¹) = 1
      ·
        have h3 : π (e'⁻¹ * d * e'⁻¹⁻¹) = π d := by
          rw [eq_inv_of_mul_eq_one_right h1, ← map_inv, hD.inv_eq hd]
        rw [map_mul, map_mul, map_inv, inv_inv] at h3
        change π e' * π d = π d * π e'
        calc π e' * π d = π e' * ((π e')⁻¹ * π d * π e') := by rw [h3]
          _ = π d * π e' := by group
      · exfalso
        rcases hroot.orderOf_mul ⟨d, hd, rfl⟩ ⟨_, he', rfl⟩ with ho | ho | ho
        ·
          have hc : Commute (π d) (π (e'⁻¹ * d * e'⁻¹⁻¹)) :=
            (commute_iff_mul_sq_eq_one (by rw [← map_mul, hD.mul_self_eq_one hd, map_one])
              (by rw [← map_mul, hD.mul_self_eq_one he', map_one])).mpr
              (by rw [← ho, pow_orderOf_eq_one])
          have hne : π d ≠ π (e'⁻¹ * d * e'⁻¹⁻¹) := fun h => h1 (by
            rw [← h, ← map_mul, hD.mul_self_eq_one hd, map_one])
          obtain ⟨f, hf, hfe⟩ := mul_mem_mk ⟨d₀, rfl⟩ hD hsq hopp hd he' hc hne
          exact hnot f hf (hfe ▸ hmemN)
        ·
          obtain ⟨f, hf, hfe⟩ := hroot.sq_mem ⟨d, hd, rfl⟩ ⟨_, he', rfl⟩ ho
          exact hnot f hf (hfe ▸ pow_mem hmemN 2)
        · rw [hk] at ho
          have hk0 : k = 0 := by
            by_contra hk0
            exact (Nat.not_even_iff_odd.mpr ho) ((Nat.even_pow' hk0).mpr even_two)
          rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
          exact h1 hk
    rw [eq_bot_iff, ← hZ]
    intro n hn
    rw [mem_center_iff]
    intro y
    have hy : y ∈ closure (π '' D) := hgen' ▸ mem_top y
    induction hy using closure_induction with
    | mem y hy =>
      obtain ⟨d, hd, rfl⟩ := hy
      exact (hcomm n hn d hd).symm.eq
    | one => rw [one_mul, mul_one]
    | mul x y _ _ hx hy => exact (Commute.mul_left (a := x) (b := y) (c := n) hx hy)
    | inv x _ hx => exact (Commute.inv_left (a := x) (b := n) hx).eq
  ·
    obtain ⟨d, hd, e, he, h4⟩ := h4
    refine ⟨π d, ⟨d, hd, rfl⟩, π e, ⟨e, he, rfl⟩, ?_⟩
    have hdv := hdvd d e
    rw [h4] at hdv
    have hsq' : (π d * π e) ^ 2 ≠ 1 := by
      rw [← map_mul, ← map_pow]
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact not_mem_center hclass hopp (hD.sq_mem hd he h4) h1
    have hle := Nat.le_of_dvd (by norm_num) hdv
    interval_cases hk : orderOf (π d * π e)
    · exact absurd hdv (by norm_num)
    · exact absurd (by rw [orderOf_eq_one_iff.mp hk, one_pow]) hsq'
    · exact absurd (by rw [← hk, pow_orderOf_eq_one]) hsq'
    · exact absurd hdv (by norm_num)
    · rfl

include hclass hD hopp in
theorem noOddCent_quotient_center
    (h2 : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, Commute x y → Commute x z → ∃ k : ℕ, orderOf (y * z) = 2 ^ k) :
    NoOddCent (π '' D) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hxy hxz hodd
  obtain ⟨k, hk⟩ := h2 x hx y hy z hz (commute_of_commute_mk hclass hD hopp hx hy hxy)
    (commute_of_commute_mk hclass hD hopp hx hz hxz)
  have hdv : orderOf (π y * π z) ∣ 2 ^ k := by
    rw [← hk, ← map_mul]
    exact orderOf_map_dvd _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdv
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hj0).mpr even_two)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  rw [eq_inv_of_mul_eq_one_left hj, ← map_inv, hD.inv_eq hz]

end Quotient

variable {X : Type*} [Group X] {t : X}

namespace Setup

variable [Finite X] (h : Setup t)
include h

theorem hyp_quotient (hpair : ∃ τ ∈ conjCent t, τ ≠ t)
    (h4 : ∃ d ∈ cls t, ∃ e ∈ cls t, orderOf (d * e) = 4) :
    Hyp (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))
      (QuotientGroup.mk' (center ↥(normalClosure ({t} : Set X))) '' clsIn t) := by
  have hopp := h.exists_opposite h4
  obtain ⟨d, hd, e, he, hde, hodd⟩ := hopp
  obtain ⟨τ, ⟨hτt, hτ⟩, hτne⟩ := hpair
  obtain ⟨a, ha, b, hb, hab⟩ := h4
  refine hyp_quotient_center ⟨tIn t, h.clsIn_eq ⟨d, hd, e, he, hde, hodd⟩⟩
    h.isRootInvolutionSet_clsIn (closure_clsIn t)
    (fun d hd e he hde hne => h.mul_mem_clsIn hd he hde hne)
    ⟨⟨d, cls_subset t hd⟩, hd, ⟨e, cls_subset t he⟩, he,
      fun hc => hde (commute_coe_iff.mpr hc), by rw [← Subgroup.orderOf_coe]; exact hodd⟩
    ⟨tIn t, tIn_mem_clsIn t, ⟨τ, cls_subset t hτ⟩, hτ,
      fun heq => hτne (congrArg Subtype.val heq).symm, commute_coe_iff.mp hτt.symm⟩
    ⟨⟨a, cls_subset t ha⟩, ha, ⟨b, cls_subset t hb⟩, hb, by
      rw [← Subgroup.orderOf_coe]; exact hab⟩

theorem noOddCent_quotient (h4 : ∃ d ∈ cls t, ∃ e ∈ cls t, orderOf (d * e) = 4) :
    NoOddCent (QuotientGroup.mk' (center ↥(normalClosure ({t} : Set X))) '' clsIn t) := by
  obtain ⟨d, hd, e, he, hde, hodd⟩ := h.exists_opposite h4
  exact noOddCent_quotient_center ⟨tIn t, h.clsIn_eq ⟨d, hd, e, he, hde, hodd⟩⟩
    h.isRootInvolutionSet_clsIn
    ⟨⟨d, cls_subset t hd⟩, hd, ⟨e, cls_subset t he⟩, he,
      fun hc => hde (commute_coe_iff.mpr hc), by rw [← Subgroup.orderOf_coe]; exact hodd⟩
    (fun x hx y hy z hz hxy hxz => h.exists_orderOf_eq_two_pow_clsIn hx hy hz hxy hxz)

end Setup

end CFSG.Timmesfeld.CorB
