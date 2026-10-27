module

public import CFSG.Timmesfeld.Bridge.RootSetsQuot
public import CFSG.Timmesfeld.Bridge.RootSetsRankGen
public import CFSG.Timmesfeld.Bridge.RootStructOD
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Timmesfeld.Exceptional.CaseIThm31
public import CFSG.Timmesfeld.Bridge.RootSetsSolv
public import CFSG.Timmesfeld.Closure.MinCex

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge

section TwoQuotient

variable {K : Type*} [Group K]

theorem orderOf_mk_eq_of_odd {P : Subgroup K} [P.Normal] (hP : IsPGroup 2 P) {g : K}
    (hg : Odd (orderOf g)) : orderOf (QuotientGroup.mk' P g) = orderOf g := by
  refine Nat.dvd_antisymm (orderOf_map_dvd _ g) ?_
  set k := orderOf (QuotientGroup.mk' P g)
  have hk : g ^ k ∈ P := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact pow_orderOf_eq_one _
  obtain ⟨n, hn⟩ := hP ⟨g ^ k, hk⟩
  have hn' : (g ^ k) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hodd : Odd (orderOf (g ^ k)) := hg.of_dvd_nat (orderOf_pow_dvd k)
  have h1 : orderOf (g ^ k) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hodd))
      (orderOf_dvd_of_pow_eq_one hn')
  exact orderOf_dvd_of_pow_eq_one (orderOf_eq_one_iff.1 h1)

theorem pCore_quotient_pCore_eq_bot : CFSG.pCore 2 (K ⧸ CFSG.pCore 2 K) = ⊥ := by
  set N : Subgroup K := CFSG.pCore 2 K with hN
  set M : Subgroup K := (CFSG.pCore 2 (K ⧸ N)).comap (QuotientGroup.mk' N) with hM
  have hMp : IsPGroup 2 M := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := K ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := K) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hMn : M.Normal := Subgroup.Normal.comap CFSG.pCore_normal _
  have hMN : M ≤ N := le_sSup ⟨hMn, hMp⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N y
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hMN hy

end TwoQuotient

section Class

variable {G : Type*} [Group G] {D : Set G}

@[expose] def subClass (X : Subgroup G) (x : G) : Set X := {y | (y : G) ∈ classIn X x}

@[expose] def barClass (X : Subgroup G) (x : G) : Set (X ⧸ CFSG.pCore 2 X) :=
  QuotientGroup.mk' (CFSG.pCore 2 X) '' subClass X x

theorem mem_subClass_self {X : Subgroup G} {x : G} (hxX : x ∈ X) :
    (⟨x, hxX⟩ : X) ∈ subClass X x :=
  mem_classIn_self X x

theorem subClass_eq {X : Subgroup G} {x : G} (hxX : x ∈ X) :
    subClass X x = {y | IsConj (⟨x, hxX⟩ : X) y} := by
  ext y
  constructor
  · rintro ⟨g, hg, hy⟩
    exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simp [hy])⟩
  · intro hy
    obtain ⟨g, hg⟩ := isConj_iff.1 hy
    refine ⟨g, g.2, ?_⟩
    rw [← hg]
    simp

theorem barClass_eq {X : Subgroup G} {x : G} (hxX : x ∈ X) :
    barClass X x = {y | IsConj (QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hxX⟩) y} := by
  ext y
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [subClass_eq hxX] at he
    exact (QuotientGroup.mk' _).map_isConj he
  · intro hy
    obtain ⟨c, hc⟩ := isConj_iff.1 hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ c
    refine ⟨g * ⟨x, hxX⟩ * g⁻¹, ?_, by rw [← hc]; simp⟩
    rw [subClass_eq hxX]
    exact isConj_iff.2 ⟨g, rfl⟩

theorem mem_of_mem_subClass (hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D) {X : Subgroup G} {x : G}
    (hx : x ∈ D) {y : X} (hy : y ∈ subClass X x) : (y : G) ∈ D :=
  classIn_subset_of_normal hN X hx hy

theorem closure_subClass_eq_top {X : Subgroup G} {x : G} {S : Set G}
    (hSX : S ⊆ classIn X x) (hX : X = Subgroup.closure S) :
    Subgroup.closure (subClass X x) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  have hg' : g ∈ Subgroup.closure S := hX ▸ hg
  induction hg' using Subgroup.closure_induction with
  | mem y hy =>
    exact Subgroup.subset_closure (show (⟨y, hX ▸ Subgroup.subset_closure hy⟩ : X) ∈
      subClass X x from hSX hy)
  | one => exact Subgroup.one_mem _
  | mul a b ha hb iha ihb =>
    exact Subgroup.mul_mem _ (iha (hX ▸ ha)) (ihb (hX ▸ hb))
  | inv a ha iha => exact Subgroup.inv_mem _ (iha (hX ▸ ha))

theorem not_mem_pCore_of_mem_subClass {X : Subgroup G} {x d : G} (hxX : x ∈ X) (hdX : d ∈ X)
    (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x)))
    (hgen : Subgroup.closure (subClass X x) = ⊤) {y : X} (hy : y ∈ subClass X x) :
    y ∉ CFSG.pCore 2 X := by
  intro hyP
  have hle : Subgroup.closure (subClass X x) ≤ CFSG.pCore 2 X := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [subClass_eq hxX] at hy hz
    obtain ⟨c, rfl⟩ := isConj_iff.1 (hy.symm.trans hz)
    exact CFSG.pCore_normal.conj_mem _ hyP c
  rw [hgen, top_le_iff] at hle
  have hP : IsPGroup 2 X := by
    intro g
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (G := X) (p := 2) ⟨g, hle ▸ Subgroup.mem_top g⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  obtain ⟨n, hn⟩ := hP (⟨d, hdX⟩ * ⟨x, hxX⟩)
  have hn' : (d * x) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 : orderOf (d * x) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hodd))
      (orderOf_dvd_of_pow_eq_one hn')
  apply hdx
  rw [orderOf_eq_one_iff] at h1
  rw [eq_inv_of_mul_eq_one_left h1]
  exact (Commute.refl x).inv_left

theorem isRootInvolutionSet_barClass [Finite G] (hD : IsRootInvolutionSet D)
    (hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D) {X : Subgroup G} {x d : G} (hx : x ∈ D)
    (hxX : x ∈ X) (hdX : d ∈ X) (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x)))
    (hgen : Subgroup.closure (subClass X x) = ⊤) : IsRootInvolutionSet (barClass X x) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hne1 : ∀ e ∈ subClass X x, π e ≠ 1 := fun e he h1 =>
    not_mem_pCore_of_mem_subClass hxX hdX hdx hodd hgen he ((QuotientGroup.eq_one_iff e).1 h1)
  have hmemD : ∀ e ∈ subClass X x, (e : G) ∈ D := fun e he => mem_of_mem_subClass hN hx he
  have hsq : ∀ e ∈ subClass X x, e * e = 1 := fun e he =>
    Subtype.ext (by simpa using hD.mul_self_eq_one (hmemD e he))
  have horder : ∀ e ∈ subClass X x, ∀ f ∈ subClass X x,
      orderOf (e * f) = 2 ∨ orderOf (e * f) = 4 ∨ Odd (orderOf (e * f)) := by
    intro e he f hf
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact hD.orderOf_mul (hmemD e he) (hmemD f hf)
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact orderOf_eq_prime (by rw [sq, ← map_mul, hsq e he, map_one]) (hne1 e he)
  · rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
    rw [← map_mul]
    have hdvd := orderOf_map_dvd π (e * f)
    rcases horder e he f hf with h2 | h4 | ho
    · rw [h2] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
      · right; right; rw [h1]; exact odd_one
      · left; exact h1
    · rw [h4] at hdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (show orderOf (π (e * f)) ∣ 2 ^ 2 from hdvd)
      interval_cases k
      · right; right; rw [hk']; exact odd_one
      · left; exact hk'
      · right; left; exact hk'
    · right; right; exact ho.of_dvd_nat hdvd
  · rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ h4
    rw [← map_mul] at h4
    have hdvd := orderOf_map_dvd π (e * f)
    rw [h4] at hdvd
    have h4' : orderOf (e * f) = 4 := by
      rcases horder e he f hf with h | h | h
      · rw [h] at hdvd
        exact absurd hdvd (by decide)
      · exact h
      · exact absurd (h.of_dvd_nat hdvd) (by decide)
    have h4G : orderOf ((e : G) * f) = 4 := by
      rw [← h4', ← Subgroup.orderOf_coe, Subgroup.coe_mul]
    rcases sq_mem_classIn_or_mem_pCoreOf hD hN hx hxX he hf h4G with hw | hw
    · refine ⟨(e * f) ^ 2, ?_, by rw [map_pow, map_mul]⟩
      show (((e * f) ^ 2 : X) : G) ∈ classIn X x
      simpa using hw
    · exfalso
      obtain ⟨w, hwP, hw'⟩ := hw
      have hw'' : w = (e * f) ^ 2 := Subtype.ext (by simpa using hw')
      have h1 : π ((e * f) ^ 2) = 1 := by
        rw [← hw'', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hwP
      have := orderOf_dvd_of_pow_eq_one (show (π (e * f)) ^ 2 = 1 by rw [← map_pow, h1])
      rw [h4] at this
      exact absurd this (by decide)

theorem opposite_mk_iff (hD : IsRootInvolutionSet D) (hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D)
    {X : Subgroup G} {x : G} (hx : x ∈ D) {e f : X} (he : e ∈ subClass X x)
    (hf : f ∈ subClass X x) :
    (¬ Commute (QuotientGroup.mk' (CFSG.pCore 2 X) e) (QuotientGroup.mk' (CFSG.pCore 2 X) f) ∧
      Odd (orderOf (QuotientGroup.mk' (CFSG.pCore 2 X) e *
        QuotientGroup.mk' (CFSG.pCore 2 X) f))) ↔
      (¬ Commute (e : G) f ∧ Odd (orderOf ((e : G) * f))) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have heD := mem_of_mem_subClass hN hx he
  have hfD := mem_of_mem_subClass hN hx hf
  have hf2 : f * f = 1 := Subtype.ext (by simpa using hD.mul_self_eq_one hfD)
  have hoG : orderOf ((e : G) * f) = orderOf (e * f) := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
  have hcG : Commute (e : G) f ↔ Commute e f :=
    ⟨fun h => Subtype.ext h.eq, fun h => congrArg Subtype.val h.eq⟩
  have hcomm : ∀ {a b : X ⧸ CFSG.pCore 2 X}, a * b = 1 → Commute a b := fun {a b} h => by
    rw [eq_inv_of_mul_eq_one_left h]
    exact (Commute.refl b).inv_left
  have hcomm' : ∀ {a b : X}, a * b = 1 → Commute a b := fun {a b} h => by
    rw [eq_inv_of_mul_eq_one_left h]
    exact (Commute.refl b).inv_left
  rw [hoG, hcG, ← map_mul]
  constructor
  · rintro ⟨hnc, ho⟩
    have key : orderOf (e * f) ∣ 2 ^ 2 → False := fun h4 => by
      have hdvd : orderOf (π (e * f)) ∣ 2 ^ 2 := (orderOf_map_dvd π _).trans h4
      have h1 : orderOf (π (e * f)) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 ho)) hdvd
      rw [orderOf_eq_one_iff, map_mul] at h1
      exact hnc (hcomm h1)
    refine ⟨fun hc => hnc (hc.map π), ?_⟩
    rcases hD.orderOf_mul heD hfD with h | h | h <;> rw [hoG] at h
    · exact (key (by rw [h]; norm_num)).elim
    · exact (key (by rw [h]; norm_num)).elim
    · exact h
  · rintro ⟨hnc, ho⟩
    have hord : orderOf (π (e * f)) = orderOf (e * f) :=
      orderOf_mk_eq_of_odd (CFSG.pCore_isPGroup (G := X) (p := 2)) ho
    refine ⟨fun hc => hnc ?_, by rw [hord]; exact ho⟩
    have he2 : π e * π e = 1 := by
      rw [← map_mul, show e * e = 1 from Subtype.ext (by simpa using hD.mul_self_eq_one heD),
        map_one]
    have hsq : (π (e * f)) ^ 2 = 1 := by
      rw [map_mul]
      exact (commute_iff_mul_sq_eq_one he2 (by rw [← map_mul, hf2, map_one])).1 hc
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [hord] at hdvd
    have h1 : orderOf (e * f) = 1 := Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 ho) hdvd
    exact hcomm' (orderOf_eq_one_iff.1 h1)

end Class

section Center

variable {K : Type*} [Group K] {F : Set K}

theorem exists_collinear_pair (hclass : ∃ d₀ : K, F = {g | IsConj d₀ g})
    (hF : IsRootInvolutionSet F) (hnd : ∃ d ∈ F, ∃ e ∈ F, orderOf (d * e) = 4) :
    ∃ u₁ ∈ F, ∃ u₂ ∈ F, u₁ ≠ u₂ ∧ Commute u₁ u₂ ∧ u₁ * u₂ ∈ F := by
  obtain ⟨d, hd, e, he, h4⟩ := hnd
  obtain ⟨hw, hdw, hew, -⟩ := sq_mem_of_orderOf_eq_four hF hd he h4
  refine ⟨d, hd, (d * e) ^ 2, hw, fun heq => ?_, hdw,
    mul_sq_mem_of_orderOf_eq_four hclass hF hd he h4⟩
  have hde : Commute d e := by rw [heq]; exact hew.symm
  have hdvd := orderOf_dvd_of_pow_eq_one
    ((commute_iff_mul_sq_eq_one (hF.mul_self_eq_one hd) (hF.mul_self_eq_one he)).1 hde)
  rw [h4] at hdvd
  exact absurd hdvd (by decide)

theorem odd_card_center [Finite K] (h2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) :
    Odd (Nat.card (Subgroup.center K)) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz' : orderOf (z : K) = 2 := by rwa [Subgroup.orderOf_coe]
  have hnormal : (Subgroup.zpowers (z : K)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ z.2 i) g, mul_inv_cancel_right]
    exact hx
  have hp : IsPGroup 2 (Subgroup.zpowers (z : K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz', pow_one])
  have hbot := h2 _ hnormal hp
  rw [Subgroup.zpowers_eq_bot] at hbot
  rw [hbot, orderOf_one] at hz'
  exact absurd hz' (by decide)

theorem not_mem_center (hclass : ∃ d₀ : K, F = {g | IsConj d₀ g}) (hF : IsRootInvolutionSet F)
    (hnd : ∃ d ∈ F, ∃ e ∈ F, orderOf (d * e) = 4) :
    ∀ d ∈ F, d ∉ Subgroup.center K := by
  intro d hd hdc
  obtain ⟨d', hd', e, he, h4⟩ := hnd
  have hcomm : ∀ y ∈ F, y ∈ Subgroup.center K := by
    intro y hy
    obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass hd hy)
    rw [Subgroup.mem_center_iff.mp hdc g, mul_inv_cancel_right]
    exact hdc
  have hde : Commute d' e := (Subgroup.mem_center_iff.mp (hcomm d' hd') e).symm
  have hdvd := orderOf_dvd_of_pow_eq_one
    ((commute_iff_mul_sq_eq_one (hF.mul_self_eq_one hd') (hF.mul_self_eq_one he)).1 hde)
  rw [h4] at hdvd
  exact absurd hdvd (by decide)

theorem hyp_quotient_center [Finite K] (hclass : ∃ d₀ : K, F = {g | IsConj d₀ g})
    (hF : IsRootInvolutionSet F) (hgen : Subgroup.closure F = ⊤)
    (hnd : ∃ d ∈ F, ∃ e ∈ F, orderOf (d * e) = 4)
    (h2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) :
    Hyp (K ⧸ Subgroup.center K) (QuotientGroup.mk' (Subgroup.center K) '' F) := by
  set Z := Subgroup.center K with hZ
  set π := QuotientGroup.mk' Z with hπ
  have hFZ := not_mem_center hclass hF hnd
  obtain ⟨h1, h2', h3, h4⟩ := Moufang.quotient_rootClass Z hclass hF hgen hnd hFZ
  obtain ⟨u₁, hu₁, u₂, hu₂, hne, hc, hu₃⟩ := exists_collinear_pair hclass hF hnd
  have hZodd := odd_card_center h2
  have hpre : ∀ N : Subgroup (K ⧸ Z), N.Normal → N.comap π ≤ Z → N = ⊥ := by
    intro N _ hle
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective Z y
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hle hy
  refine ⟨inferInstance, h1, h2', h3, ?_, ?_, h4⟩
  ·
    intro N hN hodd
    refine hpre N hN (le_center_of_odd_card hclass hF hgen hu₁ hu₂ hne hc hu₃
      (Subgroup.Normal.comap hN π) ?_)
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro hdvd
    obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hm' : orderOf (m : K) = 2 := by rwa [Subgroup.orderOf_coe]
    have hmN : π m ∈ N := m.2
    have hπm : orderOf (π m) = 1 := by
      have h1 : orderOf (⟨π m, hmN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
      have h2 : orderOf (π m) ∣ 2 := hm' ▸ orderOf_map_dvd π (m : K)
      rw [← Subgroup.orderOf_mk (π m) hmN] at h2
      rw [← Subgroup.orderOf_mk (π m) hmN]
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1
        (Nat.coprime_two_right.2 hodd)) h2
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπm
    have hdvd' : orderOf (⟨m, hπm⟩ : Z) ∣ Nat.card Z := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hm'] at hdvd'
    exact (Nat.not_even_iff_odd.2 hZodd) (even_iff_two_dvd.2 hdvd')
  ·
    intro N hN hP
    have hMn : (N.comap π).Normal := Subgroup.Normal.comap hN π
    refine hpre N hN (le_center_of_isSolvable hclass hF hgen hu₁ hu₂ hne hc hu₃ h2 hMn ?_)
    set M := N.comap π with hM
    have hMP : IsPGroup 2 (M ⧸ Subgroup.center M) := by
      intro y
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ y
      obtain ⟨k, hk⟩ := hP ⟨π m, m.2⟩
      have hk' : π ((m : K) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk'
      refine ⟨k, ?_⟩
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (by simpa using Subgroup.mem_center_iff.mp hk' (g : K))
    have : Group.IsNilpotent M := Group.of_quotient_center_nilpotent hMP.isNilpotent
    infer_instance

theorem opposite_mk_center_iff (hF : IsRootInvolutionSet F) {e f : K} (he : e ∈ F)
    (hf : f ∈ F) :
    (¬ Commute (QuotientGroup.mk' (Subgroup.center K) e)
        (QuotientGroup.mk' (Subgroup.center K) f) ∧
      Odd (orderOf (QuotientGroup.mk' (Subgroup.center K) e *
        QuotientGroup.mk' (Subgroup.center K) f))) ↔
      (¬ Commute e f ∧ Odd (orderOf (e * f))) := by
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have he2 := hF.mul_self_eq_one he
  have hcomm : ∀ {a b : K ⧸ Subgroup.center K}, a * b = 1 → Commute a b := fun {a b} h => by
    rw [eq_inv_of_mul_eq_one_left h]
    exact (Commute.refl b).inv_left
  rw [← map_mul]
  constructor
  · rintro ⟨hnc, ho⟩
    refine ⟨fun hc => hnc (hc.map π), ?_⟩
    have key : orderOf (e * f) ∣ 2 ^ 2 → False := fun h4 => by
      have hdvd : orderOf (π (e * f)) ∣ 2 ^ 2 := (orderOf_map_dvd π _).trans h4
      have h1 : orderOf (π (e * f)) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 ho)) hdvd
      rw [orderOf_eq_one_iff, map_mul] at h1
      exact hnc (hcomm h1)
    rcases hF.orderOf_mul he hf with h | h | h
    · exact (key (by rw [h]; norm_num)).elim
    · exact (key (by rw [h]; norm_num)).elim
    · exact h
  · rintro ⟨hnc, ho⟩
    refine ⟨fun hc => hnc ?_, ho.of_dvd_nat (orderOf_map_dvd π _)⟩
    have hsq : (π (e * f)) ^ 2 = 1 := by
      rw [map_mul]
      exact (commute_iff_mul_sq_eq_one (by rw [← map_mul, he2, map_one])
        (by rw [← map_mul, hF.mul_self_eq_one hf, map_one])).1 hc
    have h1 : orderOf (π (e * f)) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 (ho.of_dvd_nat
        (orderOf_map_dvd π _))) (orderOf_dvd_of_pow_eq_one hsq)
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hc := Subgroup.mem_center_iff.mp h1 e
    have hf' : f = e * f * e := by rw [← hc, ← mul_assoc, he2, one_mul]
    show e * f = f * e
    calc e * f = e * (e * f * e) := by rw [← hf']
      _ = f * e := by rw [← mul_assoc, ← mul_assoc, he2, one_mul]

end Center

@[expose] def RankOneShape (K : Type*) [Group K] : Prop :=
  (∃ n, 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model n)) ∨
    (∃ n, 1 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.SzModel n)) ∨
    ∃ s t : K, Subgroup.closure {s, t} = ⊤ ∧ orderOf s = 2 ∧ orderOf t = 2 ∧
      Odd (orderOf (s * t))

theorem RankOneShape.of_mulEquiv {K L : Type*} [Group K] [Group L] (hK : RankOneShape K)
    (e : K ≃* L) : RankOneShape L := by
  rcases hK with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨s, t, hst, hs, ht, ho⟩
  · exact Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · refine Or.inr (Or.inr ⟨e s, e t, ?_, by rwa [MulEquiv.orderOf_eq], by rwa [MulEquiv.orderOf_eq],
      by rwa [← map_mul, MulEquiv.orderOf_eq]⟩)
    have h := congrArg (Subgroup.map e.toMonoidHom) hst
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.surjective] at h
    rw [← h]
    congr 1
    ext y
    simp [Set.mem_insert_iff]

@[expose] def RootGenQuotientStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Asc72.IsOddTransp D →
    Connectivity.IsNormalSet D → ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x →
      RankOneShape (↥(Subgroup.closure (insert x (rootSet D d))) ⧸
        CFSG.pCore 2 ↥(Subgroup.closure (insert x (rootSet D d))))

noncomputable def topQuotientEquiv {K : Type*} [Group K] (hK : CFSG.pCore 2 K = ⊥)
    {X : Subgroup K} (hX : X = ⊤) : (↥X ⧸ CFSG.pCore 2 ↥X) ≃* K := by
  let e₁ : ↥X ≃* K := (MulEquiv.subgroupCongr hX).trans Subgroup.topEquiv
  have hbot : CFSG.pCore 2 ↥X = ⊥ := by
    have h := CFSG.pCore_map_iso 2 e₁
    rw [hK] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₁.injective).1 h
  exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans e₁

theorem commute_iff_not_opposite {K : Type*} [Group K] {F : Set K} (hF : Asc72.IsOddTransp F)
    {a b : K} (ha : a ∈ F) (hb : b ∈ F) :
    Commute a b ↔ ¬ (¬ Commute a b ∧ Odd (orderOf (a * b))) := by
  refine ⟨fun hc h => h.1 hc, fun h => by_contra fun hnc => h ⟨hnc, ?_⟩⟩
  rcases hF.2 a ha b hb with h2 | ho
  · exfalso
    apply hnc
    have ha2 : a * a = 1 := by rw [← sq, ← hF.1 a ha, pow_orderOf_eq_one]
    have hb2 : b * b = 1 := by rw [← sq, ← hF.1 b hb, pow_orderOf_eq_one]
    exact (commute_iff_mul_sq_eq_one ha2 hb2).2 (orderOf_dvd_iff_pow_eq_one.1 h2)
  · exact ho

theorem rankOneShape_quotient (h120 : RootGenQuotientStmt) {G : Type} [Group G] {D : Set G}
    (h : Hyp G D) (IH : RootIHStruct G) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdx : ¬ Commute d x) (hodd : Odd (orderOf (d * x))) {S : Set G} (hS : S ⊆ rootSet D d)
    (hdS : d ∈ S) (hne : Subgroup.closure (insert x S) ≠ ⊤) :
    RankOneShape (↥(Subgroup.closure (insert x S)) ⧸
      CFSG.pCore 2 ↥(Subgroup.closure (insert x S))) := by
  have := h.finite
  have hclass := h.isClass
  have hD := h.root
  have hN : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D := fun g y hy => conj_mem_of_isClass hclass g hy
  set X := Subgroup.closure (insert x S) with hX
  set π := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hxX : x ∈ X := Subgroup.subset_closure (Set.mem_insert x S)
  have hSX : ∀ s ∈ S, s ∈ X := fun s hs => Subgroup.subset_closure (Set.mem_insert_of_mem x hs)
  have hdX := hSX d hdS
  have hSopp : ∀ s ∈ S, ¬ Commute s x ∧ Odd (orderOf (s * x)) := fun s hs =>
    ⟨fun hc => hdx (((hS hs).2 x hx).1 hc),
      (odd_orderOf_mul_iff_of_mem_rootSet hD hd (hS hs) hx hdx).2 hodd⟩
  have hSc : insert x S ⊆ classIn X x := by
    rintro y (rfl | hy)
    · exact mem_classIn_self X y
    · exact mem_classIn_of_odd hD hx (hS hy).1 hxX (hSX y hy)
        (by rw [orderOf_mul_comm_eq]; exact (hSopp y hy).2)
  have hgen : Subgroup.closure (subClass X x) = ⊤ := closure_subClass_eq_top hSc rfl
  have hroot := isRootInvolutionSet_barClass hD hN hx hxX hdX hdx hodd hgen
  have hclassB : ∃ d₀, barClass X x = {g | IsConj d₀ g} := ⟨_, barClass_eq hxX⟩
  have hgenB : Subgroup.closure (barClass X x) = ⊤ := by
    rw [barClass, ← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hO2 : CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := pCore_quotient_pCore_eq_bot
  have hO2' : ∀ N : Subgroup (X ⧸ CFSG.pCore 2 X), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hNn hNp => eq_bot_iff.2 (hO2 ▸ le_sSup ⟨hNn, hNp⟩)
  have hmemS : ∀ s (hs : s ∈ S), (⟨s, hSX s hs⟩ : X) ∈ subClass X x := fun s hs =>
    hSc (Set.mem_insert_of_mem x hs)
  have hxS : (⟨x, hxX⟩ : X) ∈ subClass X x := mem_subClass_self hxX
  have hdS' := hmemS d hdS
  have hclosureX : Subgroup.closure ((fun s : X => π s) ''
      (insert (⟨x, hxX⟩ : X) {y : X | (y : G) ∈ S})) = ⊤ := by
    have h1 : Subgroup.closure (insert (⟨x, hxX⟩ : X) {y : X | (y : G) ∈ S}) = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨g, hg⟩ -
      have hg' : g ∈ Subgroup.closure (insert x S) := hg
      induction hg' using Subgroup.closure_induction with
      | mem y hy =>
        rcases hy with rfl | hy
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hy)
      | one => exact Subgroup.one_mem _
      | mul a b ha hb iha ihb => exact Subgroup.mul_mem _ (iha ha) (ihb hb)
      | inv a ha iha => exact Subgroup.inv_mem _ (iha ha)
    rw [← MonoidHom.map_closure, h1,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hoppB : ∀ y ∈ subClass X x, ∀ s (hs : s ∈ S),
      (¬ Commute (π ⟨s, hSX s hs⟩) (π y) ∧ Odd (orderOf (π ⟨s, hSX s hs⟩ * π y))) ↔
        (¬ Commute (π ⟨d, hdX⟩) (π y) ∧ Odd (orderOf (π ⟨d, hdX⟩ * π y))) := by
    intro y hy s hs
    rw [opposite_mk_iff hD hN hx (hmemS s hs) hy, opposite_mk_iff hD hN hx hdS' hy]
    have hyD := mem_of_mem_subClass hN hx hy
    have hc : Commute s (y : G) ↔ Commute d (y : G) := (hS hs).2 _ hyD
    constructor
    · rintro ⟨hnc, ho⟩
      have hnc' : ¬ Commute d (y : G) := fun h' => hnc (hc.2 h')
      exact ⟨hnc', (odd_orderOf_mul_iff_of_mem_rootSet hD hd (hS hs) hyD hnc').1 ho⟩
    · rintro ⟨hnc, ho⟩
      exact ⟨fun h' => hnc (hc.1 h'),
        (odd_orderOf_mul_iff_of_mem_rootSet hD hd (hS hs) hyD hnc).2 ho⟩
  have hdxB : ¬ Commute (π ⟨d, hdX⟩) (π ⟨x, hxX⟩) ∧
      Odd (orderOf (π ⟨d, hdX⟩ * π ⟨x, hxX⟩)) :=
    (opposite_mk_iff hD hN hx hdS' hxS).2 ⟨hdx, hodd⟩
  by_cases hnd : ∃ e ∈ barClass X x, ∃ f ∈ barClass X x, orderOf (e * f) = 4
  ·
    exfalso
    set K := X ⧸ CFSG.pCore 2 X
    set ρ := QuotientGroup.mk' (Subgroup.center K) with hρ
    have hH := hyp_quotient_center hclassB hroot hgenB hnd hO2'
    have hlt : Nat.card (K ⧸ Subgroup.center K) < Nat.card G := by
      have h1 : Nat.card (K ⧸ Subgroup.center K) ≤ Nat.card K :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      have h2 : Nat.card K ≤ Nat.card X :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      have h3 : Nat.card X < Nat.card G :=
        lt_of_le_of_ne (Subgroup.card_le_card_group X) fun heq =>
          hne ((Subgroup.card_eq_iff_eq_top X).1 heq)
      omega
    have hmemB : ∀ y ∈ subClass X x, π y ∈ barClass X x := fun y hy => ⟨y, hy, rfl⟩
    have hmemC : ∀ y ∈ subClass X x, ρ (π y) ∈ ρ '' barClass X x := fun y hy =>
      ⟨π y, hmemB y hy, rfl⟩
    have hOD := oppositeDetermines_of_hyp hH
    have hSroot : ∀ s (hs : s ∈ S), ρ (π ⟨s, hSX s hs⟩) ∈
        rootSet (ρ '' barClass X x) (ρ (π ⟨d, hdX⟩)) := by
      intro s hs
      refine hOD _ (hmemC _ hdS') _ (hmemC _ (hmemS s hs)) ?_
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rw [opposite_mk_center_iff hroot (hmemB _ hdS') (hmemB y hy),
        opposite_mk_center_iff hroot (hmemB _ (hmemS s hs)) (hmemB y hy)]
      exact (hoppB y hy s hs).symm
    have hdxC := (opposite_mk_center_iff hroot (hmemB _ hdS') (hmemB _ hxS)).2 hdxB
    refine rootIHGen_of_struct IH _ _ hH hlt _ (hmemC _ hdS') _ (hmemC _ hxS) hdxC.1 hdxC.2 ?_
    rw [eq_top_iff]
    have htop : Subgroup.closure (ρ '' ((fun s : X => π s) ''
        (insert (⟨x, hxX⟩ : X) {y : X | (y : G) ∈ S}))) = ⊤ := by
      rw [← MonoidHom.map_closure, hclosureX,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [← htop, Subgroup.closure_le]
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rcases hy with rfl | hy
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (hSroot y hy))
  ·
    push Not at hnd
    have hOT : Asc72.IsOddTransp (barClass X x) := by
      refine ⟨hroot.1, fun e he f hf => ?_⟩
      rcases hroot.2.1 e he f hf with h2 | h4 | ho
      · exact Or.inl (dvd_of_eq h2)
      · exact absurd h4 (hnd e he f hf)
      · exact Or.inr ho
    have hNB : Connectivity.IsNormalSet (barClass X x) := by
      intro g y hy
      rw [barClass_eq hxX] at hy ⊢
      exact hy.trans (isConj_iff.2 ⟨g, rfl⟩)
    have hmemB : ∀ y ∈ subClass X x, π y ∈ barClass X x := fun y hy => ⟨y, hy, rfl⟩
    have hSroot : ∀ s (hs : s ∈ S), π ⟨s, hSX s hs⟩ ∈ rootSet (barClass X x) (π ⟨d, hdX⟩) := by
      intro s hs
      refine ⟨hmemB _ (hmemS s hs), ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [commute_iff_not_opposite hOT (hmemB _ (hmemS s hs)) (hmemB y hy),
        commute_iff_not_opposite hOT (hmemB _ hdS') (hmemB y hy), hoppB y hy s hs]
    have htop : Subgroup.closure (insert (π ⟨x, hxX⟩)
        (rootSet (barClass X x) (π ⟨d, hdX⟩))) = ⊤ := by
      rw [eq_top_iff, ← hclosureX, Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with rfl | hy
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (hSroot _ hy))
    exact (h120 _ _ hOT hNB _ (hmemB _ hdS') _ (hmemB _ hxS) hdxB.1).of_mulEquiv
      (topQuotientEquiv hO2 htop)

end CFSG.Timmesfeld.Bridge.RootClosure
