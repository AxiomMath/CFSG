module

public import CFSG.Timmesfeld.Exceptional.CaseIComponents
public import CFSG.Timmesfeld.Exceptional.CaseIWeakTI

public section

namespace CFSG.Timmesfeld.Moufang

@[expose] def Tim75Thm31 : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → Closure.CommConnected D

variable {G : Type*} [Group G] {D : Set G}

theorem not_isPGroup_two [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hgen : Subgroup.closure D = ⊤)
    (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) : ¬ IsPGroup 2 G := by
  intro hP
  obtain ⟨d, hd, e, he, h4⟩ := hnd
  have hnil : Group.IsNilpotent G := hP.isNilpotent
  have hcyc : Subgroup.zpowers d = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hdM⟩ := (eq_top_or_exists_le_coatom (Subgroup.zpowers d)).resolve_left hne
    have hMn := Subgroup.NormalizerCondition.normal_of_coatom M
      Group.normalizerCondition_of_isNilpotent hM
    apply hM.1
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro z hz
    obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass hd hz)
    exact hMn.conj_mem _ (hdM (Subgroup.mem_zpowers d)) c
  have hde : Commute d e := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hcyc ▸ Subgroup.mem_top e)
    exact (Commute.refl d).zpow_right k
  have hdvd := orderOf_dvd_of_pow_eq_one
    ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he)).1 hde)
  rw [h4] at hdvd
  exact absurd hdvd (by decide)

theorem not_mem_of_odd_or_isPGroup [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hgen : Subgroup.closure D = ⊤)
    (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) (N : Subgroup G) [hN : N.Normal]
    (hN2 : Odd (Nat.card N) ∨ IsPGroup 2 N) : ∀ d ∈ D, d ∉ N := by
  intro d hd hdN
  rcases hN2 with hodd | hP
  · have h2 := Subgroup.orderOf_dvd_natCard N hdN
    rw [hD.orderOf_eq_two hd] at h2
    exact hodd.not_two_dvd_nat h2
  · have htop : N = ⊤ := by
      rw [eq_top_iff, ← hgen, Subgroup.closure_le]
      intro z hz
      obtain ⟨c, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass hd hz)
      exact hN.conj_mem _ hdN c
    refine not_isPGroup_two hclass hD hgen hnd fun g => ?_
    obtain ⟨k, hk⟩ := hP ⟨g, htop ▸ Subgroup.mem_top g⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

section Quotient

variable (N : Subgroup G) [N.Normal]

theorem commute_of_commute_mk (hD : IsRootInvolutionSet D) (hN : ∀ d ∈ D, d ∉ N) {d e : G}
    (hd : d ∈ D) (he : e ∈ D) (hne : QuotientGroup.mk' N d ≠ QuotientGroup.mk' N e)
    (hc : Commute (QuotientGroup.mk' N d) (QuotientGroup.mk' N e)) : Commute d e := by
  set φ := QuotientGroup.mk' N
  have hd2 : φ d * φ d = 1 := by rw [← map_mul, hD.mul_self_eq_one hd, map_one]
  have he2 : φ e * φ e = 1 := by rw [← map_mul, hD.mul_self_eq_one he, map_one]
  have hsq : (φ d * φ e) ^ 2 = 1 := by rw [hc.mul_pow, pow_two, pow_two, hd2, he2, one_mul]
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hd he with h | h4 | ⟨hodd, -⟩
  · exact h
  · refine absurd ((QuotientGroup.eq_one_iff _).1 ?_) (hN _ (hD.sq_mem hd he h4))
    change φ ((d * e) ^ 2) = 1
    rw [map_pow, map_mul, hsq]
  · have h1 : orderOf (φ d * φ e) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h2 : Odd (orderOf (φ d * φ e)) := by
      rw [← map_mul]
      exact hodd.of_dvd_nat (orderOf_map_dvd φ _)
    have h3 : orderOf (φ d * φ e) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
      · exact h
      · rw [h] at h2
        exact absurd h2 (by decide)
    rw [orderOf_eq_one_iff] at h3
    exact absurd (by rw [eq_inv_of_mul_eq_one_right h3, inv_eq_of_mul_eq_one_right hd2]) hne

theorem quotient_rootClass (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hgen : Subgroup.closure D = ⊤)
    (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) (hN : ∀ d ∈ D, d ∉ N) :
    (∃ d₀ : G ⧸ N, QuotientGroup.mk' N '' D = {g | IsConj d₀ g}) ∧
      IsRootInvolutionSet (QuotientGroup.mk' N '' D) ∧
      Subgroup.closure (QuotientGroup.mk' N '' D) = ⊤ ∧
      ∃ d ∈ QuotientGroup.mk' N '' D, ∃ e ∈ QuotientGroup.mk' N '' D, orderOf (d * e) = 4 := by
  set φ := QuotientGroup.mk' N
  have hne1 : ∀ d ∈ D, φ d ≠ 1 := fun d hd h => hN d hd ((QuotientGroup.eq_one_iff d).1 h)
  have hsq1 : ∀ d ∈ D, φ d ^ 2 = 1 := fun d hd => by
    rw [pow_two, ← map_mul, hD.mul_self_eq_one hd, map_one]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨d₀, hd₀⟩ := hclass
    refine ⟨φ d₀, Set.ext fun x => ⟨?_, fun hx => ?_⟩⟩
    · rintro ⟨d, hd, rfl⟩
      rw [hd₀] at hd
      exact φ.map_isConj hd
    · obtain ⟨c, hc⟩ := isConj_iff.1 hx
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N c
      refine ⟨g * d₀ * g⁻¹, ?_, ?_⟩
      · rw [hd₀]
        exact isConj_iff.2 ⟨g, rfl⟩
      · rw [map_mul, map_mul, map_inv]
        exact hc
  · rintro _ ⟨d, hd, rfl⟩
    exact orderOf_eq_prime (hsq1 d hd) (hne1 d hd)
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩
    rw [← map_mul]
    have hdvd := orderOf_map_dvd φ (d * e)
    rcases hD.orderOf_mul hd he with h | h | h
    · rw [h] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
      · right; right; rw [h1]; exact odd_one
      · left; exact h1
    · rw [h] at hdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (show orderOf (φ (d * e)) ∣ 2 ^ 2 from hdvd)
      interval_cases k
      · right; right; rw [hk']; exact odd_one
      · left; exact hk'
      · right; left; exact hk'
    · right; right; exact h.of_dvd_nat hdvd
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ h4
    rw [← map_mul] at h4
    have hdvd := orderOf_map_dvd φ (d * e)
    rw [h4] at hdvd
    have h4' : orderOf (d * e) = 4 := by
      rcases hD.orderOf_mul hd he with h | h | h
      · rw [h] at hdvd
        exact absurd hdvd (by decide)
      · exact h
      · exact absurd (h.of_dvd_nat hdvd) (by decide)
    exact ⟨(d * e) ^ 2, hD.sq_mem hd he h4', by rw [map_pow, map_mul]⟩
  · rw [← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  · obtain ⟨d, hd, e, he, h4⟩ := hnd
    refine ⟨φ d, ⟨d, hd, rfl⟩, φ e, ⟨e, he, rfl⟩, ?_⟩
    rw [← map_mul]
    have hdvd : orderOf (φ (d * e)) ∣ 2 ^ 2 := by
      have := orderOf_map_dvd φ (d * e)
      rw [h4] at this
      exact this
    have hn2 : ¬ orderOf (φ (d * e)) ∣ 2 := fun h =>
      hne1 _ (hD.sq_mem hd he h4) (by rw [map_pow]; exact orderOf_dvd_iff_pow_eq_one.1 h)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    interval_cases k
    · exact absurd (hk' ▸ one_dvd 2) hn2
    · exact absurd (hk' ▸ dvd_refl 2) hn2
    · exact hk'

theorem commConnected_of_quotient (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4)
    (hN : ∀ d ∈ D, d ∉ N) (hQ : Closure.CommConnected (QuotientGroup.mk' N '' D)) :
    Closure.CommConnected D := by
  set φ := QuotientGroup.mk' N
  intro S hSD ⟨s, hs⟩ hScl
  have hsD := hSD hs
  have hne : ({x | x ∈ φ '' D ∧ ∀ y ∈ D, φ y = x → y ∈ S} : Set (G ⧸ N)).Nonempty := by
    obtain ⟨d₀, hd₀, e₀, he₀, h4⟩ := hnd
    obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_isClass hclass hd₀ hsD)
    have he := conj_mem_of_isClass hclass g he₀
    have h4' : orderOf (s * (g * e₀ * g⁻¹)) = 4 := by
      rw [← hg, show g * d₀ * g⁻¹ * (g * e₀ * g⁻¹) = g * (d₀ * e₀) * g⁻¹ by group,
        orderOf_conj_eq]
      exact h4
    obtain ⟨hf, hsf, -, -⟩ := sq_mem_of_orderOf_eq_four hD hsD he h4'
    have hsfD := mul_sq_mem_of_orderOf_eq_four hclass hD hsD he h4'
    have hfS := hScl s hs _ hf hsf
    refine ⟨φ s, ⟨s, hsD, rfl⟩, fun y hy hys => ?_⟩
    have hyf : φ y ≠ φ ((s * (g * e₀ * g⁻¹)) ^ 2) := by
      rw [hys]
      intro h
      refine hN _ hsfD ((QuotientGroup.eq_one_iff _).1 ?_)
      change φ (s * (s * (g * e₀ * g⁻¹)) ^ 2) = 1
      rw [map_mul, ← h, ← map_mul, hD.mul_self_eq_one hsD, map_one]
    have hc := commute_of_commute_mk N hD hN hy hf hyf (by rw [hys]; exact hsf.map φ)
    exact hScl _ hfS y hy hc.symm
  have hcl : ∀ x ∈ {x | x ∈ φ '' D ∧ ∀ y ∈ D, φ y = x → y ∈ S}, ∀ z ∈ φ '' D, Commute x z →
      z ∈ {x | x ∈ φ '' D ∧ ∀ y ∈ D, φ y = x → y ∈ S} := by
    rintro x ⟨⟨x₀, hx₀, rfl⟩, hxS⟩ z ⟨z₀, hz₀, rfl⟩ hxz
    refine ⟨⟨z₀, hz₀, rfl⟩, fun y hy hyz => ?_⟩
    by_cases hxz' : φ x₀ = φ z₀
    · exact hxS y hy (hyz.trans hxz'.symm)
    · have hc := commute_of_commute_mk N hD hN hx₀ hy (by rw [hyz]; exact hxz')
        (by rw [hyz]; exact hxz)
      exact hScl x₀ (hxS x₀ hx₀ rfl) y hy hc
  have key := hQ _ (fun x hx => hx.1) hne hcl
  intro d hd
  exact (key ⟨d, hd, rfl⟩).2 d hd rfl

end Quotient

theorem commConnected_of_tim75Thm31 (hT : Tim75Thm31) {G : Type} [Group G] [Finite G]
    {D : Set G} (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hgen : Subgroup.closure D = ⊤) (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    Closure.CommConnected D := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (D : Set G), Nat.card G = n →
      (∃ d₀ : G, D = {g | IsConj d₀ g}) → IsRootInvolutionSet D → Subgroup.closure D = ⊤ →
      (∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) → Closure.CommConnected D from
    key _ G D rfl hclass hD hgen hnd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ D hn hclass hD hgen hnd
    by_cases hN : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ (Odd (Nat.card N) ∨ IsPGroup 2 N)
    · obtain ⟨N, hNn, hNb, hN2⟩ := hN
      have := hNn
      have hND := not_mem_of_odd_or_isPGroup hclass hD hgen hnd N hN2
      obtain ⟨h1, h2, h3, h4⟩ := quotient_rootClass N hclass hD hgen hnd hND
      have hlt : Nat.card (G ⧸ N) < n := by
        have c1 := (Subgroup.one_lt_card_iff_ne_bot N).2 hNb
        have c2 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        have c3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
        rw [← hn]
        nlinarith
      exact commConnected_of_quotient N hclass hD hnd hND (ih _ hlt (G ⧸ N) _ rfl h1 h2 h3 h4)
    · exact hT G D ⟨inferInstance, hclass, hD, hgen,
        fun N hNn hodd => by_contra fun hb => hN ⟨N, hNn, hb, Or.inl hodd⟩,
        fun N hNn hP => by_contra fun hb => hN ⟨N, hNn, hb, Or.inr hP⟩, hnd⟩

theorem collConnected_of_tim75Thm31 (hT : Tim75Thm31) {G : Type} [Group G] [Finite G]
    {D : Set G} (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hgen : Subgroup.closure D = ⊤) (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    ExcCollConnected D :=
  collConnected_of_commConnected (fun _ _ _ _ h1 h2 h3 h4 => commConnected_of_tim75Thm31 hT h1 h2
    h3 h4) hclass hD hgen hnd

theorem collConnected_of_hyp (hT : Tim75Thm31) {G : Type} [Group G] {D : Set G}
    (h : Hyp G D) : ExcCollConnected D := by
  have := h.finite
  exact collConnected_of_tim75Thm31 hT h.isClass h.root h.gen h.nondeg

@[expose] def CaseICommPQInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    ¬ NoLevi D → CommLambda D ∧ ExcPQ D

theorem exceptionalLeviStep_of_tim75 (hT : Tim75Thm31) (hI : CaseICommPQInput) :
    ExceptionalLeviStep :=
  exceptionalLeviStep_of_commInput fun G _ D h IH hsing hex hNL =>
    have hc := hI G D h IH hsing hex hNL
    ⟨hc.1, hc.2, collConnected_of_hyp hT h⟩

end CFSG.Timmesfeld.Moufang
