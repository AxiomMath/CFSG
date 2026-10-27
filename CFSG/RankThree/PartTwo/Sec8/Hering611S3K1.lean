module

public import CFSG.RankThree.PartTwo.Sec8.Hering611S3Odd
public import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem theta_K_odd (hbig : NoBig3 G) {A K : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : 27 < Nat.card A) (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card'
    (G := inSubgroup (aschbacherSolvableCore 3) K) 2 h2
  obtain ⟨t, htθ, hto⟩ : ∃ t : G,
      t ∈ inSubgroup (aschbacherSolvableCore 3) K ∧ orderOf t = 2 :=
    ⟨(t' : G), t'.2, (Subgroup.orderOf_coe t').trans ht'⟩
  have hQ2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
  have hQθ : Subgroup.zpowers t ≤ inSubgroup (aschbacherSolvableCore 3) K :=
    Subgroup.zpowers_le.mpr htθ
  have hAθ : A ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K : Set G) :=
    hAK.trans (Sec6.normalizer_le_normalizer_theta K)
  have hθ3 : ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) :=
    Sec11.not_three_dvd_card_inSubgroup_theta K
  have hbot := eq_bot_of_two_subgroup_of_normalized hbig hA hA27 hθ3 hAθ hQθ hQ2
  have ht1 : t = 1 := by
    have hmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  rw [ht1, orderOf_one] at hto
  norm_num at hto

theorem kernel_odd (hbig : NoBig3 G) {A K : Subgroup G} {d : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : 27 < Nat.card A) (hdA : d ∈ A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAdec : ∀ x ∈ A, ∃ k ∈ A ⊓ K, x * k⁻¹ ∈ Subgroup.zpowers d)
    (hdK : K ≤ Subgroup.centralizer ({d} : Set G)) :
    ¬ 2 ∣ Nat.card (Sec4.thetaQuotCentralizer K ⊓ Subgroup.centralizer ({d} : Set G) :
      Subgroup G) := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup G := Sec4.thetaQuotCentralizer K ⊓ Subgroup.centralizer ({d} : Set G)
    with hD
  set θ : Subgroup G := inSubgroup (aschbacherSolvableCore 3) K with hθ
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 h2
  obtain ⟨t, htD, hto⟩ : ∃ t : G, t ∈ D ∧ orderOf t = 2 :=
    ⟨(t' : G), t'.2, (Subgroup.orderOf_coe t').trans ht'⟩
  have htC : t ∈ Sec4.thetaQuotCentralizer K := (Subgroup.mem_inf.mp htD).1
  have htZ : t ∈ Subgroup.centralizer ({d} : Set G) := (Subgroup.mem_inf.mp htD).2
  have hdt : d * t = t * d := Subgroup.mem_centralizer_iff.mp htZ d (Set.mem_singleton d)
  have hθ3 : ¬ 3 ∣ Nat.card θ := Sec11.not_three_dvd_card_inSubgroup_theta K
  have hdθ : d ∈ Subgroup.normalizer (θ : Set G) :=
    Sec6.normalizer_le_normalizer_theta K (hAK hdA)
  have htθ : t ∈ Subgroup.normalizer (θ : Set G) :=
    Sec6.normalizer_le_normalizer_theta K (Sec6.thetaQuotCentralizer_le_normalizer K htC)
  have hQ2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
  have hM3' : ¬ 3 ∣ Nat.card (Subgroup.zpowers t ⊔ θ : Subgroup G) :=
    Sec6.not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hQ2
      (Subgroup.zpowers_le.mpr htθ) hθ3
  set M : Subgroup G := θ ⊔ Subgroup.zpowers t with hM
  have hM3 : ¬ 3 ∣ Nat.card M := by
    rw [hM, sup_comm]
    exact hM3'
  have hTM : t ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hconj : ∀ x : G, x ∈ Subgroup.normalizer (θ : Set G) → x * t * x⁻¹ ∈ M →
      ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    intro x hxθ hxt m hm
    have hle : M ≤ M.comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hxθ a).mp ha)
      · rw [Subgroup.mem_comap]
        exact hxt
    exact hle hm
  have hdt1 : d * t * d⁻¹ = t := by
    calc d * t * d⁻¹ = (t * d) * d⁻¹ := by rw [hdt]
      _ = t := by group
  have hdt2 : d⁻¹ * t * d⁻¹⁻¹ = t := by
    calc d⁻¹ * t * d⁻¹⁻¹ = d⁻¹ * (t * d) := by group
      _ = d⁻¹ * (d * t) := by rw [hdt]
      _ = t := by group
  have hnorm : ∀ x : G, x ∈ Subgroup.normalizer (θ : Set G) → x * t * x⁻¹ ∈ M →
      x⁻¹ * t * x⁻¹⁻¹ ∈ M → x ∈ Subgroup.normalizer (M : Set G) := by
    intro x hx1 hx2 hx3
    refine Subgroup.mem_normalizer_iff.mpr fun m =>
      ⟨fun hm => hconj x hx1 hx2 m hm, fun hm => ?_⟩
    have h3 := hconj x⁻¹ (inv_mem hx1) hx3 (x * m * x⁻¹) hm
    have e : x⁻¹ * (x * m * x⁻¹) * x⁻¹⁻¹ = m := by group
    rw [e] at h3
    exact h3
  have hdM : d ∈ Subgroup.normalizer (M : Set G) :=
    hnorm d hdθ (by rw [hdt1]; exact hTM) (by rw [hdt2]; exact hTM)
  have hKt : ∀ k ∈ K, k * t * k⁻¹ ∈ M := by
    intro k hk
    have hc := (Sec6.mem_thetaQuotCentralizer_iff.mp htC).2 k⁻¹ (inv_mem hk)
    have e : k * t * k⁻¹ = (k⁻¹⁻¹ * (t * k⁻¹ * t⁻¹)) * t := by group
    rw [e]
    exact M.mul_mem (Subgroup.mem_sup_left hc) hTM
  have hkM : ∀ k ∈ K, k ∈ Subgroup.normalizer (M : Set G) := fun k hk =>
    hnorm k (Sec6.le_normalizer_theta K hk) (hKt k hk) (hKt k⁻¹ (inv_mem hk))
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := hAdec x hx
    have hzd : Subgroup.zpowers d ≤ Subgroup.normalizer (M : Set G) :=
      Subgroup.zpowers_le.mpr hdM
    have h4 := mul_mem (hzd hxk) (hkM k (Subgroup.mem_inf.mp hk).2)
    rwa [inv_mul_cancel_right] at h4
  have hQM : Subgroup.zpowers t ≤ M := Subgroup.zpowers_le.mpr hTM
  have hbot := eq_bot_of_two_subgroup_of_normalized hbig hA hA27 hM3 hAM hQM hQ2
  have ht1 : t = 1 := by
    have hmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  rw [ht1, orderOf_one] at hto
  norm_num at hto

end CFSG.RankThree.PartTwo.Sec8.Hering611
