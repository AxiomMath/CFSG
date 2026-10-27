module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SBasic
public import CFSG.RankThree.PartTwo.Sec8.Hering611SMax
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section D


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem exists_d_mem_K (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    (hZ3 : Nat.card (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) = 3) :
    ∃ dK : K, (dK : G) = d ∧ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) =
      Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 K) dK) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := C.toFrame611.isElemAbelian
  have hAmax := C.toFrame611.maximal
  have hAK := C.A_le_normalizer_K h45
  have hd3 := C.toFrame611.d_pow_three
  have hd1 := C.toFrame611.d_ne_one
  have hd_ord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  obtain ⟨y₁, hyZ, hy₁ord⟩ : ∃ y₁ ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K),
      orderOf y₁ = 3 := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) 3 (by rw [hZ3])
    exact ⟨z, z.2, by rw [Subgroup.orderOf_coe, hz]⟩
  have hy₁3 : y₁ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₁
    rwa [hy₁ord] at h
  have hy₁ne : y₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy₁ord
    exact absurd hy₁ord (by norm_num)
  have hZy : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = Subgroup.zpowers y₁ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyZ) ?_).symm
    rw [hZ3, Nat.card_zpowers, hy₁ord]
  have hfix : ∀ a : G, ∀ ha : a ∈ A, Sec12.thetaBarAct K ⟨a, hAK ha⟩ y₁ = y₁ := by
    intro a ha
    set γ := Sec12.thetaBarAct K ⟨a, hAK ha⟩ with hγdef
    have hγ3 : γ ^ 3 = 1 := by
      have h1 : (⟨a, hAK ha⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hAe.2 a ha)
      rw [hγdef, ← map_pow, h1, map_one]
    have hγ3' : γ * (γ * γ) = 1 := by
      rw [← pow_three]
      exact hγ3
    have h3 : ∀ x, γ (γ (γ x)) = x := by
      intro x
      have := congrArg (fun σ : MulAut (K ⧸ aschbacherSolvableCore 3 K) => σ x) hγ3'
      simpa only [MulAut.mul_apply, MulAut.one_apply] using this
    have hγZ : γ y₁ ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨h, rfl⟩ := EquivLike.surjective γ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hyZ h]
    rw [hZy] at hγZ
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hγZ)
    have hpm : y₁ ^ (n % 3) = y₁ ^ n := by
      have h := pow_mod_orderOf y₁ n
      rwa [hy₁ord] at h
    obtain ⟨j, hj3, hjγ⟩ : ∃ j : ℕ, j < 3 ∧ γ y₁ = y₁ ^ j :=
      ⟨n % 3, Nat.mod_lt _ (by norm_num), (hpm.trans hn).symm⟩
    have hγne : γ y₁ ≠ 1 := fun h =>
      hy₁ne ((map_eq_one_iff γ (EquivLike.injective γ)).mp h)
    interval_cases j
    · exact absurd (hjγ.trans (pow_zero y₁)) hγne
    · exact hjγ.trans (pow_one y₁)
    · exfalso
      have e1 : γ (γ y₁) = (y₁ ^ 2) ^ 2 := by rw [hjγ, map_pow, hjγ]
      have e2 : γ (γ (γ y₁)) = ((y₁ ^ 2) ^ 2) ^ 2 := by
        rw [e1, map_pow, map_pow, hjγ]
      have e3 : y₁ ^ 8 = y₁ := by
        have h8 := e2.symm.trans (h3 y₁)
        rw [← pow_mul, ← pow_mul] at h8
        simpa using h8
      have e8 : y₁ ^ 8 = y₁ ^ 2 := by
        rw [show (8 : ℕ) = 3 * 2 + 2 from rfl, pow_add, pow_mul, hy₁3, one_pow, one_mul]
      have hsq : y₁ * y₁ = y₁ := by
        rw [← pow_two]
        exact e8.symm.trans e3
      exact hy₁ne (mul_right_cancel (b := y₁) (by rw [one_mul]; exact hsq))
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 K) y₁
  have hxA : ∀ a ∈ A, a * (y₀ : G) * a⁻¹ * (y₀ : G)⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) K := by
    intro a ha
    have h1 := hfix a ha
    rw [← hy₀, Sec12.thetaBarAct_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 : (((K.normalizerMonoidHom ⟨a, hAK ha⟩ y₀)⁻¹ * y₀ : K) : G) ∈
        inSubgroup (aschbacherSolvableCore 3) K := ⟨_, h1, rfl⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, normalizerMonoidHom_apply_coe] at h2
    have h3 : (y₀ : G)⁻¹ * (a * (y₀ : G) * a⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) K := by
      have e : (y₀ : G)⁻¹ * (a * (y₀ : G) * a⁻¹) =
          ((a * (y₀ : G) * a⁻¹)⁻¹ * (y₀ : G))⁻¹ := by
        group
      rw [e]
      exact (inSubgroup (aschbacherSolvableCore 3) K).inv_mem h2
    have h4 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta K y₀.2) _).mp h3
    have e4 : (y₀ : G) * ((y₀ : G)⁻¹ * (a * (y₀ : G) * a⁻¹)) * (y₀ : G)⁻¹ =
        a * (y₀ : G) * a⁻¹ * (y₀ : G)⁻¹ := by
      group
    rwa [e4] at h4
  have hx3 : (y₀ : G) ^ 3 ∈ inSubgroup (aschbacherSolvableCore 3) K := by
    have h1 : y₀ ^ 3 ∈ aschbacherSolvableCore 3 K := by
      have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (y₀ ^ 3) = 1 := by
        rw [map_pow, hy₀, hy₁3]
      rw [QuotientGroup.mk'_apply] at h2
      exact (QuotientGroup.eq_one_iff _).mp h2
    exact ⟨y₀ ^ 3, h1, by simp⟩
  have hNX : inSubgroup (aschbacherSolvableCore 3) K ≤ K := Subgroup.map_subtype_le _
  obtain ⟨y, hyA, hyK, hyN⟩ := exists_mem_of_fixed_coset hAe hAmax hNX
    (Sec6.le_normalizer_theta K) (fun a ha => Sec6.normalizer_le_normalizer_theta K (hAK ha))
    (Sec11.not_three_dvd_card_inSubgroup_theta K) y₀.2 hx3 hxA
  have hy'mk : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨y, hyK⟩ : K) = y₁ := by
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hyN
    have hk' : (k : G) = y⁻¹ * (y₀ : G) := hkeq
    have hk2 : (⟨y, hyK⟩ : K)⁻¹ * y₀ = k := Subtype.ext (by simp [hk'])
    rw [← hy₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hk2]
    exact hk
  have hyC : y ∈ thetaQuotCentralizer K := by
    rw [Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (hAK hyA), Sec12.thetaBarAct_of_mem hyK,
      hy'mk]
    exact Sec12.conj_eq_one_of_mem_center hyZ
  have hyc : y ∈ A ⊓ thetaQuotCentralizer K := ⟨hyA, hyC⟩
  rw [C.cent_K] at hyc
  have hy_ne : y ≠ 1 := by
    intro h
    have h1 : (⟨y, hyK⟩ : K) = 1 := Subtype.ext h
    apply hy₁ne
    rw [← hy'mk, h1, map_one]
  have hyord : orderOf y = 3 := by
    have hdvd : orderOf y ∣ orderOf d := orderOf_dvd_of_mem_zpowers hyc
    rw [hd_ord] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy_ne
    · exact h
  have hzy : Subgroup.zpowers y = Subgroup.zpowers d := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyc) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hd_ord, hyord]
  have hdy : d ∈ Subgroup.zpowers y := by
    rw [hzy]
    exact Subgroup.mem_zpowers d
  have hdK : d ∈ K := (Subgroup.zpowers_le.mpr hyK) hdy
  refine ⟨⟨d, hdK⟩, rfl, ?_⟩
  obtain ⟨k₀, hk₀⟩ := Subgroup.mem_zpowers_iff.mp hdy
  have hdbar : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨d, hdK⟩ : K) = y₁ ^ k₀ := by
    have hc : (⟨d, hdK⟩ : K) = (⟨y, hyK⟩ : K) ^ k₀ := Subtype.ext (by simp [hk₀])
    rw [hc, map_zpow, hy'mk]
  have hdZ : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨d, hdK⟩ : K) ∈
      Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
    rw [hdbar]
    exact zpow_mem hyZ k₀
  have hdne : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨d, hdK⟩ : K) ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdN : d ∈ inSubgroup (aschbacherSolvableCore 3) K := ⟨_, h1, rfl⟩
    have hdvd : orderOf d ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) K) :=
      Subgroup.orderOf_dvd_natCard _ hdN
    rw [hd_ord] at hdvd
    exact Sec11.not_three_dvd_card_inSubgroup_theta K hdvd
  have hdord : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨d, hdK⟩ : K)) = 3 := by
    refine orderOf_eq_prime ?_ hdne
    rw [← map_pow]
    have h3 : (⟨d, hdK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [h3, map_one]
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdZ) ?_).symm
  rw [hZ3, Nat.card_zpowers, hdord]

end D

end CFSG.RankThree.PartTwo.Sec8.Hering611
