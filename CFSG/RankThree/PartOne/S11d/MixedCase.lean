module

public import CFSG.RankThree.PartOne.S11d.Sec109Common
public import CFSG.RankThree.PartOne.S11d.FactsNormalizer

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven
open scoped commutatorElement

namespace Sec109

theorem mixedCaseImpossible_of (hOut : FieldAutNormalizerPower) : MixedCaseImpossible := by
  intro G _ _ p A c L B n h b S K hW hK hSK hEven hZ a d haA hdA hd1 hAeq hdK hfa hc
  have hp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp7 : p = 7 := h.p_eq
  have hbB : b ∈ B := hW.b_mem
  have hbA : b ∈ A := h.B_le_A hbB
  have hb1 : b ≠ 1 := hW.b_ne_one
  have hbp : b ^ p = 1 := h.pow_p_eq_one hbA
  have hdp : d ^ p = 1 := h.pow_p_eq_one hdA
  have hKθ : K ∈ thetaComponentsAt p b := hK.2
  have hKF : K ≤ centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hKθ).1
  have hdK' : d ∈ K := (mem_inf.mp (hdK ▸ mem_zpowers d)).2
  have hperf : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsAt hKθ
  have hq : CFSG.IsQuasisimple ↥K := S11d.isQuasisimple_of_evenLie hperf hEven
  have hbK : ∀ k ∈ K, k * b = b * k := fun k hk => mem_centralizer_singleton_iff.mp (hKF hk)
  obtain ⟨x, lam, hxL, hx1, hxNB, hlam, hxB⟩ := h.exists_x
  have hxc : x * c = c * x := h.mem_L_comm_c hxL
  have hxA : x ∈ normalizer (A : Set G) := h.mem_normalizer_A hxNB hxc
  have hxb : x * b * x⁻¹ = b ^ lam := hxB b hbB
  have hlam7 : ¬ (p : ℤ) ∣ lam - 1 := by rw [hp7]; exact_mod_cast hlam
  have hlam0 : ¬ (p : ℤ) ∣ lam := by
    intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    apply hb1
    have h1 : b ^ lam = 1 := by
      rw [hk, zpow_mul, zpow_natCast, hbp, one_zpow]
    have h2 : x * b * x⁻¹ = 1 := by rw [hxb, h1]
    simpa using h2
  obtain ⟨s, t, hst⟩ := (S11d.mem_zpowers_sup_zpowers_iff
    (show Commute b d from h.A_comm b hbA d hdA)).mp hc
  have hconj_c : x * c * x⁻¹ = c := by rw [hxc]; group
  have hxbs : x * b ^ s * x⁻¹ = b ^ (lam * s) := by
    rw [← conj_zpow, hxb, ← zpow_mul]
  have hxdt : x * d ^ t * x⁻¹ = (x * d * x⁻¹) ^ t := conj_zpow.symm
  have h1 : b ^ s * d ^ t = b ^ (lam * s) * (x * d * x⁻¹) ^ t := by
    have e1 : x * (b ^ s * d ^ t) * x⁻¹ = (x * b ^ s * x⁻¹) * (x * d ^ t * x⁻¹) := by group
    rw [hxbs, hxdt, ← hst, hconj_c] at e1
    rw [← hst]
    exact e1
  have hxd : x * d * x⁻¹ ∈ A := S11d.conj_mem_of_mem_normalizer hxA hdA
  by_cases hKK : conjBy x K = K
  ·
    have hxK : x ∈ normalizer (K : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq]
      exact hKK
    have hd'K : x * d * x⁻¹ ∈ K := S11d.conj_mem_of_mem_normalizer hxK hdK'
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hdK ▸ (mem_inf.mpr ⟨hxd, hd'K⟩) : x * d * x⁻¹ ∈ zpowers d)
    have h2 : b ^ s * d ^ t = b ^ (lam * s) * d ^ (m * t) := by
      rw [h1, ← hm, ← zpow_mul]
    have hg : d ^ (m * t - t) = b ^ (s - lam * s) := by
      have e : (b ^ (lam * s))⁻¹ * b ^ s = d ^ (m * t) * (d ^ t)⁻¹ := by
        have e2 : (b ^ (lam * s))⁻¹ * (b ^ s * d ^ t) * (d ^ t)⁻¹ =
            (b ^ (lam * s))⁻¹ * (b ^ (lam * s) * d ^ (m * t)) * (d ^ t)⁻¹ := by rw [h2]
        simpa [mul_assoc] using e2
      calc d ^ (m * t - t) = d ^ (m * t) * (d ^ t)⁻¹ := by rw [zpow_sub]
        _ = (b ^ (lam * s))⁻¹ * b ^ s := e.symm
        _ = b ^ (s - lam * s) := by rw [← zpow_neg, ← zpow_add]; congr 1; ring
    have hgK : d ^ (m * t - t) ∈ K := zpow_mem hdK' _
    have hgc : (⟨d ^ (m * t - t), hgK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      show (k : G) * d ^ (m * t - t) = d ^ (m * t - t) * (k : G)
      rw [hg]
      exact ((show Commute (k : G) b from hbK k k.2).zpow_right _).eq
    have hg1 : d ^ (m * t - t) = 1 := by
      have hgp : (⟨d ^ (m * t - t), hgK⟩ : K) ^ p = 1 := Subtype.ext (by
        show (d ^ (m * t - t)) ^ p = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow])
      exact congrArg Subtype.val (S11d.eq_one_of_mem_center_of_pow hp hZ hgc hgp)
    have hbs : b ^ (s - lam * s) = 1 := hg ▸ hg1
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hdvd : (p : ℤ) ∣ s := by
      have hord : orderOf b = p := orderOf_eq_prime hbp hb1
      have h3 : (orderOf b : ℤ) ∣ s - lam * s := orderOf_dvd_iff_zpow_eq_one.mpr hbs
      rw [hord] at h3
      have h4 : (p : ℤ) ∣ s * (lam - 1) := by
        have : s * (lam - 1) = -(s - lam * s) := by ring
        rw [this]
        exact (dvd_neg).mpr h3
      rcases hpZ.dvd_or_dvd h4 with h5 | h5
      · exact h5
      · exact absurd h5 hlam7
    have hbs1 : b ^ s = 1 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, zpow_mul, zpow_natCast, hbp, one_zpow]
    have hcd : c = d ^ t := by rw [hst, hbs1, one_mul]
    have hcK : c ∈ K := hcd ▸ zpow_mem hdK' t
    have key : x * a * x⁻¹ * a ^ (-lam) ∈ K ⊔ centralizer (K : Set G) := by
      obtain ⟨β, hβ, j, hajeq⟩ := h.exists_decomp haA
      have hβA : β ∈ A := h.B_le_A hβ
      have hβc : Commute β c := h.A_comm β hβA c h.c_mem
      have hβγ : Commute β (c ^ j) := hβc.zpow_right j
      have hxβ : x * β * x⁻¹ = β ^ lam := hxB β hβ
      have hxγ : x * c ^ j * x⁻¹ = c ^ j := by rw [← conj_zpow, hconj_c]
      have hγβ : Commute (c ^ j) (β ^ (-lam)) := (hβγ.symm).zpow_right (-lam)
      have e1 : x * a * x⁻¹ = β ^ lam * c ^ j := by
        rw [hajeq]
        calc x * (β * c ^ j) * x⁻¹ = (x * β * x⁻¹) * (x * c ^ j * x⁻¹) := by group
          _ = β ^ lam * c ^ j := by rw [hxβ, hxγ]
      have e2 : a ^ (-lam) = β ^ (-lam) * (c ^ j) ^ (-lam) := by
        rw [hajeq]
        exact hβγ.mul_zpow (-lam)
      have e3 : x * a * x⁻¹ * a ^ (-lam) = (c ^ j) ^ (1 - lam) := by
        rw [e1, e2]
        calc β ^ lam * c ^ j * (β ^ (-lam) * (c ^ j) ^ (-lam))
            = β ^ lam * (c ^ j * β ^ (-lam)) * (c ^ j) ^ (-lam) := by group
          _ = β ^ lam * (β ^ (-lam) * c ^ j) * (c ^ j) ^ (-lam) := by rw [hγβ.eq]
          _ = (c ^ j) ^ (1 - lam) := by
            rw [sub_eq_add_neg, zpow_add, zpow_one]
            group
      rw [e3]
      exact Subgroup.mem_sup_left (zpow_mem (zpow_mem hcK j) _)
    have hevK : CFSG.Assembly.evenRank ↥(K ⊔ zpowers a) ≤ 3 :=
      (Sec9A.evenRank_subgroup_le (K ⊔ zpowers a)).trans (sectionTenSetup_evenRank_eq h.setup).le
    have := hOut G p K a x lam ⟨hp, by omega, hq, hEven, hevK, hZ, hfa⟩ (by omega) hxK key
    exact hlam7 this
  ·
    set K' := conjBy x K with hK'
    have hK'θ : K' ∈ thetaComponentsAt p b :=
      S11d.conjBy_mem_thetaComponentsAt_of_zpow hp hKθ hbp hlam0 hxb
    have huK' : (x * d * x⁻¹) ^ t ∈ K' := by
      refine zpow_mem ?_ t
      rw [hK', Equivariance.mem_conjBy]
      have e : x⁻¹ * (x * d * x⁻¹) * x = d := by group
      rw [e]
      exact hdK'
    have hvK : d ^ t ∈ K := zpow_mem hdK' t
    have hvz : d ^ t = b ^ (lam * s - s) * (x * d * x⁻¹) ^ t := by
      calc d ^ t = b ^ (-s) * (b ^ s * d ^ t) := by group
        _ = b ^ (-s) * (b ^ (lam * s) * (x * d * x⁻¹) ^ t) := by rw [h1]
        _ = b ^ (lam * s - s) * (x * d * x⁻¹) ^ t := by
          rw [← mul_assoc, ← zpow_add]
          congr 2
          ring
    have huF : (x * d * x⁻¹) ^ t ∈ centralizer ({b} : Set G) :=
      (mem_thetaComponentsAt_iff.mp hK'θ).1 huK'
    have hcomm : ∀ k ∈ K, d ^ t * k * (d ^ t)⁻¹ * k⁻¹ ∈
        inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set G)) := by
      intro k hk
      have hkF : k ∈ centralizer ({b} : Set G) := hKF hk
      have hwF : (x * d * x⁻¹) ^ t * k * ((x * d * x⁻¹) ^ t)⁻¹ ∈ centralizer ({b} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ huF hkF) (Subgroup.inv_mem _ huF)
      have hzw : Commute (b ^ (lam * s - s))
          ((x * d * x⁻¹) ^ t * k * ((x * d * x⁻¹) ^ t)⁻¹) := by
        have h5 : Commute ((x * d * x⁻¹) ^ t * k * ((x * d * x⁻¹) ^ t)⁻¹) b :=
          mem_centralizer_singleton_iff.mp hwF
        exact (h5.zpow_right _).symm
      have e : d ^ t * k * (d ^ t)⁻¹ * k⁻¹ =
          (x * d * x⁻¹) ^ t * k * ((x * d * x⁻¹) ^ t)⁻¹ * k⁻¹ := by
        rw [hvz]
        calc b ^ (lam * s - s) * (x * d * x⁻¹) ^ t * k *
              (b ^ (lam * s - s) * (x * d * x⁻¹) ^ t)⁻¹ * k⁻¹
            = (b ^ (lam * s - s) * ((x * d * x⁻¹) ^ t * k * ((x * d * x⁻¹) ^ t)⁻¹) *
                (b ^ (lam * s - s))⁻¹) * k⁻¹ := by group
          _ = (x * d * x⁻¹) ^ t * k * ((x * d * x⁻¹) ^ t)⁻¹ * k⁻¹ := by
            rw [hzw.eq]
            group
      rw [e]
      exact S11d.commutator_mem_theta_of_ne hp hK'θ hKθ hKK _ huK' k hk
    have hvc : (⟨d ^ t, hvK⟩ : K) ∈ Subgroup.center K := by
      apply S11d.mem_center_of_commutators_mem_center hq
      intro k'
      have h2 := hcomm k' k'.2
      have h3 : (d ^ t * (k' : G) * (d ^ t)⁻¹ * (k' : G)⁻¹) ∈ K :=
        K.mul_mem (K.mul_mem (K.mul_mem hvK k'.2) (K.inv_mem hvK)) (K.inv_mem k'.2)
      have h4 : (d ^ t * (k' : G) * (d ^ t)⁻¹ * (k' : G)⁻¹) ∈
          inSubgroup (aschbacherSolvableCore p) K := by
        rw [theta_eq_inf_of_mem_thetaComponentsAt hp hKθ]
        exact ⟨h3, h2⟩
      obtain ⟨y, hy, hyeq⟩ := h4
      have hyc := theta_le_center_of_quasisimple hp hq hy
      have hyy : (⟨d ^ t, hvK⟩ * k' * ⟨d ^ t, hvK⟩⁻¹ * k'⁻¹ : K) = y :=
        Subtype.ext (by simpa using hyeq.symm)
      rw [hyy]
      exact hyc
    have hv1 : d ^ t = 1 := by
      have hvp : (⟨d ^ t, hvK⟩ : K) ^ p = 1 := Subtype.ext (by
        show (d ^ t) ^ p = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow])
      exact congrArg Subtype.val (S11d.eq_one_of_mem_center_of_pow hp hZ hvc hvp)
    apply h.c_notMem_B
    rw [hst, hv1, mul_one]
    exact zpow_mem hbB s

end Sec109

end CFSG.RankThree.PartOne
