module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassSetup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingClassClosure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassBasic

public section

namespace CFSG.ShultStronglyClosedTI.MixedClass

open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem thompsonPairs_odd_half {H Q : Subgroup G} {z u : G}
    (h : InvolutionPointLocalEmbedding H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (heven : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    (hu : orderOf u = 2) (hzu : ¬ IsConj z u)
    (hcent : ∀ v : G, IsConj u v → ∀ g : G,
      rightCosetTranslate H (rightCosetMk H g) v = rightCosetMk H g →
        ∀ q ∈ Q, Commute v (g⁻¹ * q * g))
    {a : G} (ha : orderOf a = 2) {p : G × G} (hp : p ∈ InvolutionCounting.thompsonPairs u z a) :
    IsConj z (a * p.1) ∧ Commute (a * p.1) p.1 ∧ Odd (orderOf (a * p.1 * p.2)) := by
  have hz2 : z * z = 1 := InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two h.distinguished_order
  have hu2 : u * u = 1 := InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two hu
  have ha2 : a * a = 1 := InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two ha
  have hcen := InvolutionCounting.mem_centralizer_of_mem_thompsonPairs hu2 hz2 ha2 hp
  obtain ⟨h1, h2, hmem⟩ := hp
  have hv := InvolutionCounting.mul_self_eq_one_of_isConj hu2 h1
  have hs := InvolutionCounting.mul_self_eq_one_of_isConj hz2 h2
  have hvs : ¬ IsConj p.1 p.2 := fun hc =>
    hzu (isConj_comm.mp ((h1.trans hc).trans (isConj_comm.mp h2)))
  obtain ⟨d, hd0, hd⟩ := InvolutionCounting.exists_orderOf_mul_eq_two_mul hv hs hvs
  have hwc : a = (p.1 * p.2) ^ d :=
    (InvolutionCounting.mem_zpowers_iff_eq_pow_half hd hd0 ha).mp hmem
  rcases Nat.even_or_odd d with hde | hdo
  · exfalso
    obtain ⟨rfl, hsq⟩ :=
      InvolutionCounting.eq_two_and_isConj_sq_of_even hz2 hv h2 heven hprod hd hd0 hde
    rw [← hwc] at hsq
    have haD : a ∈ involutionPointClass z := mem_pointClass_iff_isConj.mpr hsq
    obtain ⟨γ, hγ⟩ := class_fixed_exists h haD
    obtain ⟨g, rfl⟩ := exists_rightCosetMk γ
    have hva : Commute a p.1 := (Subgroup.mem_centralizer_singleton_iff.mp hcen.1).symm
    have hsa : Commute a p.2 := (Subgroup.mem_centralizer_singleton_iff.mp hcen.2).symm
    have hvfix := class_fixed_of_commute h haD hva hγ
    have hsfix := class_fixed_of_commute h haD hsa hγ
    have hsQ := conj_mem_point_subgroup_of_fixed h hQclass (mem_pointClass_iff_isConj.mpr h2) hsfix
    have hcomm := hcent p.1 h1 g hvfix _ hsQ
    rw [show g⁻¹ * (g * p.2 * g⁻¹) * g = p.2 by group] at hcomm
    have hsq1 : (p.1 * p.2) ^ 2 = 1 := by
      rw [sq, show p.1 * p.2 * (p.1 * p.2) = p.1 * (p.2 * p.1) * p.2 by group, ← hcomm.eq,
        show p.1 * (p.1 * p.2) * p.2 = (p.1 * p.1) * (p.2 * p.2) by group, hv, hs, one_mul]
    rw [← hwc] at hsq1
    rw [hsq1, orderOf_one] at ha
    exact absurd ha (by norm_num)
  · obtain ⟨hr, hrv⟩ := InvolutionCounting.isConj_pow_mul_and_commute_of_odd hz2 hv h2 hd hdo
    rw [← hwc] at hr hrv
    refine ⟨hr, hrv, ?_⟩
    obtain ⟨j, rfl⟩ := hdo
    refine Odd.of_dvd_nat ⟨j, rfl⟩ (orderOf_dvd_of_pow_eq_one ?_)
    rw [hwc, mul_assoc, ← pow_succ, ← pow_mul,
      show (2 * j + 1 + 1) * (2 * j + 1) = 2 * (2 * j + 1) * (j + 1) by ring, pow_mul, ← hd,
      pow_orderOf_eq_one, one_pow]

theorem thompsonPairCount_eq_zero_of_not_isConj {H Q : Subgroup G} {z u w : G}
    (h : InvolutionPointLocalEmbedding H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (heven : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    (hu : orderOf u = 2) (hzu : ¬ IsConj z u)
    (hcent : ∀ v : G, IsConj u v → ∀ g : G,
      rightCosetTranslate H (rightCosetMk H g) v = rightCosetMk H g →
        ∀ q ∈ Q, Commute v (g⁻¹ * q * g))
    (hmixed : ∀ v r : G, IsConj u v → IsConj z r → Commute v r → IsConj w (v * r))
    {a : G} (ha : orderOf a = 2) (hwa : ¬ IsConj w a) :
    InvolutionCounting.thompsonPairCount u z a = 0 := by
  refine Nat.card_eq_zero.mpr (Or.inl ⟨fun p => hwa ?_⟩)
  obtain ⟨hr, hrv, -⟩ := thompsonPairs_odd_half h hQclass heven hprod hu hzu hcent ha p.2
  have hva := hmixed _ _ p.2.1 hr hrv.symm
  have ha2 : a * a = 1 := InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two ha
  have hv2 : (p : G × G).1 * (p : G × G).1 = 1 :=
    InvolutionCounting.mul_self_eq_one_of_isConj
      (InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two hu) p.2.1
  rwa [← hrv.eq, mul_assoc, hv2, mul_one] at hva

theorem thompsonPairs_eq_singleton {H Q : Subgroup G} {z u e : G}
    (h : InvolutionPointLocalEmbedding H z) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (heven : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    (hu : orderOf u = 2) (hzu : ¬ IsConj z u)
    (hcent : ∀ v : G, IsConj u v → ∀ g : G,
      rightCosetTranslate H (rightCosetMk H g) v = rightCosetMk H g →
        ∀ q ∈ Q, Commute v (g⁻¹ * q * g))
    (he : e ∈ (Q : Set G) \ {1}) (hw : orderOf (u * e) = 2)
    (hwH : Subgroup.centralizer ({u * e} : Set G) ≤ H)
    (hU : ∀ f ∈ (Q : Set G) \ {1}, ¬ IsConj u (u * f)) :
    InvolutionCounting.thompsonPairs u z (u * e) = {(u, e)} := by
  have hsqQ : ∀ x ∈ Q, x * x = 1 := fun x hx => by rw [← sq]; exact hQ.2 x hx
  have hw2 : u * e * (u * e) = 1 := InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two hw
  have hu2 : u * u = 1 := InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two hu
  have hz2 : z * z = 1 := InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two h.distinguished_order
  ext p
  constructor
  · intro hp
    obtain ⟨hr, hrv, hodd⟩ := thompsonPairs_odd_half h hQclass heven hprod hu hzu hcent hw hp
    have hcen := InvolutionCounting.mem_centralizer_of_mem_thompsonPairs hu2 hz2 hw2 hp
    set w := u * e with hwdef
    have hwC : w ∈ Subgroup.centralizer ({w} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hrC : w * p.1 ∈ Subgroup.centralizer ({w} : Set G) := Subgroup.mul_mem _ hwC hcen.1
    have hrQ : w * p.1 ∈ (Q : Set G) \ {1} := by
      rw [← class_inter_point h hQclass]
      exact ⟨mem_pointClass_iff_isConj.mpr hr, hwH hrC⟩
    have hsQ : p.2 ∈ (Q : Set G) \ {1} := by
      rw [← class_inter_point h hQclass]
      exact ⟨mem_pointClass_iff_isConj.mpr hp.2.1, hwH hcen.2⟩
    have hprodQ : w * p.1 * p.2 ∈ Q := Q.mul_mem hrQ.1 hsQ.1
    have hone : w * p.1 * p.2 = 1 := by
      have hdvd : orderOf (w * p.1 * p.2) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsqQ _ hprodQ)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact orderOf_eq_one_iff.mp h1
      · rw [h2] at hodd
        exact absurd hodd (by decide)
    have hs_eq : p.2 = w * p.1 := by
      have h' : p.2 = (w * p.1)⁻¹ := eq_inv_of_mul_eq_one_right hone
      rw [h', inv_eq_of_mul_eq_one_right (hsqQ _ hrQ.1)]
    have hv_eq : p.1 = u * (e * (w * p.1)) := by
      rw [hwdef, show u * (e * (u * e * p.1)) = (u * e) * (u * e) * p.1 by group, hw2, one_mul]
    have her : e * (w * p.1) = 1 := by
      by_contra hne
      exact hU _ ⟨Q.mul_mem he.1 hrQ.1, hne⟩ (hv_eq ▸ hp.1)
    have hr_eq : w * p.1 = e := by
      rw [← inv_eq_of_mul_eq_one_right (hsqQ e he.1)]
      exact eq_inv_of_mul_eq_one_right her
    have hv' : p.1 = u := by rw [hv_eq, her, mul_one]
    ext
    · exact hv'
    · rw [hs_eq, hr_eq]
  · rintro rfl
    exact ⟨IsConj.refl u, mem_pointClass_iff_isConj.mp (point_subgroup_class h hQclass he),
      Subgroup.mem_zpowers _⟩

theorem thompsonPairCount_eq_one {H Q : Subgroup G} {z u e : G}
    (h : InvolutionPointLocalEmbedding H z) (hQ : CFSG.Open.IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    (heven : ∀ r s : G, IsConj z r → IsConj z s → Even (orderOf (r * s)) → Commute r s)
    (hprod : ∀ r s : G, IsConj z r → IsConj z s → r ≠ s → Commute r s → IsConj z (r * s))
    (hu : orderOf u = 2) (hzu : ¬ IsConj z u)
    (hcent : ∀ v : G, IsConj u v → ∀ g : G,
      rightCosetTranslate H (rightCosetMk H g) v = rightCosetMk H g →
        ∀ q ∈ Q, Commute v (g⁻¹ * q * g))
    (he : e ∈ (Q : Set G) \ {1}) (hw : orderOf (u * e) = 2)
    (hwH : Subgroup.centralizer ({u * e} : Set G) ≤ H)
    (hU : ∀ f ∈ (Q : Set G) \ {1}, ¬ IsConj u (u * f)) :
    InvolutionCounting.thompsonPairCount u z (u * e) = 1 := by
  rw [InvolutionCounting.thompsonPairCount,
    thompsonPairs_eq_singleton h hQ hQclass heven hprod hu hzu hcent he hw hwH hU,
    Nat.card_coe_set_eq, Set.ncard_singleton]

end CFSG.ShultStronglyClosedTI.MixedClass
