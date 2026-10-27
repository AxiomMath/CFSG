module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainSylE
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainDstr
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainFStr
public import CFSG.LocalAnalysis.StandardType.FS81.GoldSharedSylow
public import CFSG.LocalAnalysis.StandardType.FS81.GoldSharedNine

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private theorem nm_normalizes_of_sylow_two {X : Type} [Group X] [Finite X] {H R T₀ : Subgroup X}
    (hTR : T₀ ≤ R) (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hTn : ∀ r ∈ R, ∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀)
    (hT2 : IsPGroup 2 T₀) (hodd : Odd (T₀.relIndex R)) :
    ∀ h ∈ H, ∀ t ∈ T₀, h * t * h⁻¹ ∈ T₀ := by
  have key : ∀ x ∈ R, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ T₀ := by
    intro x hx hx2
    obtain ⟨k, hk⟩ := hx2
    have hN : (T₀.subgroupOf R).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hTn (g : X) g.2 (n : X) hn
    have hpow : x ^ (T₀.relIndex R) ∈ T₀ := by
      have h := @Subgroup.pow_index_mem R _ (T₀.subgroupOf R) hN ⟨x, hx⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa [Subgroup.relIndex] using h
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hm2 : (T₀.relIndex R).Coprime (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
    have hmo : (T₀.relIndex R).Coprime (orderOf x) :=
      Nat.Coprime.coprime_dvd_right hdvd hm2
    exact (Subgroup.zpowers_le.2 hpow)
      ((mem_zpowers_pow_iff (g := x) (k := T₀.relIndex R)).2 hmo)
  intro h hh t ht
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  refine key (h * t * h⁻¹) (hRn h hh t (hTR ht)) ⟨k, ?_⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [conj_pow, htk]
  simp

private theorem nm_fgrp_isPGroup {X : Type} [Group X] [Finite X] (S : N7MSetup X) :
    IsPGroup 2 S.Fgrp := by
  intro f
  refine ⟨1, ?_⟩
  show f ^ (2 ^ 1) = 1
  rw [pow_one, pow_two]
  exact Subtype.ext (S.ρ_inj (by
    show S.ρ (f.1 * f.1) = S.ρ 1
    rw [map_mul, map_one]
    exact nmF_sq f.2))

private theorem nm_false_of_odd_section {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    {R T₀ : Subgroup X} (hTR : T₀ ≤ R)
    (hRN : R ≤ Subgroup.normalizer (S.F1grp : Set X))
    (hRn : ∀ n ∈ Subgroup.normalizer (S.F1grp : Set X), ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    (hTn : ∀ r ∈ R, ∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) (hT2 : IsPGroup 2 T₀)
    (hodd : Odd (T₀.relIndex R)) (hne : ¬ R ≤ T₀) : False := by
  have hH1N : S.H1grp ≤ Subgroup.normalizer (S.F1grp : Set X) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr ((nm_normalizer_F1 S).mpr hx)
  have hRH1 : R ≤ S.H1grp := fun r hr =>
    (nm_normalizer_F1 S).mp (Subgroup.mem_normalizer_iff.mp (hRN hr))
  have hRnH : ∀ n ∈ S.H1grp, ∀ r ∈ R, n * r * n⁻¹ ∈ R := fun n hn r hr => hRn n (hH1N hn) r hr
  have hT0F : T₀ ≤ S.Fgrp := nm_le_F_of_normal_two S (hTR.trans (hRH1.trans S.H1grp_le_FKgrp))
    (nm_normalizes_of_sylow_two hTR hRnH hTn hT2 hodd) hT2
  have hRF : R ≤ S.Fgrp := nm_le_F_of_odd_normal S (hRH1.trans S.H1grp_le_FKgrp) hRnH
    (hodd.of_dvd_nat (Subgroup.relIndex_dvd_of_le_left R hT0F))
  refine hne ?_
  have hdvd : T₀.relIndex R ∣ Nat.card R := by
    simpa only [Subgroup.relIndex] using Subgroup.index_dvd_card (T₀.subgroupOf R)
  obtain ⟨k, hk⟩ := isPGroup_iff_card_dvd_pow.mp ((nm_fgrp_isPGroup S).to_le hRF)
  have hcop : Nat.Coprime (T₀.relIndex R) (2 ^ k) :=
    (Nat.coprime_two_right.mpr hodd).pow_right k
  exact Subgroup.relIndex_eq_one.mp (hcop.eq_one_of_dvd (hdvd.trans hk))

theorem nm_not_weak (hG : GoldExclusionSylow) {X : Type} [Group X] [Finite X]
    (S : N7MSetup X) : ¬ S.Weak := by
  intro hW
  obtain ⟨P, t, hPH, hF1P, htE6, htc⟩ := nm_sylow_E6 S hW
  have htF1 : t ∈ S.F1grp := nmE6_subset_nmF1 htE6
  have hcl := stronglyClosed_of_centralizer P (hF1P htF1) htc S.F1grp
    (nm_closure_F1 S hW hPH hF1P htE6).symm S.F1grp_comm
    (fun a ha d hd hPd => nm_strong_D S hW htE6 ha hd hPH hPd)
  rcases hG X S.odd_core P S.F1grp hF1P S.F1grp_comm hcl with hN | hdata
  · exact (not_le.mpr S.big) (nm_card_le_of_F1_normal S hN)
  · obtain ⟨R, T₀, -, hTR, hRN, hRn, hTn, hT2, hodd, hne⟩ := hdata
    exact nm_false_of_odd_section S hTR hRN hRn hTn hT2 hodd hne

end CFSG.StandardType.FrameRoute.FS81

end
