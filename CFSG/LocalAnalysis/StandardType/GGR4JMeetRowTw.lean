module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKernelCore
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift
public import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
public import CFSG.LieType.Steinberg.CentralExt.GriessExceptional

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule

private theorem rwf_not_three_dvd_two_pow_add_one_of_dvd_sub {f : ℕ} (h : 3 ∣ 2 ^ f - 1) :
    ¬ 3 ∣ 2 ^ f + 1 := by
  intro h1
  have hsub : 3 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h1 h
  have heq : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by
    have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  rw [heq] at hsub
  omega

private theorem rwf_two_le_of_three_dvd_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f)
    (h : 3 ∣ 2 ^ f - 1) : 2 ≤ f := by
  by_contra hlt
  have hf1 : f = 1 := by omega
  subst hf1
  norm_num at h

theorem ggR4RowFact_twE6
  {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f - 1) :
    LargeEvenLabelAll ⟨.twE6, 0, f⟩ fun R _ I _ => GGR4RowFact R I := by
  have hf2 : 2 ≤ f := rwf_two_le_of_three_dvd_two_pow_sub_one hf h3
  have h3' : ¬ 3 ∣ 2 ^ f + 1 := rwf_not_three_dvd_two_pow_add_one_of_dvd_sub h3
  have hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* twistedE6Group 2 f),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : twistedE6Group 2 f →* E, ∀ h, π (s h) = h := by
    intro E _ _ π hπ hc
    rcases Nat.lt_or_ge f 3 with hlt | hge
    · have hf2eq : f = 2 := by omega
      subst hf2eq
      have hcard : Nat.card (GaloisField 2 (2 * 2)) = 4 ^ 2 := by
        simpa using CFSG.LieType.Universal.card_galoisField_two_mul 2 2 (by norm_num)
      exact CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_four_exists_section
        (K := GaloisField 2 (2 * 2)) (θ := frobQ 2 2) hcard
        (fun c => by rw [frobQ_apply]; norm_num) hπ hc
    · refine CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.twistedE6_exists_section_of_central
        (k := GaloisField 2 (2 * f)) (θ := frobQ 2 f) (q := 2 ^ f) ?_ ?_ ?_ hπ hc
      · calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
      · exact CFSG.LieType.Universal.card_galoisField_two_mul 2 f (by omega)
      · intro c
        rw [frobQ_apply]
  intro Q hQ
  obtain ⟨K, hField, hFinite, hK, hq⟩ := hQ
  letI : Field K := hField
  letI : Finite K := hFinite
  refine ⟨K, hField, hFinite, hK, hq, ?_⟩
  refine ⟨?_, ?_⟩
  · intro φ hφ
    have hmem : φ ∈ LargeEvenInnSet (TwE6Delta.RecipeR K f) :=
      chevIDImage_subset_inn (A := LargeEvenCartanE 6) (K := K) (H := TwE6Delta.RecipeH K f)
        (fun a ha =>
          CFSG.LocalAnalysis.GLTheoremA.K155X.diagHom_mem_twE6_of_not_three_dvd hf hK h3' ha) hφ
    obtain ⟨r, hr⟩ := hmem
    exact ⟨r, hr.symm⟩
  · intro L' _ _ ψ hψ hker hperf g hg
    obtain ⟨q', hq'surj, hq'ker⟩ := TwE6Delta.exists_sc_surjection hf hK
    haveI : Finite (twistedE6Group 2 f) := by
      have : Finite (Module.End (GaloisField 2 (2 * f))
          (Fin e6Data.d →₀ GaloisField 2 (2 * f))) :=
        Module.finite_of_finite (GaloisField 2 (2 * f))
      infer_instance
    have h1 : Nat.card ψ.ker ∣ 1 := by
      have hdvd := E6ThreeKernel.card_ker_dvd_of_split hq'surj hsec hψ hker hperf
      refine hdvd.trans ((Subgroup.card_dvd_of_le hq'ker).trans ?_)
      have hcard : Nat.card (Subgroup.center (twistedE6Group 2 f)) = Nat.gcd 3 (2 ^ f + 1) :=
        (CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
          (k := GaloisField 2 (2 * f)) (θ := frobQ 2 f)
          (q := 2 ^ f) (CFSG.LieType.Universal.card_galoisField_two_mul 2 f (by omega))
          (fun c => by rw [frobQ_apply])).1
      have hg : Nat.gcd 3 (2 ^ f + 1) = 1 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3'
      rw [hcard, hg]
    have hker1 : Nat.card ψ.ker = 1 := Nat.dvd_one.mp h1
    have hcenter_le : Subgroup.center L' ≤ ψ.ker := by
      intro z hz
      rw [MonoidHom.mem_ker]
      have hzR : ψ z ∈ Subgroup.center (TwE6Delta.RecipeR K f) := by
        rw [Subgroup.mem_center_iff]
        intro r
        obtain ⟨x, rfl⟩ := hψ r
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
      rwa [TwE6Delta.center_recipeR_eq_bot hf hK, Subgroup.mem_bot] at hzR
    have hgker : g ∈ ψ.ker := hcenter_le hg
    have hord : orderOf g ∣ Nat.card ψ.ker := by
      have h2 : orderOf (⟨g, hgker⟩ : ψ.ker) ∣ Nat.card ψ.ker := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk] at h2
    rw [hker1, Nat.dvd_one] at hord
    rw [hord]
    exact Nat.coprime_one_right 3

end CFSG.StandardType

end
