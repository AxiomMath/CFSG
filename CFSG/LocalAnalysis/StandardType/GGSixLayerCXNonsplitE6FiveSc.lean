module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6FiveAd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCentralMarking
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Cover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

namespace E6Nonsplit

section Sc


theorem e6Isogeny_ker_pow_three {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∀ z ∈ (e6Isogeny K).ker, z ^ 3 = 1 := by
  intro z hz
  have hker := CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)
  have hgc : z ∈ Subgroup.center ↥(e6Data_valid.minGroup K) := by
    rw [← hker]
    exact hz
  exact CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 K hgc

theorem ggNonsplitCoreAt_E6_sc_of_five {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hq1 : ¬ p ∣ Nat.card K - 1) (hq2 : ¬ p ∣ Nat.card K + 1)
    (hpf : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 5).eval (Nat.card K : ℤ))
    (hpC : p ∣ Nat.card ↥(adjointGroup .E6 K)) :
    ExcNonsplit.GGNonsplitCoreAt ↥(e6Data_valid.minGroup K) p := by
  haveI : Finite ↥(e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
      (Nat.card K : ℤ) + 1 := by simpa [CFSG.RankThree.Chevalley.exhaustionPhi] using hpf
  obtain ⟨hp7, -, -⟩ := CFSG.RankThree.PartOne.KE.CTE6.e6Five_data hp hp5 hpf'
  have : Fact p.Prime := ⟨hp⟩
  have hπs := e6Isogeny_surjective K
  have hkerc : (e6Isogeny K).ker ≤ Subgroup.center ↥(e6Data_valid.minGroup K) :=
    (CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center (K := K)).le
  have hcop : Nat.gcd 3 p = 1 := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  have hker1 : ∀ z, e6Isogeny K z = 1 → z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have h3 := e6Isogeny_ker_pow_three (K := K) z hz
    have := pow_gcd_eq_one.mpr ⟨h3, hzp⟩
    rwa [hcop, pow_one] at this
  refine ExcNonsplit.ggNonsplitCoreAt_of_cyclic_components hp hp2 hp3
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 K)
    (hpC.trans (Subgroup.card_dvd_of_surjective hπs)) ?_ ?_ ?_
  · intro a b ha hb hab ha1
    exact ExcNonsplit.mem_zpowers_of_central_cover (e6Isogeny K) hp hp3
      (e6Isogeny_ker_pow_three (K := K))
      (fun a' b' ha' hb' hab' ha1' => mem_zpowers_E6_ad_of_five hp hp5 hpf a' b' ha' hb' hab' ha1')
      ha hb hab ha1
  · intro X hX lab hlab hc hM
    exact not_halfSplit_of_isComponentOf_top_sc hp3 hq1 (fun h => by omega) hX hlab hc hM
  · intro a ha X hX _ hmark
    have hπa1 : e6Isogeny K a ≠ 1 := by
      intro h1
      have ha1 : a = 1 := hker1 a h1 (by rw [← ha]; exact pow_orderOf_eq_one a)
      rw [ha1, orderOf_one] at ha
      exact hp.one_lt.ne ha
    have hπo : orderOf (e6Isogeny K a) = p :=
      orderOf_eq_prime (by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]) hπa1
    have hX' := isComponentOf_map_centralizer_of_central_cover (e6Isogeny K) hπs hkerc a hX
    have hnorm : ∀ j ∈ X, a⁻¹ * j * a ∈ X := by
      intro j hj
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hX.1 hj)
      rwa [mul_assoc, hc, inv_mul_cancel_left]
    exact not_ggNbrClauseFiveMarking_of_isComponentOf_E6_ad_of_five hp hp5 hq1 hq2 hpf _ hπo _ hX'
      (ExcNonsplit.ggNbrClauseFiveMarking_map_of_central (e6Isogeny K) hkerc hnorm hmark)

end Sc

end E6Nonsplit

end CFSG.StandardType
