module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCoreReduction
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingular

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open Subgroup
open scoped Pointwise

theorem d4A2Sigma_eq_trialityStdA2 : d4A2Sigma = trialityStdA2 := by
  ext v
  simp only [d4A2Sigma, trialityStdA2, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem singularCentralizerData_threeSix {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1) {g : ModGL TwistTag.D4.tag Ω}
    (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω) (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ d) (a : Fin TwistTag.D4.tag.rank → Ωˣ)
    (ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε)
    (hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = p) (hne : (survivingRoots a).Nonempty)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    SingularCentralizerData σ (ℓ ^ f) x := by
  have : Fact p.Prime := ⟨hp⟩
  have ha1 : rootDiagUnit TwistTag.D4.tag a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hTp : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p :=
    ⟨ha, by rw [← hord]; exact pow_orderOf_eq_one _⟩
  obtain ⟨i, hi⟩ : ∃ i, survivingRoots a = trialitySigma i := by
    obtain ⟨-, -, -, hall⟩ :=
      triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ Ω Fr hFr hε hd
    obtain ⟨-, -, hp'⟩ := hall g hgG hFg
    obtain ⟨-, -, -, -, -, -, -, hsurv, -, -⟩ := hp' p hp hp3 hpd
    by_contra hnot
    push Not at hnot
    have hnoline : ∀ i, rootDiagUnit TwistTag.D4.tag a ∉ threeSixLine Ω Fr ε p i :=
      fun i hi => hnot i ((hsurv a hTp ha1).1 i hi)
    exact hne.ne_empty ((hsurv a hTp ha1).2 hnoline)
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4, (fun α => v • α) '' d4A2Sigma = survivingRoots a := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
    exact ⟨w, by rw [hi, d4A2Sigma_eq_trialityStdA2, ← hw]⟩
  obtain ⟨-, -, hR, -, -, hq, hZ, -, hDR, hk, z, -, X, hXR, -, -, hXk⟩ :=
    triality_three_six_singular_fixed_centralizers hℓ hf K hK σ hσ Ω Fr hFr hε hd g hgG hFg hp
      hp3 hpd a ha hord v hv x hx
  refine ⟨by rw [hR]; exact hq, ?_, by rw [hR]; exact hDR, X, by rw [hR]; exact hXR, ?_⟩
  · rw [hR, hZ]
    have h3 : (Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) : ℤ) ∣ 3 := Int.gcd_dvd_left ..
    have h3' : Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) ∣ 3 := by exact_mod_cast h3
    exact (by decide : Odd 3).of_dvd_nat h3'
  · rw [← natCard_closure_trace_threeSixEmb K Ω σ X, hXk, hk]

end CFSG.RankThree.Chevalley
