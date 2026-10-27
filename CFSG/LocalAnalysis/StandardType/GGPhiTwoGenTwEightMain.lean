module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightInput
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightDefs
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightLang
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightSU6
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightD4
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightConj
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh


theorem phiTwoTwE6Eight_holds : PhiTwoTwE6Eight := by
  intro K _ _ σ hcard hσ v Fr g0 hv hFr hg0C hg0
  classical
  have hcard' : Nat.card K = (2 ^ 3) ^ 2 := by simpa using hcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 3) hcard'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hcard]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : (x : K) ≠ 1 := by
    intro h
    have h1 : x = 1 := Units.ext h
    rw [h1, orderOf_one] at hx
    omega
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, ζ ^ 2 + ζ + 1 = 0 := by
    refine ⟨(x : K), ?_⟩
    have h3 : (x : K) ^ 3 = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hx3
      simpa using this
    have h : ((x : K) - 1) * ((x : K) ^ 2 + (x : K) + 1) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hx1
    · exact h
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    haveI := Fintype.ofFinite K
    have h64 : Fintype.card K = 64 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    rw [hσ, hσ, ← pow_mul, show 8 * 8 = Fintype.card K by rw [h64], FiniteField.pow_card]
  have hε : σ.toRingHom (1 : K) = -1 := by
    rw [map_one, CharTwo.neg_eq]
  obtain ⟨Ψ, hΨ⟩ := TwSU6.exists_isPsiTw σ.toRingHom hσσ (one_ne_zero) hε Nat.prime_two
    (f := 6) (by norm_num) (by rw [hcard]; norm_num)
  set abar := baseChangeGL (algebraMap K (AlgebraicClosure K)) (frameLang ζ hζ) with habar
  have hJoin : PhiJoin K σ abar = ⊤ :=
    phiJoin_eq_top_of_su6_center σ abar 1 Ψ hΨ hσσ one_ne_zero hε
      (su6AmbientCut_frameLang hcard hσ hζ hΨ) (centerCut_frameLang hcard hσ hζ)
  have hcomm : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      Fr.comp (algebraMap K (AlgebraicClosure K)) := by
    ext c
    simp [hσ, hFr]
  have htw : twistHom TwistTag.E6 (AlgebraicClosure K) Fr abar =
      abar * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v := by
    rw [habar, twistHom_baseChangeGL (algebraMap K (AlgebraicClosure K)) hcomm,
      twistHom_frameLang hσ hζ hv, map_mul, baseChangeGL_canonicalRep]
  have hkfix : twistHom TwistTag.E6 (AlgebraicClosure K) Fr (g0 * abar⁻¹) = g0 * abar⁻¹ := by
    rw [map_mul, map_inv, hg0, htw]
    group
  have hadj : abar ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    refine CFSG.LocalAnalysis.ComponentInitial.baseChangeGL_mem_adjointGroup
      (algebraMap K (AlgebraicClosure K)) ?_
    exact mul_mem (mul_mem (mul_mem (rootSL2_mem_adjointGroup _ _) (rootSL2_mem_adjointGroup _ _))
      (rootSL2_mem_adjointGroup _ _)) (rootSL2_mem_adjointGroup _ _)
  have hkmem : g0 * abar⁻¹ ∈ twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2
      ⟨mul_mem hg0C (inv_mem hadj), hkfix⟩
  have hσ' : ∀ c, σ.toRingHom c = c ^ (2 ^ 3) := fun c => by simpa using hσ c
  have hFr' : ∀ c, Fr c = c ^ (2 ^ 3) := fun c => by simpa using hFr c
  have hamb := exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 (p := 2) (f := 3)
    Nat.prime_two (by norm_num) K (by simpa [TwistTag.order] using hcard) σ.toRingHom hσ'
    (AlgebraicClosure K) Fr hFr'
  have hknorm := hamb.2.2.2.2.2 hkmem
  have htop := iSup_phiTwoCompIn_eq_top_of_mem_normalizer_map hknorm hJoin
  rw [show g0 * abar⁻¹ * abar = g0 by group] at htop
  exact htop

end CFSG.StandardType.PhiTwoRootGen

end
