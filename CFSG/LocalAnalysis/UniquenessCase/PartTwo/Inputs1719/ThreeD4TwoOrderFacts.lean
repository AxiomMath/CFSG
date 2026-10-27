module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoFacts
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Is3D4)
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.Open (ordTrialityD4)

theorem exists_mulEquiv_graphFixedRootGroup_of_is3D4_one
    {X : Type} [Group X] (h : Is3D4 X 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = 2 ^ 3 ∧
      (∀ c, σ c = c ^ 2) ∧
      Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hX' : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 1 :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 h).2
  obtain ⟨⟨hp, hf, -⟩, hmod⟩ := hX'
  obtain ⟨K, hF, hFin, σ, hK, hσ, he⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hmod
  refine ⟨K, hF, hFin, σ, ?_, by simpa only [pow_one] using hσ, he⟩
  rw [hK]
  norm_num [TwistTag.order]

theorem card_eq_of_is3D4_one
    {X : Type} [Group X] [Finite X] (h : Is3D4 X 1) : Nat.card X = 211341312 := by
  obtain ⟨K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_of_is3D4_one h
  have hK3 : Nat.card K = (2 ^ 1) ^ 3 := by
    simpa only [pow_one] using hK
  have hσ1 : ∀ c, σ.toRingHom c = c ^ (2 ^ 1) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, pow_one]
    exact hσ c
  have hC : Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      ordTrialityD4 (2 ^ 1) :=
    CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two (f := 1) le_rfl hK3
      σ.toRingHom hσ1
  calc
    Nat.card X = Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      Nat.card_congr e.toEquiv
    _ = ordTrialityD4 (2 ^ 1) := hC
    _ = 211341312 := by norm_num [CFSG.Open.ordTrialityD4]

theorem k_3D4TwoSmallRank_holds :
    K_3D4TwoSmallRank := by
  intro X _ _ hX p hp hp2 hp3 hp7
  have hcard : Nat.card X = 211341312 := card_eq_of_is3D4_one hX
  have hnd : ¬ p ^ 2 ∣ Nat.card X := by
    rw [hcard]
    have hfac : (211341312 : ℕ) = 2 ^ 12 * 3 ^ 4 * 7 ^ 2 * 13 := by norm_num
    rw [hfac]
    intro hdvd
    have hpdvd : p ∣ 2 ^ 12 * 3 ^ 4 * 7 ^ 2 * 13 :=
      Nat.dvd_of_pow_dvd (by norm_num) hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hpdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
        · have hp2' : p = 2 :=
            (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)
          exact hp2 hp2'
        · have hp3' : p = 3 :=
            (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
          exact hp3 hp3'
      · have hp7' : p = 7 :=
          (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h2)
        exact hp7 hp7'
    · have hp13 : p = 13 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1
      rw [hp13] at hdvd
      exact absurd hdvd (by norm_num)
  have h1 : CFSG.pRank p X ≤ 1 :=
    CFSG.RankThree.PartTwo.Sec4.Res417Three.pRank_le_one_of_not_dvd hnd
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top p X] at h1

@[expose] def K_3D4TwoSevenNormalizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K], LieModel K .trialityD4 0 2 1 →
    ∀ x : K, orderOf x = 7 →
      CFSG.Open.pRank 3 (⊤ : Subgroup (normalizer (Subgroup.zpowers x : Set K))) = 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
