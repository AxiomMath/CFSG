module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3BstarCentralizer
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTags
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfTwoLocal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank ExcFrames
  ExcFramesHalf

section Core

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}

theorem GGSixCtxV2.twoLocalRank_eq_four_of_a3 (ha₀ : GGLNoncyclicInput)
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) (hA : GGSixLSevenA3Case J) :
    p = 3 ∧ LargeEvenTwoLocalRank p G = 4 := by
  obtain ⟨hp3, hB, -⟩ := hctx.a3_structure ha₀ hA
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  subst hp3
  refine ⟨rfl, ?_⟩
  have h : 3 ^ LargeEvenTwoLocalRank 3 G = 3 ^ 4 := hBc.symm.trans hB
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h

theorem rank_pred_le_twoLocalRank_of_half {τ : Tag} {K : Type} [Field K] {q : ℕ} (hq : q.Prime)
    (χ : adjointGroup τ K →* G) (hχ : Function.Injective χ)
    (h1 : ∃ E U : Subgroup (adjointGroup τ K), IsElemAbelian q E ∧
      Nat.card E = q ^ (τ.rank - 1) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        E ≤ Subgroup.normalizer (U : Set (adjointGroup τ K))) :
    τ.rank - 1 ≤ LargeEvenTwoLocalRank q G := by
  obtain ⟨E, U, hE, hEc, hU, hU2, hEU⟩ := h1
  have hUne : U.map χ ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hχ]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map χ : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  have hle : E.map χ ≤ Subgroup.normalizer ((U.map χ : Subgroup G) : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hn := Subgroup.mem_normalizer_iff.mp (hEU he)
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨e * u * e⁻¹, (hn u).mp hu, by simp only [map_mul, map_inv]⟩
    · rintro ⟨u', hu', hyu⟩
      have hy : y = χ (e⁻¹ * u' * e) := by
        simp only [map_mul, map_inv, hyu]
        group
      refine ⟨_, ?_, hy.symm⟩
      exact (hn (e⁻¹ * u' * e)).mpr (by
        rw [show e * (e⁻¹ * u' * e) * e⁻¹ = u' by group]
        exact hu')
  refine TableB.le_twoLocalRank hq.one_lt hTL (TableB.le_pRank_of_le hq.one_lt hle
    (isElemAbelian_map_frame χ hE) ?_)
  rw [Subgroup.card_map_of_injective hχ, hEc]

end Core

theorem three_dvd_two_pow_pred_or_succ (f : ℕ) : 3 ∣ 2 ^ f - 1 ∨ 3 ∣ 2 ^ f + 1 := by
  have h : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by
    induction f with
    | zero => left; norm_num
    | succ k ih => rw [pow_succ]; omega
  omega

section Tags


theorem ggSixLSixSevenConjA3At_E8 : GGSixLSixSevenConjA3At .E8 := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ _ hA
  exfalso
  obtain ⟨hp3, hm⟩ := hctx.twoLocalRank_eq_four_of_a3 ggLNoncyclicInput_holds hA
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have := Fact.mk hp
  obtain ⟨-, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  rcases three_dvd_two_pow_pred_or_succ f with h | h
  · have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK, hp3]; exact h
    have h8 := rank_le_twoLocalRank (τ := .E8) (by decide) hp hpK
      (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E8 (Nat.coprime_one_left p)) ψ hinj
    rw [hm] at h8
    exact absurd h8 (by decide)
  · have hpK : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK, hp3]; exact h
    have h8 := rank_pred_le_twoLocalRank_of_half (τ := .E8) hp ψ hinj
      (ggExcHalfTwoLocalInput_E8 (GaloisField 2 f) p hp hp2 hpK (Or.inl hp3))
    rw [hm] at h8
    exact absurd h8 (by decide)

end Tags

section TagsE7


theorem ggSixLSixSevenConjA3At_E7 : GGSixLSixSevenConjA3At .E7 := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ _ hA
  exfalso
  obtain ⟨hp3, hm⟩ := hctx.twoLocalRank_eq_four_of_a3 ggLNoncyclicInput_holds hA
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have := Fact.mk hp
  obtain ⟨-, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  set e := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f) with he
  set χ : adjointGroup .E7 (GaloisField 2 f) →* G := ψ.comp e.symm.toMonoidHom with hχ
  have hχinj : Function.Injective χ := hinj.comp e.symm.injective
  rcases three_dvd_two_pow_pred_or_succ f with h | h
  · have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK, hp3]; exact h
    have h7 := rank_le_twoLocalRank (τ := .E7) (by decide) hp hpK
      (TableBExc.isUnit_det_cartan_of_eq hp det_cartan_E7
        ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))) χ hχinj
    rw [hm] at h7
    exact absurd h7 (by decide)
  · have hpK : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK, hp3]; exact h
    have h7 := rank_pred_le_twoLocalRank_of_half (τ := .E7) hp χ hχinj
      (ggExcHalfTwoLocalInput_E7 (GaloisField 2 f) p hp hp2 hpK (Or.inl hp3))
    rw [hm] at h7
    exact absurd h7 (by decide)

end TagsE7

end CFSG.StandardType
