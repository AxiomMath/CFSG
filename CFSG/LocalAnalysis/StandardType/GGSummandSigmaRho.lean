module

public import CFSG.LocalAnalysis.StandardType.GGSummandNormality

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Config

variable {X : Type} [Group X] [Finite X] (V E K : Subgroup X)
  [hN : ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

theorem ggSum_sigma_surjective : Function.Surjective (ggSumSigma V E K) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
  refine ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  change (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))
      (Subgroup.inclusion (ggSumH_le V E K) ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩) = y.1
  rw [show Subgroup.inclusion (ggSumH_le V E K) ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩ = x
      from Subtype.ext rfl]
  exact hxy

theorem ggSum_rho_surjective : Function.Surjective (ggSumRho V E K) := by
  rw [ggSumRho]
  exact (QuotientGroup.mk'_surjective (N := CFSG.pCore 2 ↥(ggSumT V E K))).comp
    (ggSum_sigma_surjective V E K)

theorem ggSum_sigma_eq_one (h : ↥(E ⊔ (K ⊓ V))) :
    ggSumSigma V E K h = 1 ↔ (h : X) ∈ ggRCSU V E K := by
  constructor
  · intro h1
    have hval : (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))
        (Subgroup.inclusion (ggSumH_le V E K) h) = 1 := by
      have := congrArg (Subtype.val) h1
      exact this
    have hmem : Subgroup.inclusion (ggSumH_le V E K) h ∈
        (ggRCSU V E K).subgroupOf (E ⊔ K) := by
      rw [QuotientGroup.mk'_apply] at hval
      exact (QuotientGroup.eq_one_iff _).mp hval
    rwa [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hmem
  · intro hh
    apply Subtype.ext
    change (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))
        (Subgroup.inclusion (ggSumH_le V E K) h) = 1
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr
      (by rwa [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion])

theorem ggSum_exists_pow_mem_U (h : ↥(E ⊔ (K ⊓ V))) (hh : ggSumRho V E K h = 1) :
    ∃ k : ℕ, (h : X) ^ (2 ^ k) ∈ ggRCSU V E K := by
  have hmem : ggSumSigma V E K h ∈ CFSG.pCore 2 ↥(ggSumT V E K) := by
    have hval : (QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K)))
        (ggSumSigma V E K h) = 1 := by
      simpa [ggSumRho] using hh
    rw [QuotientGroup.mk'_apply] at hval
    exact (QuotientGroup.eq_one_iff _).mp hval
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥(ggSumT V E K)))
    ⟨ggSumSigma V E K h, hmem⟩
  refine ⟨k, ?_⟩
  have hk' : (ggSumSigma V E K h) ^ (2 ^ k) = 1 := by
    have := congrArg (Subtype.val) hk
    simpa [Subgroup.coe_pow] using this
  have hpow : ggSumSigma V E K (h ^ (2 ^ k)) = 1 := by
    rw [map_pow, hk']
  have := (ggSum_sigma_eq_one V E K (h ^ (2 ^ k))).mp hpow
  simpa [Subgroup.coe_pow] using this

theorem ggSum_rho_eq_one_of_mem_pCore (hEV : E ≤ V) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (h : ↥(E ⊔ (K ⊓ V))) (hh : (h : X) ∈ pCoreOf 2 (K ⊓ V)) : ggSumRho V E K h = 1 := by
  have hQ0norm : ((pCoreOf 2 (K ⊓ V)).subgroupOf (E ⊔ (K ⊓ V))).Normal :=
    normal_pCoreOf_subgroupOf_sup (E := E) (N := K ⊓ V)
      (le_normalizer_inf_of_le hEV hEK)
  have hσsurj : Function.Surjective (ggSumSigma V E K) := ggSum_sigma_surjective V E K
  have hmapnorm : (((pCoreOf 2 (K ⊓ V)).subgroupOf (E ⊔ (K ⊓ V))).map
      (ggSumSigma V E K)).Normal :=
    Subgroup.Normal.map hQ0norm (ggSumSigma V E K) hσsurj
  have hmap2 : IsPGroup 2 (((pCoreOf 2 (K ⊓ V)).subgroupOf (E ⊔ (K ⊓ V))).map
      (ggSumSigma V E K)) := by
    have hQ0p : IsPGroup 2 ((pCoreOf 2 (K ⊓ V)).subgroupOf (E ⊔ (K ⊓ V))) :=
      (isPGroup_pCoreOf' 2 (K ⊓ V)).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le' 2 (K ⊓ V)).trans le_sup_right)).symm
    exact hQ0p.map (ggSumSigma V E K)
  have hle_core : ((pCoreOf 2 (K ⊓ V)).subgroupOf (E ⊔ (K ⊓ V))).map
      (ggSumSigma V E K) ≤ CFSG.pCore 2 ↥(ggSumT V E K) := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le _ (le_iSup_of_le hmapnorm (le_iSup_of_le hmap2 le_rfl))
  have hmemQ : h ∈ (pCoreOf 2 (K ⊓ V)).subgroupOf (E ⊔ (K ⊓ V)) := by
    rw [Subgroup.mem_subgroupOf]
    exact hh
  have hsig : ggSumSigma V E K h ∈ ((pCoreOf 2 (K ⊓ V)).subgroupOf
      (E ⊔ (K ⊓ V))).map (ggSumSigma V E K) :=
    Subgroup.mem_map.mpr ⟨h, hmemQ, rfl⟩
  have hcore : ggSumSigma V E K h ∈ CFSG.pCore 2 ↥(ggSumT V E K) := hle_core hsig
  show (QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K))) (ggSumSigma V E K h) = 1
  rw [QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff _).mpr hcore

end Config

end CFSG.StandardType
