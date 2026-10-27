module

public import CFSG.LocalAnalysis.StandardType.GGGroupPerfectLift
public import CFSG.LocalAnalysis.StandardType.GGComponentOfSSup
public import CFSG.LocalAnalysis.StandardType.GGSubgroupOfSSup
public import CFSG.LocalAnalysis.StandardType.GGCommutatorSupElemAbelian
public import CFSG.LocalAnalysis.StandardType.GGSummandImgSubnormal
public import CFSG.LocalAnalysis.StandardType.GGSummandImgQuasisimple
public import CFSG.LocalAnalysis.StandardType.GGSummandMarking

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

theorem exists_derivedSeries_succ_eq' (G : Type*) [Group G] [Finite G] :
    ∃ n, derivedSeries G (n + 1) = derivedSeries G n := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G))
      (SetLike.coe_injective : Function.Injective (fun H : Subgroup G => (H : Set G)))
  obtain ⟨k, hk⟩ := WellFoundedLT.antitone_chain_condition (derivedSeries_antitone (G := G))
  exact ⟨k, (hk (k + 1) (Nat.le_succ k)).symm⟩

section Config

variable {X : Type} [Group X] [Finite X] (V E K : Subgroup X)
  [hN : ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]
  {p : ℕ} {Q : Subgroup X} {𝒞 : Set (Subgroup X)}

theorem ggSum_perfect_le_img (hE : IsElemAbelian p E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hS : GGSummandStruct E K V Q 𝒞)
    {Y : Subgroup (GGHypQuot (ggSumT V E K))} (hY : ⁅Y, Y⁆ = Y) :
    Y ≤ sSup ((fun S => ggSumImg V E K S) '' 𝒞) := by
  have hENV : E ≤ Subgroup.normalizer ((K ⊓ V : Subgroup X) : Set X) :=
    le_normalizer_inf_of_le hEV hEK
  have hcomm := commutator_sup_le_of_isElemAbelian hE hENV
  obtain ⟨P, hPN, hPperf, hPY⟩ :=
    exists_perfect_lift (ggSumRho V E K) (ggSum_rho_surjective V E K) hcomm hY
  have hP'N : P.map (E ⊔ (K ⊓ V)).subtype ≤ K ⊓ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hPN hx)
  have hP'perf : ⁅P.map (E ⊔ (K ⊓ V)).subtype, P.map (E ⊔ (K ⊓ V)).subtype⁆ =
      P.map (E ⊔ (K ⊓ V)).subtype := by
    rw [← Subgroup.map_commutator, hPperf]
  have hP'S := hS.2.1 _ hP'N hP'perf
  have hPS : P ≤ (sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V)) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hP'S ⟨x, hx, rfl⟩)
  have h𝒞H : ∀ S ∈ 𝒞, S ≤ E ⊔ (K ⊓ V) := fun S hS𝒞 =>
    ((hS.2.2 S hS𝒞).1).trans le_sup_right
  rw [← hPY]
  calc P.map (ggSumRho V E K) ≤ ((sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))).map (ggSumRho V E K) :=
        Subgroup.map_mono hPS
    _ = sSup ((fun S => (S.subgroupOf (E ⊔ (K ⊓ V))).map (ggSumRho V E K)) '' 𝒞) :=
        map_subgroupOf_sSup (ggSumRho V E K) h𝒞H

theorem ggSum_isComponentOf_img (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E)
    (hEV : E ≤ V) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hS : GGSummandStruct E K V Q 𝒞) {S : Subgroup X} (hS𝒞 : S ∈ 𝒞) :
    IsComponentOf (ggSumImg V E K S) ⊤ :=
  ⟨le_top, ggSum_img_isSubnormal V E K hEV hEK hS hS𝒞,
    ggSum_img_isQuasisimple V E K hp hp2 hE hEV hEK hS hS𝒞⟩

theorem ggSum_component_eq' (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E)
    (hEV : E ≤ V) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hS : GGSummandStruct E K V Q 𝒞) (C : Subgroup (GGHypQuot (ggSumT V E K)))
    (hC : IsComponentOf C ⊤) : ∃ S ∈ 𝒞, C = ggSumImg V E K S := by
  have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp ⟨hC.2.2.1⟩
  have hle := ggSum_perfect_le_img V E K hE hEV hEK hS hCperf
  have hmem := isComponentOf_mem_of_le_sSup hC (by
    rintro D ⟨S, hS𝒞, rfl⟩
    exact ggSum_isComponentOf_img V E K hp hp2 hE hEV hEK hS hS𝒞) hle
  obtain ⟨S, hS𝒞, hSC⟩ := hmem
  exact ⟨S, hS𝒞, hSC.symm⟩

theorem ggSum_layer_eq (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E)
    (hEV : E ≤ V) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hS : GGSummandStruct E K V Q 𝒞) :
    LargeEvenLayer (⊤ : Subgroup (GGHypQuot (ggSumT V E K))) =
      sSup ((fun S => ggSumImg V E K S) '' 𝒞) := by
  apply le_antisymm
  · refine sSup_le fun C hC => ?_
    obtain ⟨S, hS𝒞, rfl⟩ := ggSum_component_eq' V E K hp hp2 hE hEV hEK hS C hC
    exact le_sSup ⟨S, hS𝒞, rfl⟩
  · refine sSup_le ?_
    rintro _ ⟨S, hS𝒞, rfl⟩
    exact le_sSup (ggSum_isComponentOf_img V E K hp hp2 hE hEV hEK hS hS𝒞)

theorem ggSum_layer' (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E)
    (hEV : E ≤ V) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hS : GGSummandStruct E K V Q 𝒞) :
    commutator ↥(ggHypLayer (ggSumT V E K)) = ⊤ ∨
      LargeEvenLayer (⊤ : Subgroup (GGHypQuot (ggSumT V E K))) = ⊥ := by
  have hΛ := ggSum_layer_eq V E K hp hp2 hE hEV hEK hS
  by_cases h𝒞 : 𝒞.Nonempty
  swap
  · right
    rw [hΛ, Set.not_nonempty_iff_eq_empty.mp h𝒞, Set.image_empty, sSup_empty]
  left
  obtain ⟨S₁, hS₁⟩ := h𝒞
  have hQS₀ : Q ≤ sSup 𝒞 := ((hS.2.2 S₁ hS₁).2.1).trans (le_sSup hS₁)
  have hS₀N : sSup 𝒞 ≤ K ⊓ V := sSup_le fun S hS𝒞 => (hS.2.2 S hS𝒞).1
  have hS₀H : sSup 𝒞 ≤ E ⊔ (K ⊓ V) := hS₀N.trans le_sup_right
  have hQH : Q ≤ E ⊔ (K ⊓ V) := hQS₀.trans hS₀H
  have hUH : ggRCSU V E K ≤ E ⊔ (K ⊓ V) := inf_le_left
  have h𝒞H : ∀ S ∈ 𝒞, S ≤ E ⊔ (K ⊓ V) := fun S hS𝒞 =>
    ((hS.2.2 S hS𝒞).1).trans le_sup_right
  have hΛ' : LargeEvenLayer (⊤ : Subgroup (GGHypQuot (ggSumT V E K))) =
      ((sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))).map (ggSumRho V E K) := by
    rw [hΛ]
    exact (map_subgroupOf_sSup (ggSumRho V E K) h𝒞H).symm
  have hlayer : ggHypLayer (ggSumT V E K) =
      (((sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))).map (ggSumSigma V E K)).map
        (ggSumT V E K).subtype := by
    ext w
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨h, rfl⟩ := ggSum_sigma_surjective V E K t
      have hρ : ggSumRho V E K h ∈
          ((sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))).map (ggSumRho V E K) := by
        rw [← hΛ']
        exact ht
      obtain ⟨s, hs, hsρ⟩ := hρ
      have hk : ggSumRho V E K (s⁻¹ * h) = 1 := by
        rw [map_mul, map_inv, hsρ, inv_mul_cancel]
      have hkQU := (ggSum_ker_rho V E K hp hp2 hE hEV hEK hS (s⁻¹ * h)).mp hk
      have hkQU' : s⁻¹ * h ∈ Q.subgroupOf (E ⊔ (K ⊓ V)) ⊔
          (ggRCSU V E K).subgroupOf (E ⊔ (K ⊓ V)) := by
        rw [← Subgroup.subgroupOf_sup hQH hUH]
        exact hkQU
      have hσk : ggSumSigma V E K (s⁻¹ * h) ∈ (Q.subgroupOf (E ⊔ (K ⊓ V))).map
          (ggSumSigma V E K) := by
        have hmem := Subgroup.mem_map_of_mem (ggSumSigma V E K) hkQU'
        rw [Subgroup.map_sup] at hmem
        have hbot : ((ggRCSU V E K).subgroupOf (E ⊔ (K ⊓ V))).map (ggSumSigma V E K) = ⊥ := by
          rw [eq_bot_iff]
          rintro _ ⟨u, hu, rfl⟩
          rw [Subgroup.mem_bot]
          exact (ggSum_sigma_eq_one V E K u).mpr (Subgroup.mem_subgroupOf.mp hu)
        rwa [hbot, sup_bot_eq] at hmem
      obtain ⟨q, hq, hqσ⟩ := hσk
      refine ⟨ggSumSigma V E K (s * q), ⟨s * q, ?_, rfl⟩, ?_⟩
      · exact (((sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))).mul_mem hs
          (Subgroup.mem_subgroupOf.mpr (hQS₀ (Subgroup.mem_subgroupOf.mp hq))))
      · have : ggSumSigma V E K (s * q) = ggSumSigma V E K h := by
          rw [map_mul, hqσ, map_mul, map_inv, mul_inv_cancel_left]
        rw [this]
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨ggSumSigma V E K s, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, hΛ']
      exact ⟨s, hs, rfl⟩
  have hS₀perf : ⁅(sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V)), (sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))⁆ =
      (sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V)) := by
    apply Subgroup.map_injective (E ⊔ (K ⊓ V)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hS₀H]
    exact commutator_sSup_eq_self (fun S hS𝒞 => (hS.2.2 S hS𝒞).2.2.2.1)
  rw [hlayer]
  have hB : ⁅(((sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))).map (ggSumSigma V E K)).map
        (ggSumT V E K).subtype, (((sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))).map
        (ggSumSigma V E K)).map (ggSumT V E K).subtype⁆ =
      (((sSup 𝒞).subgroupOf (E ⊔ (K ⊓ V))).map (ggSumSigma V E K)).map
        (ggSumT V E K).subtype := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hS₀perf]
  exact (Subgroup.isPerfect_iff.mpr hB).commutator_eq_top

theorem ggSum_derived' (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E)
    (hEV : E ≤ V) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hS : GGSummandStruct E K V Q 𝒞) :
    ∃ k : ℕ, derivedSeries ↥(ggSumT V E K) k ≤
      (ggHypLayer (ggSumT V E K)).subgroupOf (ggSumT V E K) := by
  obtain ⟨k, hk⟩ := exists_derivedSeries_succ_eq' ↥(ggSumT V E K)
  refine ⟨k, fun t ht => ?_⟩
  have hperf : ⁅derivedSeries ↥(ggSumT V E K) k, derivedSeries ↥(ggSumT V E K) k⁆ =
      derivedSeries ↥(ggSumT V E K) k := by
    rw [← derivedSeries_succ, hk]
  have hY : ⁅(derivedSeries ↥(ggSumT V E K) k).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K))),
      (derivedSeries ↥(ggSumT V E K) k).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K)))⁆ =
      (derivedSeries ↥(ggSumT V E K) k).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K))) := by
    rw [← Subgroup.map_commutator, hperf]
  have hle := ggSum_perfect_le_img V E K hE hEV hEK hS hY
  rw [← ggSum_layer_eq V E K hp hp2 hE hEV hEK hS] at hle
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K)) t ∈
      LargeEvenLayer (⊤ : Subgroup (GGHypQuot (ggSumT V E K))) := hle ⟨t, ht, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr ⟨t, hmem, rfl⟩

end Config

theorem ggRCSAutKIIIFlat_of_summandStruct {X : Type} [Group X] [Finite X] {p : ℕ}
    {E K V Q : Subgroup X} {𝒞 : Set (Subgroup X)} (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsElemAbelian p E) (hEV : E ≤ V) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hS : GGSummandStruct E K V Q 𝒞) : GGRCSAutKIIIFlat V E K := by
  intro hN
  refine ⟨fun C hC => ?_, ggSum_layer' V E K hp hp2 hE hEV hEK hS,
    ggSum_derived' V E K hp hp2 hE hEV hEK hS⟩
  obtain ⟨S, hS𝒞, rfl⟩ := ggSum_component_eq' V E K hp hp2 hE hEV hEK hS C hC
  exact ggSum_marking V E K hp hp2 hE hEV hEK hS hS𝒞

end CFSG.StandardType
