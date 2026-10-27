module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOMTailA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration QuadraticMap Module
open scoped commutatorElement

theorem s16t3_minus_census_of_three_le {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {r : ℕ} (hr : 3 ≤ r) : S16t3MinusCensus K r := by
  haveI : IsF2 K := IsF2.of_natCard_eq_two hK
  letI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) hK'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := irreducible_one_one
  let qA : QuadraticForm K (Fin 2 → K) := minusTailForm K 1 1
  let d : Fin ((r + 1) / 2 + 1) → ℕ := s16t3MinusCuts r
  let E : Subgroup (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := orthElementaryGroup (quadTail r qA)
  let P₀ : Subgroup ↥E := orthParab r qA d
  let Y : Subgroup (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := tailUnipotent r qA
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have hd : OrthCuts r d := s16t3_minus_cuts_orthCuts (by omega)
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA)⁆ = E :=
    commutator_orthogonalGroup_quadTail_minus (b := 1) (c := 1) hr hirr
  have hani : qA.Anisotropic := anisotropic_minusTailForm hirr
  have hreg : (polarBilin qA).Nondegenerate := nondegenerate_minusTailForm hirr
  have hm : finrank K (Fin 2 → K) = 1 ∨ finrank K (Fin 2 → K) = 2 :=
    Or.inr finrank_fin_two_fun
  have hYsyl : CFSG.ABGLocalTools.IsSylowOf 2 Y E := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨tailUnipotent_le, ?_, ?_⟩
    · exact (isPGroup_tailUnipotent (qA := qA) (p := 2) hani).of_equiv
        (Subgroup.subgroupOfEquivOfLe tailUnipotent_le)
    · exact not_dvd_index_tailUnipotent (p := 2) hr hani hreg hm
  have hYsub : CFSG.ABGLocalTools.IsSylowOf 2 (Y.subgroupOf E) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff E]
    have h1 : ((Y.subgroupOf E).map E.subtype) = Y := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr tailUnipotent_le]
    have h2 : ((⊤ : Subgroup ↥E).map E.subtype) = E := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1, h2]
    exact hYsyl
  have hYPsub : Y.subgroupOf E ≤ P₀ := by
    intro y hy
    rw [mem_orthParab]
    intro i
    have hy' : (y : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) ∈ Y := Subgroup.mem_subgroupOf.1 hy
    have hb : (y : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) ∈ tailBorel r qA :=
      tailUnipotent_le_tailBorel hani hy'
    have hb' := (mem_tailBorel.1 hb).2
    by_cases h0 : d i = 0
    · rw [h0, tailFlag_zero]
      simp
    · refine hb' (d i) (by omega) ?_
      change s16t3MinusCuts r i ≤ r
      exact min_le_right _ _
  let β : ↥P₀ →* ∀ j : Fin ((r + 1) / 2) ⊕ Unit, orthLeviGroup K r d j :=
    orthLeviHom (b := 1) (c := 1) hd
  let H : Subgroup (∀ j : Fin ((r + 1) / 2) ⊕ Unit, orthLeviGroup K r d j) := β.range
  have hker : IsPGroup 2 β.ker := isPGroup_ker_orthLeviHom (b := 1) (c := 1) hd
  have hker' : IsPGroup 2 β.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hle_pi : Subgroup.pi Set.univ (orthLeviBlock K r d 1 1) ≤ H :=
    pi_orthLeviBlock_le_range hd hr hE
  have hdvd_upper : Nat.card ↥H ∣ 6 ^ (r / 2 + 1) := by
    have hle : H ≤ (⊤ : Subgroup (∀ j : Fin ((r + 1) / 2) ⊕ Unit, orthLeviGroup K r d j)) :=
      le_top
    have h := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_top, s16t3_orthLeviGroup_prod hK' (by omega)] at h
  have hdvd_lower : 6 ^ (r / 2) * 3 ∣ Nat.card ↥H := by
    have h := Subgroup.card_dvd_of_le hle_pi
    rwa [s16t3_orthLeviBlock_prod hK' (by omega)] at h
  have hlo : 2 ^ (r / 2) * 3 ^ (r / 2 + 1) ∣ Nat.card ↥H := by
    have h := hdvd_lower
    rwa [show 6 ^ (r / 2) * 3 = 2 ^ (r / 2) * 3 ^ (r / 2 + 1) by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_pow]; ring] at h
  have hhi : Nat.card ↥H ∣ 2 ^ (r / 2 + 1) * 3 ^ (r / 2 + 1) := by
    have h := hdvd_upper
    rwa [show 6 ^ (r / 2 + 1) = 2 ^ (r / 2 + 1) * 3 ^ (r / 2 + 1) by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_pow]] at h
  obtain ⟨x, hx⟩ := s16t3_card_eq_two_pow_mul_three_pow hlo hhi
  have hcardP₀ : Nat.card ↥P₀ = 3 ^ ((r + 2) / 2) * 2 ^ (Nat.card ↥E).factorization 2 := by
    have hcard := s16t3_card_of_surjective_isPGroup_ker (G := (⊤ : Subgroup ↥E)) (P := P₀)
      (Y := Y.subgroupOf E) (x := x) (a := (r + 2) / 2) le_top hYsub hYPsub
      β.rangeRestrict β.rangeRestrict_surjective hker' (by
        rw [hx, show (r + 2) / 2 = r / 2 + 1 by omega])
    rwa [Subgroup.card_top] at hcard
  have h6 : ∀ j : Fin ((r + 1) / 2) ⊕ Unit, ∀ g : orthLeviGroup K r d j, g ^ 6 = 1 := by
    intro j g
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_natCard g).trans (s16t3_orthLeviGroup_card_dvd_six hK' (by omega) j)
  have hexpH : ∀ h : ↥H, ∀ k : ℕ, h ^ 3 ^ k = 1 → h ^ 3 = 1 := by
    refine s16t3_pow_three_of_pow_six ?_
    intro h
    apply Subtype.ext
    funext j
    simpa using h6 j ((h : ∀ j : Fin ((r + 1) / 2) ⊕ Unit, orthLeviGroup K r d j) j)
  have hexpP₀ : ∀ p : ↥P₀, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 :=
    s16t3_pow_three_of_isPGroup_ker β.rangeRestrict hker' hexpH
  refine ⟨?_, ?_⟩
  · rw [show s16t3MinusParab K r = P₀.map E.subtype from rfl,
      Subgroup.card_map_of_injective (K := P₀) (f := E.subtype) E.subtype_injective]
    exact hcardP₀
  · intro p hp k hpk
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hp
    have hq3 : q ^ 3 = 1 := by
      have hqk : (⟨q, hq⟩ : ↥P₀) ^ 3 ^ k = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using hpk
      exact congrArg Subtype.val (hexpP₀ ⟨q, hq⟩ k hqk)
    rw [← map_pow, hq3, map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
