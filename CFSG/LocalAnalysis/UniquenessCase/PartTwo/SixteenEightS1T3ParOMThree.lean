module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOMDef
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped Pointwise

private theorem s16t3_gl_two_card {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) = 6 := by
  rw [Matrix.card_GL_field, Fin.prod_univ_two, hK]
  norm_num

private theorem s16t3_resLevi_two_card {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) :
    Nat.card (((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K))) = 6 := by
  rw [show Nat.card (((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K))) =
      Nat.card ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) from
    Nat.card_congr (LinearEquiv.autCongr (LinearEquiv.uniqueProd (R := K)
      (M := Fin 2 → K) (M₂ := Fin 0 ⊕ Fin 0 → K))).toEquiv,
    show Nat.card ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) =
      Nat.card (LinearMap.GeneralLinearGroup K (Fin 2 → K)) from
    Nat.card_congr
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 → K)).symm.toEquiv,
    show Nat.card (LinearMap.GeneralLinearGroup K (Fin 2 → K)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) from
    Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := K)).toEquiv.symm,
    s16t3_gl_two_card hK]

private theorem s16t3_pow_six_of_card_dvd_six {G : Type*} [Group G] (hG : Nat.card G ∣ 6)
    (g : G) : g ^ 6 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  exact (orderOf_dvd_natCard g).trans hG

private theorem s16t3_pow_three_of_pow_six {G : Type*} [Group G] (h6 : ∀ g : G, g ^ 6 = 1) :
    ∀ g : G, ∀ k : ℕ, g ^ 3 ^ k = 1 → g ^ 3 = 1 := by
  intro g k hk
  have hdk : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hd6 : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one (h6 g)
  have hcop : Nat.Coprime (orderOf g) 2 := by
    have h32 : Nat.Coprime (3 : ℕ) 2 := by decide
    exact (h32.pow_left k).coprime_dvd_left hdk
  have hd3 : orderOf g ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using hd6)
  rwa [← orderOf_dvd_iff_pow_eq_one]

private theorem s16t3_orthLeviGroup_two_card_dvd_six {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) (d : Fin 2 → ℕ) (hd0 : d 0 = 0) (hd1 : d 1 = 2)
    (j : Fin 1 ⊕ Unit) : Nat.card (orthLeviGroup K 2 d j) ∣ 6 := by
  rcases j with l | u
  · obtain rfl : l = 0 := Subsingleton.elim l 0
    change Nat.card (Matrix.GeneralLinearGroup
      (Fin (d ((0 : Fin 1).succ) - d ((0 : Fin 1).castSucc))) K) ∣ 6
    rw [show d ((0 : Fin 1).succ) - d ((0 : Fin 1).castSucc) = 2 by
      rw [show ((0 : Fin 1).succ) = (1 : Fin 2) from rfl,
        show ((0 : Fin 1).castSucc) = (0 : Fin 2) from rfl, hd1, hd0]]
    rw [s16t3_gl_two_card hK]
  · obtain rfl : u = () := Subsingleton.elim u ()
    change Nat.card (((Fin (2 - d (Fin.last 1)) ⊕ Fin (2 - d (Fin.last 1)) → K) ×
      (Fin 2 → K)) ≃ₗ[K] ((Fin (2 - d (Fin.last 1)) ⊕ Fin (2 - d (Fin.last 1)) → K) ×
        (Fin 2 → K))) ∣ 6
    rw [show 2 - d (Fin.last 1) = 0 by
      rw [show Fin.last 1 = (1 : Fin 2) from rfl, hd1]]
    rw [s16t3_resLevi_two_card hK]

theorem s16t3_minus_census_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    S16t3MinusCensus K 2 := by
  haveI : IsF2 K := IsF2.of_natCard_eq_two hK
  letI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) hK'
  have hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := irreducible_one_one
  have ha₀ : (Pi.single 0 1 : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  have hEcard : Nat.card ↥(orthElementaryGroup (quadTail 2 (minusTailForm K 1 1))) = 25920 := by
    have hφ : ∀ v : (Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K),
        quadMinus 3 K 1 1 ((minusTailIsometry 3 K 1 1).toLinearEquiv v) =
          quadTail 2 (minusTailForm K 1 1) v :=
      fun v => (minusTailIsometry 3 K 1 1).map_app' v
    have hcomm := commutator_orthogonalGroup_eq_of_isometry_minus
      (Q := quadTail 2 (minusTailForm K 1 1)) (m := 3) (by norm_num)
      (minusTailIsometry 3 K 1 1).toLinearEquiv hφ
    have hEeq : orthElementaryGroup (quadTail 2 (minusTailForm K 1 1)) = orthResDer K 1 1 2 := by
      rw [show orthResDer K 1 1 2 = ⁅TauCeti.QuadraticMap.orthogonalGroup
          (quadTail 2 (minusTailForm K 1 1)),
          TauCeti.QuadraticMap.orthogonalGroup (quadTail 2 (minusTailForm K 1 1))⁆ from rfl,
        hcomm]
      rfl
    rw [hEeq, (orthResDer_two_facts (K := K) (b := 1) (c := 1) hirr).2.2, hK]
    norm_num
  have hprod : (∏ j ∈ Finset.range 2, ((((2 : ℕ) : ℚ) ^ (2 - j) - 1) *
      (((2 : ℕ) : ℚ) ^ (2 + 2 - j - 1) + 1))) /
      (∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℚ) ^ i - 1)) = 45 := by
    rw [Finset.prod_range_succ, Finset.prod_range_one,
      Finset.prod_Icc_succ_top (by norm_num : (1 : ℕ) ≤ 1 + 1), Finset.Icc_self,
      Finset.prod_singleton]
    norm_num
  have hsubCard : Nat.card (singularSubspaces (quadTail 2 (minusTailForm K 1 1)) 2) = 45 := by
    have h := card_singularSubspaces_tail (K := K) (A := Fin 2 → K) (r := 2)
      (qA := minusTailForm K 1 1) (anisotropic_minusTailForm hirr)
      (nondegenerate_minusTailForm hirr) (k := 2) (le_refl 2)
    rw [finrank_fin_two_fun, hK, hprod] at h
    exact_mod_cast h
  have hmem : tailFlag K (Fin 2 → K) 2 2 ∈
      singularSubspaces (quadTail 2 (minusTailForm K 1 1)) 2 :=
    ⟨finrank_tailFlag (le_refl 2), fun _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩
  have hP₀eq : orthParab 2 (minusTailForm K 1 1) (s16t3MinusCuts 2) =
      MulAction.stabilizer (orthElementaryGroup (quadTail 2 (minusTailForm K 1 1)))
        (tailFlag K (Fin 2 → K) 2 2) := by
    ext x
    rw [mem_orthParab]
    constructor
    · intro h
      change (tailFlag K (Fin 2 → K) 2 2).map
        (x : (Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K) →ₗ[K]
          (Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) = tailFlag K (Fin 2 → K) 2 2
      simpa [s16t3MinusCuts] using h 1
    · intro h i
      have h' : (tailFlag K (Fin 2 → K) 2 2).map
          (x : (Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K) →ₗ[K]
            (Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) = tailFlag K (Fin 2 → K) 2 2 := h
      fin_cases i
      · simp [s16t3MinusCuts, tailFlag_zero]
      · simpa [s16t3MinusCuts] using h'
  have hP₀index : (orthParab 2 (minusTailForm K 1 1) (s16t3MinusCuts 2)).index = 45 := by
    rw [hP₀eq, index_stabilizer_eq_card (qA := minusTailForm K 1 1) (r := 2)
      (anisotropic_minusTailForm hirr) ⟨Pi.single 0 1, ha₀⟩ (k := 2) (le_refl 2) hmem]
    exact hsubCard
  have hP₀card : Nat.card ↥(orthParab 2 (minusTailForm K 1 1) (s16t3MinusCuts 2)) = 576 := by
    have h := Subgroup.card_mul_index (orthParab 2 (minusTailForm K 1 1) (s16t3MinusCuts 2))
    rw [hEcard, hP₀index] at h
    omega
  have hfac : (25920 : ℕ).factorization 2 = 6 := by
    rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 405), add_zero]
  refine ⟨?_, ?_⟩
  · have hmapped : Nat.card ↥(s16t3MinusParab K 2) =
        Nat.card ↥(orthParab 2 (minusTailForm K 1 1) (s16t3MinusCuts 2)) :=
      Subgroup.card_map_of_injective
        (K := orthParab 2 (minusTailForm K 1 1) (s16t3MinusCuts 2))
        (f := (orthElementaryGroup (quadTail 2 (minusTailForm K 1 1))).subtype)
        (orthElementaryGroup (quadTail 2 (minusTailForm K 1 1))).subtype_injective
    rw [hmapped, hP₀card, hEcard, hfac]
    norm_num
  · intro p hp k hpk
    have hp' : p ∈ (orthParab 2 (minusTailForm K 1 1) (s16t3MinusCuts 2)).map
        (orthElementaryGroup (quadTail 2 (minusTailForm K 1 1))).subtype := hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp'
    have hd0 : s16t3MinusCuts 2 0 = 0 := by decide
    have hd1 : s16t3MinusCuts 2 1 = 2 := by decide
    have hd : OrthCuts 2 (s16t3MinusCuts 2) := ⟨by decide, by decide, by decide⟩
    have h6coord : ∀ j : Fin 1 ⊕ Unit,
        ∀ g : orthLeviGroup K 2 (s16t3MinusCuts 2) j, g ^ 6 = 1 :=
      fun j => s16t3_pow_six_of_card_dvd_six
        (s16t3_orthLeviGroup_two_card_dvd_six hK' (s16t3MinusCuts 2) hd0 hd1 j)
    have hH : ∀ h : (∀ j : Fin 1 ⊕ Unit, orthLeviGroup K 2 (s16t3MinusCuts 2) j),
        ∀ k : ℕ, h ^ 3 ^ k = 1 → h ^ 3 = 1 := by
      apply s16t3_pow_three_of_pow_six
      intro h
      funext j
      exact h6coord j (h j)
    have hker : IsPGroup 2 (orthLeviHom (1 : K) (1 : K) hd).ker :=
      isPGroup_ker_orthLeviHom (b := 1) (c := 1) hd
    have hexp := s16t3_pow_three_of_isPGroup_ker (orthLeviHom (1 : K) (1 : K) hd) hker hH
    have hq3 : q ^ 3 = 1 := by
      have h3 := hexp ⟨q, hq⟩ k (Subtype.ext
        ((orthElementaryGroup (quadTail 2 (minusTailForm K 1 1))).subtype_injective (by
          simpa using hpk)))
      simpa using congrArg Subtype.val h3
    simpa using congrArg
      (orthElementaryGroup (quadTail 2 (minusTailForm K 1 1))).subtype hq3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
