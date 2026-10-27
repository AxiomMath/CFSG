module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParO
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOPCensus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Spin
open scoped Pointwise

private theorem s16t3_flag_iff_mem_flag {m : ℕ} {K : Type} [Field K] {i : ℕ}
    {v : Fin m ⊕ Fin m → K} :
    v ∈ s16t3Flag (k := m) (R := Fin m) (K := K) i ↔
      v ∈ CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i := by
  rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_flag_iff_coord]
  constructor
  · intro hv
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · by_contra h
      obtain ⟨l, hl, -⟩ := hv (Sum.inr j) h
      exact absurd hl (by simp)
    · by_contra h
      obtain ⟨l, hl, hlt⟩ := hv (Sum.inl j) h
      simp only [Sum.inl.injEq] at hl
      omega
  · rintro ⟨h1, h2⟩ c hc
    rcases c with j | j
    · refine ⟨j, rfl, ?_⟩
      by_contra hlt
      exact hc (h2 j (not_lt.1 hlt))
    · exact absurd (h1 j) hc

theorem s16t3_omplus_std_of_census {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) (hC : S16t3PlusCensus K m) :
    ∃ P : Subgroup (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K),
      P ≤ StatedOmega (StatedQuadPlus m K) ∧
      (∀ y ∈ s16t3Borel (StatedQuadPlus m K) (m - 1), ∀ p ∈ P, y * p * y⁻¹ ∈ P) ∧
      (∀ y ∈ s16t3Borel (StatedQuadPlus m K) (m - 1),
        y ∈ StatedOmega (StatedQuadPlus m K) → y ∈ P) ∧
      Nat.card ↥P = 3 ^ ((m + 2) / 2) *
        2 ^ (Nat.card ↥(StatedOmega (StatedQuadPlus m K))).factorization 2 ∧
      ∀ p ∈ P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    letI := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    exact charP_of_card_eq_prime hK'
  classical
  set φ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K ≃*
      ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) K with hφ
  set P₀ : Subgroup ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) :=
    plusFlagStab K m (s16t3PlusCuts m) with hP₀
  have hOmega : StatedOmega (StatedQuadPlus m K) =
      (orthElementaryGroup (quadPlus m K)).map φ.symm.toMonoidHom := by
    rw [hφ]
    exact CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_map_elementaryGroup
      (CFSG.LieType.Universal.Spin.coe_quadPlus m K)
      (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.commutator_orthogonalGroup_quadPlus
        (K := K) hm)
  have hmemOmega : ∀ g : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K,
      g ∈ StatedOmega (StatedQuadPlus m K) ↔
        φ g ∈ orthElementaryGroup (quadPlus m K) := by
    intro g
    rw [hOmega]
    constructor
    · rintro ⟨e, he, heq⟩
      rw [← heq, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact he
    · intro hg
      exact ⟨φ g, hg, by simp⟩
  have hnormalizes : ∀ y ∈ s16t3Borel (StatedQuadPlus m K) (m - 1),
      ∀ e ∈ orthElementaryGroup (quadPlus m K),
        φ y * e * (φ y)⁻¹ ∈ orthElementaryGroup (quadPlus m K) := by
    intro y hy e he
    have hyO : φ y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [hφ, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
        CFSG.LieType.Universal.Spin.coe_quadPlus m K]
      exact hy.1 v
    exact conj_mem_orthElementaryGroup (K := K) hyO he
  have hstab_map : ∀ y ∈ s16t3Borel (StatedQuadPlus m K) (m - 1),
      ∀ i, 1 ≤ i → i ≤ m - 1 →
        (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i).map
          ((φ y : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K))) =
          CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i := by
    intro y hy i hi1 him
    apply Submodule.eq_of_le_of_finrank_le
    · rintro _ ⟨v, hv, rfl⟩
      show (φ y) v ∈ CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i
      rw [hφ, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
      exact (s16t3_flag_iff_mem_flag (K := K) (i := i)).mp
        (hy.2 i hi1 him v ((s16t3_flag_iff_mem_flag (K := K) (i := i)).mpr hv))
    · exact le_of_eq
        (LinearEquiv.finrank_map_eq (φ y)
          (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i)).symm
  have hstab : ∀ y ∈ s16t3Borel (StatedQuadPlus m K) (m - 1),
      ∀ i, 1 ≤ i → i ≤ m - 1 →
        (φ y) • CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i =
          CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i :=
    fun y hy i hi1 him => hstab_map y hy i hi1 him
  refine ⟨P₀.comap φ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    rw [Subgroup.mem_comap] at hg
    rw [hP₀, CFSG.AGLEmbedding.LeviBlock.mem_plusFlagStab] at hg
    simp only [MulEquiv.coe_toMonoidHom] at hg
    exact (hmemOmega g).mpr hg.1
  ·
    intro y hy p hp
    rw [Subgroup.mem_comap] at hp ⊢
    rw [hP₀, CFSG.AGLEmbedding.LeviBlock.mem_plusFlagStab] at hp ⊢
    simp only [MulEquiv.coe_toMonoidHom] at hp ⊢
    have hfixy : ∀ d ∈ s16t3PlusCuts m,
        (φ y) • CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K d =
          CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K d :=
      fun d hd => hstab y hy d (s16t3_mem_plusCuts.mp hd).1
        (by have := (s16t3_mem_plusCuts.mp hd).2.1; omega)
    have hconj : φ (y * p * y⁻¹) = φ y * φ p * (φ y)⁻¹ := by simp [map_mul]
    rw [hconj]
    refine ⟨hnormalizes y hy (φ p) hp.1, ?_⟩
    intro d hd
    have hyd := hfixy d hd
    have hpd := hp.2 d hd
    have hinv : (φ y)⁻¹ • CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K d =
        CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K d := by
      conv_lhs => rw [← hyd]
      rw [← mul_smul, inv_mul_cancel, one_smul]
    rw [mul_smul, mul_smul, hinv, hpd, hyd]
  ·
    intro y hy hyOmega
    rw [Subgroup.mem_comap]
    rw [hP₀, CFSG.AGLEmbedding.LeviBlock.mem_plusFlagStab]
    simp only [MulEquiv.coe_toMonoidHom]
    exact ⟨(hmemOmega y).mp hyOmega, fun d hd => hstab y hy d
      (s16t3_mem_plusCuts.mp hd).1
      (by have := (s16t3_mem_plusCuts.mp hd).2.1; omega)⟩
  ·
    have hcardP : Nat.card ↥(P₀.comap φ.toMonoidHom) = Nat.card ↥P₀ := by
      rw [Subgroup.comap_equiv_eq_map_symm' φ P₀]
      exact Nat.card_congr (φ.symm.subgroupMap P₀).toEquiv.symm
    have hcardOmega : Nat.card ↥(StatedOmega (StatedQuadPlus m K)) =
        Nat.card ↥(orthElementaryGroup (quadPlus m K)) := by
      rw [hOmega]
      exact Nat.card_congr
        (φ.symm.subgroupMap (orthElementaryGroup (quadPlus m K))).toEquiv.symm
    rw [hcardP, hcardOmega]
    exact hC.1
  ·
    intro p hp k hk
    have hpΦ : φ p ∈ P₀ := by
      rw [Subgroup.mem_comap] at hp
      exact hp
    have hpow : (φ p) ^ 3 ^ k = 1 := by
      rw [← map_pow, hk, map_one]
    have h3 : (φ p) ^ 3 = 1 := hC.2 (φ p) (by rwa [hP₀] at hpΦ) k hpow
    exact φ.injective (by rw [map_pow, h3, map_one])

theorem s16t3_omplus_std {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) :
    ∃ P : Subgroup (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K),
      P ≤ StatedOmega (StatedQuadPlus m K) ∧
      (∀ y ∈ s16t3Borel (StatedQuadPlus m K) (m - 1), ∀ p ∈ P, y * p * y⁻¹ ∈ P) ∧
      (∀ y ∈ s16t3Borel (StatedQuadPlus m K) (m - 1),
        y ∈ StatedOmega (StatedQuadPlus m K) → y ∈ P) ∧
      Nat.card ↥P = 3 ^ ((m + 2) / 2) *
        2 ^ (Nat.card ↥(StatedOmega (StatedQuadPlus m K))).factorization 2 ∧
      ∀ p ∈ P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 := by
  exact s16t3_omplus_std_of_census hK hm (s16t3_plus_census hK hm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
