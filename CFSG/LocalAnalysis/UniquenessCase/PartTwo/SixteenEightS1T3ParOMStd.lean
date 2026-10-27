module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParO
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOMTail
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOMThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.AGLEmbedding.LeviBlock
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped Matrix Pointwise

private theorem s16t3_symm_mem_tailFlag_iff {K : Type} [Field K] {r : ℕ}
    (v : Fin r ⊕ Fin r ⊕ Fin 2 → K) (i : ℕ) :
    (tailModelEquiv r K (Fin 2)).symm v ∈ tailFlag K (Fin 2 → K) r i ↔
      v ∈ s16t3Flag (k := r) (R := Fin r ⊕ Fin 2) (K := K) i := by
  rw [mem_tailFlag_iff, CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_flag]
  have c1 : ∀ j : Fin r,
      ((tailModelEquiv r K (Fin 2)).symm v).1 (Sum.inr j) = v (Sum.inr (Sum.inl j)) :=
    fun _ => rfl
  have c2 : ∀ j : Fin r,
      ((tailModelEquiv r K (Fin 2)).symm v).1 (Sum.inl j) = v (Sum.inl j) :=
    fun _ => rfl
  have c3 : ∀ j : Fin 2,
      ((tailModelEquiv r K (Fin 2)).symm v).2 j = v (Sum.inr (Sum.inr j)) :=
    fun _ => rfl
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ c hc
    rcases c with j | j
    · by_cases hj : (j : ℕ) < i
      · exact ⟨j, rfl, hj⟩
      · exact absurd (by rw [← c2 j]; exact h2 j (not_lt.1 hj)) hc
    · rcases j with j | j
      · exact absurd (by rw [← c1 j]; exact h1 j) hc
      · have h3j : ((tailModelEquiv r K (Fin 2)).symm v).2 j = 0 := by
          simpa using congrFun h3 j
        exact absurd (by rw [← c3 j]; exact h3j) hc
  · intro hv
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j
      by_contra h
      obtain ⟨l, hl, -⟩ := hv (Sum.inr (Sum.inl j)) h
      exact absurd hl (by simp)
    · intro j hj
      by_contra h
      obtain ⟨l, hl, hlt⟩ := hv (Sum.inl j) h
      simp only [Sum.inl.injEq] at hl
      omega
    · funext j
      show ((tailModelEquiv r K (Fin 2)).symm v).2 j = 0
      by_contra hj
      have hvj : v (Sum.inr (Sum.inr j)) ≠ 0 := fun h0 => hj (by rw [c3 j, h0])
      obtain ⟨l, hl, -⟩ := hv (Sum.inr (Sum.inr j)) hvj
      exact absurd hl (by simp)

private theorem s16t3_map_mem_tailFlag_iff {K : Type} [Field K] {r : ℕ}
    (w : (Fin r ⊕ Fin r → K) × (Fin 2 → K)) (i : ℕ) :
    tailModelEquiv r K (Fin 2) w ∈ s16t3Flag (k := r) (R := Fin r ⊕ Fin 2) (K := K) i ↔
      w ∈ tailFlag K (Fin 2 → K) r i := by
  have h := s16t3_symm_mem_tailFlag_iff (K := K) (r := r) (tailModelEquiv r K (Fin 2) w) i
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem s16t3_omminus_std_of_census {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hC : S16t3MinusCensus K (m - 1)) :
    ∃ P : Subgroup (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K),
      P ≤ StatedOmega (StatedQuadMinus m K b c) ∧
      (∀ y ∈ s16t3Borel (StatedQuadMinus m K b c) (m - 1), ∀ p ∈ P, y * p * y⁻¹ ∈ P) ∧
      (∀ y ∈ s16t3Borel (StatedQuadMinus m K b c) (m - 1),
        y ∈ StatedOmega (StatedQuadMinus m K b c) → y ∈ P) ∧
      Nat.card ↥P = 3 ^ ((m + 1) / 2) *
        2 ^ (Nat.card ↥(StatedOmega (StatedQuadMinus m K b c))).factorization 2 ∧
      ∀ p ∈ P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 := by
  haveI : IsF2 K := IsF2.of_natCard_eq_two hK
  have hc : c = 1 := by
    apply IsF2.eq_one_of_ne_zero
    intro hc0
    apply hbc 0
    rw [hc0]
    ring
  have hb : b = 1 := by
    apply IsF2.eq_one_of_ne_zero
    intro hb0
    apply hbc 1
    rw [hb0, hc]
    calc (1 : K) ^ 2 + 0 * 1 + 1 = 1 + 1 := by ring
      _ = 0 := IsF2.one_add_one
  subst hb
  subst hc
  let Q : QuadraticForm K ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) :=
    quadTail (m - 1) (minusTailForm K 1 1)
  let E : Subgroup (((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K))) := orthElementaryGroup Q
  let e : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := tailModelEquiv (m - 1) K (Fin 2)
  have hφ : ∀ w, StatedQuadMinus m K 1 1 (e w) = Q w := by
    intro w
    have h := (minusTailIsometry m K 1 1).map_app' w
    rw [coe_quadMinus m K 1 1] at h
    exact h
  have hφq : ∀ w, quadMinus m K 1 1 (e w) = Q w := by
    intro w
    rw [coe_quadMinus m K 1 1]
    exact hφ w
  let ψ : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K ≃*
      (((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K))) :=
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).trans (conjAut e).symm
  have ψ_apply : ∀ (A : Matrix.GeneralLinearGroup
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
      (w : (Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)),
      ψ A w = e.symm (A *ᵥ e w) := fun _ _ => rfl
  have hEcomm : E = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    (commutator_orthogonalGroup_eq_of_isometry_minus (Q := Q) (m := m) (by omega) e hφq).symm
  have hOmega : StatedOmega (StatedQuadMinus m K 1 1) = E.comap ψ.toMonoidHom := by
    rw [statedOmega_eq_comap_conjAut e hφ, ← hEcomm]
  let P : Subgroup (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :=
    (s16t3MinusParab K (m - 1)).comap ψ.toMonoidHom
  have hs16le : s16t3MinusParab K (m - 1) ≤ E := by
    show (orthParab (m - 1) (minusTailForm K 1 1) (s16t3MinusCuts (m - 1))).map
      (orthElementaryGroup (quadTail (m - 1) (minusTailForm K 1 1))).subtype ≤ E
    exact Subgroup.map_subtype_le _
  have hmap_flag : ∀ (y : Matrix.GeneralLinearGroup
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K),
      y ∈ s16t3Borel (StatedQuadMinus m K 1 1) (m - 1) →
      ∀ i : Fin ((m - 1 + 1) / 2 + 1),
        (tailFlag K (Fin 2 → K) (m - 1) (s16t3MinusCuts (m - 1) i)).map
          (ψ y : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) →ₗ[K]
            ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K))) =
          tailFlag K (Fin 2 → K) (m - 1) (s16t3MinusCuts (m - 1) i) := by
    intro y hy i
    by_cases hi : (i : ℕ) = 0
    · have hd0 : s16t3MinusCuts (m - 1) i = 0 := by
        rw [s16t3MinusCuts, hi]
        simp
      rw [hd0, tailFlag_zero, Submodule.map_bot]
    · have hi1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr hi
      have hd1 : 1 ≤ s16t3MinusCuts (m - 1) i := by
        rw [s16t3MinusCuts]
        omega
      have hdr : s16t3MinusCuts (m - 1) i ≤ m - 1 := by
        rw [s16t3MinusCuts]
        exact min_le_right _ _
      refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
      intro v hv
      rw [Submodule.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hwe : e w ∈ s16t3Flag (k := m - 1) (R := Fin (m - 1) ⊕ Fin 2) (K := K)
          (s16t3MinusCuts (m - 1) i) :=
        (s16t3_map_mem_tailFlag_iff (K := K) (r := m - 1) w
          (s16t3MinusCuts (m - 1) i)).mpr hw
      have hyw := hy.2 (s16t3MinusCuts (m - 1) i) hd1 hdr (e w) hwe
      change e.symm (Matrix.mulVec (y : Matrix _ _ K) (e w)) ∈
        tailFlag K (Fin 2 → K) (m - 1) (s16t3MinusCuts (m - 1) i)
      exact (s16t3_symm_mem_tailFlag_iff (K := K) (r := m - 1)
        (Matrix.mulVec (y : Matrix _ _ K) (e w)) (s16t3MinusCuts (m - 1) i)).mpr hyw
  have hparab : ∀ z : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)),
      z ∈ s16t3MinusParab K (m - 1) ↔
        z ∈ E ∧ ∀ i : Fin ((m - 1 + 1) / 2 + 1),
          (tailFlag K (Fin 2 → K) (m - 1) (s16t3MinusCuts (m - 1) i)).map
            (z : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) →ₗ[K]
              ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K))) =
            tailFlag K (Fin 2 → K) (m - 1) (s16t3MinusCuts (m - 1) i) := by
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz
      refine ⟨hxz ▸ x.2, fun i => ?_⟩
      rw [← hxz]
      exact mem_orthParab.mp hx i
    · rintro ⟨hzE, hzstab⟩
      exact Subgroup.mem_map.mpr ⟨⟨z, hzE⟩, mem_orthParab.mpr hzstab, rfl⟩
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [hOmega, Subgroup.mem_comap]
    exact hs16le (Subgroup.mem_comap.mp hg)
  · intro y hy p hp
    rw [Subgroup.mem_comap] at hp ⊢
    rw [map_mul, map_mul, map_inv]
    obtain ⟨hpE, hpstab⟩ := (hparab (ψ p)).mp hp
    refine (hparab (ψ y * ψ p * (ψ y)⁻¹)).mpr ⟨?_, ?_⟩
    · have hψyO : ψ y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro w
        calc Q (ψ y w) = Q (e.symm (y *ᵥ e w)) := by rw [ψ_apply y w]
          _ = StatedQuadMinus m K 1 1 (e (e.symm (y *ᵥ e w))) := (hφ _).symm
          _ = StatedQuadMinus m K 1 1 (y *ᵥ e w) := by rw [LinearEquiv.apply_symm_apply]
          _ = StatedQuadMinus m K 1 1 (e w) := hy.1 (e w)
          _ = Q w := hφ w
      have hnorm : ψ y ∈ Subgroup.normalizer E := by
        rw [hEcomm]
        exact Subgroup.normalizer_commutator_ge_left _ _ hψyO
      exact (Subgroup.mem_normalizer_iff.mp hnorm (ψ p)).1 hpE
    · intro i
      have h1 : ψ y ∈ MulAction.stabilizer
          (((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
            ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)))
          (tailFlag K (Fin 2 → K) (m - 1) (s16t3MinusCuts (m - 1) i)) :=
        (Submodule.mem_stabilizer_submodule_iff_map_eq).mpr (hmap_flag y hy i)
      have h2 : ψ p ∈ MulAction.stabilizer
          (((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
            ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)))
          (tailFlag K (Fin 2 → K) (m - 1) (s16t3MinusCuts (m - 1) i)) :=
        (Submodule.mem_stabilizer_submodule_iff_map_eq).mpr (hpstab i)
      exact (Submodule.mem_stabilizer_submodule_iff_map_eq).mp
        (mul_mem (mul_mem h1 h2) (inv_mem h1))
  · intro y hy hyOmega
    rw [Subgroup.mem_comap]
    refine (hparab (ψ y)).mpr ⟨?_, ?_⟩
    · rw [hOmega, Subgroup.mem_comap] at hyOmega
      exact hyOmega
    · intro i
      exact hmap_flag y hy i
  · have hPcard : Nat.card ↥P = Nat.card ↥(s16t3MinusParab K (m - 1)) := by
      rw [show P = (s16t3MinusParab K (m - 1)).map ψ.symm.toMonoidHom from
        Subgroup.comap_equiv_eq_map_symm ψ (s16t3MinusParab K (m - 1))]
      exact Subgroup.card_map_of_injective ψ.symm.injective
    have hEcard : Nat.card ↥E = Nat.card ↥(StatedOmega (StatedQuadMinus m K 1 1)) := by
      rw [hOmega]
      rw [show E.comap ψ.toMonoidHom = E.map ψ.symm.toMonoidHom from
        Subgroup.comap_equiv_eq_map_symm ψ E]
      exact (Subgroup.card_map_of_injective ψ.symm.injective).symm
    rw [hPcard, hC.1]
    change 3 ^ ((m - 1 + 2) / 2) * 2 ^ (Nat.card ↥E).factorization 2 =
      3 ^ ((m + 1) / 2) *
        2 ^ (Nat.card ↥(StatedOmega (StatedQuadMinus m K 1 1))).factorization 2
    rw [hEcard, show m - 1 + 2 = m + 1 by omega]
  · intro p hp k hpk
    have hψ : (ψ p) ^ 3 ^ k = 1 := by
      have h1 : (ψ p) ^ 3 ^ k = ψ (p ^ 3 ^ k) := (map_pow ψ p (3 ^ k)).symm
      rw [h1, hpk, map_one]
    have hψ3 : (ψ p) ^ 3 = 1 := hC.2 (ψ p) (Subgroup.mem_comap.mp hp) k hψ
    exact ψ.injective (by rw [map_pow, hψ3, map_one])

theorem s16t3_omminus_std {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ P : Subgroup (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K),
      P ≤ StatedOmega (StatedQuadMinus m K b c) ∧
      (∀ y ∈ s16t3Borel (StatedQuadMinus m K b c) (m - 1), ∀ p ∈ P, y * p * y⁻¹ ∈ P) ∧
      (∀ y ∈ s16t3Borel (StatedQuadMinus m K b c) (m - 1),
        y ∈ StatedOmega (StatedQuadMinus m K b c) → y ∈ P) ∧
      Nat.card ↥P = 3 ^ ((m + 1) / 2) *
        2 ^ (Nat.card ↥(StatedOmega (StatedQuadMinus m K b c))).factorization 2 ∧
      ∀ p ∈ P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 := by
  have hC : S16t3MinusCensus K (m - 1) := by
    rcases Nat.lt_or_ge m 4 with h | h
    · obtain rfl : m = 3 := by omega
      exact s16t3_minus_census_two hK
    · exact s16t3_minus_census_of_three_le hK (by omega)
  exact s16t3_omminus_std_of_census hK hm hbc hC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
