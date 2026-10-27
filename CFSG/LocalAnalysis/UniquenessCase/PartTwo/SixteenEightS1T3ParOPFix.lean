module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParO
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
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

theorem s16t3_omplus_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {X : Subgroup (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K)}
    (hX : IsPGroup 2 ↥X)
    (hXQ : ∀ x ∈ X, ∀ v : Fin m ⊕ Fin m → K,
      StatedQuadPlus m K (Matrix.mulVec (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) v) =
        StatedQuadPlus m K v) :
    ∃ g ∈ StatedOmega (StatedQuadPlus m K),
      ∀ x ∈ X, g⁻¹ * x * g ∈ s16t3Borel (StatedQuadPlus m K) (m - 1) := by
  haveI hprime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    let _ := Fintype.ofFinite K
    exact charP_of_card_eq_prime (p := 2) (Nat.card_eq_fintype_card.symm.trans hK)
  haveI := hchar
  have hm1 : 1 ≤ m := by omega
  set φ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K ≃*
      ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin m ⊕ Fin m) K with hφ
  set X' : Subgroup ((Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) :=
    X.map φ.toMonoidHom with hX'def
  have hX' : IsPGroup 2 ↥X' := by
    rw [hX'def]
    exact hX.of_equiv (φ.subgroupMap X)
  have hX'O : X' ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) := by
    intro y hy
    rw [hX'def] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [MulEquiv.coe_toMonoidHom, hφ, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      CFSG.LieType.Universal.Spin.coe_quadPlus m K]
    exact hXQ x hx v
  set s₀ : Fin (m - 1) → Submodule K (Fin m ⊕ Fin m → K) :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.stdFlag m K with hs₀
  have hinv : ∀ x ∈ X', ∀ t ∈ MulAction.orbit ↥(orthElementaryGroup (quadPlus m K)) s₀,
      x • t ∈ MulAction.orbit ↥(orthElementaryGroup (quadPlus m K)) s₀ := by
    intro x hx t ht
    rw [hX'def] at hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hzX' : φ.toMonoidHom z ∈ X' := by
      rw [hX'def]; exact Subgroup.mem_map_of_mem φ.toMonoidHom hz
    rw [hs₀, CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.orbit_stdFlag hm1] at ht ⊢
    exact CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.map_mem_singularFlags
      (hX'O hzX') ht
  have hodd : ¬ 2 ∣ Nat.card (MulAction.orbit ↥(orthElementaryGroup (quadPlus m K)) s₀) := by
    have h1 : Nat.card (MulAction.orbit ↥(orthElementaryGroup (quadPlus m K)) s₀) =
        (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flagStab m K).relIndex
          (orthElementaryGroup (quadPlus m K)) := by
      rw [hs₀, CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.orbit_stdFlag hm1]
      exact (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.relIndex_flagStab
        (K := K) hm1).symm
    have hmod := CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.relIndex_flagStab_modEq
      (K := K) hm1
    rw [← h1] at hmod
    exact CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.not_dvd_of_modEq_one
      (K := K) 2 hmod
  obtain ⟨g, hgE, hgstab⟩ := s16t3_exists_conj_stabilizer
    (G := (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (E := orthElementaryGroup (quadPlus m K)) (X := X') s₀ hX' hodd hinv
  set g' : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K := φ.symm g with hg'def
  refine ⟨g', ?_, ?_⟩
  · rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_map_elementaryGroup
      (CFSG.LieType.Universal.Spin.coe_quadPlus m K)
      (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.commutator_orthogonalGroup_quadPlus
        (K := K) hm)]
    rw [hg'def, hφ]
    exact Subgroup.mem_map_of_mem (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin m ⊕ Fin m) K).symm.toMonoidHom hgE
  · intro x hx
    have hxX' : φ x ∈ X' := by
      rw [hX'def]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
    have hxO : φ x ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) := hX'O hxX'
    have hstab := hgstab (φ x) hxX'
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) :=
      orthElementaryGroup_le (quadPlus m K) hgE
    set y : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K) := g⁻¹ * φ x * g with hydef
    have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) := by
      rw [hydef]
      exact mul_mem (mul_mem (inv_mem hgO) hxO) hgO
    have hconj : φ (g'⁻¹ * x * g') = g⁻¹ * φ x * g := by
      rw [hg'def, hφ]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    have hmv : ∀ v : Fin m ⊕ Fin m → K,
        Matrix.mulVec ((g'⁻¹ * x * g' : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) v = y v := by
      intro v
      rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, ← hφ, hconj, hydef]
    have hmap : ∀ j : Fin (m - 1),
        (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.stdFlag m K j).map
          (y : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) =
        CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.stdFlag m K j := by
      intro j
      have h := congrFun (MulAction.mem_stabilizer_iff.mp hstab) j
      rw [hs₀] at h
      exact h
    rw [s16t3Borel]
    refine ⟨?_, ?_⟩
    · intro v
      rw [hmv v, ← CFSG.LieType.Universal.Spin.coe_quadPlus m K]
      exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hyO) v
    · intro i hi1 hid v hv
      obtain ⟨j, hj⟩ : ∃ j : Fin (m - 1), (j : ℕ) + 1 = i :=
        ⟨⟨i - 1, by omega⟩, by simp only [Fin.val_mk]; omega⟩
      have hmapj := hmap j
      simp only [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.stdFlag] at hmapj
      rw [hj] at hmapj
      have hv' : v ∈ CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i :=
        (s16t3_flag_iff_mem_flag (K := K) (i := i)).mp hv
      have hyv : y v ∈ CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.flag m K i := by
        rw [← hmapj]
        exact ⟨v, hv', rfl⟩
      rw [hmv v]
      exact (s16t3_flag_iff_mem_flag (K := K) (i := i)).mpr hyv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
