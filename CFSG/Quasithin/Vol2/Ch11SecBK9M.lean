module

public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.Quasithin.Vol2.Ch11SecBK7B
public import CFSG.Quasithin.Vol2.Ch11SecBK9E

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K] [CharP K 2]

theorem exists_stabQ_apply_eq {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)} (hQ : IsSpForm Q)
    {c c' : Fin 2 ⊕ Fin 2 → K} (hc : c ≠ 0) (hc' : c' ≠ 0) (hQc : Q c' = Q c) :
    ∃ δ ∈ stabQ Q, mat 2 K δ *ᵥ c = c' := by
  obtain ⟨g, hg, hgc⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    (polarBilin_nondegenerate hQ) ![c] ![c']
    (linearIndependent_unique_iff.mpr (by simpa using hc))
    (linearIndependent_unique_iff.mpr (by simpa using hc'))
    (fun i => by
      obtain rfl := Subsingleton.elim i 0
      simpa using hQc)
    (fun i j => by
      obtain rfl := Subsingleton.elim i j
      rw [hQ, hQ, K7.bil_self, K7.bil_self])
  have hgQ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  obtain ⟨γ, hγ⟩ := exists_sp_of_isometry (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] _).toLinearMap
    fun u v => by
      rw [← hQ, ← hQ]
      exact polar_map_of_iso _ hgQ u v
  refine ⟨γ, fun x => ?_, ?_⟩
  · rw [hγ]
    exact hgQ x
  · rw [hγ]
    simpa using hgc 0

@[expose] noncomputable def perpProj (b u x : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K :=
  x + spB K x u • b + spB K x b • u

theorem spB_perpProj_left {b u : Fin 2 ⊕ Fin 2 → K} (hbu : spB K b u = 1)
    (x : Fin 2 ⊕ Fin 2 → K) : spB K b (perpProj b u x) = 0 := by
  rw [perpProj, K7.bil_add_right, K7.bil_add_right, K7.bil_smul_right, K7.bil_smul_right,
    K7.bil_self, hbu, mul_zero, add_zero, mul_one, K7.bil_comm b x, CharTwo.add_self_eq_zero]

theorem spB_perpProj_right {b u : Fin 2 ⊕ Fin 2 → K} (hbu : spB K b u = 1)
    (x : Fin 2 ⊕ Fin 2 → K) : spB K u (perpProj b u x) = 0 := by
  rw [perpProj, K7.bil_add_right, K7.bil_add_right, K7.bil_smul_right, K7.bil_smul_right,
    K7.bil_self, K7.bil_comm u b, hbu, mul_zero, add_zero, mul_one, K7.bil_comm u x,
    CharTwo.add_self_eq_zero]

theorem spB_perpProj_of_perp {b u p : Fin 2 ⊕ Fin 2 → K} (hb : spB K b p = 0)
    (hu : spB K u p = 0) (y : Fin 2 ⊕ Fin 2 → K) : spB K p (perpProj b u y) = spB K p y := by
  rw [perpProj, K7.bil_add_right, K7.bil_add_right, K7.bil_smul_right, K7.bil_smul_right,
    K7.bil_comm p b, hb, K7.bil_comm p u, hu, mul_zero, mul_zero, add_zero, add_zero]

theorem exists_not_mem_span (b u : Fin 2 ⊕ Fin 2 → K) :
    ∃ x, x ∉ Submodule.span K (Set.range ![b, u]) := by
  by_contra h
  simp only [not_exists, not_not] at h
  have htop : Submodule.span K (Set.range ![b, u]) = ⊤ := eq_top_iff.mpr fun x _ => h x
  have h1 := finrank_range_le_card (R := K) ![b, u]
  rw [Set.finrank, htop, finrank_top, finrank_four, Fintype.card_fin] at h1
  omega

theorem perpProj_ne_zero {b u x : Fin 2 ⊕ Fin 2 → K}
    (hx : x ∉ Submodule.span K (Set.range ![b, u])) : perpProj b u x ≠ 0 := by
  intro h
  apply hx
  have e : x = perpProj b u x - spB K x u • b - spB K x b • u := by
    rw [perpProj]
    abel
  rw [e, h, zero_sub]
  refine Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ ?_))
    (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩

theorem exists_perp_nonsingular {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)} (hQ : IsSpForm Q)
    {b u : Fin 2 ⊕ Fin 2 → K} (hbu : spB K b u = 1) :
    ∃ p, spB K b p = 0 ∧ spB K u p = 0 ∧ Q p ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_not_mem_span b u
  obtain ⟨y, hy⟩ := K7.exists_bil_eq_one (perpProj_ne_zero hx)
  have h12 : spB K (perpProj b u x) (perpProj b u y) = 1 := by
    rw [spB_perpProj_of_perp (spB_perpProj_left hbu x) (spB_perpProj_right hbu x), K7.bil_comm]
    exact hy
  by_cases h1 : Q (perpProj b u x) = 0
  · by_cases h2 : Q (perpProj b u y) = 0
    · refine ⟨perpProj b u x + perpProj b u y, ?_, ?_, ?_⟩
      · rw [K7.bil_add_right, spB_perpProj_left hbu, spB_perpProj_left hbu, add_zero]
      · rw [K7.bil_add_right, spB_perpProj_right hbu, spB_perpProj_right hbu, add_zero]
      · have h := hQ (perpProj b u x) (perpProj b u y)
        simp only [polar] at h
        rw [h12, h1, h2, sub_zero, sub_zero] at h
        rw [h]
        exact one_ne_zero
    · exact ⟨perpProj b u y, spB_perpProj_left hbu y, spB_perpProj_right hbu y, h2⟩
  · exact ⟨perpProj b u x, spB_perpProj_left hbu x, spB_perpProj_right hbu x, h1⟩

theorem exists_bil_quad [Finite K] (hK : Nat.card K = 4) {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)}
    (hQ : IsSpForm Q) {b : Fin 2 ⊕ Fin 2 → K} (hb : b ≠ 0) (μ q : K) :
    ∃ c, spB K b c = μ ∧ Q c = q := by
  have := Fintype.ofFinite K
  have h4 : ∀ a : K, a ^ 4 = a := fun a => by
    have h := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hK] at h
  obtain ⟨u, hu⟩ := K7.exists_bil_eq_one hb
  have hbu : spB K b u = 1 := by
    rw [K7.bil_comm]
    exact hu
  obtain ⟨p, hbp, hup, hp⟩ := exists_perp_nonsingular hQ hbu
  obtain ⟨s, hs⟩ : ∃ s : K, s * Q p = q - μ ^ 2 * Q u :=
    ⟨(q - μ ^ 2 * Q u) / Q p, div_mul_cancel₀ _ hp⟩
  refine ⟨μ • u + s ^ 2 • p, ?_, ?_⟩
  · rw [K7.bil_add_right, K7.bil_smul_right, K7.bil_smul_right, hbu, hbp, mul_zero, add_zero,
      mul_one]
  · have h := hQ (μ • u) (s ^ 2 • p)
    simp only [polar] at h
    rw [K7.bil_smul_left, K7.bil_smul_right, hup, mul_zero, mul_zero] at h
    rw [show Q (μ • u + s ^ 2 • p) = Q (μ • u) + Q (s ^ 2 • p) by linear_combination h,
      QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul,
      show s ^ 2 * s ^ 2 = s by rw [← pow_add]; exact h4 s, hs]
    ring

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
