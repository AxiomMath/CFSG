module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLGen

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ComponentClassification.CatalogueBHigherLinearAction CFSG.LinearGroups

section Conj

variable {n : ℕ} {K : Type} [Field K]

theorem slConjugation_tv (A : GL (Fin n) K) {v φ : Fin n → K} (h : φ ⬝ᵥ v = 0) :
    slConjugation n K A (tv v φ h) = tv ((A : Matrix (Fin n) (Fin n) K) *ᵥ v)
      (φ ᵥ* ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (by rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one, h]) := by
  apply Subtype.ext
  rw [slConjugation_matrix, tv_coe, tv_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Units.mul_inv]

end Conj

section Main


theorem subfieldPairSL {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) : SubfieldPairSL n := by
  intro K _ _ hchar k d hd hd5 hK A hne
  have : CharP K 2 := hchar
  set G₀ := slSub n k with hG₀
  set G₁ := G₀.map (slConjugation n K A).toMonoidHom with hG₁
  set H := Subgroup.closure ((G₀ : Set (SpecialLinearGroup (Fin n) K)) ∪
    (G₁ : Set (SpecialLinearGroup (Fin n) K))) with hH
  have hk : G₀ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hk1 : G₁ ≤ H := fun x hx => Subgroup.subset_closure (Or.inr hx)
  by_contra hHtop
  have NIR : ∀ a ∉ k, ∀ (i j : Fin n) (hij : i ≠ j),
      SpecialLinearGroup.transvection hij a ∉ H :=
    fun a ha i j hij hmem => hHtop (eq_top_of_root_not_mem hk hn3 hd hK ha hij hmem)
  have hd2 : d ≠ 2 := by omega
  have hnd : n < d := by omega
  have hall : ∀ (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0), tv v φ h ∈ H → v ≠ 0 → tv v φ h ∈ G₀ := by
    intro v φ h hmem hv0
    by_cases hφ0 : φ = 0
    · subst hφ0
      have h1 : tv v 0 h = 1 := Subtype.ext (by simp [tv_coe])
      rw [h1]
      exact G₀.one_mem
    · rcases tv_mem_slSub_or_generic hk hn3 NIR h hmem hv0 with hrat | hgen
      · exact hrat
      · obtain ⟨a, ha, i, j, hij, hmem'⟩ :=
          exists_root_of_generic hd hd2 hnd hn3 hK hk h hmem hφ0 hgen
        exact absurd hmem' (NIR a ha i j hij)
  have hroot : ∀ (i j : Fin n) (hij : i ≠ j) (c : K), c ∈ k →
      slConjugation n K A (SpecialLinearGroup.transvection hij c) ∈ G₀ := by
    intro i j hij c hc
    have h1 : slConjugation n K A (SpecialLinearGroup.transvection hij c) ∈ H :=
      hk1 (Subgroup.mem_map_of_mem _ (transvection_mem_slSub hij hc))
    have hne0 : (A : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i 1 : Fin n → K) ≠ 0 := by
      intro h0
      have h2 := congrArg (fun w => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) h0
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      simpa using congrFun h2 i
    rw [transvection_eq_tv hij c, slConjugation_tv] at h1 ⊢
    exact hall _ _ _ h1 hne0
  have hle : G₁ ≤ G₀ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨g₀, rfl⟩ := hy
    have hmem : g₀ ∈ Subgroup.closure (elementarySet n k) := by
      rw [special_linear_elementary_generation]
      trivial
    refine Subgroup.closure_induction
      (p := fun g _ => slConjugation n K A (SpecialLinearGroup.map k.subtype g) ∈ G₀) ?_ ?_ ?_ ?_
      hmem
    · rintro _ ⟨i, j, hij, c, rfl⟩
      rw [SpecialLinearGroup.map_transvection]
      exact hroot i j hij c c.2
    · rw [map_one, map_one]
      exact G₀.one_mem
    · intro x y _ _ hx hy
      rw [map_mul, map_mul]
      exact G₀.mul_mem hx hy
    · intro x _ hx
      rw [map_inv, map_inv]
      exact G₀.inv_mem hx
  have hcard : Nat.card G₁ = Nat.card G₀ :=
    Subgroup.card_map_of_injective (slConjugation n K A).injective
  exact hne (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

end Main

end CFSG.RankThree.PartOne.CTP
