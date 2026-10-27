module

public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.RankThree.GF2n.Smith81

open scoped Matrix

section Alg

variable {F : Type} [Field F] {n : ℕ}

theorem exists_vecMul_eq_zero_dotProduct_ne {A : Matrix (Fin n) (Fin n) F} {y : Fin n → F}
    (hy : ¬ ∃ z, A *ᵥ z = y) : ∃ g : Fin n → F, g ᵥ* A = 0 ∧ g ⬝ᵥ y ≠ 0 := by
  have hyS : y ∉ LinearMap.range (Matrix.mulVecLin A) := by
    rintro ⟨z, hz⟩
    exact hy ⟨z, hz⟩
  obtain ⟨f, hfy, hfS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyS inferInstance
  obtain ⟨g, hfg⟩ : ∃ g : Fin n → F, ∀ u : Fin n → F, f u = g ⬝ᵥ u := by
    refine ⟨fun i => f (Pi.single i 1), fun u => ?_⟩
    have hsingle : ∀ (i : Fin n) (c : F), Pi.single i c = c • Pi.single i (1 : F) := by
      intro i c
      ext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_apply, h]
    calc f u = f (∑ i, Pi.single i (u i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i, f (Pi.single i (u i)) := by rw [map_sum]
      _ = ∑ i, u i * f (Pi.single i (1 : F)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsingle i (u i), map_smul, smul_eq_mul]
      _ = (fun i => f (Pi.single i (1 : F))) ⬝ᵥ u := by
          simp only [dotProduct]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨g, ?_, ?_⟩
  · have hz : ∀ z : Fin n → F, (g ᵥ* A) ⬝ᵥ z = 0 := by
      intro z
      have hmem : A *ᵥ z ∈ LinearMap.range (Matrix.mulVecLin A) :=
        LinearMap.mem_range_self (Matrix.mulVecLin A) z
      have hmap : f (A *ᵥ z) ∈ Submodule.map f (LinearMap.range (Matrix.mulVecLin A)) :=
        Submodule.mem_map_of_mem hmem
      rw [hfS, Submodule.mem_bot] at hmap
      rw [← Matrix.dotProduct_mulVec, ← hfg, hmap]
    funext i
    simpa [dotProduct_single] using hz (Pi.single i 1)
  · rw [← hfg]
    exact hfy

theorem lemmaL_matrix {N : Matrix (Fin n) (Fin n) F} (hN0 : N ≠ 0) {v w : Fin n → F}
    (hW : ∀ (s f : Fin n → F), f ᵥ* N = 0 → (f ⬝ᵥ v) • (N *ᵥ s) = 0)
    (hW' : ∀ (c s : Fin n → F), N *ᵥ c = 0 → (c ⬝ᵥ w) • (Nᵀ *ᵥ s) = 0) :
    (∃ z, N *ᵥ z = v) ∧ (∃ z, Nᵀ *ᵥ z = w) := by
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j : Fin n, N i j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hN0
    ext i j
    simp [hcon i j]
  have hs : N *ᵥ Pi.single j₀ (1 : F) ≠ 0 := by
    intro h
    apply hij
    have h' := congrFun h i₀
    simpa [Matrix.mulVec_single_one] using h'
  constructor
  · by_contra hv
    obtain ⟨f, hf0, hfv⟩ := exists_vecMul_eq_zero_dotProduct_ne hv
    exact hs ((smul_eq_zero.mp (hW (Pi.single j₀ (1 : F)) f hf0)).resolve_left hfv)
  · by_contra hw
    obtain ⟨g, hg0, hgw⟩ := exists_vecMul_eq_zero_dotProduct_ne hw
    rw [Matrix.vecMul_transpose] at hg0
    have hr : Nᵀ *ᵥ Pi.single i₀ (1 : F) = 0 :=
      (smul_eq_zero.mp (hW' g (Pi.single i₀ (1 : F)) hg0)).resolve_left hgw
    apply hij
    have := congrFun hr j₀
    simpa [Matrix.mulVec_single_one] using this


end Alg

section InvCoord

variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E] [Field F] {n : ℕ}

structure InvCoord (T : E ≃ₗ[K] E) (Ψ : E ≃+ (Fin n → F) × (Fin n → F))
    (X₀ : Matrix (Fin n) (Fin n) F) : Prop where
  act : ∀ e, Ψ (T e) = (X₀ *ᵥ (Ψ e).1, X₀ᵀ *ᵥ (Ψ e).2)

variable {T : E ≃ₗ[K] E} {Ψ : E ≃+ (Fin n → F) × (Fin n → F)} {X₀ : Matrix (Fin n) (Fin n) F}

theorem InvCoord.fixed_iff (h : InvCoord T Ψ X₀) (e : E) :
    T e = e ↔ (X₀ - 1) *ᵥ (Ψ e).1 = 0 ∧ (X₀ - 1)ᵀ *ᵥ (Ψ e).2 = 0 := by
  have key1 : ∀ (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F),
      (M - 1) *ᵥ v = 0 ↔ M *ᵥ v = v := by
    intro M v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have key2 : ∀ (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F),
      (M - 1)ᵀ *ᵥ v = 0 ↔ Mᵀ *ᵥ v = v := by
    intro M v
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero]
  rw [key1, key2]
  constructor
  · intro he
    have h1 : Ψ (T e) = Ψ e := by rw [he]
    rw [h.act e] at h1
    exact Prod.ext_iff.mp h1
  · intro he
    apply Ψ.injective
    rw [h.act e]
    exact Prod.ext he.1 he.2

theorem InvCoord.exists_sub_iff (h : InvCoord T Ψ X₀) (e : E) :
    (∃ u, T u - u = e) ↔
      ∃ v' w' : Fin n → F, Ψ e = ((X₀ - 1) *ᵥ v', (X₀ - 1)ᵀ *ᵥ w') := by
  have key1 : ∀ (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F),
      (M - 1) *ᵥ v = M *ᵥ v - v := by
    intro M v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have key2 : ∀ (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F),
      (M - 1)ᵀ *ᵥ v = Mᵀ *ᵥ v - v := by
    intro M v
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(Ψ u).1, (Ψ u).2, ?_⟩
    rw [map_sub, h.act u, key1, key2]
    refine Prod.ext ?_ ?_ <;> simp
  · rintro ⟨v', w', hv'⟩
    refine ⟨Ψ.symm (v', w'), ?_⟩
    apply Ψ.injective
    rw [map_sub, h.act, AddEquiv.apply_symm_apply, hv', key1, key2]
    refine Prod.ext ?_ ?_ <;> simp

theorem InvCoord.commute_of_transv (h : InvCoord T Ψ X₀) (U : E ≃ₗ[K] E) {r f : Fin n → F}
    (hU : ∀ e, Ψ (U e) =
      ((Ψ e).1 + (f ⬝ᵥ (Ψ e).1) • r, (Ψ e).2 - (r ⬝ᵥ (Ψ e).2) • f))
    (hr : X₀ *ᵥ r = r) (hf : f ᵥ* X₀ = f) (e : E) : U (T e) = T (U e) := by
  apply Ψ.injective
  have h1 : Ψ (U (T e)) = (X₀ *ᵥ (Ψ e).1 + (f ⬝ᵥ (X₀ *ᵥ (Ψ e).1)) • r,
      X₀ᵀ *ᵥ (Ψ e).2 - (r ⬝ᵥ (X₀ᵀ *ᵥ (Ψ e).2)) • f) := by
    rw [hU (T e), h.act e]
  have h2 : Ψ (T (U e)) = (X₀ *ᵥ ((Ψ e).1 + (f ⬝ᵥ (Ψ e).1) • r),
      X₀ᵀ *ᵥ ((Ψ e).2 - (r ⬝ᵥ (Ψ e).2) • f)) := by
    rw [h.act (U e), hU e]
  have hrw : r ⬝ᵥ (X₀ᵀ *ᵥ (Ψ e).2) = r ⬝ᵥ (Ψ e).2 := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hr]
  have hfv : f ⬝ᵥ (X₀ *ᵥ (Ψ e).1) = f ⬝ᵥ (Ψ e).1 := by
    rw [Matrix.dotProduct_mulVec, hf]
  rw [h1, h2, hrw, hfv]
  congr 1
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hr]
  · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_transpose X₀ f, hf]

theorem InvCoord.exists_sub_of_transv₁ (h : InvCoord T Ψ X₀) (U : E ≃ₗ[K] E)
    {r f s : Fin n → F}
    (hU : ∀ e, Ψ (U e) =
      ((Ψ e).1 + (f ⬝ᵥ (Ψ e).1) • r, (Ψ e).2 - (r ⬝ᵥ (Ψ e).2) • f))
    (hr : r = (X₀ - 1) *ᵥ s) {e : E} (he : T e = e) : ∃ u, T u - u = U e - e := by
  obtain ⟨-, hw0⟩ := (h.fixed_iff e).mp he
  have hd : r ⬝ᵥ (Ψ e).2 = 0 := by
    rw [hr, dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, hw0, dotProduct_zero]
  have hUe : Ψ (U e - e) = ((f ⬝ᵥ (Ψ e).1) • r, 0) := by
    rw [map_sub, hU e, hd, zero_smul, sub_zero]
    refine Prod.ext ?_ ?_ <;> simp
  refine (h.exists_sub_iff (U e - e)).mpr ⟨(f ⬝ᵥ (Ψ e).1) • s, 0, ?_⟩
  rw [hUe, Matrix.mulVec_smul, ← hr, Matrix.mulVec_zero]

theorem InvCoord.exists_sub_of_transv₂ (h : InvCoord T Ψ X₀) (U : E ≃ₗ[K] E)
    {r f s : Fin n → F}
    (hU : ∀ e, Ψ (U e) =
      ((Ψ e).1 + (f ⬝ᵥ (Ψ e).1) • r, (Ψ e).2 - (r ⬝ᵥ (Ψ e).2) • f))
    (hf : f = (X₀ - 1)ᵀ *ᵥ s) {e : E} (he : T e = e) : ∃ u, T u - u = U e - e := by
  obtain ⟨hv0, -⟩ := (h.fixed_iff e).mp he
  have hc : f ⬝ᵥ (Ψ e).1 = 0 := by
    rw [hf, dotProduct_comm, Matrix.dotProduct_transpose_mulVec, hv0, dotProduct_zero]
  have hUe : Ψ (U e - e) = (0, -((r ⬝ᵥ (Ψ e).2) • f)) := by
    rw [map_sub, hU e, hc, zero_smul, add_zero]
    refine Prod.ext ?_ ?_ <;> simp
  refine (h.exists_sub_iff (U e - e)).mpr ⟨0, (-(r ⬝ᵥ (Ψ e).2)) • s, ?_⟩
  rw [hUe, Matrix.mulVec_zero, Matrix.mulVec_smul, ← hf, neg_smul]

end InvCoord

end CFSG.RankThree.GF2n.Smith81
