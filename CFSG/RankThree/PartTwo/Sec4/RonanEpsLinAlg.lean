module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

theorem exists_eigenvector_of_commute_sq_zero {F : Type*} [Field F]
    {g N : Matrix (Fin 3) (Fin 3) F} (hN : N ≠ 0) (hN2 : N * N = 0) (hgN : g * N = N * g) :
    ∃ (v : Fin 3 → F) (μ : F), v ≠ 0 ∧ g.mulVec v = μ • v := by
  obtain ⟨L, hL⟩ : ∃ L : (Fin 3 → F) →ₗ[F] (Fin 3 → F), ∀ x, L x = N.mulVec x :=
    ⟨N.mulVecLin, fun x => Matrix.mulVecLin_apply N x⟩
  have hle : LinearMap.range L ≤ LinearMap.ker L := by
    intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [LinearMap.mem_ker, hL, hL, Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  have hmono := Submodule.finrank_mono hle
  have hdim : Module.finrank F (Fin 3 → F) = 3 := by simp
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (Matrix.ext fun i j => by simp [h i j])
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 → F, w = N.mulVec (Pi.single j 1) := ⟨_, rfl⟩
  have hwi : w i = N i j := by
    rw [hw]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hw0 : w ≠ 0 := by
    intro h
    apply hij
    rw [← hwi]
    simp [h]
  have hwL : w ∈ LinearMap.range L :=
    LinearMap.mem_range.mpr ⟨Pi.single j 1, by rw [hL, hw]⟩
  have hne : LinearMap.range L ≠ ⊥ := by
    intro h
    exact hw0 ((Submodule.eq_bot_iff _).mp h w hwL)
  have hpos : 1 ≤ Module.finrank F (LinearMap.range L) :=
    Submodule.one_le_finrank_iff.mpr hne
  have hrank : Module.finrank F (LinearMap.range L) = 1 := by omega
  have hgw : g.mulVec w ∈ LinearMap.range L :=
    LinearMap.mem_range.mpr
      ⟨g.mulVec (Pi.single j 1), by
        rw [hL, hw, Matrix.mulVec_mulVec, ← hgN, Matrix.mulVec_mulVec]⟩
  have hnz : (⟨w, hwL⟩ : LinearMap.range L) ≠ 0 := by
    intro h
    apply hw0
    simpa using congrArg Subtype.val h
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' _ hnz).mp hrank (⟨g.mulVec w, hgw⟩ : LinearMap.range L)
  refine ⟨w, c, hw0, ?_⟩
  simpa using (congrArg Subtype.val hc).symm

theorem pow_three_eq_of_eigenvector {F : Type*} [Field F] {g : Matrix (Fin 3) (Fin 3) F}
    {c μ : F} (hg : g ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F)) {v : Fin 3 → F} (hv : v ≠ 0)
    (hgv : g.mulVec v = μ • v) : μ ^ 3 = c := by
  have hk : ∀ k : ℕ, (g ^ k).mulVec v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ g k, ← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ' μ k]
  have h1 : (g ^ 3).mulVec v = μ ^ 3 • v := hk 3
  have h2 : (g ^ 3).mulVec v = c • v := by
    rw [hg, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h3 : (μ ^ 3 - c) • v = 0 := by
    rw [sub_smul, ← h1, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

end CFSG.RankThree.PartTwo.Sec4.RonanEps
