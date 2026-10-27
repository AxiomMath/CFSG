module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.Q1327F

open CFSG.Assembly.LowTwoRank Polynomial

theorem exists_pow_p_scalar {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {p k : ℕ}
    [Fact p.Prime] (hn : Fintype.card ι ≤ p) {K : Type} [Field K] [Finite K] [CharP K p]
    (A : Matrix ι ι K) (c : K) (hA : A ^ p ^ k = Matrix.scalar ι c) :
    ∃ c' : K, A ^ p = Matrix.scalar ι c' := by
  classical
  have : ExpChar K p := ExpChar.prime (Fact.out)
  have : PerfectRing K p := inferInstance
  have : PerfectRing K (p ^ k) := inferInstance
  obtain ⟨μ, hμ⟩ := (PerfectRing.bijective_frobenius (R := K) (p := p ^ k)).2 c
  set S : Matrix ι ι K := Matrix.scalar ι μ with hS
  have hcomm : Commute A S := (Matrix.scalar_commute μ (fun r => Commute.all _ _) A).symm
  have hSpow : ∀ m : ℕ, S ^ m = Matrix.scalar ι (μ ^ m) := fun m => by
    rw [hS, map_pow]
  have hN : (A - S) ^ p ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute p k hcomm, hA, hSpow]
    simp only [hμ]
    exact sub_self _
  have hnil : IsNilpotent (A - S) := ⟨p ^ k, hN⟩
  have hcp : (A - S).charpoly = X ^ Fintype.card ι := by
    rw [← sub_eq_zero]
    exact IsNilpotent.eq_zero (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil)
  have hNn : (A - S) ^ Fintype.card ι = 0 := by
    have := Matrix.aeval_self_charpoly (A - S)
    rwa [hcp, map_pow, aeval_X] at this
  have hNp : (A - S) ^ p = 0 := by
    rw [show p = Fintype.card ι + (p - Fintype.card ι) by omega, pow_add, hNn, zero_mul]
  refine ⟨μ ^ p, ?_⟩
  have h1 : A = S + (A - S) := by abel
  have hc2 : Commute S (A - S) := hcomm.symm.sub_right (Commute.refl S)
  calc A ^ p = (S + (A - S)) ^ p := by rw [← h1]
    _ = S ^ p + (A - S) ^ p := add_pow_char_of_commute p hc2
    _ = Matrix.scalar ι (μ ^ p) := by rw [hNp, add_zero, hSpow]

theorem statedProj_pow_p_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {p : ℕ}
    [Fact p.Prime] (hn : Fintype.card ι ≤ p) {K : Type} [Field K] [Finite K] [CharP K p]
    (M : Subgroup (GL ι K)) (y : StatedProj M) (hy : ∃ k : ℕ, y ^ p ^ k = 1) : y ^ p = 1 := by
  classical
  obtain ⟨k, hk⟩ := hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : g ^ p ^ k ∈ (StatedScalars ι K).subgroupOf M := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h1
  have hA : ((g : GL ι K) : Matrix ι ι K) ^ p ^ k = Matrix.scalar ι (c : K) := by
    have := congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using this.symm
  obtain ⟨c', hc'⟩ := exists_pow_p_scalar hn _ _ hA
  have hdet : (((g : GL ι K) ^ p : GL ι K) : Matrix ι ι K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
  have hc'0 : c' ≠ 0 := by
    intro h0
    apply hdet
    rw [Units.val_pow_eq_pow_val, hc', h0]
    simp
  have hg : (g : GL ι K) ^ p = Matrix.GeneralLinearGroup.scalar ι (Units.mk0 c' hc'0) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hc', Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.2 (by
    rw [Subgroup.coe_pow, hg]
    exact ⟨_, rfl⟩)

end CFSG.RankThree.PartOne.Q1327F
