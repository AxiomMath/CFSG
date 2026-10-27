module

public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem exists_toPGL_eq_sq {K : Type*} [Field K] (g : PGL2 K) :
    ∃ x : PSL2 K, Matrix.ProjectiveSpecialLinearGroup.toPGL x = g ^ 2 :=
  CFSG.GorensteinWalter.pgl2_sq_mem_psl2Range g

theorem exists_toPGL_eq_of_pow_odd {K : Type*} [Field K] {g : PGL2 K} {n : ℕ} (hn : Odd n)
    (hg : g ^ n = 1) : ∃ x : PSL2 K, Matrix.ProjectiveSpecialLinearGroup.toPGL x = g :=
  CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_pow_odd hn hg

theorem mem_range_pglAction_of_rightHom_eq_one {K : Type*} [Field K] [Finite K]
    {α : MulAut (PSL2 K)} (h : SemidirectProduct.rightHom ((semilinearEquivAut K).symm α) = 1) :
    α ∈ (pglAction K).range := by
  set x := (semilinearEquivAut K).symm α with hx
  have hα : semilinearAction K x = α := (semilinearEquivAut K).apply_symm_apply α
  have hr : x.right = 1 := h
  have hx2 := congrArg (semilinearAction K) (SemidirectProduct.inl_left_mul_inr_right x)
  rw [map_mul, semilinearAction_inl, semilinearAction_inr, hr, map_one, mul_one, hα] at hx2
  exact ⟨x.left, hx2⟩

theorem exists_pow_eq_of_pow_three_ringEquiv {K : Type*} [Field K] [Finite K] {s t : K ≃+* K}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (ht3 : t ^ 3 = 1) : ∃ j : ℕ, s ^ j = t := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, m, hp, hK⟩ := FiniteField.card' K
  have := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K
    (by rw [Nat.card_eq_fintype_card, hK])).2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht : IsOfFinOrder t := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, ht3⟩
  have hs : IsOfFinOrder s := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hs3⟩
  have := ht.finite_zpowers
  have hle : Subgroup.zpowers t ≤ Subgroup.zpowers s := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime hs3 hs1]
    exact orderOf_dvd_of_pow_eq_one ht3
  have hmem := hle (Subgroup.mem_zpowers t)
  rw [← hs.mem_powers_iff_mem_zpowers] at hmem
  exact (Submonoid.mem_powers_iff _ _).mp hmem

theorem exists_pow_mul_isInnerAut_psl2 {K : Type*} [Field K] [Finite K]
    {P : Subgroup (MulAut (PSL2 K))} (hP : IsPGroup 3 P) {σ τ : MulAut (PSL2 K)} (hσP : σ ∈ P)
    (hτP : τ ∈ P) (hσ3 : σ ^ 3 = 1) (hσ : ¬ IsInnerAut σ) (hτ3 : τ ^ 3 = 1) :
    ∃ i : ℕ, IsInnerAut (σ ^ i * τ) := by
  let ψ : MulAut (PSL2 K) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom
  have hs3 : ψ σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have ht3 : ψ τ ^ 3 = 1 := by rw [← map_pow, hτ3, map_one]
  have hs1 : ψ σ ≠ 1 := fun h =>
    hσ (isInnerAut_of_mem_inndiag_of_pow_three (mem_range_pglAction_of_rightHom_eq_one h) hσ3)
  obtain ⟨j, hj⟩ := exists_pow_eq_of_pow_three_ringEquiv hs3 hs1 ht3
  refine ⟨2 * j, ?_⟩
  have hψ : ψ (σ ^ (2 * j) * τ) = 1 := by
    rw [map_mul, map_pow, ← hj, ← pow_add, show 2 * j + j = 3 * j by ring, pow_mul, hs3,
      one_pow]
  obtain ⟨g, hg⟩ := mem_range_pglAction_of_rightHom_eq_one hψ
  obtain ⟨k, hk⟩ := hP ⟨_, mul_mem (pow_mem hσP _) hτP⟩
  have hk' : (σ ^ (2 * j) * τ) ^ 3 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hg' : g ^ 3 ^ k = 1 := pglAction_injective (by rw [map_pow, hg, hk', map_one])
  obtain ⟨x, hx⟩ := exists_toPGL_eq_of_pow_odd (Odd.pow (by decide)) hg'
  exact ⟨x, by rw [← hg, ← hx, pglAction_toPGL]⟩

theorem exists_pow_mul_isInnerAut_of_mulEquiv_psl2 {X : Type*} [Group X] {K : Type*} [Field K]
    [Finite K] (e : X ≃* PSL2 K) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) {σ τ : MulAut X}
    (hσP : σ ∈ P) (hτP : τ ∈ P) (hσ3 : σ ^ 3 = 1) (hσ : ¬ IsInnerAut σ) (hτ3 : τ ^ 3 = 1) :
    ∃ i : ℕ, IsInnerAut (σ ^ i * τ) := by
  obtain ⟨i, hi⟩ := exists_pow_mul_isInnerAut_psl2 (hP.map (MulAut.congr e).toMonoidHom)
    (σ := MulAut.congr e σ) (τ := MulAut.congr e τ) ⟨σ, hσP, rfl⟩ ⟨τ, hτP, rfl⟩
    (by rw [← map_pow, hσ3, map_one]) (by rwa [isInnerAut_congr])
    (by rw [← map_pow, hτ3, map_one])
  refine ⟨i, ?_⟩
  rwa [← map_pow, ← map_mul, isInnerAut_congr] at hi

end CFSG.RankThree.PartTwo.KFacts
