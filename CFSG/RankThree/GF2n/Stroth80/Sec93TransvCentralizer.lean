module

public import CFSG.CGT.Timmesfeld75.ListWCLinPSL
public import CFSG.RankThree.GF2n.Stroth80.Sec93TransvAlgebra

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Matrix CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

theorem one_add_vecMulVec_mul_self_center [CharP K 2] {c a : Fin m → K} (h : a ⬝ᵥ c = 0) :
    (1 + vecMulVec c a) * (1 + vecMulVec c a) = (1 : Matrix (Fin m) (Fin m) K) := by
  rw [one_add_vecMulVec_mul_center m K c a a h, ← two_smul K a, CharTwo.two_eq_zero,
    zero_smul, vecMulVec_zero, add_zero]

theorem one_add_vecMulVec_mul_self_axis [CharP K 2] {a v : Fin m → K} (h : a ⬝ᵥ v = 0) :
    (1 + vecMulVec v a) * (1 + vecMulVec v a) = (1 : Matrix (Fin m) (Fin m) K) := by
  rw [one_add_vecMulVec_mul_axis m K a v v h, ← two_smul K v, CharTwo.two_eq_zero,
    zero_smul, zero_vecMulVec, add_zero]

theorem eq_one_of_mul_eq_smul_mul_char_two [CharP K 2] (hm : 1 ≤ m) {S T : Matrix (Fin m) (Fin m) K}
    (hS : S.det ≠ 0) (hT : T * T = 1) {r : K} (h : T * S = r • (S * T)) : r = 1 := by
  have h1 : S = (r * r) • S := by
    have e1 : T * (T * S) = r • (r • S) := by
      rw [h, Matrix.mul_smul, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.mul_assoc S T T, hT,
        Matrix.mul_one]
    calc S = (T * T) * S := by rw [hT, Matrix.one_mul]
      _ = T * (T * S) := by rw [Matrix.mul_assoc]
      _ = r • (r • S) := e1
      _ = (r * r) • S := by rw [smul_smul]
  have h2 : ((r * r) - 1) • S = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  have hS0 : S ≠ 0 := by
    rintro rfl
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact hS Matrix.det_zero
  have h3 : (r * r) - 1 = 0 := (smul_eq_zero.1 h2).resolve_right hS0
  exact eq_one_of_mul_self_eq_one_char_two (sub_eq_zero.1 h3)

theorem mem_transvImage_center_of_centralizes [CharP K 2] (hm : 2 ≤ m) {c : Fin m → K}
    (hc : c ≠ 0) {x : StatedProj (StatedSL m K)}
    (hx : ∀ y ∈ transvImage m K (transvCenter m K c), x * y = y * x) :
    x ∈ transvImage m K (transvCenter m K c) := by
  set ε := specialLinearGroupEquivStatedSL m K with hε
  obtain ⟨xt, rfl⟩ := QuotientGroup.mk_surjective x
  set s : SL(m, K) := ε.symm xt with hs
  have hxs : ε s = xt := ε.apply_symm_apply xt
  have hdet : ((s : Matrix (Fin m) (Fin m) K)).det ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact one_ne_zero
  have memT : ∀ g : SL(m, K), g ∈ tvCenterSL c →
      (QuotientGroup.mk (ε g) : StatedProj (StatedSL m K)) ∈
        transvImage m K (transvCenter m K c) := by
    intro g hg
    refine ⟨ε g, ?_, rfl⟩
    rw [← map_tvCenterSL]
    exact Subgroup.mem_map_of_mem _ hg
  have hcomm : ∀ a : Fin m → K, a ⬝ᵥ c = 0 →
      (s : Matrix (Fin m) (Fin m) K) * (1 + vecMulVec c a) =
        (1 + vecMulVec c a) * (s : Matrix (Fin m) (Fin m) K) := by
    intro a ha
    set t : SL(m, K) := tvSL c a ha with ht
    have h1 := hx _ (memT t ⟨a, ha, rfl⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      ← map_center_eq_statedScalars m K] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have hz' : z = (s * t)⁻¹ * (t * s) := by
      apply ε.injective
      have hzeq' : ε z = (xt * ε t)⁻¹ * (ε t * xt) := hzeq
      rw [hzeq', map_mul, map_inv, map_mul, map_mul, hxs]
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
    have h2 : (t : Matrix (Fin m) (Fin m) K) * (s : Matrix (Fin m) (Fin m) K) =
        r • ((s : Matrix (Fin m) (Fin m) K) * (t : Matrix (Fin m) (Fin m) K)) := by
      have h3 : t * s = (s * t) * z := by rw [hz']; group
      have h4 := congrArg (fun g : SL(m, K) => (g : Matrix (Fin m) (Fin m) K)) h3
      simp only [Matrix.SpecialLinearGroup.coe_mul, ← hr] at h4
      rw [h4, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    have hr1 : r = 1 :=
      eq_one_of_mul_eq_smul_mul_char_two (by omega) hdet
        (by rw [coe_tvSL]; exact one_add_vecMulVec_mul_self_center ha) h2
    rw [hr1, one_smul] at h2
    rw [coe_tvSL] at h2
    exact h2.symm
  obtain ⟨μ, b, hb, hS⟩ := eq_smul_one_add_vecMulVec_of_commute_center hm hc hcomm
  have hμ : μ ≠ 0 := by
    rintro rfl
    have h1 : (s : Matrix (Fin m) (Fin m) K) *ᵥ c = 0 := by
      rw [hS, zero_smul, zero_add, Matrix.vecMulVec_mulVec, hb, op_smul_eq_smul, zero_smul]
    apply hc
    have h2 := inv_mulVec_mulVec' s c
    rw [h1, Matrix.mulVec_zero] at h2
    exact h2.symm
  have hb' : (μ⁻¹ • b) ⬝ᵥ c = 0 := by rw [smul_dotProduct, hb, smul_zero]
  set g : SL(m, K) := tvSL c (μ⁻¹ • b) hb' with hg
  have hSg : (s : Matrix (Fin m) (Fin m) K) = μ • (g : Matrix (Fin m) (Fin m) K) := by
    rw [hS, hg, coe_tvSL, smul_add, vecMulVec_smul, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  have hgT : g ∈ tvCenterSL c := ⟨μ⁻¹ • b, hb', rfl⟩
  have hmk : (QuotientGroup.mk (ε g) : StatedProj (StatedSL m K)) = QuotientGroup.mk xt := by
    rw [QuotientGroup.eq, ← map_center_eq_statedScalars m K]
    refine ⟨g⁻¹ * s, ?_, ?_⟩
    · rw [SetLike.mem_coe, Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨μ, ?_, ?_⟩
      · have hd := Matrix.SpecialLinearGroup.det_coe s
        rw [hSg, Matrix.det_smul, Matrix.SpecialLinearGroup.det_coe g, mul_one,
          Fintype.card_fin] at hd
        rw [Fintype.card_fin]
        exact hd
      · rw [Matrix.SpecialLinearGroup.coe_mul, hSg, Matrix.mul_smul, coe_inv_mul_coe',
          Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    · show ε (g⁻¹ * s) = (ε g)⁻¹ * xt
      rw [map_mul, map_inv, hxs]
  rw [← hmk]
  exact memT g hgT

theorem mem_transvImage_axis_of_centralizes [CharP K 2] (hm : 2 ≤ m) {a : Fin m → K}
    (ha : a ≠ 0) {x : StatedProj (StatedSL m K)}
    (hx : ∀ y ∈ transvImage m K (transvAxis m K a), x * y = y * x) :
    x ∈ transvImage m K (transvAxis m K a) := by
  set ε := specialLinearGroupEquivStatedSL m K with hε
  obtain ⟨xt, rfl⟩ := QuotientGroup.mk_surjective x
  set s : SL(m, K) := ε.symm xt with hs
  have hxs : ε s = xt := ε.apply_symm_apply xt
  have hdet : ((s : Matrix (Fin m) (Fin m) K)).det ≠ 0 := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact one_ne_zero
  have memT : ∀ g : SL(m, K), g ∈ tvAxisSL a →
      (QuotientGroup.mk (ε g) : StatedProj (StatedSL m K)) ∈
        transvImage m K (transvAxis m K a) := by
    intro g hg
    refine ⟨ε g, ?_, rfl⟩
    rw [← map_tvAxisSL]
    exact Subgroup.mem_map_of_mem _ hg
  have hcomm : ∀ v : Fin m → K, a ⬝ᵥ v = 0 →
      (s : Matrix (Fin m) (Fin m) K) * (1 + vecMulVec v a) =
        (1 + vecMulVec v a) * (s : Matrix (Fin m) (Fin m) K) := by
    intro v hv
    set t : SL(m, K) := tvSL v a hv with ht
    have h1 := hx _ (memT t ⟨v, hv, rfl⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      ← map_center_eq_statedScalars m K] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have hz' : z = (s * t)⁻¹ * (t * s) := by
      apply ε.injective
      have hzeq' : ε z = (xt * ε t)⁻¹ * (ε t * xt) := hzeq
      rw [hzeq', map_mul, map_inv, map_mul, map_mul, hxs]
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
    have h2 : (t : Matrix (Fin m) (Fin m) K) * (s : Matrix (Fin m) (Fin m) K) =
        r • ((s : Matrix (Fin m) (Fin m) K) * (t : Matrix (Fin m) (Fin m) K)) := by
      have h3 : t * s = (s * t) * z := by rw [hz']; group
      have h4 := congrArg (fun g : SL(m, K) => (g : Matrix (Fin m) (Fin m) K)) h3
      simp only [Matrix.SpecialLinearGroup.coe_mul, ← hr] at h4
      rw [h4, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    have hr1 : r = 1 :=
      eq_one_of_mul_eq_smul_mul_char_two (by omega) hdet
        (by rw [coe_tvSL]; exact one_add_vecMulVec_mul_self_axis hv) h2
    rw [hr1, one_smul] at h2
    rw [coe_tvSL] at h2
    exact h2.symm
  obtain ⟨μ, w, hw, hS⟩ := eq_smul_one_add_vecMulVec_of_commute_axis hm ha hcomm
  have hμ : μ ≠ 0 := by
    rintro rfl
    have h1 : a ᵥ* (s : Matrix (Fin m) (Fin m) K) = 0 := by
      rw [hS, zero_smul, zero_add, Matrix.vecMul_vecMulVec, hw, zero_smul]
    exact vecMul_ne_zero' s ha h1
  have hw' : a ⬝ᵥ (μ⁻¹ • w) = 0 := by rw [dotProduct_smul, hw, smul_zero]
  set g : SL(m, K) := tvSL (μ⁻¹ • w) a hw' with hg
  have hSg : (s : Matrix (Fin m) (Fin m) K) = μ • (g : Matrix (Fin m) (Fin m) K) := by
    rw [hS, hg, coe_tvSL, smul_add, smul_vecMulVec, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  have hgT : g ∈ tvAxisSL a := ⟨μ⁻¹ • w, hw', rfl⟩
  have hmk : (QuotientGroup.mk (ε g) : StatedProj (StatedSL m K)) = QuotientGroup.mk xt := by
    rw [QuotientGroup.eq, ← map_center_eq_statedScalars m K]
    refine ⟨g⁻¹ * s, ?_, ?_⟩
    · rw [SetLike.mem_coe, Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨μ, ?_, ?_⟩
      · have hd := Matrix.SpecialLinearGroup.det_coe s
        rw [hSg, Matrix.det_smul, Matrix.SpecialLinearGroup.det_coe g, mul_one,
          Fintype.card_fin] at hd
        rw [Fintype.card_fin]
        exact hd
      · rw [Matrix.SpecialLinearGroup.coe_mul, hSg, Matrix.mul_smul, coe_inv_mul_coe',
          Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    · show ε (g⁻¹ * s) = (ε g)⁻¹ * xt
      rw [map_mul, map_inv, hxs]
  rw [← hmk]
  exact memT g hgT

end CFSG.RankThree.GF2n.Stroth80
