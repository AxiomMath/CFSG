module

public import CFSG.RankThree.GF2n.Smith81.S81E7Fe3

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

theorem IsRootElt.mem_E {g : (Module.End K (V K))ˣ} (hg : IsRootElt g) : g ∈ EGrp K := by
  obtain ⟨h, hh, γ, c, -, -, rfl⟩ := hg
  exact mul_mem (mul_mem hh (e7Data_valid.xu_mem K γ c)) (inv_mem hh)

theorem isRootEltG_mk [CharP K 2] {x : (Module.End K (V K))ˣ} (hm : x ∈ EGrp K) (hx : IsRootElt x) :
    IsRootEltG (⟨x, hm⟩ : ↥(e7Data_valid.minGroup K)) := by
  obtain ⟨h, hh, γ, c, hγ, hc, he⟩ := hx
  refine ⟨⟨h, hh⟩, γ, c, hγ, hc, ?_⟩
  exact Subtype.ext he

theorem fe3_conj [CharP K 2] {x y : (Module.End K (V K))ˣ} (hx : IsRootElt x) (hy : IsRootElt y)
    (ho : Odd (orderOf (x * y))) (h1 : x * y ≠ 1) :
    ∃ e ∈ EGrp K, ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      e * x * e⁻¹ = e7Data_valid.xu K theta a ∧ e * y * e⁻¹ = e7Data_valid.xu K (-theta) b := by
  have hord : orderOf ((⟨x, hx.mem_E⟩ : ↥(e7Data_valid.minGroup K)) * ⟨y, hy.mem_E⟩) =
      orderOf (x * y) := (Subgroup.orderOf_coe _).symm
  have hne : (⟨x, hx.mem_E⟩ : ↥(e7Data_valid.minGroup K)) * ⟨y, hy.mem_E⟩ ≠ 1 :=
    fun h => h1 (congrArg Subtype.val h)
  obtain ⟨e, a, b, ha, hb, hXe, hYe⟩ :=
    fe3_conj_core (isRootEltG_mk hx.mem_E hx) (isRootEltG_mk hy.mem_E hy) (by rw [hord]; exact ho) hne
  exact ⟨(e : (Module.End K (V K))ˣ), e.2, a, b, ha, hb, congrArg Subtype.val hXe,
    congrArg Subtype.val hYe⟩

theorem trace_low_up [CharP K 2] (a b : K) :
    ((MinData.Valid.slLower K a * MinData.Valid.slUpper K b :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace = a * b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val, MinData.Valid.slUpper_val,
    Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h2

theorem slLower_mul_slUpper_apply_10 (a b : K) :
    ((MinData.Valid.slLower K a * MinData.Valid.slUpper K b :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = a := by
  rw [Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val, MinData.Valid.slUpper_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end CFSG.RankThree.GF2n.Smith81.E7Model
