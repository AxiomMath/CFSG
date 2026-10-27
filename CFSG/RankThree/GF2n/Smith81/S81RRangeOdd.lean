module

public import CFSG.RankThree.GF2n.Smith81.S81NMask

open CFSG.RankThree.GF2n.Smith81.A5Cube

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

private theorem rho_one_scr : rho K (1 : GL (Fin 6) K) = 1 :=
  map_one (TauCeti.extPowerRep K 6 3)

private theorem rho_mul_apply_scr (g h : GL (Fin 6) K) (ξ : Cube K) :
    rho K (g * h) ξ = rho K g (rho K h ξ) := by
  rw [rho, map_mul, Module.End.mul_apply]

private theorem rho_inv_cancel_apply (c : GL (Fin 6) K) (η : Cube K) :
    rho K c⁻¹ (rho K c η) = η := by
  rw [← rho_mul_apply_scr, inv_mul_cancel, rho_one_scr, Module.End.one_apply]

private theorem rho_conj_apply (c x : GL (Fin 6) K) (η : Cube K) :
    rho K (c * x * c⁻¹) (rho K c η) = rho K c (rho K x η) := by
  rw [rho_mul_apply_scr, rho_inv_cancel_apply, rho_mul_apply_scr]

private theorem rho_sub_one_conj (c x : GL (Fin 6) K) (η : Cube K) :
    rho K c ((rho K x - 1) η) = (rho K (c * x * c⁻¹) - 1) (rho K c η) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, rho_conj_apply]

private theorem cfm_eq_zero_of_mem_range_transv [CharP K 2] (i j : Fin 6) (hij : i ≠ j) (c : K)
    {η : Cube K} (hη : η ∈ LinearMap.range (rho K (transvGL K i j hij c) - 1))
    {m : ℕ} (hm : m < 64)
    (hsupp : ¬(m.testBit i.val = true ∧ m.testBit j.val = false)) :
    cfm K η m = 0 := by
  obtain ⟨ξ, rfl⟩ := LinearMap.mem_range.mp hη
  rw [LinearMap.sub_apply, Module.End.one_apply, cfm_sub,
    cfm_rho_transv i j hij c ξ m hm, if_neg hsupp]
  simp

private theorem eq_zero_of_two_ranges [CharP K 2] {α β : K} {ζ : Cube K}
    (h1 : ζ ∈ LinearMap.range (rho K (transvGL K 0 1 (by decide) α) - 1))
    (h2 : ζ ∈ LinearMap.range (rho K (transvGL K 1 0 (by decide) β) - 1)) : ζ = 0 := by
  refine cfm_ext (fun m hm => ?_)
  rw [cfm_zero]
  by_cases hA : m.testBit 0 = true ∧ m.testBit 1 = false
  · refine cfm_eq_zero_of_mem_range_transv 1 0 (by decide) β h2 hm ?_
    rintro ⟨h1', -⟩
    exact absurd (hA.2.symm.trans h1') (by decide)
  · exact cfm_eq_zero_of_mem_range_transv 0 1 (by decide) α h1 hm hA

theorem range_inf_range_eq_bot_odd [Finite K] [CharP K 2] {x y : GL (Fin 6) K}
    (hx : IsTransvec K x) (hy : IsTransvec K y) (hodd : Odd (orderOf (x * y)))
    (hne : x * y ≠ 1) :
    LinearMap.range (rho K x - 1) ⊓ LinearMap.range (rho K y - 1) = ⊥ := by
  obtain ⟨c, α, β, -, -, -, hcx, hcy⟩ := fe3_conj hx hy hodd hne
  rw [Submodule.eq_bot_iff]
  intro ξ hξ
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hξ
  obtain ⟨η1, hη1⟩ := LinearMap.mem_range.mp h1
  obtain ⟨η2, hη2⟩ := LinearMap.mem_range.mp h2
  have hT1 : rho K c ξ ∈ LinearMap.range (rho K (transvGL K 0 1 (by decide) α) - 1) := by
    refine LinearMap.mem_range.mpr ⟨rho K c η1, ?_⟩
    rw [← hcx, ← rho_sub_one_conj, hη1]
  have hT2 : rho K c ξ ∈ LinearMap.range (rho K (transvGL K 1 0 (by decide) β) - 1) := by
    refine LinearMap.mem_range.mpr ⟨rho K c η2, ?_⟩
    rw [← hcy, ← rho_sub_one_conj, hη2]
  have h0 : rho K c ξ = 0 := eq_zero_of_two_ranges hT1 hT2
  calc ξ = rho K c⁻¹ (rho K c ξ) := (rho_inv_cancel_apply c ξ).symm
    _ = 0 := by rw [h0, map_zero]

end CFSG.RankThree.GF2n.Smith81.A5Cube
