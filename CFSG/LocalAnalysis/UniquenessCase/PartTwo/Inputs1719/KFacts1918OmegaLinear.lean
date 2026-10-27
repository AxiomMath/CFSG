module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.LocalAnalysis.EvenBN.Tits.I21LUna

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.EvenBN.Tits.I21L

variable {ι : Type} [Fintype ι] [DecidableEq ι]

section

local instance instAddCommGroupPiZMod2 : AddCommGroup (ι → ZMod 2) :=
  { Pi.addCommGroup with toAddCommMonoid := Pi.addCommMonoid }

private lemma two_mul_finrank_map_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (B : V →ₗ[ZMod 2] V) (hBB : B * B = 0)
    (X : Submodule (ZMod 2) V) (hX : ∀ x ∈ X, B x ∈ X) :
    2 * Module.finrank (ZMod 2) (X.map B) ≤ Module.finrank (ZMod 2) X := by
  classical
  have h1 : Module.finrank (ZMod 2) (X.map B) +
      Module.finrank (ZMod 2) ((LinearMap.ker B).comap X.subtype) =
      Module.finrank (ZMod 2) X := by
    have h := LinearMap.finrank_range_add_finrank_ker (B.domRestrict X)
    rw [show LinearMap.range (B.domRestrict X) = X.map B from
        LinearMap.range_domRestrict X B,
      show LinearMap.ker (B.domRestrict X) = (LinearMap.ker B).comap X.subtype from
        LinearMap.ker_domRestrict X B] at h
    exact h
  have hker : Module.finrank (ZMod 2) ((LinearMap.ker B).comap X.subtype) =
      Module.finrank (ZMod 2) (X ⊓ LinearMap.ker B : Submodule (ZMod 2) V) := by
    have hmap : (X ⊓ LinearMap.ker B : Submodule (ZMod 2) V) =
        ((LinearMap.ker B).comap X.subtype).map X.subtype :=
      (Submodule.map_comap_subtype (p := X) (p' := LinearMap.ker B)).symm
    rw [hmap]
    exact (Submodule.finrank_map_subtype_eq X ((LinearMap.ker B).comap X.subtype)).symm
  have hle : X.map B ≤ (X ⊓ LinearMap.ker B : Submodule (ZMod 2) V) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hX y hy, ?_⟩
    show B (B y) = 0
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
      congrArg (fun f : V →ₗ[ZMod 2] V => f y) hBB
  have hfinle : Module.finrank (ZMod 2) (X.map B) ≤
      Module.finrank (ZMod 2) (X ⊓ LinearMap.ker B : Submodule (ZMod 2) V) :=
    Submodule.finrank_mono hle
  omega

theorem rank_sub_one_le_of_commute_orderOf_five (hι : Fintype.card ι ≤ 8)
    {g d : GL ι (ZMod 2)} (hg : g * g = 1) (hd : orderOf d = 5) (hgd : g * d = d * g) :
    ((g : Matrix ι ι (ZMod 2)) - 1).rank ≤ (Fintype.card ι - 4) / 2 ∨
      (Fintype.card ι = 8 ∧ Even ((g : Matrix ι ι (ZMod 2)) - 1).rank) := by
  classical
  let x : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2)
      (Matrix.GeneralLinearGroup.toLin d)
  let y : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2)
      (Matrix.GeneralLinearGroup.toLin g)
  let B : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
    (y : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) - 1
  let U : Submodule (ZMod 2) (ι → ZMod 2) := LinearMap.ker (nu x)
  let W : Submodule (ZMod 2) (ι → ZMod 2) := LinearMap.range (nu x)
  have hxeq : x = LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2)
      (Matrix.GeneralLinearGroup.toLin d) := rfl
  have hyeq : y = LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2)
      (Matrix.GeneralLinearGroup.toLin g) := rfl
  have hBlin : ((g : Matrix ι ι (ZMod 2)) - 1).mulVecLin = B := by
    apply LinearMap.ext
    intro v
    simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, B, y,
      LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin]
  have hrank : ((g : Matrix ι ι (ZMod 2)) - 1).rank =
      Module.finrank (ZMod 2) (LinearMap.range B) := by
    rw [Matrix.rank, hBlin]
  have hd5 : d ^ 5 = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  have hu5 : (Matrix.GeneralLinearGroup.toLin d) ^ 5 = 1 := by
    rw [← map_pow, hd5, map_one]
  have hx5 : x ^ 5 = 1 := by rw [hxeq, ← map_pow, hu5, map_one]
  have hgg : (Matrix.GeneralLinearGroup.toLin g) * (Matrix.GeneralLinearGroup.toLin g) = 1 := by
    rw [← map_mul, hg, map_one]
  have hy2 : y * y = 1 := by rw [hyeq, ← map_mul, hgg, map_one]
  have hxy : x * y = y * x := by
    have hd' : (Matrix.GeneralLinearGroup.toLin d) * (Matrix.GeneralLinearGroup.toLin g) =
        (Matrix.GeneralLinearGroup.toLin g) * (Matrix.GeneralLinearGroup.toLin d) := by
      rw [← map_mul, ← map_mul, hgd.symm]
    have h := congrArg (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (ι → ZMod 2)) hd'
    rw [map_mul, map_mul] at h
    simpa only [hxeq, hyeq] using h
  have hyxlin : (y : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) *
      (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) =
      (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) *
      (y : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) := by
    rw [← LinearEquiv.coe_toLinearMap_mul, ← LinearEquiv.coe_toLinearMap_mul, hxy.symm]
  have hcomm_xy : ∀ v : ι → ZMod 2,
      (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2))
        ((y : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) v) =
      (y : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2))
        ((x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) v) := by
    intro v
    have h := congrArg (fun f : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) => f v) hyxlin
    simpa only [Module.End.mul_apply] using h.symm
  have hxorder : orderOf x = 5 := by
    have h1 : orderOf x = orderOf (Matrix.GeneralLinearGroup.toLin d) :=
      MulEquiv.orderOf_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
        (ι → ZMod 2)) (Matrix.GeneralLinearGroup.toLin d)
    have h2 : orderOf (Matrix.GeneralLinearGroup.toLin d) = orderOf d :=
      MulEquiv.orderOf_eq (Matrix.GeneralLinearGroup.toLin (n := ι) (R := ZMod 2)) d
    exact h1.trans (h2.trans hd)
  have hxodd : Odd (orderOf x) := by rw [hxorder]; norm_num
  have hcompl : IsCompl U W := by
    have := isCompl_fixSp_range_nu x hxodd
    simpa only [U, W, fixSp] using this
  have hUWdim : Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) U =
      Module.finrank (ZMod 2) (ι → ZMod 2) := by
    have := LinearMap.finrank_range_add_finrank_ker (nu x)
    simpa only [W, U] using this
  have hWstable : Stable x W := by
    intro w hw
    have hw' : w ∈ LinearMap.range (nu x) := hw
    obtain ⟨v, rfl⟩ := hw'
    refine ⟨x v, ?_⟩
    show nu x (x v) = (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (nu x v)
    rw [nu_apply, nu_apply,
      LinearMap.map_sub (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2))]
    rfl
  have hWfix : ∀ w ∈ W, x w = w → w = 0 := by
    intro w hw hxw
    have hwU : w ∈ U := LinearMap.mem_ker.mpr (by simp only [nu_apply, hxw, sub_self])
    have hmem : w ∈ (U ⊓ W : Submodule (ZMod 2) (ι → ZMod 2)) := ⟨hwU, hw⟩
    rw [hcompl.inf_eq_bot] at hmem
    simpa using hmem
  have hWne : W ≠ ⊥ := by
    intro h
    have hrangeW : LinearMap.range (nu x) = ⊥ := h
    have hz : nu x = 0 := LinearMap.range_eq_bot.mp hrangeW
    have hx1 : x = 1 := by
      apply LinearEquiv.ext
      intro v
      have hv := congrArg (fun f : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) => f v) hz
      simpa [nu_apply, sub_eq_zero] using hv
    rw [hx1, orderOf_one] at hxorder
    omega
  have hdvdW : 4 ∣ Module.finrank (ZMod 2) W :=
    four_dvd_finrank_of_stable hx5 hWstable hWfix
  have hWle : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (ι → ZMod 2) :=
    Submodule.finrank_le W
  have hdimV : Module.finrank (ZMod 2) (ι → ZMod 2) = Fintype.card ι := by
    simpa using Module.finrank_fintype_fun_eq_card (R := ZMod 2)
  have hfinWpos : 0 < Module.finrank (ZMod 2) W := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hWne (Submodule.finrank_eq_zero.mp h0)
  have hcases : Module.finrank (ZMod 2) W = 4 ∨ Module.finrank (ZMod 2) W = 8 := by
    obtain ⟨k, hk⟩ := hdvdW
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with hk1 | hk1 <;> [left; right] <;> omega
  have hBB : B * B = 0 := by
    apply LinearMap.ext
    intro v
    change nu y (nu y v) = 0
    exact nu_nu_of_sq y hy2 v
  have hBxlin : B * (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) =
      (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) * B := by
    simp only [B]
    rw [sub_mul, mul_sub, one_mul, mul_one, hyxlin]
  have hBx : ∀ v, B ((x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) v) =
      (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (B v) := by
    intro v
    have := congrArg (fun f : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) => f v) hBxlin
    simpa only [Module.End.mul_apply] using this
  have hBU : ∀ u ∈ U, B u ∈ U := by
    intro u hu
    have hu' : nu x u = 0 := LinearMap.mem_ker.mp hu
    have hxu : (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) u = u := by
      have h := hu'
      rw [nu_apply] at h
      exact sub_eq_zero.mp h
    refine LinearMap.mem_ker.mpr ?_
    change (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2))
          ((y : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) u - u) -
        ((y : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) u - u) = 0
    rw [LinearMap.map_sub (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)),
      hcomm_xy u, hxu]
    abel
  have hBW : ∀ w ∈ W, B w ∈ W := by
    intro w hw
    have hw' : w ∈ LinearMap.range (nu x) := hw
    obtain ⟨v, rfl⟩ := hw'
    refine ⟨B v, ?_⟩
    change (x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) (B v) - B v =
      B ((x : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2)) v - v)
    simp only [LinearMap.map_sub B, hBx v]
  have h2BU : 2 * Module.finrank (ZMod 2) (U.map B) ≤ Module.finrank (ZMod 2) U :=
    two_mul_finrank_map_le B hBB U hBU
  have h2BW : 2 * Module.finrank (ZMod 2) (W.map B) ≤ Module.finrank (ZMod 2) W :=
    two_mul_finrank_map_le B hBB W hBW
  have hBWle : W.map B ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact hBW w hw
  have hBWstable : Stable x (W.map B) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨x w, hWstable w hw, hBx w⟩
  have hBWfix : ∀ z ∈ W.map B, x z = z → z = 0 := fun z hz => hWfix z (hBWle hz)
  have hBWdvd : 4 ∣ Module.finrank (ZMod 2) (W.map B) :=
    four_dvd_finrank_of_stable hx5 hBWstable hBWfix
  have hrange : LinearMap.range B = U.map B ⊔ W.map B := by
    rw [← Submodule.map_top B, ← hcompl.sup_eq_top, Submodule.map_sup]
  rcases hcases with hW4 | hW8
  ·
    left
    have hle2 : Module.finrank (ZMod 2) (W.map B) ≤ 2 := by omega
    have hBW0 : Module.finrank (ZMod 2) (W.map B) = 0 := by
      obtain ⟨k, hk⟩ := hBWdvd
      omega
    have hBWbot : W.map B = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      exact hBW0
    have hrange4 : LinearMap.range B = U.map B := by
      rw [hrange, hBWbot, sup_bot_eq]
    have h2r : 2 * Module.finrank (ZMod 2) (U.map B) ≤ Fintype.card ι - 4 := by
      have := h2BU
      omega
    have hbd : Module.finrank (ZMod 2) (U.map B) ≤ (Fintype.card ι - 4) / 2 :=
      (Nat.le_div_iff_mul_le (show 0 < 2 by norm_num)).mpr (by omega)
    rw [hrank, hrange4]
    exact hbd
  ·
    right
    have hdimV8 : Module.finrank (ZMod 2) (ι → ZMod 2) = 8 := by
      have := hWle
      omega
    have hcard8 : Fintype.card ι = 8 := by omega
    have hU0 : Module.finrank (ZMod 2) U = 0 := by omega
    have hUbot : U = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      exact hU0
    have hrange8 : LinearMap.range B = W.map B := by
      rw [hrange, hUbot, Submodule.map_bot, bot_sup_eq]
    have hdvd_rank : 4 ∣ Module.finrank (ZMod 2) (LinearMap.range B) := by
      rw [hrange8]
      exact hBWdvd
    refine ⟨hcard8, ?_⟩
    rw [hrank]
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num : (2 : ℕ) ∣ 4) hdvd_rank)

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
