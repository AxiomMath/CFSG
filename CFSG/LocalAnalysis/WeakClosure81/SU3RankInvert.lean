module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

private theorem su3_pow_mul_eq_mul_inv {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    {y t : LGL 2 F} (ht : t * t = 1) (hty : t * y * t = y⁻¹) (j : ℕ) :
    y ^ j * t = t * (y ^ j)⁻¹ := by
  have hyt : y * t = t * y⁻¹ := by
    have h := congrArg (fun z => t * z) hty
    rwa [← mul_assoc, ← mul_assoc, ht, one_mul] at h
  induction j with
  | zero => simp
  | succ j ih =>
    calc y ^ (j + 1) * t = y ^ j * (y * t) := by rw [pow_succ, mul_assoc]
      _ = y ^ j * (t * y⁻¹) := by rw [hyt]
      _ = (y ^ j * t) * y⁻¹ := by rw [mul_assoc]
      _ = (t * (y ^ j)⁻¹) * y⁻¹ := by rw [ih]
      _ = t * ((y ^ j)⁻¹ * y⁻¹) := by rw [mul_assoc]
      _ = t * (y * y ^ j)⁻¹ := by rw [← mul_inv_rev]
      _ = t * (y ^ (j + 1))⁻¹ := by rw [pow_succ' y j]

theorem finrank_range_sub_le_two_mul_modCommRank {F : Type} [AddCommGroup F]
    [Module (ZMod 2) F] [Finite F] {t y : LGL 2 F} (ht : t * t = 1) (hty : t * y * t = y⁻¹)
    (hy : Odd (orderOf y)) :
    Module.finrank (ZMod 2) (LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id)) ≤
      2 * modCommRank t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup (LGL 2 F) := Subgroup.zpowers y with hY
  set W : Submodule (ZMod 2) F := commSub Y with hW
  have hWrange : W = LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id) := by
    rw [hW, hY, commSub_zpowers]
  rw [← hWrange]
  have htY : t ∈ Subgroup.normalizer (Y : Set (LGL 2 F)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hY]
    show (Subgroup.zpowers y).map (MulAut.conj t).toMonoidHom = Subgroup.zpowers y
    rw [MonoidHom.map_zpowers]
    have hconj : (MulAut.conj t).toMonoidHom y = y⁻¹ := by
      change MulAut.conj t y = y⁻¹
      rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right ht]
      exact hty
    rw [hconj, Subgroup.zpowers_inv]
  set T : Subgroup (LGL 2 F) := Subgroup.zpowers t with hT
  set TY : Subgroup (LGL 2 F) := Subgroup.zpowers (t * y) with hTYd
  set C : Submodule (ZMod 2) F := W ⊓ fixSub T with hC
  set C' : Submodule (ZMod 2) F := W ⊓ fixSub TY with hC'
  have hoddY : Odd (Nat.card Y) := by rw [hY, Nat.card_zpowers]; exact hy
  have hcompl : IsCompl (fixSub Y) (commSub Y) := isCompl_fixSub_commSub_of_odd Y hoddY
  obtain ⟨j, hj⟩ := hy
  let u : LGL 2 F := y ^ j
  have huY : u ∈ Y := by
    rw [hY]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by simp [u]⟩
  have huWle : W.map (u : F →ₗ[ZMod 2] F) ≤ W := by
    rintro w ⟨v, hv, rfl⟩
    rw [hW] at hv ⊢
    exact map_mem_commSub Y huY hv
  have huW : W.map (u : F →ₗ[ZMod 2] F) = W := by
    refine le_antisymm huWle ?_
    intro w hw
    refine ⟨u⁻¹ w, ?_, by simp⟩
    rw [hW] at hw ⊢
    exact map_mem_commSub Y (Y.inv_mem huY) hw
  have hu_t : u * t * u⁻¹ = t * y := by
    have hut : u * t = t * u⁻¹ := su3_pow_mul_eq_mul_inv (y := y) (t := t) ht hty j
    have hy2j : y ^ (2 * j) = y⁻¹ := by
      have h : y ^ (2 * j) * y = 1 := by
        rw [← pow_succ, ← hj, pow_orderOf_eq_one]
      exact eq_inv_of_mul_eq_one_left h
    calc u * t * u⁻¹ = (t * u⁻¹) * u⁻¹ := by rw [hut]
      _ = t * (u⁻¹ * u⁻¹) := by rw [mul_assoc]
      _ = t * (u * u)⁻¹ := by rw [← mul_inv_rev]
      _ = t * (y ^ j * y ^ j)⁻¹ := rfl
      _ = t * (y ^ (j + j))⁻¹ := by rw [← pow_add]
      _ = t * (y ^ (2 * j))⁻¹ := by rw [← two_mul]
      _ = t * (y⁻¹)⁻¹ := by rw [hy2j]
      _ = t * y := by rw [inv_inv]
  have hTY_cj : TY = cj u T := by
    have hcj : cj u (Subgroup.zpowers t) = Subgroup.zpowers (u * t * u⁻¹) := by
      show (Subgroup.zpowers t).map (MulAut.conj u).toMonoidHom = _
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hTYd, hT, hcj, hu_t]
  have hCeq : C' = C.map (u : F →ₗ[ZMod 2] F) := by
    rw [hC', hC, hTY_cj, fixSub_cj,
      Submodule.map_inf (u : F →ₗ[ZMod 2] F) u.injective, huW]
  have hfinC : Module.finrank (ZMod 2) C' = Module.finrank (ZMod 2) C := by
    rw [hCeq]
    exact (Submodule.equivMapOfInjective (u : F →ₗ[ZMod 2] F) u.injective C).finrank_eq.symm
  have hinf : C ⊓ C' = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwC, hwC'⟩ := hw
    rw [hC, Submodule.mem_inf] at hwC
    obtain ⟨hwW, hwfixT⟩ := hwC
    rw [hC', Submodule.mem_inf] at hwC'
    obtain ⟨-, hwfixTY⟩ := hwC'
    have htw : t w = w :=
      (mem_fixSub T).mp hwfixT t (by rw [hT]; exact Subgroup.mem_zpowers t)
    have htyw : (t * y) w = w :=
      (mem_fixSub TY).mp hwfixTY (t * y)
        (by rw [hTYd]; exact Subgroup.mem_zpowers (t * y))
    have hyw : y w = w := by
      have h1 : (t * (t * y)) w = t w := by rw [LinearEquiv.mul_apply, htyw]
      have h2 : t * (t * y) = y := by rw [← mul_assoc, ht, one_mul]
      rw [h2] at h1
      rw [h1, htw]
    have hwfixY : w ∈ fixSub Y := by
      rw [hY, fixSub_zpowers, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero]
      exact hyw
    have hwcommY : w ∈ commSub Y := by rw [hW] at hwW; exact hwW
    have hmem : w ∈ fixSub Y ⊓ commSub Y := ⟨hwfixY, hwcommY⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem
    exact hmem
  haveI : Module.Finite (ZMod 2) C := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) C' := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have h2C : 2 * Module.finrank (ZMod 2) C ≤ Module.finrank (ZMod 2) W := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq C C'
    rw [hinf, finrank_bot, add_zero] at h1
    have hCW : C ≤ W := by rw [hC]; exact inf_le_left
    have hC'W : C' ≤ W := by rw [hC']; exact inf_le_left
    have h4 : Module.finrank (ZMod 2) ↥(C ⊔ C') ≤ Module.finrank (ZMod 2) W :=
      Submodule.finrank_mono (sup_le hCW hC'W)
    rw [h1, hfinC] at h4
    omega
  let g : W →ₗ[ZMod 2] F := ((t : F →ₗ[ZMod 2] F).comp W.subtype) - W.subtype
  have hC_eq : C = W ⊓ LinearMap.ker ((t : F →ₗ[ZMod 2] F) - LinearMap.id) := by
    rw [hC, hT, fixSub_zpowers]
  have hkerC : (LinearMap.ker g).map W.subtype = C := by
    rw [hC_eq]
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      exact LinearMap.mem_ker.mpr (by
        have h := LinearMap.mem_ker.mp hw
        simpa [g, LinearMap.sub_apply] using h)
    · rintro ⟨hvW, hvker⟩
      refine ⟨⟨v, hvW⟩, ?_, rfl⟩
      exact LinearMap.mem_ker.mpr (by
        have h := LinearMap.mem_ker.mp hvker
        simpa [g, LinearMap.sub_apply] using h)
  have hfin_ker : Module.finrank (ZMod 2) (LinearMap.ker g) = Module.finrank (ZMod 2) C := by
    rw [← hkerC]
    exact (Submodule.equivMapOfInjective W.subtype W.subtype_injective
      (LinearMap.ker g)).finrank_eq
  have hrn : Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) (LinearMap.ker g) +
        Module.finrank (ZMod 2) (LinearMap.range g) := by
    have h := LinearMap.finrank_range_add_finrank_ker g
    omega
  have hrange_le : LinearMap.range g ≤
      LinearMap.range ((t : F →ₗ[ZMod 2] F) - LinearMap.id) := by
    rintro v ⟨w, rfl⟩
    exact ⟨(w : F), by simp [g, LinearMap.sub_apply]⟩
  have hrange : Module.finrank (ZMod 2) (LinearMap.range g) ≤ modCommRank t :=
    Submodule.finrank_mono hrange_le
  have hC_le : Module.finrank (ZMod 2) C ≤ Module.finrank (ZMod 2) (LinearMap.range g) := by
    omega
  calc Module.finrank (ZMod 2) W
      = Module.finrank (ZMod 2) (LinearMap.ker g) +
          Module.finrank (ZMod 2) (LinearMap.range g) := hrn
    _ = Module.finrank (ZMod 2) C + Module.finrank (ZMod 2) (LinearMap.range g) := by
          rw [hfin_ker]
    _ ≤ Module.finrank (ZMod 2) (LinearMap.range g) +
          Module.finrank (ZMod 2) (LinearMap.range g) := add_le_add hC_le le_rfl
    _ = 2 * Module.finrank (ZMod 2) (LinearMap.range g) := by rw [two_mul]
    _ ≤ 2 * modCommRank t := Nat.mul_le_mul_left 2 hrange

end CFSG.LocalAnalysis.WeakClosure81

end
