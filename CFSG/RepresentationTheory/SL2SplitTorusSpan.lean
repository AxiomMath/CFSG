module

public import CFSG.RankThree.LocalRank.ElementaryTwoWeights
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.RepresentationTheory.SL2SplitTorus

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.LocalRank
open scoped MatrixGroups

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

noncomputable local instance moduleZModTwo : Module (ZMod 2) (Additive (Multiplicative F)) :=
  AddCommGroup.zmodModule fun x => CharTwo.two_nsmul (Multiplicative.toAdd (Additive.toMul x))

private noncomputable instance : Fintype (Module.Dual (ZMod 2) (Additive (Multiplicative F))) :=
  haveI : Finite (Module.Dual (ZMod 2) (Additive (Multiplicative F))) :=
    Finite.of_injective _ LinearMap.coe_injective
  Fintype.ofFinite _

private theorem units_eq_one_of_sq_eq_one {x : Fˣ} (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (x : F) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have h3 : ((x : F) + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h2, one_pow, CharTwo.add_self_eq_zero]
  have h4 : (x : F) + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h3
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h4
  exact Units.val_eq_one.mp h4

@[expose] noncomputable def upperHom : Multiplicative F →* SL(2, F) where
  toFun c := sl2Upper F (Multiplicative.toAdd c)
  map_one' := sl2Upper_zero
  map_mul' a b := sl2Upper_add (Multiplicative.toAdd a) (Multiplicative.toAdd b)

@[expose] noncomputable def mulLeftAdd (s : F) : Additive (Multiplicative F) →+ Additive (Multiplicative F) where
  toFun x := Additive.ofMul (Multiplicative.ofAdd (s * Multiplicative.toAdd (Additive.toMul x)))
  map_zero' := mul_zero s
  map_add' x y := mul_add s _ _

@[expose] noncomputable def shiftDual (s : F) (χ : Module.Dual (ZMod 2) (Additive (Multiplicative F))) :
    Module.Dual (ZMod 2) (Additive (Multiplicative F)) :=
  χ ∘ₗ AddMonoidHom.toZModLinearMap 2 (mulLeftAdd s)

theorem shiftDual_ne_self {χ : Module.Dual (ZMod 2) (Additive (Multiplicative F))} (hχ : χ ≠ 0)
    {s : F} (hs : s ≠ 1) : shiftDual s χ ≠ χ := by
  intro h
  apply hχ
  refine LinearMap.ext fun x => ?_
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  set y : Additive (Multiplicative F) :=
    Additive.ofMul (Multiplicative.ofAdd ((s - 1)⁻¹ * Multiplicative.toAdd (Additive.toMul x)))
  have hy : x = mulLeftAdd s y - y := by
    show x = Additive.ofMul (Multiplicative.ofAdd (s * ((s - 1)⁻¹ *
      Multiplicative.toAdd (Additive.toMul x)) - (s - 1)⁻¹ * Multiplicative.toAdd (Additive.toMul x)))
    have : s * ((s - 1)⁻¹ * Multiplicative.toAdd (Additive.toMul x)) -
        (s - 1)⁻¹ * Multiplicative.toAdd (Additive.toMul x) = Multiplicative.toAdd (Additive.toMul x) := by
      field_simp
    rw [this]
    rfl
  have hχy : χ (mulLeftAdd s y) = χ y := LinearMap.congr_fun h y
  rw [hy, map_sub, LinearMap.zero_apply]
  exact sub_eq_zero.mpr hχy

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

noncomputable abbrev upperRep (ρ : Representation k SL(2, F) V) :
    Representation k (Multiplicative F) V :=
  ρ.comp upperHom

private theorem sl2Diag_mul_aux (a b : Fˣ) : sl2Diag F (a * b) = sl2Diag F a * sl2Diag F b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem sl2Diag_one_aux : sl2Diag F (1 : Fˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem sum_range_shift_of_eq {M : Type*} [AddCommGroup M] (f : ℕ → M) (p : ℕ)
    (h : f p = f 0) : ∑ j ∈ Finset.range p, f (j + 1) = ∑ j ∈ Finset.range p, f j := by
  have h1 := Finset.sum_range_succ' f p
  have h2 := Finset.sum_range_succ f p
  rw [h, h1] at h2
  exact add_right_cancel h2

private theorem rho_sl2Diag_orbitSum (ρ : Representation k SL(2, F) V) (lam : Fˣ) (v : V) :
    ρ (sl2Diag F lam) (∑ j ∈ Finset.range (orderOf lam), ρ (sl2Diag F (lam ^ j)) v) =
      ∑ j ∈ Finset.range (orderOf lam), ρ (sl2Diag F (lam ^ j)) v := by
  rw [map_sum]
  have hshift : ∀ j, ρ (sl2Diag F lam) (ρ (sl2Diag F (lam ^ j)) v) =
      ρ (sl2Diag F (lam ^ (j + 1))) v := by
    intro j
    rw [← Module.End.mul_apply, ← map_mul, ← sl2Diag_mul_aux, pow_succ']
  simp only [hshift]
  exact sum_range_shift_of_eq (fun j => ρ (sl2Diag F (lam ^ j)) v) (orderOf lam)
    (by simp only [pow_orderOf_eq_one, pow_zero])

theorem rho_sl2Diag_mem_signWeightSpace (ρ : Representation k SL(2, F) V) (s : Fˣ)
    {χ : Module.Dual (ZMod 2) (Additive (Multiplicative F))} {v : V}
    (hv : v ∈ signWeightSpace (upperRep ρ) χ) :
    ρ (sl2Diag F s) v ∈ signWeightSpace (upperRep ρ) (shiftDual (((s : F) ^ 2)⁻¹) χ) := by
  rw [mem_signWeightSpace] at hv ⊢
  intro a
  have hs : ((s : F) ^ 2) ≠ 0 := pow_ne_zero 2 s.ne_zero
  set d : F := ((s : F) ^ 2)⁻¹ * Multiplicative.toAdd a
  have hcomm : sl2Upper F (Multiplicative.toAdd a) * sl2Diag F s = sl2Diag F s * sl2Upper F d := by
    rw [sl2Diag_mul_upper, show (s : F) ^ 2 * d = Multiplicative.toAdd a by
      simp only [d]; field_simp]
  have hd := hv (Multiplicative.ofAdd d)
  calc upperRep ρ a (ρ (sl2Diag F s) v)
      = ρ (sl2Upper F (Multiplicative.toAdd a) * sl2Diag F s) v := by
        rw [map_mul]
        rfl
    _ = ρ (sl2Diag F s) (upperRep ρ (Multiplicative.ofAdd d) v) := by
        rw [hcomm, map_mul]
        rfl
    _ = (-1 : k) ^ ZMod.val ((shiftDual (((s : F) ^ 2)⁻¹) χ) (Additive.ofMul a)) •
          ρ (sl2Diag F s) v := by
        rw [hd, map_smul]
        rfl

private theorem signProjection_mem_of_mem (ρ : Representation k SL(2, F) V) {W : Submodule k V}
    (hW : ∀ g v, v ∈ W → ρ g v ∈ W) (χ : Module.Dual (ZMod 2) (Additive (Multiplicative F)))
    {v : V} (hv : v ∈ W) : signProjection (upperRep ρ) χ v ∈ W := by
  rw [signProjection_apply]
  refine W.smul_mem _ (W.sum_mem fun a _ => W.smul_mem _ ?_)
  exact hW _ v hv

theorem rho_sub_mem_of_fixed_le (hk2 : (2 : k) ≠ 0) (ρ : Representation k SL(2, F) V) {lam : Fˣ}
    (W : Submodule k V) (hW : ∀ g v, v ∈ W → ρ g v ∈ W) (hfix : ∀ v, ρ (sl2Diag F lam) v = v → v ∈ W)
    (g : SL(2, F)) (v : V) : ρ g v - v ∈ W := by
  classical
  have hweight : ∀ χ : Module.Dual (ZMod 2) (Additive (Multiplicative F)), χ ≠ 0 →
      ∀ v ∈ signWeightSpace (upperRep ρ) χ, v ∈ W := by
    intro χ hχ v hv
    set w : V := ∑ j ∈ Finset.range (orderOf lam), ρ (sl2Diag F (lam ^ j)) v with hw
    have hwW : w ∈ W := hfix w (rho_sl2Diag_orbitSum ρ lam v)
    have hPw : signProjection (upperRep ρ) χ w = v := by
      rw [hw, map_sum, Finset.sum_eq_single 0]
      · rw [pow_zero, sl2Diag_one_aux, map_one, Module.End.one_apply]
        exact signProjection_of_mem_self (upperRep ρ) hk2 hv
      · intro j hj hj0
        refine signProjection_of_mem_ne (upperRep ρ) hk2 ?_
          (rho_sl2Diag_mem_signWeightSpace ρ (lam ^ j) hv)
        refine shiftDual_ne_self hχ fun h1 => ?_
        have h2 : ((lam ^ j : Fˣ) : F) ^ 2 = 1 := by
          have := congrArg (·⁻¹) h1
          simpa using this
        refine pow_ne_one_of_lt_orderOf hj0 (Finset.mem_range.mp hj) (units_eq_one_of_sq_eq_one ?_)
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact h2
      · intro h
        exact absurd (Finset.mem_range.mpr (orderOf_pos lam)) h
    rw [← hPw]
    exact signProjection_mem_of_mem ρ hW χ hwW
  have hupper : ∀ c : F, ∀ v : V, ρ (sl2Upper F c) v - v ∈ W := by
    intro c v
    set r : k := (Fintype.card (Multiplicative F) : k)⁻¹ *
      Fintype.card (Module.Dual (ZMod 2) (Additive (Multiplicative F)))
    have hr : r ≠ 0 := mul_ne_zero (inv_ne_zero (natCast_card_ne_zero_of_two_module hk2))
      (natCast_card_dual_ne_zero hk2)
    have hsum := sum_signProjection (upperRep ρ) hk2 v
    have hterm : ∀ χ : Module.Dual (ZMod 2) (Additive (Multiplicative F)),
        upperRep ρ (Multiplicative.ofAdd c) (signProjection (upperRep ρ) χ v) -
          signProjection (upperRep ρ) χ v ∈ W := by
      intro χ
      by_cases hχ : χ = 0
      · have h0 := (mem_signWeightSpace (upperRep ρ) χ _).mp
          (signProjection_mem (upperRep ρ) χ v) (Multiplicative.ofAdd c)
        rw [h0, hχ, LinearMap.zero_apply, ZMod.val_zero, pow_zero, one_smul, sub_self]
        exact W.zero_mem
      · have hm := hweight χ hχ _ (signProjection_mem (upperRep ρ) χ v)
        exact W.sub_mem (hW _ _ hm) hm
    have hmem : upperRep ρ (Multiplicative.ofAdd c) (r • v) - r • v ∈ W := by
      rw [← hsum, map_sum, ← Finset.sum_sub_distrib]
      exact W.sum_mem fun χ _ => hterm χ
    rw [map_smul, ← smul_sub] at hmem
    have := W.smul_mem r⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hr, one_smul] at this
  have hlower : ∀ c : F, ∀ v : V, ρ (sl2Lower F c) v - v ∈ W := by
    intro c v
    have hω : sl2Lower F c = sl2Weyl F 1 * sl2Upper F (-c) * (sl2Weyl F 1)⁻¹ := by
      rw [sl2Weyl_mul_upper, mul_assoc, mul_inv_cancel, mul_one]
      congr 1
      simp
    have h := hW (sl2Weyl F 1) _ (hupper (-c) (ρ (sl2Weyl F 1)⁻¹ v))
    have hωv : ρ (sl2Weyl F 1) (ρ (sl2Weyl F 1)⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e1 : ρ (sl2Lower F c) v - v = ρ (sl2Weyl F 1)
        (ρ (sl2Upper F (-c)) (ρ (sl2Weyl F 1)⁻¹ v) - ρ (sl2Weyl F 1)⁻¹ v) := by
      rw [map_sub, hωv, hω, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    rw [e1]
    exact h
  let S : Subgroup SL(2, F) :=
    { carrier := {g | ∀ v : V, ρ g v - v ∈ W}
      one_mem' := fun v => by rw [map_one, Module.End.one_apply, sub_self]; exact W.zero_mem
      mul_mem' := fun {a b} ha hb v => by
        have h := W.add_mem (hW a _ (hb v)) (ha v)
        rw [map_sub] at h
        rw [map_mul, Module.End.mul_apply]
        convert h using 1
        abel
      inv_mem' := fun {a} ha v => by
        have h := ha (ρ a⁻¹ v)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
        have h' := W.neg_mem h
        rw [neg_sub] at h'
        exact h' }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← sl2_closure_upper_lower (K := F), Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hupper c
    · exact hlower c
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  exact hg v

theorem span_translates_fixed_eq_top (hk2 : (2 : k) ≠ 0) (ρ : Representation k SL(2, F) V) {lam : Fˣ}
    (hkn : (orderOf lam : k) ≠ 0) :
    Submodule.span k (⋃ g : SL(2, F), ρ g '' {v | ρ (sl2Diag F lam) v = v}) = ⊤ := by
  classical
  set W := Submodule.span k (⋃ g : SL(2, F), ρ g '' {v | ρ (sl2Diag F lam) v = v}) with hWdef
  have hgen : ∀ g : SL(2, F), ∀ u, ρ (sl2Diag F lam) u = u → ρ g u ∈ W := fun g u hu =>
    Submodule.subset_span (Set.mem_iUnion.mpr ⟨g, u, hu, rfl⟩)
  have hW : ∀ g v, v ∈ W → ρ g v ∈ W := by
    intro g v hv
    refine Submodule.span_induction (p := fun v _ => ρ g v ∈ W) ?_ ?_ ?_ ?_ hv
    · intro x hx
      obtain ⟨h, u, hu, rfl⟩ := Set.mem_iUnion.mp hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact hgen (g * h) u hu
    · rw [map_zero]
      exact W.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact W.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact W.smul_mem a hx
  have hfix : ∀ v, ρ (sl2Diag F lam) v = v → v ∈ W := fun v hv => by
    have := hgen 1 v hv
    rwa [map_one, Module.End.one_apply] at this
  have htriv := rho_sub_mem_of_fixed_le hk2 ρ W hW hfix
  rw [eq_top_iff]
  intro v _
  set e : V := ∑ j ∈ Finset.range (orderOf lam), ρ (sl2Diag F (lam ^ j)) v with he
  have heW : e ∈ W := hfix e (rho_sl2Diag_orbitSum ρ lam v)
  have hdiff : (orderOf lam : k) • v - e ∈ W := by
    have : (orderOf lam : k) • v - e =
        ∑ j ∈ Finset.range (orderOf lam), (v - ρ (sl2Diag F (lam ^ j)) v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, he, Nat.cast_smul_eq_nsmul]
    rw [this]
    refine W.sum_mem fun j _ => ?_
    have := W.neg_mem (htriv (sl2Diag F (lam ^ j)) v)
    rwa [neg_sub] at this
  have hpv : (orderOf lam : k) • v ∈ W := by
    have := W.add_mem hdiff heW
    rwa [sub_add_cancel] at this
  have := W.smul_mem (orderOf lam : k)⁻¹ hpv
  rwa [smul_smul, inv_mul_cancel₀ hkn, one_smul] at this

end CFSG.RepresentationTheory.SL2SplitTorus

end
