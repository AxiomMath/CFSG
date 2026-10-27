module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
import CFSG.LocalAnalysis.StandardType.GGLargeDepRestrictAux
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPath
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymLin
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymRel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l04fD5C_move_conj {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] (X q : W ≃ₗ[ZMod p] W) :
    ggLinMove (X * q * X⁻¹) = (ggLinMove q).map (X : W →ₗ[ZMod p] W) := by
  have h : (X * q * X⁻¹).toLinearMap - LinearMap.id =
      X.toLinearMap.comp ((q.toLinearMap - LinearMap.id).comp X⁻¹.toLinearMap) := by
    ext v
    simp [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [ggLinMove, h, LinearMap.range_comp, LinearMap.range_comp]
  have hsurj : LinearMap.range (X⁻¹ : W ≃ₗ[ZMod p] W).toLinearMap = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact (X⁻¹).surjective
  rw [hsurj, Submodule.map_top]
  rfl

private lemma l04fD5C_refl_conj {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {X q : W ≃ₗ[ZMod p] W} (hq : GGLinRefl q) :
    GGLinRefl (X * q * X⁻¹) := by
  obtain ⟨h2, hdim⟩ := hq
  refine ⟨?_, ?_⟩
  · calc (X * q * X⁻¹) * (X * q * X⁻¹)
        = X * (q * (X⁻¹ * X) * q) * X⁻¹ := by group
      _ = X * (q * 1 * q) * X⁻¹ := by rw [inv_mul_cancel]
      _ = X * (q * q) * X⁻¹ := by rw [mul_one]
      _ = X * 1 * X⁻¹ := by rw [h2]
      _ = 1 := by group
  · rw [l04fD5C_move_conj, LinearEquiv.finrank_map_eq]
    exact hdim

private lemma l04fD5C_isConj_map_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) (a b : G) :
    IsConj (e a) (e b) ↔ IsConj a b := by
  rw [isConj_iff, isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨e.symm c, ?_⟩
    apply e.injective
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hc
  · rintro ⟨c, hc⟩
    exact ⟨e c, by simpa only [map_mul, map_inv] using congrArg e hc⟩

private lemma l04fD5C_commute_coe {p n : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {Q : Subgroup (W ≃ₗ[ZMod p] W)}
    {e : Q ≃* Equiv.Perm (Fin n)} {x y : Q} (h : Commute (e x) (e y)) :
    Commute ((x : Q) : W ≃ₗ[ZMod p] W) ((y : Q) : W ≃ₗ[ZMod p] W) := by
  have h1 : x * y = y * x := e.injective (by
    rw [map_mul, map_mul]
    exact h)
  show (x : W ≃ₗ[ZMod p] W) * (y : W ≃ₗ[ZMod p] W) =
    (y : W ≃ₗ[ZMod p] W) * (x : W ≃ₗ[ZMod p] W)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, h1]

private lemma l04fD5C_orderOf_e_coe {p n : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W]
    [Module (ZMod p) W] {Q : Subgroup (W ≃ₗ[ZMod p] W)}
    (e : Q ≃* Equiv.Perm (Fin n)) (x : Q) :
    orderOf (e x) = orderOf ((x : Q) : W ≃ₗ[ZMod p] W) := by
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]

theorem ggLargeDep_noSym_aug {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) (_hconn : GGLargeConnected r s)
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) (_hρ : GGLargeRestr r s hA)
    (hd : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N)
    (e : ↥(ggLargeRho r s hA).range ≃*
      Equiv.Perm (Fin (Module.finrank (ZMod p) ↥(ggFixLineT r s) + 1)))
    (he : ∀ q : ↥(ggLargeRho r s hA).range,
      GGLinRefl (q : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) →
        ∃ i j, i ≠ j ∧ e q = Equiv.swap i j) : False := by
  have hp2 : p ≠ 2 := C.lin.p_ne_two
  have hN : 11 ≤ N := C.lin.N_ge
  let Tfix : Submodule (ZMod p) V := ggFixLineT r s
  have hdimT : Module.finrank (ZMod p) ↥Tfix = N := hd
  have hmem : ∀ i : Fin (N - 1), h i ∈ Tfix := fun i => l04fD2_h_mem_T C i
  let u : Fin (N - 1) → ↥Tfix := fun i => ⟨h i, hmem i⟩
  let a : Fin (N - 1) → Module.Dual (ZMod p) ↥Tfix := fun i => (α i).comp Tfix.subtype
  have hpair' : ∀ i j, a i (u j) = (CartanMatrix.A (N - 1) i j : ZMod p) := by
    intro i j
    show α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)
    exact C.lin.pair i j
  have hrg : ∀ i : Fin (N - 1), r i ∈ ggLargeGrp r s :=
    fun i => Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_range_self i))
  let g : Fin (N - 1) → ↥(ggLargeGrp r s) := fun i => ⟨r i, hrg i⟩
  let q : Fin (N - 1) → ↥((ggLargeRho r s hA).range) :=
    fun i => ⟨(ggLargeRho r s hA) (g i), MonoidHom.mem_range.mpr ⟨g i, rfl⟩⟩
  have hq : ∀ i (w : ↥Tfix), ((q i : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix) w
      = w - a i w • u i := by
    intro i w
    apply Subtype.ext
    show (((ggLinRestrictHom Tfix ⟨r i, hA (hrg i)⟩) w : ↥Tfix) : V) =
      ((w : V) - (α i (w : V)) • h i)
    rw [l04fD2_restrict_apply, C.lin.refl_form i (w : V)]
  have hrefl : ∀ i, GGLinRefl ((q i : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix) := by
    intro i
    have h := l04fD2_restrict_refl (p := p) hp2 Tfix ⟨r i, hA (hrg i)⟩ (hmem i)
      (β := α i) (l04fD2_pair_diag C i) (C.lin.refl_form i)
    have hq_eq : ((q i : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
        = ggLinRestrictHom Tfix ⟨r i, hA (hrg i)⟩ := rfl
    rwa [hq_eq]
  have hrel := ggLargeDep_noSym_aug_rel (p := p) (m := N - 1) hp2 (by omega) (W := ↥Tfix) hpair'
    (q := fun i => ((q i : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)) hq
  obtain ⟨hrel1, hrel2⟩ := hrel
  let τ : Fin (N - 1) → Equiv.Perm (Fin (Module.finrank (ZMod p) ↥Tfix + 1)) := fun i => e (q i)
  have hswap : ∀ i, ∃ c d, c ≠ d ∧ τ i = Equiv.swap c d := by
    intro i
    exact he (q i) (hrefl i)
  have hadj : ∀ i j : Fin (N - 1), (i : ℕ) + 1 = (j : ℕ) → orderOf (τ i * τ j) = 3 := by
    intro i j hij
    have h1 : τ i * τ j = e (q i * q j) := by
      change e (q i) * e (q j) = e (q i * q j)
      rw [map_mul]
    rw [h1, l04fD5C_orderOf_e_coe, Subgroup.coe_mul]
    exact hrel1 i j hij
  have hfar : ∀ i j : Fin (N - 1), (i : ℕ) + 2 ≤ (j : ℕ) →
      Commute (τ i) (τ j) ∧ τ i ≠ τ j := by
    intro i j hij
    obtain ⟨hc, hne'⟩ := hrel2 i j hij
    constructor
    · change τ i * τ j = τ j * τ i
      have h1 : τ i * τ j = e (q i * q j) := by
        change e (q i) * e (q j) = e (q i * q j)
        rw [map_mul]
      have h2 : τ j * τ i = e (q j * q i) := by
        change e (q j) * e (q i) = e (q j * q i)
        rw [map_mul]
      rw [h1, h2]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hc
    · intro hEq
      apply hne'
      have hqij : q i = q j := e.injective (by simpa only [τ] using hEq)
      rw [hqij]
  have hn : Module.finrank (ZMod p) ↥Tfix + 1 = (N - 1) + 2 := by
    rw [hdimT]
    omega
  obtain ⟨t, ht_swap, htc, hto⟩ :=
    ggLargeDep_perm_path (m := N - 1) (n := Module.finrank (ZMod p) ↥Tfix + 1)
      (by omega) hn τ hswap hadj hfar
  let i0 : Fin (N - 1) := ⟨0, by omega⟩
  obtain ⟨c, d, hcd, hτ0⟩ := he (q i0) (hrefl i0)
  obtain ⟨a', b', hab', ht⟩ := ht_swap
  have hconj_perm : IsConj (e (q i0)) t := by
    rw [hτ0, ht]
    exact Equiv.Perm.isConj_swap hcd hab'
  let s0 : ↥((ggLargeRho r s hA).range) := e.symm t
  have hconj_Q : IsConj (q i0) s0 := by
    apply (l04fD5C_isConj_map_iff e (q i0) s0).mp
    rwa [MulEquiv.apply_symm_apply]
  obtain ⟨xx, hxx⟩ := isConj_iff.mp hconj_Q
  have hs_eq : ((s0 : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
      = ((xx : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
        * ((q i0 : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
        * (((xx : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix))⁻¹ := by
    rw [← hxx, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hs : GGLinRefl ((s0 : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix) := by
    rw [hs_eq]
    exact l04fD5C_refl_conj
      (X := ((xx : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix))
      (q := ((q i0 : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)) (hrefl i0)
  have hcomm : ∀ i : Fin (N - 1), (i : ℕ) + 2 ≤ N - 1 →
      ((s0 : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
        * ((q i : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
      = ((q i : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
        * ((s0 : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix) := by
    intro i hi
    apply l04fD5C_commute_coe (e := e) (x := s0) (y := q i)
    have h := (htc i hi).1
    rw [show t = e s0 from (MulEquiv.apply_symm_apply e t).symm,
        show τ i = e (q i) from rfl] at h
    exact h
  have hne : ∀ i : Fin (N - 1), (i : ℕ) + 2 ≤ N - 1 →
      ((s0 : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
        ≠ ((q i : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix) := by
    intro i hi
    have h := (htc i hi).2
    intro hEq
    apply h
    have hq_eq : s0 = q i := Subtype.ext hEq
    calc t = e s0 := (MulEquiv.apply_symm_apply e t).symm
      _ = e (q i) := by rw [hq_eq]
      _ = τ i := rfl
  have hord : ∀ j : Fin (N - 1), (j : ℕ) + 1 = N - 1 →
      orderOf (((s0 : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)
        * ((q j : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix)) = 3 := by
    intro j hj
    have h := hto j hj
    have h1 : t * τ j = e (s0 * q j) := by
      rw [show t = e s0 from (MulEquiv.apply_symm_apply e t).symm,
          show τ j = e (q j) from rfl, ← map_mul]
    rw [h1] at h
    rw [l04fD5C_orderOf_e_coe, Subgroup.coe_mul] at h
    exact h
  have hlin : LinearIndependent (ZMod p) u :=
    ggLargeDep_noSym_aug_lin (p := p) (m := N - 1) hp2 (W := ↥Tfix) hpair'
      (q := fun i => ((q i : ↥((ggLargeRho r s hA).range)) : ↥Tfix ≃ₗ[ZMod p] ↥Tfix))
      hq hs hcomm hne hord
  have hcomp : h = Tfix.subtype ∘ u := by
    funext i
    rfl
  have hh : LinearIndependent (ZMod p) h := by
    rw [hcomp]
    exact LinearIndependent.map' hlin Tfix.subtype (Submodule.ker_subtype Tfix)
  exact C.dep hh

end CFSG.StandardType

end
