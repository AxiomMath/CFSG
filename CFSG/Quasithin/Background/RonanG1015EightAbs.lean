module

public import CFSG.Quasithin.Background.G12Rad

public section

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Quasithin.G11

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem eq_of_add_eq_zero' {a b : U} (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [g12_vadd_self, add_zero]
    _ = (a + b) + b := by rw [add_assoc]
    _ = b := by rw [h, zero_add]

theorem f_map_of_mem_orthSub (hq : ∀ x y, q (x + y) = q x + q y + f x y) {g : GLV U}
    (hg : g ∈ orthSub q) (x y : U) : f (g x) (g y) = f x y := by
  have h1 := hq x y
  have h2 := hq (g x) (g y)
  rw [← map_add, hg (x + y), hg x, hg y, h1] at h2
  exact (add_left_cancel h2).symm

theorem eq_one_of_fix_perp [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) {v : U} (hv0 : v ≠ 0) (hqv : q v = 0)
    {g : GLV U} (hg : g ∈ orthSub q) (h : ∀ u, f v u = 0 → g u = u) : g = 1 := by
  refine LinearEquiv.ext fun x => ?_
  show g x = x
  have hperp : ∀ u, f v u = 0 → f u (g x + x) = 0 := by
    intro u hu
    have h1 := f_map_of_mem_orthSub hq hg u x
    rw [h u hu] at h1
    rw [map_add, h1]
    exact g12_add_self _
  have hmem : g x + x ∈ f.orthogonal (perp f v) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact hperp n (mem_perp_iff.1 hn)
  rw [hf.orthogonal_perp v] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  rcases g12_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul] at hc
    exact eq_of_add_eq_zero' hc.symm
  · rw [one_smul] at hc
    exfalso
    have hgx : g x = x + v := by
      calc g x = g x + (x + x) := by rw [g12_vadd_self, add_zero]
        _ = x + (g x + x) := by abel
        _ = x + v := by rw [hc]
    by_cases hxv : f v x = 0
    · have h1 := h x hxv
      apply hv0
      have : x + v = x := hgx.symm.trans h1
      simpa using this
    · have h1 : q (g x) = q x := hg x
      rw [hgx, hq, hqv, add_zero, hf.symm' x v] at h1
      apply hxv
      simpa using h1


theorem exists_dual_perp {v w : U} (hvp : v ∈ perp f v) (hwp : w ∈ perp f v)
    (hw : w ∉ Submodule.span (ZMod 2) {v}) :
    ∃ φ : perp f v →ₗ[ZMod 2] ZMod 2, φ ⟨v, hvp⟩ = 0 ∧ φ ⟨w, hwp⟩ = 1 := by
  have hx : (⟨w, hwp⟩ : perp f v) ∉ Submodule.span (ZMod 2) {(⟨v, hvp⟩ : perp f v)} := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    apply hw
    rw [Submodule.mem_span_singleton]
    exact ⟨c, congrArg Subtype.val hc⟩
  obtain ⟨φ, hφ1, hφ2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨φ, ?_, g12_eq_one_of_ne_zero _ hφ1⟩
  have : φ ⟨v, hvp⟩ ∈ (Submodule.span (ZMod 2) {(⟨v, hvp⟩ : perp f v)}).map φ :=
    Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
  rw [hφ2] at this
  exact (Submodule.mem_bot _).1 this

theorem exists_perp_not_span [Finite U] (hf : IsSymplectic f) {v : U} (hv0 : v ≠ 0)
    (hd : 3 ≤ Module.finrank (ZMod 2) U) :
    ∃ u, u ∈ perp f v ∧ u ∉ Submodule.span (ZMod 2) {v} := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  by_contra hcon
  push Not at hcon
  have hle : perp f v ≤ Submodule.span (ZMod 2) {v} := fun u hu => hcon u hu
  have h1 := Submodule.finrank_mono hle
  have h2 := hf.finrank_perp hv0
  rw [finrank_span_singleton hv0] at h1
  omega

structure QSetting (f : LinearMap.BilinForm (ZMod 2) U) (q : U → ZMod 2) (Q : Subgroup (GLV U))
    (v : U) : Prop where
  hf : IsSymplectic f
  hq : ∀ x y, q (x + y) = q x + q y + f x y
  hv0 : v ≠ 0
  hqv : q v = 0
  hd : 3 ≤ Module.finrank (ZMod 2) U
  hQO : Q ≤ orthSub q
  hvp : v ∈ perp f v
  hfull : FullTransvections Q (perp f v) v hvp

section Setting

variable [Finite U] {Q : Subgroup (GLV U)} {v : U} (S : QSetting f q Q v)
include S

theorem Q_fix_v {y : GLV U} (hy : y ∈ Q) : y v = v := by
  obtain ⟨φ, hφv, hφ⟩ := S.hfull.1 y hy
  have := hφ ⟨v, S.hvp⟩
  simp only at this
  rw [this, hφv, zero_smul, add_zero]

theorem fixed_of_mem_Q {w : U} (hw : ∀ y ∈ Q, y w = w) : w = 0 ∨ w = v := by
  by_cases hwp : w ∈ perp f v
  · by_contra hcon
    push Not at hcon
    have hws : w ∉ Submodule.span (ZMod 2) {v} := by
      intro h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
      rcases g12_eq_zero_or_one c with rfl | rfl
      · rw [zero_smul] at hc
        exact hcon.1 hc.symm
      · rw [one_smul] at hc
        exact hcon.2 hc.symm
    obtain ⟨φ, hφv, hφw⟩ := exists_dual_perp S.hvp hwp hws
    obtain ⟨y, hyQ, hy⟩ := S.hfull.2 φ hφv
    have h1 := hy ⟨w, hwp⟩
    simp only at h1
    rw [hφw, one_smul, hw y hyQ] at h1
    apply S.hv0
    have : w + v = w := h1.symm
    simpa using this
  · exfalso
    have hfv : f v w = 1 := g12_eq_one_of_ne_zero _ (fun h => hwp (mem_perp_iff.2 h))
    obtain ⟨u₀, hu₀p, hu₀s⟩ := exists_perp_not_span S.hf S.hv0 S.hd
    obtain ⟨φ, hφv, hφu⟩ := exists_dual_perp S.hvp hu₀p hu₀s
    obtain ⟨y, hyQ, hy⟩ := S.hfull.2 φ hφv
    have h1 := f_map_of_mem_orthSub S.hq (S.hQO hyQ) u₀ w
    have h2 := hy ⟨u₀, hu₀p⟩
    simp only at h2
    rw [hw y hyQ, h2, hφu, one_smul, map_add, LinearMap.add_apply, hfv] at h1
    have : f u₀ w + 1 = f u₀ w := h1
    have h3 : (1 : ZMod 2) = 0 := by simpa using this
    exact one_ne_zero h3

end Setting


section Setting2

variable [Finite U] {Q : Subgroup (GLV U)} {v : U} (S : QSetting f q Q v)
include S

theorem conj_mem_Q {g : GLV U} (hg : g ∈ orthSub q) (hgv : g v = v) {y : GLV U} (hy : y ∈ Q) :
    g * y * g⁻¹ ∈ Q := by
  obtain ⟨φ, hφv, hφ⟩ := S.hfull.1 y hy
  have hginv : ∀ u ∈ perp f v, (g⁻¹ : GLV U) u ∈ perp f v := by
    intro u hu
    rw [mem_perp_iff] at hu ⊢
    have h1 := f_map_of_mem_orthSub S.hq hg v ((g⁻¹ : GLV U) u)
    have h2 : g ((g⁻¹ : GLV U) u) = u := by simp
    rw [hgv, h2, hu] at h1
    exact h1.symm
  let gi : perp f v →ₗ[ZMod 2] perp f v := ((g⁻¹ : GLV U) : U →ₗ[ZMod 2] U).restrict hginv
  have hgiv : (g⁻¹ : GLV U) v = v := by
    show g.symm v = v
    rw [LinearEquiv.symm_apply_eq]
    exact hgv.symm
  have hψv : (φ ∘ₗ gi) ⟨v, S.hvp⟩ = 0 := by
    have : gi ⟨v, S.hvp⟩ = ⟨v, S.hvp⟩ := Subtype.ext hgiv
    rw [LinearMap.comp_apply, this, hφv]
  obtain ⟨y', hy'Q, hy'⟩ := S.hfull.2 (φ ∘ₗ gi) hψv
  have e1 : ∀ u (hu : u ∈ perp f v), (g * y * g⁻¹) u = y' u := by
    intro u hu
    have hz := hginv u hu
    have h1 := hφ ⟨(g⁻¹ : GLV U) u, hz⟩
    have h2 := hy' ⟨u, hu⟩
    simp only at h1 h2
    show g (y ((g⁻¹ : GLV U) u)) = y' u
    have h3 : g ((g⁻¹ : GLV U) u) = u := by simp
    rw [h1, h2, map_add, map_smul, hgv, h3]
    rfl
  have hkey : y'⁻¹ * (g * y * g⁻¹) = 1 := by
    refine eq_one_of_fix_perp S.hf S.hq S.hv0 S.hqv ?_ ?_
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (S.hQO hy'Q))
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (S.hQO hy)) (Subgroup.inv_mem _ hg))
    · intro u hu
      show y'.symm ((g * y * g⁻¹) u) = u
      rw [e1 u (mem_perp_iff.2 hu)]
      simp
  rw [← inv_mul_eq_one.1 hkey]
  exact hy'Q

theorem fix_of_normalizes {g : GLV U} (h1 : ∀ y ∈ Q, g * y * g⁻¹ ∈ Q)
    (h2 : ∀ y ∈ Q, g⁻¹ * y * g ∈ Q) : g v = v := by
  have hgv : ∀ y ∈ Q, y (g v) = g v := by
    intro y hy
    have h := Q_fix_v S (h2 y hy)
    have h' : g.symm (y (g v)) = v := h
    exact (LinearEquiv.symm_apply_eq g).1 h'
  rcases fixed_of_mem_Q S hgv with h0 | h
  · exact absurd ((g.map_eq_zero_iff).1 h0) S.hv0
  · exact h

theorem alpha_fix_v {K : Subgroup (GLV U)} (hKO : K ≤ orthSub q) (hQK : Q ≤ K) (β : ↥K ≃* ↥K)
    (hβ : ∀ (y : GLV U) (hy : y ∈ Q), β ⟨y, hQK hy⟩ = ⟨y, hQK hy⟩) (k : ↥K)
    (hk : (k : GLV U) v = v) : ((β k : ↥K) : GLV U) v = v := by
  have claim : ∀ k' : ↥K, (k' : GLV U) v = v → ∀ y ∈ Q,
      ((β k' : ↥K) : GLV U) * y * ((β k' : ↥K) : GLV U)⁻¹ =
        (k' : GLV U) * y * (k' : GLV U)⁻¹ := by
    intro k' hk' y hy
    have hc : (k' : GLV U) * y * (k' : GLV U)⁻¹ ∈ Q := conj_mem_Q S (hKO k'.2) hk' hy
    have h1 := hβ _ hc
    have h2 : (⟨(k' : GLV U) * y * (k' : GLV U)⁻¹, hQK hc⟩ : ↥K) = k' * ⟨y, hQK hy⟩ * k'⁻¹ :=
      rfl
    rw [h2, map_mul, map_mul, hβ y hy, map_inv] at h1
    exact congrArg Subtype.val h1
  apply fix_of_normalizes S
  · intro y hy
    rw [claim k hk y hy]
    exact conj_mem_Q S (hKO k.2) hk hy
  · intro y hy
    have hk' : ((k⁻¹ : ↥K) : GLV U) v = v := by
      show (k : GLV U).symm v = v
      rw [LinearEquiv.symm_apply_eq]
      exact hk.symm
    have h := claim k⁻¹ hk' y hy
    rw [map_inv] at h
    simp only [Subgroup.coe_inv, inv_inv] at h
    rw [h]
    exact conj_mem_Q S (hKO (k⁻¹).2) hk' hy

end Setting2

theorem fix_Q_of_commute {K Q : Subgroup (GLV U)} (hQK : Q ≤ K) (α : ↥K ≃* ↥K)
    (hZ : ∀ z : ↥K, (∀ m : ↥K, z * m = m * z) → z = 1)
    (hcomm : ∀ y ∈ Q, ∀ k k' : ↥K, (k' : GLV U) = y * (k : GLV U) * y⁻¹ →
      ((α k' : ↥K) : GLV U) = y * ((α k : ↥K) : GLV U) * y⁻¹) :
    ∀ (y : GLV U) (hy : y ∈ Q), α ⟨y, hQK hy⟩ = ⟨y, hQK hy⟩ := by
  intro y hy
  set y' : ↥K := ⟨y, hQK hy⟩ with hy'
  have hconj : ∀ m : ↥K, (α y') * m * (α y')⁻¹ = y' * m * y'⁻¹ := by
    intro m
    obtain ⟨k, rfl⟩ := α.surjective m
    apply Subtype.ext
    have h := hcomm y hy k (y' * k * y'⁻¹) rfl
    rw [map_mul, map_mul, map_inv] at h
    exact h
  have hz : y'⁻¹ * α y' = 1 := by
    refine hZ _ fun m => ?_
    have h := hconj m
    calc y'⁻¹ * α y' * m = y'⁻¹ * ((α y') * m * (α y')⁻¹) * (α y') := by group
      _ = y'⁻¹ * (y' * m * y'⁻¹) * α y' := by rw [h]
      _ = m * (y'⁻¹ * α y') := by group
  exact (inv_mul_eq_one.1 hz).symm


end RonanG1015

end CFSG.Quasithin
