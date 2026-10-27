module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm
import Mathlib.Tactic

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType.OrthF3

private lemma hdRo7CCoefAux_zmod3_eq_pm_one (a : ZMod 3) (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  have h : a = 0 ∨ a = 1 ∨ a = -1 := by revert a; decide
  tauto

private lemma hdRo7CCoefAux_zmod3_sq (a : ZMod 3) (ha : a ≠ 0) : a * a = 1 := by
  rcases hdRo7CCoefAux_zmod3_eq_pm_one a ha with h | h <;> rw [h] <;> decide

private lemma hdRo7CCoefAux_sp_fix_axis
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {g : V ≃ₗ[ZMod 3] V}
    (hg : C2SP 3 b g) : g (b 0) = b 0 := by
  obtain ⟨σ, c, hσ0, hc0, _, hg⟩ := hg
  rw [hg 0, hσ0, hc0, one_smul]

private theorem hdRo7CCoefAux_conj_refl
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {r : V ≃ₗ[ZMod 3] V}
    (hr : GGLinRefl r) (g : V ≃ₗ[ZMod 3] V) : GGLinRefl (g * r * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [show g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ by group, hr.1, mul_one,
      mul_inv_cancel]
  · have hmap : ggLinMove (g * r * g⁻¹) = (ggLinMove r).map g.toLinearMap := by
      rw [ggLinMove, ggLinMove]
      have hcomp : (g * r * g⁻¹).toLinearMap - LinearMap.id =
          g.toLinearMap.comp ((r.toLinearMap - LinearMap.id).comp g⁻¹.toLinearMap) := by
        ext v
        simp [LinearEquiv.mul_apply, map_sub]
      rw [hcomp, LinearMap.range_comp, LinearMap.range_comp,
        LinearMap.range_eq_top.mpr g⁻¹.surjective, Submodule.map_top]
    rw [hmap]
    have e := Submodule.equivMapOfInjective g.toLinearMap g.injective (ggLinMove r)
    rw [← LinearEquiv.finrank_eq e, hr.2]

private theorem hdRo7CCoefAux_reflNF_invol
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hNF : C2ReflNF 3 b A r u φ) : r * r = 1 := by
  have hru : r u = -u := by
    rw [hNF.hform, hNF.hφu, two_smul]
    abel
  ext v
  rw [LinearEquiv.mul_apply]
  change r (r v) = v
  conv_lhs => rw [hNF.hform v]
  rw [map_sub, map_smul, hNF.hform v, hru]
  module

private theorem hdRo7CCoefAux_KL
    (hS : C2SuppTwoLeaf) (n : ℕ) (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPle : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hNF : C2ReflNF 3 b A r u φ)
    (g : V ≃ₗ[ZMod 3] V) (hgP : C2SP 3 b g) (hgRefl : GGLinRefl g) (hgu : g u = u)
    (w : V) (hw : w ≠ 0) (hgw : g w = -w) : φ w = 0 := by
  have hrA : r ∈ A := hNF.hr
  have hrr : r * r = 1 := hdRo7CCoefAux_reflNF_invol b A r u φ hNF
  have hr0 : r (b 0) = b 0 - u := by rw [hNF.hform, hNF.hφ0, one_smul]
  have hru : r u = -u := by
    rw [hNF.hform, hNF.hφu, two_smul]
    abel
  have hg0 : g (b 0) = b 0 := hdRo7CCoefAux_sp_fix_axis b hgP
  let ρ : V ≃ₗ[ZMod 3] V := r * g * r
  have hρA : ρ ∈ A := by
    show r * g * r ∈ A
    exact A.mul_mem (A.mul_mem hrA (hPle g hgP)) hrA
  have hρ0 : ρ (b 0) = b 0 := by
    show (r * g * r) (b 0) = b 0
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr0, map_sub, hg0, hgu, map_sub, hr0, hru]
    module
  have hρrefl : GGLinRefl ρ := by
    have hr_inv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
    have hconj : r * g * r = r * g * r⁻¹ := by rw [hr_inv]
    show GGLinRefl (r * g * r)
    rw [hconj]
    exact hdRo7CCoefAux_conj_refl hgRefl r
  have hρP : C2SP 3 b ρ := hStab ρ hρA hρ0
  have hρrw : ρ (r w) = -(r w) := by
    have hrrw : r (r w) = w := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e w) hrr
      simpa [LinearEquiv.mul_apply] using h
    show (r * g * r) (r w) = -(r w)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hrrw, hgw, map_neg]
  have hrw : r w ≠ 0 := fun h => hw (r.injective (by rw [h, map_zero]))
  have hcoord_rw : b.coord 0 (r w) = 0 :=
    (hS 3 rfl n hn V b ρ hρP hρrefl (r w) hrw hρrw).1
  have hcoord_w : b.coord 0 w = 0 :=
    (hS 3 rfl n hn V b g hgP hgRefl w hw hgw).1
  have hcoord_exp : b.coord 0 (r w) = b.coord 0 w - φ w * b.coord 0 u := by
    rw [hNF.hform, map_sub, map_smul, smul_eq_mul]
  have hprod : φ w * b.coord 0 u = 0 := by
    have h := hcoord_rw
    rw [hcoord_exp, hcoord_w, zero_sub] at h
    exact neg_eq_zero.mp h
  exact (mul_eq_zero.mp hprod).resolve_right hNF.hu0

private lemma hdRo7CCoefAux_signChange_mem
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {i : Fin (n + 1)} (hi : i ≠ 0) :
    C2SP 3 b (ggOrthSignChange b i) := by
  refine ⟨1, fun j => if j = i then -1 else 1, by simp, ?_, ?_, ?_⟩
  · show (if (0 : Fin (n + 1)) = i then -1 else 1) = 1
    rw [if_neg (Ne.symm hi)]
  · intro j
    dsimp only
    by_cases hj : j = i
    · rw [if_pos hj]; right; rfl
    · rw [if_neg hj]; left; rfl
  · intro j
    rw [Equiv.Perm.one_apply]
    show ggOrthSignChange b i (b j) = (if j = i then -1 else 1) • b j
    by_cases hj : j = i
    · rw [hj, if_pos rfl, ggOrthSignChange_apply_self, neg_one_smul]
    · rw [if_neg hj, ggOrthSignChange_apply_of_ne b hj, one_smul]

private lemma hdRo7CCoefAux_signChange_fix
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) V) (i : Fin m) (u : V) (hu : b.coord i u = 0) :
    ggOrthSignChange b i u = u := by
  have hexp : u = ∑ k, b.coord k u • b k := by
    conv_lhs => rw [← b.sum_repr u]
    apply Finset.sum_congr rfl
    intro k _
    rw [Module.Basis.coord_apply]
  conv_lhs => rw [hexp]
  rw [map_sum]
  conv_rhs => rw [hexp]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  by_cases hki : k = i
  · rw [hki, ggOrthSignChange_apply_self, hu]
    simp
  · rw [ggOrthSignChange_apply_of_ne b hki]

private noncomputable def hdRo7CCoefAux_swap
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) V) (i j : Fin m) (ε : ZMod 3) (hij : i ≠ j)
    (hε : ε * ε = 1) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofInvolutive
    (b.constr (ZMod 3) fun k => if k = i then ε • b j else if k = j then ε • b i else b k)
    (by
      let T : V →ₗ[ZMod 3] V :=
        b.constr (ZMod 3) fun k => if k = i then ε • b j else if k = j then ε • b i else b k
      change Function.Involutive T
      have hT : ∀ k, T (b k) = if k = i then ε • b j else if k = j then ε • b i else b k :=
        fun k => Module.Basis.constr_basis b (ZMod 3) _ k
      have hcomp : T.comp T = LinearMap.id := by
        apply b.ext
        intro k
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [hT k]
        by_cases hki : k = i
        · rw [if_pos hki, map_smul, hT j, if_neg (Ne.symm hij), if_pos rfl, ← mul_smul, hε,
            one_smul, hki]
        · by_cases hkj : k = j
          · rw [if_neg hki, if_pos hkj, map_smul, hT i, if_pos rfl, ← mul_smul, hε, one_smul,
              hkj]
          · rw [if_neg hki, if_neg hkj, hT k, if_neg hki, if_neg hkj]
      intro x
      have hx := congrArg (fun L : V →ₗ[ZMod 3] V => L x) hcomp
      simpa [LinearMap.comp_apply] using hx)

private lemma hdRo7CCoefAux_swap_apply_i
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) V) (i j : Fin m) (ε : ZMod 3) (hij : i ≠ j)
    (hε : ε * ε = 1) : hdRo7CCoefAux_swap b i j ε hij hε (b i) = ε • b j := by
  simp only [hdRo7CCoefAux_swap, LinearEquiv.coe_ofInvolutive]
  rw [Module.Basis.constr_basis, if_pos rfl]

private lemma hdRo7CCoefAux_swap_apply_j
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) V) (i j : Fin m) (ε : ZMod 3) (hij : i ≠ j)
    (hε : ε * ε = 1) : hdRo7CCoefAux_swap b i j ε hij hε (b j) = ε • b i := by
  simp only [hdRo7CCoefAux_swap, LinearEquiv.coe_ofInvolutive]
  rw [Module.Basis.constr_basis, if_neg (Ne.symm hij), if_pos rfl]

private lemma hdRo7CCoefAux_swap_apply_of_ne
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) V) (i j : Fin m) (ε : ZMod 3) (hij : i ≠ j)
    (hε : ε * ε = 1) {k : Fin m} (hki : k ≠ i) (hkj : k ≠ j) :
    hdRo7CCoefAux_swap b i j ε hij hε (b k) = b k := by
  simp only [hdRo7CCoefAux_swap, LinearEquiv.coe_ofInvolutive]
  rw [Module.Basis.constr_basis, if_neg hki, if_neg hkj]

private theorem hdRo7CCoefAux_swap_refl
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) V) (i j : Fin m) (ε : ZMod 3) (hij : i ≠ j)
    (hε : ε * ε = 1) : GGLinRefl (hdRo7CCoefAux_swap b i j ε hij hε) := by
  set g := hdRo7CCoefAux_swap b i j ε hij hε with hg
  let v : V := ε • b j - b i
  refine ⟨?_, ?_⟩
  · apply b.ext'
    intro k
    rw [LinearEquiv.mul_apply]
    change g (g (b k)) = b k
    by_cases hki : k = i
    · rw [hki, hdRo7CCoefAux_swap_apply_i, map_smul, hdRo7CCoefAux_swap_apply_j, ← mul_smul,
        hε, one_smul]
    · by_cases hkj : k = j
      · rw [hkj, hdRo7CCoefAux_swap_apply_j, map_smul, hdRo7CCoefAux_swap_apply_i, ← mul_smul,
          hε, one_smul]
      · rw [hdRo7CCoefAux_swap_apply_of_ne b i j ε hij hε hki hkj,
          hdRo7CCoefAux_swap_apply_of_ne b i j ε hij hε hki hkj]
  · have hcoord_i_v : b.coord i v = -1 := by
      simp only [v, map_sub, map_smul, smul_eq_mul, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij,
        mul_zero, zero_sub]
    have hv : v ≠ 0 := by
      intro h
      have hc := congrArg (fun x => b.coord i x) h
      rw [hcoord_i_v, map_zero] at hc
      exact absurd hc (by decide)
    have hsub_i : (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (b i) = v := by
      change g (b i) - b i = v
      rw [hg, hdRo7CCoefAux_swap_apply_i]
    have hsub_j : (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (b j) = (-ε) • v := by
      change g (b j) - b j = (-ε) • v
      rw [hg, hdRo7CCoefAux_swap_apply_j]
      show ε • b i - b j = (-ε) • (ε • b j - b i)
      rw [smul_sub, smul_smul, show (-ε) * ε = -1 by rw [neg_mul, hε], neg_one_smul, neg_smul]
      abel
    have hsub_other : ∀ k, k ≠ i → k ≠ j →
        (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (b k) = 0 := by
      intro k hki hkj
      change g (b k) - b k = 0
      rw [hg, hdRo7CCoefAux_swap_apply_of_ne b i j ε hij hε hki hkj, sub_self]
    have hconstr : g.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V) =
        b.constr (ZMod 3)
          (fun k => (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (b k)) :=
      (Module.Basis.constr_self b (ZMod 3)
        (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V))).symm
    have hspan : ggLinMove g = Submodule.span (ZMod 3) {v} := by
      rw [ggLinMove, hconstr, Module.Basis.constr_range]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro x ⟨k, rfl⟩
        change (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (b k) ∈
          Submodule.span (ZMod 3) {v}
        by_cases hki : k = i
        · rw [hki, hsub_i]
          exact Submodule.subset_span (Set.mem_singleton v)
        · by_cases hkj : k = j
          · rw [hkj, hsub_j]
            exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
          · rw [hsub_other k hki hkj]
            exact Submodule.zero_mem _
      · rw [Submodule.span_le]
        rintro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Submodule.subset_span ⟨i, hsub_i⟩
    rw [hspan]
    exact finrank_span_singleton hv

private theorem hdRo7CCoefAux_swap_mem
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {i j : Fin (n + 1)} (ε : ZMod 3) (hij : i ≠ j)
    (hε : ε * ε = 1) (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hεpm : ε = 1 ∨ ε = -1) :
    C2SP 3 b (hdRo7CCoefAux_swap b i j ε hij hε) := by
  refine ⟨Equiv.swap i j, fun k => if k = i ∨ k = j then ε else 1, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi0) (Ne.symm hj0)]
  · dsimp only
    rw [if_neg (by
      rintro (h | h)
      · exact hi0 h.symm
      · exact hj0 h.symm)]
  · intro k
    dsimp only
    by_cases hk : k = i ∨ k = j
    · rw [if_pos hk]; exact hεpm
    · rw [if_neg hk]; left; rfl
  · intro k
    dsimp only
    by_cases hki : k = i
    · rw [hki, Equiv.swap_apply_left, if_pos (Or.inl rfl), hdRo7CCoefAux_swap_apply_i]
    · by_cases hkj : k = j
      · rw [hkj, Equiv.swap_apply_right, if_pos (Or.inr rfl), hdRo7CCoefAux_swap_apply_j]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
          if_neg (by
            rintro (h | h)
            · exact hki h
            · exact hkj h),
          hdRo7CCoefAux_swap_apply_of_ne b i j ε hij hε hki hkj, one_smul]

private lemma hdRo7CCoefAux_swap_fix
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) V) (i j : Fin m) (ε : ZMod 3) (hij : i ≠ j)
    (hε : ε * ε = 1) (u : V)
    (hi : b.coord i u * ε = b.coord j u) (hj : b.coord j u * ε = b.coord i u) :
    hdRo7CCoefAux_swap b i j ε hij hε u = u := by
  have hexp : u = ∑ k, b.coord k u • b k := by
    conv_lhs => rw [← b.sum_repr u]
    apply Finset.sum_congr rfl
    intro k _
    rw [Module.Basis.coord_apply]
  conv_lhs => rw [hexp]
  rw [map_sum]
  simp_rw [map_smul]
  conv_rhs => rw [hexp]
  apply Finset.sum_equiv (Equiv.swap i j) (fun l => by simp)
  intro k _
  by_cases hki : k = i
  · rw [hki, Equiv.swap_apply_left]
    show b.coord i u • hdRo7CCoefAux_swap b i j ε hij hε (b i) = b.coord j u • b j
    rw [hdRo7CCoefAux_swap_apply_i, smul_smul, hi]
  · by_cases hkj : k = j
    · rw [hkj, Equiv.swap_apply_right]
      show b.coord j u • hdRo7CCoefAux_swap b i j ε hij hε (b j) = b.coord i u • b i
      rw [hdRo7CCoefAux_swap_apply_j, smul_smul, hj]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
        hdRo7CCoefAux_swap_apply_of_ne b i j ε hij hε hki hkj]

private lemma hdRo7CCoefAux_zero_coord
    (hS : C2SuppTwoLeaf) (n : ℕ) (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPle : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hNF : C2ReflNF 3 b A r u φ) (i : Fin (n + 1)) (hi : i ≠ 0)
    (hai : b.coord i u = 0) : φ (b i) = 0 :=
  hdRo7CCoefAux_KL hS n hn b A hPle hStab r u φ hNF (ggOrthSignChange b i)
    (hdRo7CCoefAux_signChange_mem b hi) (ggOrthSignChange_isRefl b i)
    (hdRo7CCoefAux_signChange_fix b i u hai) (b i) (b.ne_zero i)
    (ggOrthSignChange_apply_self b i)

private lemma hdRo7CCoefAux_nonzero_coord
    (hS : C2SuppTwoLeaf) (n : ℕ) (hn : 5 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hPle : ∀ a, C2SP 3 b a → a ∈ A)
    (hStab : ∀ a ∈ A, a (b 0) = b 0 → C2SP 3 b a)
    (r : V ≃ₗ[ZMod 3] V) (u : V) (φ : V →ₗ[ZMod 3] ZMod 3)
    (hNF : C2ReflNF 3 b A r u φ) (i j : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0)
    (hij : i ≠ j) (hai : b.coord i u ≠ 0) (haj : b.coord j u ≠ 0) :
    b.coord i u * φ (b i) = b.coord j u * φ (b j) := by
  set ai := b.coord i u with hai_def
  set aj := b.coord j u with haj_def
  have hai_sq : ai * ai = 1 := hdRo7CCoefAux_zmod3_sq ai hai
  have haj_sq : aj * aj = 1 := hdRo7CCoefAux_zmod3_sq aj haj
  have hε : (aj * ai) * (aj * ai) = 1 := by
    rw [show (aj * ai) * (aj * ai) = (aj * aj) * (ai * ai) by ring, haj_sq, hai_sq, mul_one]
  have hεpm : aj * ai = 1 ∨ aj * ai = -1 := by
    rcases hdRo7CCoefAux_zmod3_eq_pm_one ai hai with h | h <;>
      rcases hdRo7CCoefAux_zmod3_eq_pm_one aj haj with h' | h' <;>
        rw [h, h'] <;> decide
  have hi_cond : ai * (aj * ai) = aj := by
    rw [show ai * (aj * ai) = aj * (ai * ai) by ring, hai_sq, mul_one]
  have hj_cond : aj * (aj * ai) = ai := by
    rw [show aj * (aj * ai) = ai * (aj * aj) by ring, haj_sq, mul_one]
  have hgP : C2SP 3 b (hdRo7CCoefAux_swap b i j (aj * ai) hij hε) :=
    hdRo7CCoefAux_swap_mem b (aj * ai) hij hε hi hj hεpm
  have hgRefl : GGLinRefl (hdRo7CCoefAux_swap b i j (aj * ai) hij hε) :=
    hdRo7CCoefAux_swap_refl b i j (aj * ai) hij hε
  have hgu : hdRo7CCoefAux_swap b i j (aj * ai) hij hε u = u := by
    apply hdRo7CCoefAux_swap_fix b i j (aj * ai) hij hε
    · rw [hai_def, haj_def]; exact hi_cond
    · rw [hai_def, haj_def]; exact hj_cond
  have hw : aj • b i - ai • b j ≠ 0 := by
    intro h
    have hc := congrArg (fun x => b.coord i x) h
    have hci : b.coord i (aj • b i - ai • b j) = aj := by
      simp only [map_sub, map_smul, smul_eq_mul, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij,
        mul_zero, mul_one, sub_zero]
    rw [hci, map_zero] at hc
    exact haj hc
  have hgw : hdRo7CCoefAux_swap b i j (aj * ai) hij hε (aj • b i - ai • b j) =
      -(aj • b i - ai • b j) := by
    rw [map_sub, map_smul, map_smul, hdRo7CCoefAux_swap_apply_i,
      hdRo7CCoefAux_swap_apply_j]
    rw [show aj • ((aj * ai) • b j) = (aj * (aj * ai)) • b j by rw [smul_smul],
      show ai • ((aj * ai) • b i) = (ai * (aj * ai)) • b i by rw [smul_smul],
      hj_cond, hi_cond]
    module
  have hKL := hdRo7CCoefAux_KL hS n hn b A hPle hStab r u φ hNF
    (hdRo7CCoefAux_swap b i j (aj * ai) hij hε) hgP hgRefl hgu
    (aj • b i - ai • b j) hw hgw
  rw [map_sub, map_smul, map_smul] at hKL
  have hrel : aj * φ (b i) = ai * φ (b j) := sub_eq_zero.mp hKL
  have hmul := congrArg (fun x => x * (ai * aj)) hrel
  have hgoal : ai * φ (b i) = aj * φ (b j) := by
    rw [show aj * φ (b i) * (ai * aj) = (aj * aj) * (ai * φ (b i)) by ring,
      show ai * φ (b j) * (ai * aj) = (ai * ai) * (aj * φ (b j)) by ring,
      haj_sq, hai_sq, one_mul, one_mul] at hmul
    exact hmul
  exact hgoal

theorem c2_reflCoef_holds : C2ReflCoefLeaf := by
  intro hS p hpFact hp n hn V _ _ b A hPle hStab r u φ hNF
  subst hp
  by_cases hex : ∃ i, i ≠ 0 ∧ b.coord i u ≠ 0
  · obtain ⟨i₀, hi₀, hai₀⟩ := hex
    refine ⟨φ (b i₀) * b.coord i₀ u, ?_⟩
    intro i hi
    by_cases hai : b.coord i u = 0
    · rw [hai, mul_zero]
      exact hdRo7CCoefAux_zero_coord hS n hn b A hPle hStab r u φ hNF i hi hai
    · by_cases hii : i = i₀
      · subst hii
        rw [mul_assoc, hdRo7CCoefAux_zmod3_sq (b.coord i u) hai, mul_one]
      · have hcomm := hdRo7CCoefAux_nonzero_coord hS n hn b A hPle hStab r u φ hNF i i₀
          hi hi₀ hii hai hai₀
        have hsq := hdRo7CCoefAux_zmod3_sq (b.coord i u) hai
        have hmul := congrArg (fun x => x * b.coord i u) hcomm
        have hbi : φ (b i) = b.coord i₀ u * φ (b i₀) * b.coord i u := by
          rw [show b.coord i u * φ (b i) * b.coord i u =
                φ (b i) * (b.coord i u * b.coord i u) by ring, hsq, mul_one] at hmul
          exact hmul
        rw [hbi]
        ring
  · push Not at hex
    refine ⟨0, ?_⟩
    intro i hi
    rw [zero_mul]
    exact hdRo7CCoefAux_zero_coord hS n hn b A hPle hStab r u φ hNF i hi (hex i hi)

end CFSG.StandardType.HdRo7C
