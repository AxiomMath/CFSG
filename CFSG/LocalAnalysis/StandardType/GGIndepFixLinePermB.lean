module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLinePermA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6kp_rinv {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (i : Fin (N - 1)) : (r i).symm = r i := by
  have hii : α i (h i) = (2 : ZMod p) := by
    rw [S.pair i i, l6kp_cartanA (p := p) (N := N) i i, if_pos rfl]
  have harg : r i (h i) = - h i := by
    rw [S.r_form i (h i), hii]
    rw [show (2 : ZMod p) • h i = h i + h i by rw [two_smul]]
    abel
  have h3 : ∀ v : V, r i (r i v) = v := by
    intro v
    calc r i (r i v) = r i (v - (α i v) • h i) := by rw [S.r_form i v]
      _ = r i v - (α i v) • r i (h i) := by rw [map_sub, map_smul]
      _ = (v - (α i v) • h i) - (α i v) • (- h i) := by rw [S.r_form i v, harg]
      _ = v := by rw [smul_neg]; abel
  ext v
  exact (r i).symm_apply_eq.mpr (h3 v).symm

private lemma l6kp_r_h {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (i j : Fin (N - 1)) :
    r i (h j) = h j - (CartanMatrix.A (N - 1) i j : ZMod p) • h i := by
  rw [S.r_form i (h j), S.pair i j]

private lemma l6kp_r_mem {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (i : Fin (N - 1)) {v : V}
    (hv : v ∈ Submodule.span (ZMod p) (Set.range h)) :
    r i v ∈ Submodule.span (ZMod p) (Set.range h) := by
  refine Submodule.span_induction (p := fun w _ =>
    r i w ∈ Submodule.span (ZMod p) (Set.range h)) ?_ ?_ ?_ ?_ hv
  · intro z hz
    obtain ⟨j, rfl⟩ := hz
    rw [l6kp_r_h S i j]
    exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self j))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact Submodule.add_mem (Submodule.span (ZMod p) (Set.range h)) ha hb
  · intro c a _ ha
    rw [map_smul]
    exact Submodule.smul_mem (Submodule.span (ZMod p) (Set.range h)) c ha

private lemma l6kp_r_map {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (i : Fin (N - 1)) :
    (Submodule.span (ZMod p) (Set.range h)).map
        ((r i : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V)
      = Submodule.span (ZMod p) (Set.range h) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact l6kp_r_mem S i hv
  · intro v hv
    refine ⟨(r i).symm v, ?_, ?_⟩
    · rw [l6kp_rinv S i]
      exact l6kp_r_mem S i hv
    · simp

private noncomputable def l6kp_rR {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (i : Fin (N - 1)) :
    (Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p]
      (Submodule.span (ZMod p) (Set.range h)) :=
  LinearEquiv.ofSubmodules (r i) _ _ (l6kp_r_map S i)

private lemma l6kp_span_h_top {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin (N - 1) → V) :
    Submodule.span (ZMod p) (Set.range (fun j : Fin (N - 1) =>
      (⟨h j, Submodule.subset_span (Set.mem_range_self j)⟩ :
        Submodule.span (ZMod p) (Set.range h)))) = ⊤ := by
  apply Submodule.map_injective_of_injective
    (Submodule.subtype_injective (Submodule.span (ZMod p) (Set.range h)))
  have hrange : ((Submodule.subtype (Submodule.span (ZMod p) (Set.range h))) ''
      Set.range (fun j : Fin (N - 1) =>
        (⟨h j, Submodule.subset_span (Set.mem_range_self j)⟩ :
          Submodule.span (ZMod p) (Set.range h)))) = Set.range h := by
    ext v
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact Set.mem_range_self j
    · rintro ⟨j, rfl⟩
      exact ⟨⟨h j, Submodule.subset_span (Set.mem_range_self j)⟩, ⟨j, rfl⟩, rfl⟩
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, hrange]

private lemma l6kp_E_r {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (i : Fin (N - 1))
    (y : Submodule.span (ZMod p) (Set.range h)) :
    l6kp_E S (l6kp_rR S i y) =
      (l6kp_rho (p := p) (N := N) (Equiv.swap i.castSucc i.succ)) (l6kp_E S y) := by
  have hfg : ((l6kp_E S).toLinearMap.comp (l6kp_rR S i).toLinearMap)
      = ((l6kp_rho (p := p) (N := N) (Equiv.swap i.castSucc i.succ)).toLinearMap.comp
          (l6kp_E S).toLinearMap) := by
    refine LinearMap.ext_on_range (l6kp_span_h_top (p := p) (N := N) (h := h)) ?_
    intro j
    change l6kp_E S (l6kp_rR S i ⟨h j, Submodule.subset_span (Set.mem_range_self j)⟩)
      = (l6kp_rho (p := p) (N := N) (Equiv.swap i.castSucc i.succ))
          (l6kp_E S ⟨h j, Submodule.subset_span (Set.mem_range_self j)⟩)
    set xj : Submodule.span (ZMod p) (Set.range h) :=
      ⟨h j, Submodule.subset_span (Set.mem_range_self j)⟩ with hxj
    set xi : Submodule.span (ZMod p) (Set.range h) :=
      ⟨h i, Submodule.subset_span (Set.mem_range_self i)⟩ with hxi
    have hstep : l6kp_rR S i xj = xj - (CartanMatrix.A (N - 1) i j : ZMod p) • xi := by
      apply Subtype.ext
      change r i (h j) = _
      rw [l6kp_r_h S i j]
      rfl
    have hrho : l6kp_rho (p := p) (N := N) (Equiv.swap i.castSucc i.succ)
        ⟨l6kp_w j, l6kp_w_mem (p := p) (N := N) j⟩
        = ⟨l6kp_w j, l6kp_w_mem (p := p) (N := N) j⟩
          - (CartanMatrix.A (N - 1) i j : ZMod p) •
            ⟨l6kp_w i, l6kp_w_mem (p := p) (N := N) i⟩ := by
      apply Subtype.ext
      exact l6kp_shat_w (p := p) (N := N) i j
    have hleft : l6kp_E S (l6kp_rR S i xj)
        = ⟨l6kp_w j, l6kp_w_mem (p := p) (N := N) j⟩
          - (CartanMatrix.A (N - 1) i j : ZMod p) •
            ⟨l6kp_w i, l6kp_w_mem (p := p) (N := N) i⟩ := by
      rw [hstep, map_sub, map_smul, l6kp_E_h S j, l6kp_E_h S i]
    have hright : (l6kp_rho (p := p) (N := N) (Equiv.swap i.castSucc i.succ))
        (l6kp_E S xj)
        = ⟨l6kp_w j, l6kp_w_mem (p := p) (N := N) j⟩
          - (CartanMatrix.A (N - 1) i j : ZMod p) •
            ⟨l6kp_w i, l6kp_w_mem (p := p) (N := N) i⟩ := by
      rw [show l6kp_E S xj = ⟨l6kp_w j, l6kp_w_mem (p := p) (N := N) j⟩ from
        l6kp_E_h S j, hrho]
    rw [hleft, hright]
  exact LinearMap.congr_fun hfg y

private lemma l6kp_hle {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Subgroup.closure (Set.range r) ≤ ggLinStab (Submodule.span (ZMod p) (Set.range h)) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨fun v hv => l6kp_r_mem S i hv, fun v hv => by
    rw [l6kp_rinv S i]
    exact l6kp_r_mem S i hv⟩

private noncomputable def l6kp_phi {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    ↥(Subgroup.closure (Set.range r)) →*
      ((Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p]
        (Submodule.span (ZMod p) (Set.range h))) :=
  (ggLinRestrictHom (Submodule.span (ZMod p) (Set.range h))).comp
    (Subgroup.inclusion (l6kp_hle S))

private lemma l6kp_phi_gen {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (i : Fin (N - 1)) :
    l6kp_phi S ⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩ = l6kp_rR S i := rfl

private lemma l6kp_disp {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    ∀ g ∈ Subgroup.closure (Set.range r), ∀ v : V,
      g v - v ∈ Submodule.span (ZMod p) (Set.range h) := by
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => ∀ v : V,
    g v - v ∈ Submodule.span (ZMod p) (Set.range h)) ?_ ?_ ?_ ?_ hg
  · intro y hy
    obtain ⟨i, rfl⟩ := hy
    intro v
    have h : r i v - v = -((α i v) • h i) := by
      rw [S.r_form i v]; abel
    rw [h]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i)))
  · intro v
    simp
  · intro a b _ _ ha hb v
    rw [LinearEquiv.mul_apply]
    have h : a (b v) - v = (a (b v) - b v) + (b v - v) := by abel
    rw [h]
    exact Submodule.add_mem _ (ha (b v)) (hb v)
  · intro a _ ha v
    have h1 : a (a⁻¹ v) = v := by simp
    have h2 := ha (a⁻¹ v)
    rw [h1] at h2
    have h : a⁻¹ v - v = -(v - a⁻¹ v) := by abel
    rw [h]
    exact Submodule.neg_mem _ h2

private lemma l6kp_faithful {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) {g : V ≃ₗ[ZMod p] V}
    (hgP : g ∈ Subgroup.closure (Set.range r))
    (hfix : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), g v = v) : g = 1 := by
  haveI : Module.Finite (ZMod p) V := by
    haveI : Finite ι := S.finite_family
    exact ggFixLine_finite s S.s_refl S.fix_H
  have hdisp := l6kp_disp S g hgP
  have hfixall : ∀ w : V, g (g w - w) = g w - w := fun w => hfix (g w - w) (hdisp w)
  have hker : Submodule.span (ZMod p) (Set.range h) ≤
      LinearMap.ker ((g : V →ₗ[ZMod p] V) - LinearMap.id) := by
    intro v hv
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.id_apply]
    exact sub_eq_zero.mpr (hfix v hv)
  have hle1 : Module.finrank (ZMod p) (ggLinMove g) ≤ 1 := by
    set d := Module.finrank (ZMod p)
      (LinearMap.range ((g : V →ₗ[ZMod p] V) - LinearMap.id)) with hd
    set k := Module.finrank (ZMod p)
      (LinearMap.ker ((g : V →ₗ[ZMod p] V) - LinearMap.id)) with hk
    set b := Module.finrank (ZMod p) V with hb
    have hfr : d + k = b := by
      rw [hd, hk, hb]
      exact LinearMap.finrank_range_add_finrank_ker _
    have hmono : N - 1 ≤ k := by
      rw [hk, ← l6kp_finrank_R S]
      exact Submodule.finrank_mono hker
    have hV : b ≤ N := by rw [hb]; exact S.dim_le
    have hN5 : 5 ≤ N := S.five_le
    have h1 : d + (N - 1) ≤ b := by
      calc d + (N - 1) ≤ d + k := Nat.add_le_add_left hmono d
        _ = b := hfr
    change d ≤ 1
    omega
  have hne1 : Module.finrank (ZMod p) (ggLinMove g) ≠ 1 := by
    intro h1
    exact S.no_transvection g
      (Subgroup.closure_mono (Set.subset_union_left) hgP) ⟨h1, hfixall⟩
  have hzero : Module.finrank (ZMod p) (ggLinMove g) = 0 := by omega
  have hbot : ggLinMove g = ⊥ := Submodule.finrank_eq_zero.mp hzero
  have h0 : ((g : V →ₗ[ZMod p] V) - LinearMap.id) = 0 := by
    rw [← LinearMap.range_eq_bot]
    exact hbot
  ext v
  have hv := DFunLike.congr_fun h0 v
  exact sub_eq_zero.mp hv

private lemma l6kp_phi_inj {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Function.Injective (l6kp_phi S) := by
  intro g k hgk
  have hprod : l6kp_phi S (g * k⁻¹) = 1 := by
    rw [map_mul, hgk, MonoidHom.map_inv, mul_inv_cancel]
  have hmem : (g * k⁻¹).1 ∈ Subgroup.closure (Set.range r) := (g * k⁻¹).2
  have hfix : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), (g * k⁻¹).1 v = v := by
    intro v hv
    calc (g * k⁻¹).1 v = ((l6kp_phi S (g * k⁻¹)) ⟨v, hv⟩ : V) := rfl
      _ = v := by rw [hprod]; rfl
  have hone : (g * k⁻¹) = 1 := Subtype.ext (l6kp_faithful S hmem hfix)
  exact mul_inv_eq_one.mp hone

private lemma l6kp_top_closure {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    (⊤ : Subgroup ↥(Subgroup.closure (Set.range r))) =
      Subgroup.closure (Set.range fun i : Fin (N - 1) =>
        (⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩ :
          ↥(Subgroup.closure (Set.range r)))) := by
  let P : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r)
  let gen : Fin (N - 1) → ↥P := fun i =>
    ⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  change (⊤ : Subgroup ↥P) = Subgroup.closure (Set.range gen)
  have himg : Subgroup.subtype P '' Set.range gen = Set.range r := by
    ext z
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_range_self i
    · rintro ⟨i, rfl⟩
      exact ⟨gen i, ⟨i, rfl⟩, rfl⟩
  apply Subgroup.map_injective (Subgroup.subtype_injective P)
  rw [Subgroup.map_top, Subgroup.range_subtype,
    MonoidHom.map_closure (Subgroup.subtype P) (Set.range gen), himg]

private lemma l6kp_closure_swaps {N : ℕ} :
    Subgroup.closure (Set.range fun i : Fin (N - 1) =>
      Equiv.swap i.castSucc i.succ) = ⊤ := by
  have h := Equiv.Perm.mclosure_swap_castSucc_succ (N - 1)
  have hsub : Submonoid.closure (Set.range fun i : Fin (N - 1) =>
      Equiv.swap i.castSucc i.succ) ≤
      (Subgroup.closure (Set.range fun i : Fin (N - 1) =>
        Equiv.swap i.castSucc i.succ)).toSubmonoid :=
    Submonoid.closure_le.mpr (fun x hx => Subgroup.subset_closure hx)
  rw [h] at hsub
  exact le_antisymm le_top hsub

noncomputable def l6kp_eta {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    ↥(Subgroup.closure (Set.range r)) →*
      (l6kp_H0 p (N - 1 + 1) ≃ₗ[ZMod p] l6kp_H0 p (N - 1 + 1)) where
  toFun g := ((l6kp_E S).symm.trans (l6kp_phi S g)).trans (l6kp_E S)
  map_one' := by
    ext y
    simp
  map_mul' g k := by
    ext y
    simp [l6kp_phi, LinearEquiv.mul_apply]

private lemma l6kp_eta_apply {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (g : ↥(Subgroup.closure (Set.range r)))
    (y : l6kp_H0 p (N - 1 + 1)) :
    l6kp_eta S g y =
      l6kp_E S (l6kp_phi S g ((l6kp_E S).symm y)) := by
  rfl

private lemma l6kp_eta_gen {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (i : Fin (N - 1)) :
    l6kp_eta S ⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩ =
      l6kp_rhoHom (p := p) (N := N) (Equiv.swap i.castSucc i.succ) := by
  apply LinearEquiv.ext
  intro y
  rw [l6kp_eta_apply, l6kp_phi_gen S i, l6kp_E_r S i, LinearEquiv.apply_symm_apply]
  rfl

lemma l6kp_eta_range {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    (l6kp_eta S).range = (l6kp_rhoHom (p := p) (N := N)).range := by
  have himg : (l6kp_eta S) '' (Set.range fun i : Fin (N - 1) =>
        (⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩ :
          ↥(Subgroup.closure (Set.range r)))) =
      Set.range fun i : Fin (N - 1) =>
        l6kp_eta S ⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩ := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_range_self i
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
  have himg2 : (l6kp_rhoHom (p := p) (N := N)) '' (Set.range fun i : Fin (N - 1) =>
        Equiv.swap i.castSucc i.succ) =
      Set.range fun i : Fin (N - 1) =>
        l6kp_rhoHom (p := p) (N := N) (Equiv.swap i.castSucc i.succ) := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_range_self i
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
  have h1 : (l6kp_eta S).range = Subgroup.closure (Set.range fun i : Fin (N - 1) =>
      l6kp_eta S ⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩) := by
    rw [MonoidHom.range_eq_map, l6kp_top_closure S, MonoidHom.map_closure, himg]
  have h2 : (l6kp_rhoHom (p := p) (N := N)).range =
      Subgroup.closure (Set.range fun i : Fin (N - 1) =>
        l6kp_rhoHom (p := p) (N := N) (Equiv.swap i.castSucc i.succ)) := by
    rw [MonoidHom.range_eq_map, ← l6kp_closure_swaps (N := N), MonoidHom.map_closure, himg2]
  have hfam : (fun i : Fin (N - 1) =>
      l6kp_eta S ⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩) =
      (fun i : Fin (N - 1) =>
        l6kp_rhoHom (p := p) (N := N) (Equiv.swap i.castSucc i.succ)) := by
    funext i
    exact l6kp_eta_gen S i
  rw [h1, h2, hfam]

lemma l6kp_eta_inj {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) : Function.Injective (l6kp_eta S) := by
  intro g k hgk
  apply l6kp_phi_inj S
  apply LinearEquiv.ext
  intro z
  have hx := LinearEquiv.congr_fun hgk (l6kp_E S z)
  rw [l6kp_eta_apply, l6kp_eta_apply, LinearEquiv.symm_apply_apply] at hx
  exact (l6kp_E S).injective hx

end CFSG.StandardType

end
