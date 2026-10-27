module

public import CFSG.LocalAnalysis.StandardType.GGDepEDefs
public import CFSG.LocalAnalysis.StandardType.GGDepERelation
public import CFSG.LocalAnalysis.StandardType.GGDepASmall
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma lr7em_dot_single {p : ℕ} (w : GGDepAE p 7) (i : Fin 7) :
    ggDepAdot (Pi.single i 1) w = w i := by
  rw [ggDepAdot]
  rw [← Finset.sum_subset (Finset.subset_univ ({i} : Finset (Fin 7))) (by
    intro x _ hx
    simp only [Finset.mem_singleton] at hx
    rw [Pi.single_apply, if_neg hx, zero_mul])]
  rw [Finset.sum_singleton, Pi.single_eq_same, one_mul]

private lemma lr7em_ggDepEα_eq_single {p : ℕ} (i : Fin 6) :
    ggDepEα p i = Pi.single (⟨i.val, by have := i.isLt; omega⟩ : Fin 7) 1 := by
  funext j
  rw [ggDepEα, Pi.single_apply]
  by_cases h : j = (⟨i.val, by have := i.isLt; omega⟩ : Fin 7)
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hv => h (Fin.ext hv))]

private theorem lr7em_transport {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod p) V}
    (r : Fin 6 → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha)
    (θ : V ≃ₗ[ZMod p] GGDepAE p 7) (hθh : ∀ i, θ (h i) = ggDepEh p i)
    (hθα : ∀ i v, α i v = ggDepAdot (ggDepEα p i) (θ v))
    (αa' : GGDepAE p 7) (hαa'dot : ∀ y : GGDepAE p 7, ggDepAdot αa' y = αa (θ.symm y))
    (g : Module.End (ZMod p) (GGDepAE p 7))
    (hgS : g ∈ Submonoid.closure (Set.range (fun i : Fin 6 =>
        ggDepARefl (ggDepEh p i) (ggDepEα p i)) ∪ {ggDepARefl (θ ha) αa'}))
    (htv : GGDepAIsTv g)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) :
    False := by
  classical
  let S : Set (Module.End (ZMod p) (GGDepAE p 7)) :=
    Set.range (fun i : Fin 6 => ggDepARefl (ggDepEh p i) (ggDepEα p i)) ∪
      {ggDepARefl (θ ha) αa'}
  let T : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod p] V) v = v - α i v • h i := fun i v => hr i v
  have hra_apply : ∀ v, (ra : V →ₗ[ZMod p] V) v = v - αa v • ha := fun v => hra v
  have hθα' : ∀ i v, α i v =
      ggDepAdot (ggDepEα p i) ((θ : V →ₗ[ZMod p] GGDepAE p 7) v) := fun i v => hθα i v
  have hαa'dot' : ∀ y : GGDepAE p 7,
      ggDepAdot αa' y = αa ((θ.symm : GGDepAE p 7 →ₗ[ZMod p] V) y) := fun y => hαa'dot y
  have hconj : ∀ y ∈ Submonoid.closure S, ∃ g' ∈ Subgroup.closure T,
      (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (y.comp θ.toLinearMap) := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem z hz =>
        dsimp only [S] at hz
        rcases hz with ⟨i, rfl⟩ | hz
        · refine ⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩), ?_⟩
          ext v
          rw [hr_apply i v]
          simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
          rw [l05nPT_symm_apply θ v]
          rw [show θ.symm.toLinearMap (ggDepEh p i) = h i by
            change (θ.symm : GGDepAE p 7 → V) (ggDepEh p i) = h i
            rw [← hθh i, LinearEquiv.symm_apply_apply]]
          rw [← hθα' i v]
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          refine ⟨ra, Subgroup.subset_closure (Or.inr rfl), ?_⟩
          ext v
          rw [hra_apply v]
          simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
          rw [l05nPT_symm_apply θ v]
          rw [show θ.symm.toLinearMap (θ ha) = ha by
            change (θ.symm : GGDepAE p 7 → V) (θ ha) = ha
            rw [LinearEquiv.symm_apply_apply]]
          rw [hαa'dot' (θ.toLinearMap v), l05nPT_symm_apply θ v]
    | one =>
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        ext v
        simp
    | mul y z _ _ hpy hpz =>
        obtain ⟨gy, hgy, egy⟩ := hpy
        obtain ⟨gz, hgz, ez⟩ := hpz
        refine ⟨gy * gz, Subgroup.mul_mem _ hgy hgz, ?_⟩
        rw [LinearEquiv.coe_toLinearMap_mul, egy, ez, Module.End.mul_eq_comp,
          Module.End.mul_eq_comp]
        ext v
        simp only [LinearMap.comp_apply]
        rw [l05nPT_apply_symm θ]
  obtain ⟨g', hg'T, hg'eq⟩ := hconj g hgS
  exact hnt g' hg'T ⟨by
      rw [l05nPT_conj_finrank θ g g' hg'eq]
      exact htv.1,
    l05nPT_conj_move_fix θ g g' hg'eq htv.2⟩


theorem ggDepE_model_iso {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepEFrame p h α x) (hdim : Module.finrank (ZMod p) V = 7) :
    ∃ θ : V ≃ₗ[ZMod p] GGDepAE p 7, (∀ i, θ (h i) = ggDepEh p i) ∧
      (∀ i v, α i v = ggDepAdot (ggDepEα p i) (θ v)) ∧ θ x = ggDepEx p := by
  obtain ⟨_, hxH, _⟩ := ggDepE_relation F
  obtain ⟨lam, hlamH, hlamx⟩ :=
    LinearMap.exists_extend_of_notMem (p := Submodule.span (ZMod p) (Set.range h)) (v := x)
      (0 : Submodule.span (ZMod p) (Set.range h) →ₗ[ZMod p] ZMod p) hxH 1
  have hlamh : ∀ i : Fin 6, lam (h i) = 0 := by
    intro i
    have hmem : h i ∈ Submodule.span (ZMod p) (Set.range h) := Submodule.subset_span ⟨i, rfl⟩
    have := LinearMap.congr_fun hlamH ⟨h i, hmem⟩
    simpa using this
  let θ₀ : V →ₗ[ZMod p] (Fin 7 → ZMod p) :=
    { toFun := fun v j => if hj : j.val < 6 then α ⟨j.val, hj⟩ v else lam v
      map_add' := by
        intro a b
        funext j
        by_cases hj : j.val < 6 <;> simp [hj, map_add]
      map_smul' := by
        intro c a
        funext j
        by_cases hj : j.val < 6 <;> simp [hj, map_smul] }
  have hθ₀_apply : ∀ v j, θ₀ v j =
      if hj : j.val < 6 then α ⟨j.val, hj⟩ v else lam v := fun _ _ => rfl
  have hkey : ∀ w, θ₀ w = 0 → w = 0 := by
    intro w hw
    have hlamw : lam w = 0 := by
      have h := congr_fun hw (⟨6, by omega⟩ : Fin 7)
      rw [hθ₀_apply, dif_neg (by omega : ¬ (6 : ℕ) < 6)] at h
      exact h
    have hαw : ∀ i : Fin 6, α i w = 0 := by
      intro i
      have h := congr_fun hw (⟨i.val, by have := i.isLt; omega⟩ : Fin 7)
      rw [hθ₀_apply, dif_pos i.isLt] at h
      simpa using h
    have hspan : w ∈ Submodule.span (ZMod p) {x} := F.fix w hαw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
    have hc_eq : c = lam w := by
      rw [← hc, map_smul, hlamx]
      simp
    rw [← hc, hc_eq.trans hlamw, zero_smul]
  have hθ₀_inj : Function.Injective θ₀ := by
    intro u v huv
    have : θ₀ (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hkey (u - v) this)
  have hdim' : Module.finrank (ZMod p) V = Module.finrank (ZMod p) (Fin 7 → ZMod p) := by
    rw [hdim, Module.finrank_fin_fun]
  refine ⟨LinearMap.linearEquivOfInjective θ₀ hθ₀_inj hdim', ?_, ?_, ?_⟩
  · intro i
    rw [LinearMap.linearEquivOfInjective_apply]
    funext j
    by_cases hj : j.val < 6
    · rw [hθ₀_apply, dif_pos hj, F.pair]
      simp [ggDepEh, hj]
    · rw [hθ₀_apply, dif_neg hj, hlamh i]
      simp [ggDepEh, hj]
  · intro i v
    rw [LinearMap.linearEquivOfInjective_apply]
    rw [lr7em_ggDepEα_eq_single i, lr7em_dot_single]
    rw [hθ₀_apply, dif_pos i.isLt]
  · rw [LinearMap.linearEquivOfInjective_apply]
    funext j
    by_cases hj : j.val < 6
    · rw [hθ₀_apply, dif_pos hj, F.x_ker, ggDepEx, if_neg (by omega : ¬ j.val = 6)]
    · rw [hθ₀_apply, dif_neg hj, hlamx, ggDepEx, if_pos (by omega : j.val = 6)]


theorem ggDepE_small_false {p : ℕ} [Fact p.Prime] (hcells : GGDepECells) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod p) V} {x : V} (F : GGDepEFrame p h α x)
    (r : Fin 6 → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hdim : Module.finrank (ZMod p) V = 7)
    (b c0 : Fin 6) (m n : ℤ) (hpat : GGDepEPat b c0 m n)
    (hpair : ∀ c : Fin 6, c ≠ b →
      αa (h c) = (if c = c0 then (m : ZMod p) else 0) ∧
        α c ha = (if c = c0 then (n : ZMod p) else 0))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) : False := by
  have hp3 : p = 3 := F.p3
  subst hp3
  classical
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepE_model_iso F hdim
  obtain ⟨αa', hαa'dot⟩ := l05nPT_dot_of_comp_symm (p := 3) (N := 7) αa θ
  set ha' : GGDepAE 3 7 := θ ha with ha'_def
  have hpair' : ∀ c : Fin 6, c ≠ b →
      ggDepAdot αa' (ggDepEh 3 c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        ggDepAdot (ggDepEα 3 c) ha' = (if c = c0 then (n : ZMod 3) else 0) := by
    intro c hc
    constructor
    · rw [hαa'dot]
      rw [show θ.symm (ggDepEh 3 c) = h c by
        rw [← hθh c, LinearEquiv.symm_apply_apply]]
      exact (hpair c hc).1
    · rw [ha'_def, ← hθα c ha]
      exact (hpair c hc).2
  have hha : ggDepAdot αa' ha' = 2 := by
    rw [hαa'dot, ha'_def, LinearEquiv.symm_apply_apply]
    exact hαa
  have hhw : ggDepAdot αa' (ggDepEx 3) ≠ 0 := by
    rw [hαa'dot]
    rw [show θ.symm (ggDepEx 3) = x by
      rw [← hθx, LinearEquiv.symm_apply_apply]]
    exact hw
  obtain ⟨g, hgS, htv⟩ := hcells b c0 m n hpat ha' αa' hpair' hha hhw
  exact lr7em_transport r hr ra ha αa hra θ hθh hθα αa' hαa'dot g
    (by simpa only [ha'_def] using hgS) htv hnt

end CFSG.StandardType
