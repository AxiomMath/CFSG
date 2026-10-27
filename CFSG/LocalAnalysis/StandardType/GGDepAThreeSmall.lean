module

public import CFSG.LocalAnalysis.StandardType.GGDepAThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGDepASmall
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private theorem lr7sm_transport {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha)
    (θ : V ≃ₗ[ZMod p] GGDepAE p N) (hθh : ∀ i, θ (h i) = ggDepAh p N i)
    (hθα : ∀ i v, α i v = ggDepAdot (ggDepAα p N i) (θ v))
    (αa' : GGDepAE p N) (hαa'dot : ∀ y : GGDepAE p N, ggDepAdot αa' y = αa (θ.symm y))
    (g : Module.End (ZMod p) (GGDepAE p N))
    (hgS : g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
        ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪ {ggDepARefl (θ ha) αa'}))
    (htv : GGDepAIsTv g)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) :
    False := by
  classical
  let S : Set (Module.End (ZMod p) (GGDepAE p N)) :=
    Set.range (fun i : Fin (N - 1) => ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
      {ggDepARefl (θ ha) αa'}
  let T : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod p] V) v = v - α i v • h i := fun i v => hr i v
  have hra_apply : ∀ v, (ra : V →ₗ[ZMod p] V) v = v - αa v • ha := fun v => hra v
  have hθα' : ∀ i v, α i v =
      ggDepAdot (ggDepAα p N i) ((θ : V →ₗ[ZMod p] GGDepAE p N) v) := fun i v => hθα i v
  have hαa'dot' : ∀ y : GGDepAE p N,
      ggDepAdot αa' y = αa ((θ.symm : GGDepAE p N →ₗ[ZMod p] V) y) := fun y => hαa'dot y
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
          rw [show θ.symm.toLinearMap (ggDepAh p N i) = h i by
            change (θ.symm : GGDepAE p N → V) (ggDepAh p N i) = h i
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
            change (θ.symm : GGDepAE p N → V) (θ ha) = ha
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


theorem ggDepAThree_small_false (hcells : GGDepAThreeCells9) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] {h : Fin (9 - 1) → V}
    {α : Fin (9 - 1) → Module.Dual (ZMod 3) V} {x : V} (F : GGDepAFrame 3 9 h α x)
    (r : Fin (9 - 1) → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod 3] V) (ha : V) (αa : Module.Dual (ZMod 3) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0) (b c0 : Fin (9 - 1))
    (m n : ℤ) (hpat : GGDepAPatE 9 b c0 m n)
    (hpair : ∀ c : Fin (9 - 1), c ≠ b →
      αa (h c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        α c ha = (if c = c0 then (n : ZMod 3) else 0))
    (hy : ∃ y : V, y ∉ Submodule.span (ZMod 3) {x} ∧ ∀ c, c ≠ b → α c y = 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) : False := by
  classical
  have hb : b.val = 0 ∨ b.val + 2 = 9 := by
    rcases hpat with h | h
    · exact h.1
    · exact h.2.1
  have hdim : Module.finrank (ZMod 3) V = 9 := ggDepA_finrank_eq F b hb hy
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepA_model_iso F hdim
  obtain ⟨αa', hαa'dot⟩ := l05nPT_dot_of_comp_symm (p := 3) (N := 9) αa θ
  set ha' : GGDepAE 3 9 := θ ha with ha'_def
  have hpair' : ∀ c : Fin (9 - 1), c ≠ b →
      ggDepAdot αa' (ggDepAh 3 9 c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        ggDepAdot (ggDepAα 3 9 c) ha' = (if c = c0 then (n : ZMod 3) else 0) := by
    intro c hc
    constructor
    · rw [hαa'dot]
      rw [show θ.symm (ggDepAh 3 9 c) = h c by
        rw [← hθh c, LinearEquiv.symm_apply_apply]]
      exact (hpair c hc).1
    · rw [ha'_def, ← hθα c ha]
      exact (hpair c hc).2
  have hha : ggDepAdot αa' ha' = 2 := by
    rw [hαa'dot, ha'_def, LinearEquiv.symm_apply_apply]
    exact hαa
  have hhw : ggDepAdot αa' (ggDepAx 3 9) ≠ 0 := by
    rw [hαa'dot]
    rw [show θ.symm (ggDepAx 3 9) = x by
      rw [← hθx, LinearEquiv.symm_apply_apply]]
    exact hw
  obtain ⟨g, hgS, htv⟩ := hcells b c0 m n hpat ha' αa' hpair' hha hhw
  exact lr7sm_transport r hr ra ha αa hra θ hθh hθα αa' hαa'dot g
    (by simpa only [ha'_def] using hgS) htv hnt

theorem ggDepAThree_small6 (hcells : GGDepAThreeCells6) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] {h : Fin (6 - 1) → V}
    {α : Fin (6 - 1) → Module.Dual (ZMod 3) V} {x : V} (F : GGDepAFrame 3 6 h α x)
    (r : Fin (6 - 1) → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod 3] V) (ha : V) (αa : Module.Dual (ZMod 3) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0) (b c0 : Fin (6 - 1))
    (m n : ℤ) (hpat : GGDepAPatE 6 b c0 m n)
    (hpair : ∀ c : Fin (6 - 1), c ≠ b →
      αa (h c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        α c ha = (if c = c0 then (n : ZMod 3) else 0))
    (hy : ∃ y : V, y ∉ Submodule.span (ZMod 3) {x} ∧ ∀ c, c ≠ b → α c y = 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) :
    ∃ (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (αa' : GGDepAE 3 6),
      (∀ i, θ (h i) = ggDepAh 3 6 i) ∧
      (∀ i v, α i v = ggDepAdot (ggDepAα 3 6 i) (θ v)) ∧ θ x = ggDepAx 3 6 ∧
      (∀ y, ggDepAdot αa' y = αa (θ.symm y)) ∧
      GGDepAWeylE6Data (Set.range (fun i : Fin (6 - 1) =>
        ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪ {ggDepARefl (θ ha) αa'}) := by
  classical
  have hb : b.val = 0 ∨ b.val + 2 = 6 := by
    rcases hpat with h | h
    · exact h.1
    · exact absurd h.1 (by omega)
  have hdim : Module.finrank (ZMod 3) V = 6 := ggDepA_finrank_eq F b hb hy
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepA_model_iso F hdim
  obtain ⟨αa', hαa'dot⟩ := l05nPT_dot_of_comp_symm (p := 3) (N := 6) αa θ
  set ha' : GGDepAE 3 6 := θ ha with ha'_def
  have hpair' : ∀ c : Fin (6 - 1), c ≠ b →
      ggDepAdot αa' (ggDepAh 3 6 c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        ggDepAdot (ggDepAα 3 6 c) ha' = (if c = c0 then (n : ZMod 3) else 0) := by
    intro c hc
    constructor
    · rw [hαa'dot]
      rw [show θ.symm (ggDepAh 3 6 c) = h c by
        rw [← hθh c, LinearEquiv.symm_apply_apply]]
      exact (hpair c hc).1
    · rw [ha'_def, ← hθα c ha]
      exact (hpair c hc).2
  have hha : ggDepAdot αa' ha' = 2 := by
    rw [hαa'dot, ha'_def, LinearEquiv.symm_apply_apply]
    exact hαa
  have hhw : ggDepAdot αa' (ggDepAx 3 6) ≠ 0 := by
    rw [hαa'dot]
    rw [show θ.symm (ggDepAx 3 6) = x by
      rw [← hθx, LinearEquiv.symm_apply_apply]]
    exact hw
  rcases hcells b c0 m n hpat ha' αa' hpair' hha hhw with ⟨g, hgS, htv⟩ | hdata
  · exfalso
    exact lr7sm_transport r hr ra ha αa hra θ hθh hθα αa' hαa'dot g
      (by simpa only [ha'_def] using hgS) htv hnt
  · refine ⟨θ, αa', hθh, hθα, hθx, hαa'dot, ?_⟩
    simpa only [ha'_def] using hdata

end CFSG.StandardType
