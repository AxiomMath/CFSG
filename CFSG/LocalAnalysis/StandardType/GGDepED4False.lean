module

public import CFSG.LocalAnalysis.StandardType.GGDepED4Defs
public import CFSG.LocalAnalysis.StandardType.GGDepEModel
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepED4_false_one {p : ℕ} [Fact p.Prime] (hcells : GGDepED4Cells1) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod p) V} {x : V} (F : GGDepEFrame p h α x)
    (hdim : Module.finrank (ZMod p) V = 7)
    (r : Fin 6 → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0) (c0 : Fin 6)
    (hleaf : GGDepED4Leaf c0)
    (hpair : ∀ c : Fin 6, GGDepED4In c →
      αa (h c) = (if c = c0 then (-1 : ZMod p) else 0) ∧
        α c ha = (if c = c0 then (-1 : ZMod p) else 0))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) : False := by
  have hp3 : p = 3 := F.p3
  subst hp3
  classical
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepE_model_iso F hdim
  obtain ⟨αa', hαa'dot⟩ := l05nPT_dot_of_comp_symm (p := 3) (N := 7) αa θ
  set ha' : GGDepAE 3 7 := θ ha with ha'_def
  have hαa'dot' : ∀ y : GGDepAE 3 7,
      ggDepAdot αa' y = αa ((θ.symm : GGDepAE 3 7 →ₗ[ZMod 3] V) y) := fun y => hαa'dot y
  have hpair' : GGDepED4Pairs1 c0 ha' αa' := by
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
  obtain ⟨g, hgS, htv⟩ := hcells c0 hleaf ha' αa' hpair' hha hhw
  let S : Set (Module.End (ZMod 3) (GGDepAE 3 7)) :=
    Set.range (fun i : Fin 6 => ggDepARefl (ggDepEh 3 i) (ggDepEα 3 i)) ∪
      {ggDepARefl ha' αa'}
  let T : Set (V ≃ₗ[ZMod 3] V) := Set.range r ∪ {ra}
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod 3] V) v = v - α i v • h i := fun i v => hr i v
  have hra_apply : ∀ v, (ra : V →ₗ[ZMod 3] V) v = v - αa v • ha := fun v => hra v
  have hθα' : ∀ i v, α i v =
      ggDepAdot (ggDepEα 3 i) ((θ : V →ₗ[ZMod 3] GGDepAE 3 7) v) := fun i v => hθα i v
  have hgen : ∀ y ∈ S, ∃ g' ∈ T,
      (g' : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap.comp (y.comp θ.toLinearMap) := by
    intro y hy
    dsimp only [S] at hy
    rcases hy with ⟨i, rfl⟩ | hy
    · refine ⟨r i, Or.inl ⟨i, rfl⟩, ?_⟩
      ext v
      rw [hr_apply i v]
      simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
      rw [l05nPT_symm_apply θ v]
      rw [show θ.symm.toLinearMap (ggDepEh 3 i) = h i by
        change (θ.symm : GGDepAE 3 7 → V) (ggDepEh 3 i) = h i
        rw [← hθh i, LinearEquiv.symm_apply_apply]]
      rw [← hθα' i v]
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine ⟨ra, Or.inr rfl, ?_⟩
      ext v
      rw [hra_apply v]
      simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
      rw [l05nPT_symm_apply θ v]
      rw [show θ.symm.toLinearMap ha' = ha by
        change (θ.symm : GGDepAE 3 7 → V) ha' = ha
        rw [ha'_def, LinearEquiv.symm_apply_apply]]
      rw [hαa'dot' (θ.toLinearMap v), l05nPT_symm_apply θ v]
  obtain ⟨g', hg'T, hg'eq⟩ := l05nD6_closure_conj (S := S) (T := T) θ hgen g hgS
  exact hnt g' hg'T ⟨by
      rw [l05nPT_conj_finrank θ g g' hg'eq]
      exact htv.1,
    l05nPT_conj_move_fix θ g g' hg'eq htv.2⟩

theorem ggDepED4_false_two {p : ℕ} [Fact p.Prime] (hcells : GGDepED4Cells1) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin 6 → V}
    {α : Fin 6 → Module.Dual (ZMod p) V} {x : V} (F : GGDepEFrame p h α x)
    (hdim : Module.finrank (ZMod p) V = 7)
    (r : Fin 6 → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra1 ra2 : V ≃ₗ[ZMod p] V) (ha1 ha2 : V) (αa1 αa2 : Module.Dual (ZMod p) V)
    (hra1 : ∀ v, ra1 v = v - αa1 v • ha1) (hra2 : ∀ v, ra2 v = v - αa2 v • ha2)
    (hαa1 : αa1 ha1 = 2) (hαa2 : αa2 ha2 = 2) (hw : αa1 x ≠ 0 ∨ αa2 x ≠ 0) (c c' : Fin 6)
    (hc : GGDepED4Leaf c) (hc' : GGDepED4Leaf c')
    (hpair1 : ∀ j : Fin 6, GGDepED4In j →
      αa1 (h j) = (if j = c then (-1 : ZMod p) else 0) ∧
        α j ha1 = (if j = c then (-1 : ZMod p) else 0))
    (hpair2 : ∀ j : Fin 6, GGDepED4In j →
      αa2 (h j) = (if j = c' then (-1 : ZMod p) else 0) ∧
        α j ha2 = (if j = c' then (-1 : ZMod p) else 0))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra1, ra2}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) : False := by
  have hsub1 : Set.range r ∪ ({ra1} : Set (V ≃ₗ[ZMod p] V)) ⊆
      Set.range r ∪ {ra1, ra2} := by
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (Set.mem_insert_iff.mpr (Or.inl hy))
  have hsub2 : Set.range r ∪ ({ra2} : Set (V ≃ₗ[ZMod p] V)) ⊆
      Set.range r ∪ {ra1, ra2} := by
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (Set.mem_insert_iff.mpr (Or.inr hy))
  rcases hw with hw1 | hw2
  · exact ggDepED4_false_one hcells F hdim r hr ra1 ha1 αa1 hra1 hαa1 hw1 c hc hpair1
      (fun g hg => hnt g (Subgroup.closure_mono hsub1 hg))
  · exact ggDepED4_false_one hcells F hdim r hr ra2 ha2 αa2 hra2 hαa2 hw2 c' hc' hpair2
      (fun g hg => hnt g (Subgroup.closure_mono hsub2 hg))

end CFSG.StandardType

end
