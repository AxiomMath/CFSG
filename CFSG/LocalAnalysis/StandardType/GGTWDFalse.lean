module

public import CFSG.LocalAnalysis.StandardType.GGTWDCells

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma l05nD6_closure_conj {p : ℕ} [Fact p.Prime] {V E : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup E] [Module (ZMod p) E]
    (θ : V ≃ₗ[ZMod p] E) {S : Set (Module.End (ZMod p) E)} {T : Set (V ≃ₗ[ZMod p] V)}
    (hgen : ∀ y ∈ S, ∃ g' ∈ T,
      (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (y.comp θ.toLinearMap)) :
    ∀ y ∈ Submonoid.closure S, ∃ g' ∈ Subgroup.closure T,
      (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (y.comp θ.toLinearMap) := by
  intro y hy
  induction hy using Submonoid.closure_induction with
  | mem z hz =>
      obtain ⟨g', hg'T, hg'eq⟩ := hgen z hz
      exact ⟨g', Subgroup.subset_closure hg'T, hg'eq⟩
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

theorem ggTWD_false_one {p N : ℕ} [Fact p.Prime] (hcells : GGTWDCells1 p N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (hdim : Module.finrank (ZMod p) V = N)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0) (pos : GGTWPos)
    (c0 : Fin (N - 1)) (m n : ℤ) (hpat : GGTWPat1 N pos c0.val m n)
    (hpair : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      αa (h c) = (if c = c0 then (m : ZMod p) else 0) ∧
        α c ha = (if c = c0 then (n : ZMod p) else 0))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) : False := by
  classical
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepA_model_iso F hdim
  obtain ⟨αa', hαa'dot⟩ := l05nPT_dot_of_comp_symm (p := p) (N := N) αa θ
  set ha' : GGDepAE p N := θ ha with ha'_def
  have hαa'dot' : ∀ y : GGDepAE p N,
      ggDepAdot αa' y = αa ((θ.symm : GGDepAE p N →ₗ[ZMod p] V) y) := fun y => hαa'dot y
  have hpair' : GGTWDPairs1 p N pos c0 m n ha' αa' := by
    intro c hc
    constructor
    · rw [hαa'dot]
      rw [show θ.symm (ggDepAh p N c) = h c by
        rw [← hθh c, LinearEquiv.symm_apply_apply]]
      exact (hpair c hc).1
    · rw [ha'_def, ← hθα c ha]
      exact (hpair c hc).2
  have hha : ggDepAdot αa' ha' = 2 := by
    rw [hαa'dot, ha'_def, LinearEquiv.symm_apply_apply]
    exact hαa
  have hhw : ggDepAdot αa' (ggDepAx p N) ≠ 0 := by
    rw [hαa'dot]
    rw [show θ.symm (ggDepAx p N) = x by
      rw [← hθx, LinearEquiv.symm_apply_apply]]
    exact hw
  obtain ⟨g, hgS, htv⟩ := hcells pos c0 m n hpat ha' αa' hpair' hha hhw
  let S : Set (Module.End (ZMod p) (GGDepAE p N)) :=
    Set.range (fun i : Fin (N - 1) => ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
      {ggDepARefl ha' αa'}
  let T : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod p] V) v = v - α i v • h i := fun i v => hr i v
  have hra_apply : ∀ v, (ra : V →ₗ[ZMod p] V) v = v - αa v • ha := fun v => hra v
  have hθα' : ∀ i v, α i v =
      ggDepAdot (ggDepAα p N i) ((θ : V →ₗ[ZMod p] GGDepAE p N) v) := fun i v => hθα i v
  have hgen : ∀ y ∈ S, ∃ g' ∈ T,
      (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (y.comp θ.toLinearMap) := by
    intro y hy
    dsimp only [S] at hy
    rcases hy with ⟨i, rfl⟩ | hy
    · refine ⟨r i, Or.inl ⟨i, rfl⟩, ?_⟩
      ext v
      rw [hr_apply i v]
      simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
      rw [l05nPT_symm_apply θ v]
      rw [show θ.symm.toLinearMap (ggDepAh p N i) = h i by
        change (θ.symm : GGDepAE p N → V) (ggDepAh p N i) = h i
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
        change (θ.symm : GGDepAE p N → V) ha' = ha
        rw [ha'_def, LinearEquiv.symm_apply_apply]]
      rw [hαa'dot' (θ.toLinearMap v), l05nPT_symm_apply θ v]
  obtain ⟨g', hg'T, hg'eq⟩ := l05nD6_closure_conj (S := S) (T := T) θ hgen g hgS
  exact hnt g' hg'T ⟨by
      rw [l05nPT_conj_finrank θ g g' hg'eq]
      exact htv.1,
    l05nPT_conj_move_fix θ g g' hg'eq htv.2⟩

theorem ggTWD_false_two {p N : ℕ} [Fact p.Prime] (hcells : GGTWDCells2 p N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (hdim : Module.finrank (ZMod p) V = N)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra1 ra2 : V ≃ₗ[ZMod p] V) (ha1 ha2 : V) (αa1 αa2 : Module.Dual (ZMod p) V)
    (hra1 : ∀ v, ra1 v = v - αa1 v • ha1) (hra2 : ∀ v, ra2 v = v - αa2 v • ha2)
    (hw : αa1 x ≠ 0 ∨ αa2 x ≠ 0) (pos : GGTWPos) (c : Fin (N - 1))
    (c₂ : Option (Fin (N - 1))) (hpat : GGTWPat2 N pos c.val (c₂.map Fin.val))
    (hpair : (∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
        αa1 (h c') = (if c' = c then -1 else 0) ∧ α c' ha1 = (if c' = c then -1 else 0) ∧
          αa2 (h c') = (if some c' = c₂ then -1 else 0) ∧
            α c' ha2 = (if some c' = c₂ then -1 else 0)) ∧
      αa1 ha2 = (if c₂ = none then -1 else 0) ∧ αa2 ha1 = (if c₂ = none then -1 else 0) ∧
        αa1 ha1 = 2 ∧ αa2 ha2 = 2)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra1, ra2}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) : False := by
  classical
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepA_model_iso F hdim
  obtain ⟨αa1', hαa1'dot⟩ := l05nPT_dot_of_comp_symm (p := p) (N := N) αa1 θ
  obtain ⟨αa2', hαa2'dot⟩ := l05nPT_dot_of_comp_symm (p := p) (N := N) αa2 θ
  set ha1' : GGDepAE p N := θ ha1 with ha1'_def
  set ha2' : GGDepAE p N := θ ha2 with ha2'_def
  have hαa1'dot' : ∀ y : GGDepAE p N,
      ggDepAdot αa1' y = αa1 ((θ.symm : GGDepAE p N →ₗ[ZMod p] V) y) := fun y => hαa1'dot y
  have hαa2'dot' : ∀ y : GGDepAE p N,
      ggDepAdot αa2' y = αa2 ((θ.symm : GGDepAE p N →ₗ[ZMod p] V) y) := fun y => hαa2'dot y
  have hpair' : GGTWDPairs2 p N pos c c₂ ha1' αa1' ha2' αa2' := by
    obtain ⟨hJ, h12, h21, h11, h22⟩ := hpair
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c' hc'
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hαa1'dot]
        rw [show θ.symm (ggDepAh p N c') = h c' by
          rw [← hθh c', LinearEquiv.symm_apply_apply]]
        exact (hJ c' hc').1
      · rw [ha1'_def, ← hθα c' ha1]
        exact (hJ c' hc').2.1
      · rw [hαa2'dot]
        rw [show θ.symm (ggDepAh p N c') = h c' by
          rw [← hθh c', LinearEquiv.symm_apply_apply]]
        exact (hJ c' hc').2.2.1
      · rw [ha2'_def, ← hθα c' ha2]
        exact (hJ c' hc').2.2.2
    · rw [hαa1'dot, ha2'_def, LinearEquiv.symm_apply_apply]
      exact h12
    · rw [hαa2'dot, ha1'_def, LinearEquiv.symm_apply_apply]
      exact h21
    · rw [hαa1'dot, ha1'_def, LinearEquiv.symm_apply_apply]
      exact h11
    · rw [hαa2'dot, ha2'_def, LinearEquiv.symm_apply_apply]
      exact h22
  have hhw : ggDepAdot αa1' (ggDepAx p N) ≠ 0 ∨ ggDepAdot αa2' (ggDepAx p N) ≠ 0 := by
    rcases hw with hw | hw
    · left
      rw [hαa1'dot]
      rw [show θ.symm (ggDepAx p N) = x by
        rw [← hθx, LinearEquiv.symm_apply_apply]]
      exact hw
    · right
      rw [hαa2'dot]
      rw [show θ.symm (ggDepAx p N) = x by
        rw [← hθx, LinearEquiv.symm_apply_apply]]
      exact hw
  obtain ⟨g, hgS, htv⟩ := hcells pos c c₂ hpat ha1' αa1' ha2' αa2' hpair' hhw
  let S : Set (Module.End (ZMod p) (GGDepAE p N)) :=
    Set.range (fun i : Fin (N - 1) => ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
      {ggDepARefl ha1' αa1', ggDepARefl ha2' αa2'}
  let T : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra1, ra2}
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod p] V) v = v - α i v • h i := fun i v => hr i v
  have hra1_apply : ∀ v, (ra1 : V →ₗ[ZMod p] V) v = v - αa1 v • ha1 := fun v => hra1 v
  have hra2_apply : ∀ v, (ra2 : V →ₗ[ZMod p] V) v = v - αa2 v • ha2 := fun v => hra2 v
  have hθα' : ∀ i v, α i v =
      ggDepAdot (ggDepAα p N i) ((θ : V →ₗ[ZMod p] GGDepAE p N) v) := fun i v => hθα i v
  have hgen : ∀ y ∈ S, ∃ g' ∈ T,
      (g' : V →ₗ[ZMod p] V) = θ.symm.toLinearMap.comp (y.comp θ.toLinearMap) := by
    intro y hy
    dsimp only [S] at hy
    rcases hy with ⟨i, rfl⟩ | hy
    · refine ⟨r i, Or.inl ⟨i, rfl⟩, ?_⟩
      ext v
      rw [hr_apply i v]
      simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
      rw [l05nPT_symm_apply θ v]
      rw [show θ.symm.toLinearMap (ggDepAh p N i) = h i by
        change (θ.symm : GGDepAE p N → V) (ggDepAh p N i) = h i
        rw [← hθh i, LinearEquiv.symm_apply_apply]]
      rw [← hθα' i v]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · refine ⟨ra1, Or.inr (Or.inl rfl), ?_⟩
        ext v
        rw [hra1_apply v]
        simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
        rw [l05nPT_symm_apply θ v]
        rw [show θ.symm.toLinearMap ha1' = ha1 by
          change (θ.symm : GGDepAE p N → V) ha1' = ha1
          rw [ha1'_def, LinearEquiv.symm_apply_apply]]
        rw [hαa1'dot' (θ.toLinearMap v), l05nPT_symm_apply θ v]
      · refine ⟨ra2, Or.inr (Or.inr rfl), ?_⟩
        ext v
        rw [hra2_apply v]
        simp only [LinearMap.comp_apply, l05nPT_refl_apply, map_sub, map_smul]
        rw [l05nPT_symm_apply θ v]
        rw [show θ.symm.toLinearMap ha2' = ha2 by
          change (θ.symm : GGDepAE p N → V) ha2' = ha2
          rw [ha2'_def, LinearEquiv.symm_apply_apply]]
        rw [hαa2'dot' (θ.toLinearMap v), l05nPT_symm_apply θ v]
  obtain ⟨g', hg'T, hg'eq⟩ := l05nD6_closure_conj (S := S) (T := T) θ hgen g hgS
  exact hnt g' hg'T ⟨by
      rw [l05nPT_conj_finrank θ g g' hg'eq]
      exact htv.1,
    l05nPT_conj_move_fix θ g g' hg'eq htv.2⟩

end CFSG.StandardType

end
