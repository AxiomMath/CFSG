module

public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeSurvivor
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeBasic

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def l05nDW_conjHom {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) :
    Module.End (ZMod 3) (GGDepAE 3 6) →* Module.End (ZMod 3) V where
  toFun m := θ.symm.toLinearMap.comp (m.comp θ.toLinearMap)
  map_one' := by
    ext v
    simp [Module.End.one_eq_id]
  map_mul' m n := by
    ext v
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply]
    rw [l05nPT_apply_symm θ]

private theorem l05nDW_conjHom_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    (m : Module.End (ZMod 3) (GGDepAE 3 6)) (v : V) :
    l05nDW_conjHom θ m v = θ.symm (m (θ v)) := rfl

private theorem l05nDW_conjHom_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    (m : Module.End (ZMod 3) (GGDepAE 3 6)) :
    l05nDW_conjHom θ m = θ.symm.toLinearMap.comp (m.comp θ.toLinearMap) := rfl

private theorem l05nDW_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot, smul_eq_mul]

private theorem l05nDW_coe_pow {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (e : V ≃ₗ[ZMod 3] V) (n : ℕ) :
    ((e ^ n : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) = (e : V →ₗ[ZMod 3] V) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private theorem l05nDW_linearEquiv_ext {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {e f : V ≃ₗ[ZMod 3] V}
    (h : (e : V →ₗ[ZMod 3] V) = (f : V →ₗ[ZMod 3] V)) : e = f := by
  apply LinearEquiv.coe_injective
  funext v
  exact congrArg (fun m : V →ₗ[ZMod 3] V => m v) h

private theorem l05nDW_conj_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    {S : Set (Module.End (ZMod 3) (GGDepAE 3 6))} {T : Set (V ≃ₗ[ZMod 3] V)}
    (hgen : ∀ z ∈ S, ∃ g ∈ Subgroup.closure T,
      (g : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ z) :
    ∀ y ∈ Submonoid.closure S, ∃ g ∈ Subgroup.closure T,
      (g : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ y := by
  intro y hy
  induction hy using Submonoid.closure_induction with
  | mem z hz => exact hgen z hz
  | one =>
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [map_one, LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  | mul y z hy hz ihy ihz =>
      obtain ⟨gy, hgy, egy⟩ := ihy
      obtain ⟨gz, hgz, egz⟩ := ihz
      refine ⟨gy * gz, Subgroup.mul_mem _ hgy hgz, ?_⟩
      rw [map_mul, LinearEquiv.coe_toLinearMap_mul, egy, egz]

private lemma l05nDW_transport {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {S : Set (Module.End (ZMod 3) (GGDepAE 3 6))} {T : Set (V ≃ₗ[ZMod 3] V)}
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    (hgen : ∀ y ∈ S, ∃ g' ∈ T, (g' : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ y)
    {g : Module.End (ZMod 3) (GGDepAE 3 6)} (hgS : g ∈ Submonoid.closure S)
    (htv : GGDepAIsTv g)
    (hnt : ∀ g ∈ Subgroup.closure T,
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) : False := by
  have hgen' : ∀ y ∈ S, ∃ g' ∈ Subgroup.closure T,
      (g' : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ y := by
    intro y hy
    obtain ⟨g', hg'T, hg'eq⟩ := hgen y hy
    exact ⟨g', Subgroup.subset_closure hg'T, hg'eq⟩
  obtain ⟨g', hg'T, hg'eq⟩ := l05nDW_conj_mem θ hgen' g hgS
  have hg'eq' : (g' : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap.comp (g.comp θ.toLinearMap) :=
    hg'eq.trans (l05nDW_conjHom_eq θ g)
  exact hnt g' hg'T ⟨by
      rw [l05nPT_conj_finrank θ g g' hg'eq']
      exact htv.1,
    l05nPT_conj_move_fix θ g g' hg'eq' htv.2⟩

private theorem l05nDW_e6data_of_orbit {S : Set (Module.End (ZMod 3) (GGDepAE 3 6))}
    (h : GGTWDE6Orbit S) : GGDepAWeylE6Data S := by
  obtain ⟨s, w, hrefl, hsmem, hgen, hrel, hwmem, hinj⟩ := h
  exact ⟨s, w, hsmem, hrefl, hrel, hgen, hwmem, hinj⟩

private lemma l05nDW_conj_frame {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (6 - 1) → V} {α : Fin (6 - 1) → Module.Dual (ZMod 3) V}
    (r : Fin (6 - 1) → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (hθh : ∀ i, θ (h i) = ggDepAh 3 6 i)
    (hθα : ∀ i v, α i v = ggDepAdot (ggDepAα 3 6 i) (θ v)) (i : Fin (6 - 1)) :
    (r i : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ (ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) := by
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod 3] V) v = v - α i v • h i := fun i v => hr i v
  ext v
  rw [hr_apply i v, l05nDW_conjHom_apply, l05nPT_refl_apply, map_sub, map_smul,
    LinearEquiv.symm_apply_apply]
  rw [show (θ.symm : GGDepAE 3 6 → V) (ggDepAh 3 6 i) = h i by
    rw [← hθh i, LinearEquiv.symm_apply_apply]]
  rw [← hθα i v]

private lemma l05nDW_conj_added {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ra : V ≃ₗ[ZMod 3] V) (ha : V) (αa : Module.Dual (ZMod 3) V)
    (hra : ∀ v, ra v = v - αa v • ha)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (ha' : GGDepAE 3 6) (hha' : ha' = θ ha)
    (αa' : GGDepAE 3 6) (hαa' : ∀ y, ggDepAdot αa' y = αa (θ.symm y)) :
    (ra : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ (ggDepARefl ha' αa') := by
  rw [hha']
  have hra_apply : ∀ v, (ra : V →ₗ[ZMod 3] V) v = v - αa v • ha := fun v => hra v
  ext v
  rw [hra_apply v, l05nDW_conjHom_apply, l05nPT_refl_apply, map_sub, map_smul,
    LinearEquiv.symm_apply_apply]
  rw [LinearEquiv.symm_apply_apply]
  rw [hαa' (θ v), LinearEquiv.symm_apply_apply]

theorem ggTWD_weyl_one_36
    (hcells : GGTWDCells36Orb) {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) {A : Subgroup (MulAut ↥Bs)} {h : Fin (6 - 1) → V}
    {α : Fin (6 - 1) → Module.Dual (ZMod 3) V} {x : V} (F : GGDepAFrame 3 6 h α x)
    (hdim : Module.finrank (ZMod 3) V = 6) (r : Fin (6 - 1) → (V ≃ₗ[ZMod 3] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (ra : V ≃ₗ[ZMod 3] V) (ha : V)
    (αa : Module.Dual (ZMod 3) V) (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2)
    (hw : αa x ≠ 0) (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure (Set.range r ∪ {ra}))
    (pos : GGTWPos) (c0 : Fin (6 - 1)) (m n : ℤ) (hpat : GGTWPat1 6 pos c0.val m n)
    (hpair : ∀ c : Fin (6 - 1), ggTWInJ 6 pos c.val →
      αa (h c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        α c ha = (if c = c0 then (n : ZMod 3) else 0))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) :
    GGWeylReflectionGroup 3 A := by
  classical
  have hcells' : GGTWDCellsOr 3 6 GGTWDE6Orbit := hcells
  have hc1 := hcells'.1
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepA_model_iso F hdim
  obtain ⟨αa', hαa'dot⟩ := l05nPT_dot_of_comp_symm (p := 3) (N := 6) αa θ
  set ha' : GGDepAE 3 6 := θ ha with ha'_def
  have hpair' : GGTWDPairs1 3 6 pos c0 m n ha' αa' := by
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
  have hperm := ggDepAThree_stab F r hr
  rcases hc1 pos c0 m n hpat ha' αa' hpair' hha hhw with ⟨g, hgS, htv⟩ | horb
  · let S : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
      Set.range (fun i : Fin (6 - 1) => ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪
        {ggDepARefl ha' αa'}
    let T : Set (V ≃ₗ[ZMod 3] V) := Set.range r ∪ {ra}
    have hgen : ∀ y ∈ S, ∃ g' ∈ T, (g' : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ y := by
      intro y hy
      dsimp only [S] at hy
      rcases hy with ⟨i, rfl⟩ | hy
      · exact ⟨r i, Or.inl ⟨i, rfl⟩, l05nDW_conj_frame r hr θ hθh hθα i⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨ra, Or.inr rfl, l05nDW_conj_added ra ha αa hra θ ha' ha'_def αa' hαa'dot⟩
    exact (l05nDW_transport θ hgen hgS htv hnt).elim
  · have hdata : GGDepAWeylE6Data (Set.range (fun i : Fin (6 - 1) =>
        ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪ {ggDepARefl ha' αa'}) :=
      l05nDW_e6data_of_orbit horb
    refine ggDepAThree_survivor_weyl ι F r hr ra ha αa hra hA hperm θ hθh hθα hθx αa'
      hαa'dot ?_
    simpa only [ha'_def] using hdata

private theorem l05nDW_survivor_two
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    {A : Subgroup (MulAut ↥Bs)} {h : Fin (6 - 1) → V} {α : Fin (6 - 1) → Module.Dual (ZMod 3) V}
    {x : V} (r : Fin (6 - 1) → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra1 ra2 : V ≃ₗ[ZMod 3] V) (ha1 ha2 : V) (αa1 αa2 : Module.Dual (ZMod 3) V)
    (hra1 : ∀ v, ra1 v = v - αa1 v • ha1) (hra2 : ∀ v, ra2 v = v - αa2 v • ha2)
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure (Set.range r ∪ {ra1, ra2}))
    (hperm : ∃ H : Subgroup (V ≃ₗ[ZMod 3] V), H ≤ Subgroup.closure (Set.range r) ∧
      (∀ g ∈ H, g x = x) ∧ 720 ≤ Nat.card H)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (hθh : ∀ i, θ (h i) = ggDepAh 3 6 i)
    (hθα : ∀ i v, α i v = ggDepAdot (ggDepAα 3 6 i) (θ v)) (hθx : θ x = ggDepAx 3 6)
    (αa1' : GGDepAE 3 6) (hαa1' : ∀ y, ggDepAdot αa1' y = αa1 (θ.symm y))
    (αa2' : GGDepAE 3 6) (hαa2' : ∀ y, ggDepAdot αa2' y = αa2 (θ.symm y))
    (hdata : GGDepAWeylE6Data (Set.range (fun i : Fin (6 - 1) =>
      ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪
        {ggDepARefl (θ ha1) αa1', ggDepARefl (θ ha2) αa2'})) :
    GGWeylReflectionGroup 3 A := by
  classical
  simp only [GGDepAWeylE6Data] at hdata
  obtain ⟨s', w', hs'mem, hs'refl, hrel', hgen'mem, hw'mem, hinj'⟩ := hdata
  let S0 : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
    Set.range (fun i : Fin (6 - 1) => ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪
      {ggDepARefl (θ ha1) αa1', ggDepARefl (θ ha2) αa2'}
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod 3] V) v = v - α i v • h i := fun i v => hr i v
  have hra1_apply : ∀ v, (ra1 : V →ₗ[ZMod 3] V) v = v - αa1 v • ha1 := fun v => hra1 v
  have hra2_apply : ∀ v, (ra2 : V →ₗ[ZMod 3] V) v = v - αa2 v • ha2 := fun v => hra2 v
  have hconj_i : ∀ i : Fin (6 - 1), (r i : V →ₗ[ZMod 3] V) =
      l05nDW_conjHom θ (ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) := by
    intro i
    ext v
    rw [hr_apply i v, l05nDW_conjHom_apply, l05nPT_refl_apply, map_sub, map_smul,
      LinearEquiv.symm_apply_apply]
    rw [show (θ.symm : GGDepAE 3 6 → V) (ggDepAh 3 6 i) = h i by
      rw [← hθh i, LinearEquiv.symm_apply_apply]]
    rw [← hθα i v]
  have hconj_a1 : (ra1 : V →ₗ[ZMod 3] V) =
      l05nDW_conjHom θ (ggDepARefl (θ ha1) αa1') := by
    ext v
    rw [hra1_apply v, l05nDW_conjHom_apply, l05nPT_refl_apply, map_sub, map_smul,
      LinearEquiv.symm_apply_apply]
    rw [LinearEquiv.symm_apply_apply]
    rw [hαa1' (θ v), LinearEquiv.symm_apply_apply]
  have hconj_a2 : (ra2 : V →ₗ[ZMod 3] V) =
      l05nDW_conjHom θ (ggDepARefl (θ ha2) αa2') := by
    ext v
    rw [hra2_apply v, l05nDW_conjHom_apply, l05nPT_refl_apply, map_sub, map_smul,
      LinearEquiv.symm_apply_apply]
    rw [LinearEquiv.symm_apply_apply]
    rw [hαa2' (θ v), LinearEquiv.symm_apply_apply]
  have hgen0 : ∀ z ∈ S0, ∃ g ∈ Subgroup.closure (Set.range r ∪ {ra1, ra2}),
      (g : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ z := by
    intro z hz
    dsimp only [S0] at hz
    rcases hz with ⟨i, rfl⟩ | hz
    · exact ⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩), hconj_i i⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨ra1, Subgroup.subset_closure (Or.inr (Or.inl rfl)), hconj_a1⟩
      · exact ⟨ra2, Subgroup.subset_closure (Or.inr (Or.inr rfl)), hconj_a2⟩
  let s : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i =>
    Classical.choose (l05nDW_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra1, ra2})
      hgen0 (s' i) (hs'mem i))
  have hs_mem : ∀ i, s i ∈ Subgroup.closure (Set.range r ∪ {ra1, ra2}) := fun i =>
    (Classical.choose_spec (l05nDW_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra1, ra2})
      hgen0 (s' i) (hs'mem i))).1
  have hs_conj : ∀ i, (s i : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ (s' i) := fun i =>
    (Classical.choose_spec (l05nDW_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra1, ra2})
      hgen0 (s' i) (hs'mem i))).2
  let w : Fin 72 → (V ≃ₗ[ZMod 3] V) := fun k =>
    Classical.choose (l05nDW_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra1, ra2})
      hgen0 (w' k) (hw'mem k))
  have hw_mem : ∀ k, w k ∈ Subgroup.closure (Set.range r ∪ {ra1, ra2}) := fun k =>
    (Classical.choose_spec (l05nDW_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra1, ra2})
      hgen0 (w' k) (hw'mem k))).1
  have hw_conj : ∀ k, (w k : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ (w' k) := fun k =>
    (Classical.choose_spec (l05nDW_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra1, ra2})
      hgen0 (w' k) (hw'mem k))).2
  have hsr : ∀ i, ∃ (c : V) (f : Module.Dual (ZMod 3) V),
      f c = 2 ∧ ∀ v, s i v = v - f v • c := by
    intro i
    obtain ⟨c, f, hfc, hsi⟩ := hs'refl i
    refine ⟨θ.symm c, (ggDepAform f).comp θ.toLinearMap, ?_, ?_⟩
    · rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
        l05nDW_form_apply, hfc]
    · intro v
      change (s i : V →ₗ[ZMod 3] V) v = v - ((ggDepAform f).comp θ.toLinearMap) v • θ.symm c
      rw [hs_conj i, l05nDW_conjHom_apply, hsi, l05nPT_refl_apply, map_sub, map_smul,
        LinearEquiv.symm_apply_apply, LinearMap.comp_apply, l05nDW_form_apply]
      rfl
  have hrel : ∀ i j, (s i * s j) ^ (CoxeterMatrix.E₆ i j) = 1 := by
    intro i j
    have hpow : LinearEquiv.toLinearMap ((s i * s j : V ≃ₗ[ZMod 3] V) ^
        (CoxeterMatrix.E₆ i j)) = 1 := by
      rw [l05nDW_coe_pow, LinearEquiv.coe_toLinearMap_mul, hs_conj i, hs_conj j, ← map_mul,
        ← map_pow, hrel' i j, map_one]
    exact l05nDW_linearEquiv_ext hpow
  have hgen_s : ∀ z ∈ Set.range s', ∃ g ∈ Subgroup.closure (Set.range s),
      (g : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ z := by
    rintro z ⟨i, rfl⟩
    exact ⟨s i, Subgroup.subset_closure ⟨i, rfl⟩, hs_conj i⟩
  have hgen : ∀ g ∈ Set.range r ∪ {ra1, ra2}, g ∈ Subgroup.closure (Set.range s) := by
    intro g hg
    rcases hg with ⟨i, rfl⟩ | hg
    · have hz0 : ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i) ∈ S0 := Or.inl ⟨i, rfl⟩
      obtain ⟨g', hg'mem, hg'eq⟩ := l05nDW_conj_mem (θ := θ) (S := Set.range s')
        (T := Set.range s) hgen_s (ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i))
        (hgen'mem _ hz0)
      have hgr : g' = r i := by
        ext v
        change (g' : V →ₗ[ZMod 3] V) v = (r i : V →ₗ[ZMod 3] V) v
        rw [hg'eq, hconj_i i]
      rwa [← hgr]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · have hz0 : ggDepARefl (θ ha1) αa1' ∈ S0 := Or.inr (Or.inl rfl)
        obtain ⟨g', hg'mem, hg'eq⟩ := l05nDW_conj_mem (θ := θ) (S := Set.range s')
          (T := Set.range s) hgen_s (ggDepARefl (θ ha1) αa1') (hgen'mem _ hz0)
        have hgr : g' = ra1 := by
          apply l05nDW_linearEquiv_ext
          rw [hg'eq, hconj_a1]
        rw [hg, ← hgr]
        exact hg'mem
      · have hz0 : ggDepARefl (θ ha2) αa2' ∈ S0 := Or.inr (Or.inr rfl)
        obtain ⟨g', hg'mem, hg'eq⟩ := l05nDW_conj_mem (θ := θ) (S := Set.range s')
          (T := Set.range s) hgen_s (ggDepARefl (θ ha2) αa2') (hgen'mem _ hz0)
        have hgr : g' = ra2 := by
          apply l05nDW_linearEquiv_ext
          rw [hg'eq, hconj_a2]
        rw [hg, ← hgr]
        exact hg'mem
  have hinj : Function.Injective (fun k => w k x) := by
    intro k l hkl
    apply hinj'
    have hk : w k x = θ.symm (w' k (ggDepAx 3 6)) := by
      change (w k : V →ₗ[ZMod 3] V) x = θ.symm (w' k (ggDepAx 3 6))
      rw [hw_conj k, l05nDW_conjHom_apply, hθx]
    have hl : w l x = θ.symm (w' l (ggDepAx 3 6)) := by
      change (w l : V →ₗ[ZMod 3] V) x = θ.symm (w' l (ggDepAx 3 6))
      rw [hw_conj l, l05nDW_conjHom_apply, hθx]
    exact θ.symm.injective (hk.symm.trans (hkl.trans hl))
  have hstab : ∃ H : Subgroup (V ≃ₗ[ZMod 3] V),
      H ≤ Subgroup.closure (Set.range r ∪ {ra1, ra2}) ∧ (∀ g ∈ H, g x = x) ∧
        720 ≤ Nat.card H := by
    obtain ⟨H, hHle, hHfix, hHcard⟩ := hperm
    exact ⟨H, hHle.trans (Subgroup.closure_mono Set.subset_union_left), hHfix, hHcard⟩
  exact ggDepAThree_surv_weyl ι (Set.range r ∪ {ra1, ra2}) hA x s w hs_mem hsr hrel hgen hw_mem
    hinj hstab

theorem ggTWD_weyl_two_36
    (hcells : GGTWDCells36Orb) {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) {A : Subgroup (MulAut ↥Bs)} {h : Fin (6 - 1) → V}
    {α : Fin (6 - 1) → Module.Dual (ZMod 3) V} {x : V} (F : GGDepAFrame 3 6 h α x)
    (hdim : Module.finrank (ZMod 3) V = 6) (r : Fin (6 - 1) → (V ≃ₗ[ZMod 3] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (ra1 ra2 : V ≃ₗ[ZMod 3] V) (ha1 ha2 : V)
    (αa1 αa2 : Module.Dual (ZMod 3) V) (hra1 : ∀ v, ra1 v = v - αa1 v • ha1)
    (hra2 : ∀ v, ra2 v = v - αa2 v • ha2) (hw : αa1 x ≠ 0 ∨ αa2 x ≠ 0)
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure (Set.range r ∪ {ra1, ra2}))
    (pos : GGTWPos) (c : Fin (6 - 1)) (c₂ : Option (Fin (6 - 1)))
    (hpat : GGTWPat2 6 pos c.val (c₂.map Fin.val))
    (hpair : (∀ c' : Fin (6 - 1), ggTWInJ 6 pos c'.val →
        αa1 (h c') = (if c' = c then -1 else 0) ∧ α c' ha1 = (if c' = c then -1 else 0) ∧
          αa2 (h c') = (if some c' = c₂ then -1 else 0) ∧
            α c' ha2 = (if some c' = c₂ then -1 else 0)) ∧
      αa1 ha2 = (if c₂ = none then -1 else 0) ∧ αa2 ha1 = (if c₂ = none then -1 else 0) ∧
        αa1 ha1 = 2 ∧ αa2 ha2 = 2)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra1, ra2}),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) :
    GGWeylReflectionGroup 3 A := by
  classical
  have hcells' : GGTWDCellsOr 3 6 GGTWDE6Orbit := hcells
  have hc2 := hcells'.2
  obtain ⟨θ, hθh, hθα, hθx⟩ := ggDepA_model_iso F hdim
  obtain ⟨αa1', hαa1'dot⟩ := l05nPT_dot_of_comp_symm (p := 3) (N := 6) αa1 θ
  obtain ⟨αa2', hαa2'dot⟩ := l05nPT_dot_of_comp_symm (p := 3) (N := 6) αa2 θ
  set ha1' : GGDepAE 3 6 := θ ha1 with ha1'_def
  set ha2' : GGDepAE 3 6 := θ ha2 with ha2'_def
  have hpair' : GGTWDPairs2 3 6 pos c c₂ ha1' αa1' ha2' αa2' := by
    obtain ⟨hJ, h12, h21, h11, h22⟩ := hpair
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c' hc'
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hαa1'dot]
        rw [show θ.symm (ggDepAh 3 6 c') = h c' by
          rw [← hθh c', LinearEquiv.symm_apply_apply]]
        exact (hJ c' hc').1
      · rw [ha1'_def, ← hθα c' ha1]
        exact (hJ c' hc').2.1
      · rw [hαa2'dot]
        rw [show θ.symm (ggDepAh 3 6 c') = h c' by
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
  have hhw : ggDepAdot αa1' (ggDepAx 3 6) ≠ 0 ∨ ggDepAdot αa2' (ggDepAx 3 6) ≠ 0 := by
    rcases hw with hw | hw
    · left
      rw [hαa1'dot]
      rw [show θ.symm (ggDepAx 3 6) = x by
        rw [← hθx, LinearEquiv.symm_apply_apply]]
      exact hw
    · right
      rw [hαa2'dot]
      rw [show θ.symm (ggDepAx 3 6) = x by
        rw [← hθx, LinearEquiv.symm_apply_apply]]
      exact hw
  have hperm := ggDepAThree_stab F r hr
  rcases hc2 pos c c₂ hpat ha1' αa1' ha2' αa2' hpair' hhw with ⟨g, hgS, htv⟩ | horb
  · let S : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
      Set.range (fun i : Fin (6 - 1) => ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪
        {ggDepARefl ha1' αa1', ggDepARefl ha2' αa2'}
    let T : Set (V ≃ₗ[ZMod 3] V) := Set.range r ∪ {ra1, ra2}
    have hgen : ∀ y ∈ S, ∃ g' ∈ T, (g' : V →ₗ[ZMod 3] V) = l05nDW_conjHom θ y := by
      intro y hy
      dsimp only [S] at hy
      rcases hy with ⟨i, rfl⟩ | hy
      · exact ⟨r i, Or.inl ⟨i, rfl⟩, l05nDW_conj_frame r hr θ hθh hθα i⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact ⟨ra1, Or.inr (Or.inl rfl),
            l05nDW_conj_added ra1 ha1 αa1 hra1 θ ha1' ha1'_def αa1' hαa1'dot⟩
        · exact ⟨ra2, Or.inr (Or.inr rfl),
            l05nDW_conj_added ra2 ha2 αa2 hra2 θ ha2' ha2'_def αa2' hαa2'dot⟩
    exact (l05nDW_transport θ hgen hgS htv hnt).elim
  · have hdata : GGDepAWeylE6Data (Set.range (fun i : Fin (6 - 1) =>
        ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪
          {ggDepARefl ha1' αa1', ggDepARefl ha2' αa2'}) := l05nDW_e6data_of_orbit horb
    refine l05nDW_survivor_two ι r hr ra1 ra2 ha1 ha2 αa1 αa2 hra1 hra2 hA hperm θ hθh hθα hθx
      αa1' hαa1'dot αa2' hαa2'dot ?_
    simpa only [ha1'_def, ha2'_def] using hdata

end CFSG.StandardType

end
