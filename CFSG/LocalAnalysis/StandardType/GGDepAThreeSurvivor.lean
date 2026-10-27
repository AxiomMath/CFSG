module

public import CFSG.LocalAnalysis.StandardType.GGDepAThreeSurvWeyl
public import CFSG.LocalAnalysis.StandardType.GGDepAThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def lr7sv_conjHom {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
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

private theorem lr7sv_conjHom_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    (m : Module.End (ZMod 3) (GGDepAE 3 6)) (v : V) :
    lr7sv_conjHom θ m v = θ.symm (m (θ v)) := rfl

private theorem lr7sv_form_apply {p N : ℕ} (f v : GGDepAE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot, smul_eq_mul]

private theorem lr7sv_coe_pow {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (e : V ≃ₗ[ZMod 3] V) (n : ℕ) :
    ((e ^ n : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) = (e : V →ₗ[ZMod 3] V) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private theorem lr7sv_linearEquiv_ext {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {e f : V ≃ₗ[ZMod 3] V}
    (h : (e : V →ₗ[ZMod 3] V) = (f : V →ₗ[ZMod 3] V)) : e = f := by
  apply LinearEquiv.coe_injective
  funext v
  exact congrArg (fun m : V →ₗ[ZMod 3] V => m v) h

private theorem lr7sv_conj_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    {S : Set (Module.End (ZMod 3) (GGDepAE 3 6))} {T : Set (V ≃ₗ[ZMod 3] V)}
    (hgen : ∀ z ∈ S, ∃ g ∈ Subgroup.closure T,
      (g : V →ₗ[ZMod 3] V) = lr7sv_conjHom θ z) :
    ∀ y ∈ Submonoid.closure S, ∃ g ∈ Subgroup.closure T,
      (g : V →ₗ[ZMod 3] V) = lr7sv_conjHom θ y := by
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

theorem ggDepAThree_survivor_weyl
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    {A : Subgroup (MulAut ↥Bs)} {h : Fin (6 - 1) → V} {α : Fin (6 - 1) → Module.Dual (ZMod 3) V}
    {x : V} (F : GGDepAFrame 3 6 h α x) (r : Fin (6 - 1) → (V ≃ₗ[ZMod 3] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (ra : V ≃ₗ[ZMod 3] V) (ha : V)
    (αa : Module.Dual (ZMod 3) V) (hra : ∀ v, ra v = v - αa v • ha)
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure (Set.range r ∪ {ra}))
    (hperm : ∃ H : Subgroup (V ≃ₗ[ZMod 3] V), H ≤ Subgroup.closure (Set.range r) ∧
      (∀ g ∈ H, g x = x) ∧ 720 ≤ Nat.card H)
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (hθh : ∀ i, θ (h i) = ggDepAh 3 6 i)
    (hθα : ∀ i v, α i v = ggDepAdot (ggDepAα 3 6 i) (θ v)) (hθx : θ x = ggDepAx 3 6)
    (αa' : GGDepAE 3 6) (hαa' : ∀ y, ggDepAdot αa' y = αa (θ.symm y))
    (hdata : GGDepAWeylE6Data (Set.range (fun i : Fin (6 - 1) =>
      ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪ {ggDepARefl (θ ha) αa'})) :
    GGWeylReflectionGroup 3 A := by
  classical
  simp only [GGDepAWeylE6Data] at hdata
  obtain ⟨s', w', hs'mem, hs'refl, hrel', hgen'mem, hw'mem, hinj'⟩ := hdata
  let S0 : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
    Set.range (fun i : Fin (6 - 1) => ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪
      {ggDepARefl (θ ha) αa'}
  have hr_apply : ∀ i v, (r i : V →ₗ[ZMod 3] V) v = v - α i v • h i := fun i v => hr i v
  have hra_apply : ∀ v, (ra : V →ₗ[ZMod 3] V) v = v - αa v • ha := fun v => hra v
  have hconj_i : ∀ i : Fin (6 - 1), (r i : V →ₗ[ZMod 3] V) =
      lr7sv_conjHom θ (ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) := by
    intro i
    ext v
    rw [hr_apply i v, lr7sv_conjHom_apply, l05nPT_refl_apply, map_sub, map_smul,
      LinearEquiv.symm_apply_apply]
    rw [show (θ.symm : GGDepAE 3 6 → V) (ggDepAh 3 6 i) = h i by
      rw [← hθh i, LinearEquiv.symm_apply_apply]]
    rw [← hθα i v]
  have hconj_a : (ra : V →ₗ[ZMod 3] V) = lr7sv_conjHom θ (ggDepARefl (θ ha) αa') := by
    ext v
    rw [hra_apply v, lr7sv_conjHom_apply, l05nPT_refl_apply, map_sub, map_smul,
      LinearEquiv.symm_apply_apply]
    rw [LinearEquiv.symm_apply_apply]
    rw [hαa' (θ v), LinearEquiv.symm_apply_apply]
  have hgen0 : ∀ z ∈ S0, ∃ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      (g : V →ₗ[ZMod 3] V) = lr7sv_conjHom θ z := by
    intro z hz
    rcases hz with ⟨i, rfl⟩ | hz
    · exact ⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩), hconj_i i⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨ra, Subgroup.subset_closure (Or.inr rfl), hconj_a⟩
  let s : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i =>
    Classical.choose (lr7sv_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra})
      hgen0 (s' i) (hs'mem i))
  have hs_mem : ∀ i, s i ∈ Subgroup.closure (Set.range r ∪ {ra}) := fun i =>
    (Classical.choose_spec (lr7sv_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra})
      hgen0 (s' i) (hs'mem i))).1
  have hs_conj : ∀ i, (s i : V →ₗ[ZMod 3] V) = lr7sv_conjHom θ (s' i) := fun i =>
    (Classical.choose_spec (lr7sv_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra})
      hgen0 (s' i) (hs'mem i))).2
  let w : Fin 72 → (V ≃ₗ[ZMod 3] V) := fun k =>
    Classical.choose (lr7sv_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra})
      hgen0 (w' k) (hw'mem k))
  have hw_mem : ∀ k, w k ∈ Subgroup.closure (Set.range r ∪ {ra}) := fun k =>
    (Classical.choose_spec (lr7sv_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra})
      hgen0 (w' k) (hw'mem k))).1
  have hw_conj : ∀ k, (w k : V →ₗ[ZMod 3] V) = lr7sv_conjHom θ (w' k) := fun k =>
    (Classical.choose_spec (lr7sv_conj_mem (θ := θ) (S := S0) (T := Set.range r ∪ {ra})
      hgen0 (w' k) (hw'mem k))).2
  have hsr : ∀ i, ∃ (c : V) (f : Module.Dual (ZMod 3) V),
      f c = 2 ∧ ∀ v, s i v = v - f v • c := by
    intro i
    obtain ⟨c, f, hfc, hsi⟩ := hs'refl i
    refine ⟨θ.symm c, (ggDepAform f).comp θ.toLinearMap, ?_, ?_⟩
    · rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
        lr7sv_form_apply, hfc]
    · intro v
      change (s i : V →ₗ[ZMod 3] V) v =
        v - ((ggDepAform f).comp θ.toLinearMap) v • θ.symm c
      rw [hs_conj i, lr7sv_conjHom_apply, hsi, l05nPT_refl_apply, map_sub, map_smul,
        LinearEquiv.symm_apply_apply, LinearMap.comp_apply, lr7sv_form_apply]
      rfl
  have hrel : ∀ i j, (s i * s j) ^ (CoxeterMatrix.E₆ i j) = 1 := by
    intro i j
    have hpow : LinearEquiv.toLinearMap ((s i * s j : V ≃ₗ[ZMod 3] V) ^
        (CoxeterMatrix.E₆ i j)) = 1 := by
      rw [lr7sv_coe_pow, LinearEquiv.coe_toLinearMap_mul, hs_conj i, hs_conj j, ← map_mul,
        ← map_pow, hrel' i j, map_one]
    exact lr7sv_linearEquiv_ext hpow
  have hgen_s : ∀ z ∈ Set.range s', ∃ g ∈ Subgroup.closure (Set.range s),
      (g : V →ₗ[ZMod 3] V) = lr7sv_conjHom θ z := by
    rintro z ⟨i, rfl⟩
    exact ⟨s i, Subgroup.subset_closure ⟨i, rfl⟩, hs_conj i⟩
  have hgen : ∀ g ∈ Set.range r ∪ {ra}, g ∈ Subgroup.closure (Set.range s) := by
    intro g hg
    rcases hg with ⟨i, rfl⟩ | hg
    · have hz0 : ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i) ∈ S0 := Or.inl ⟨i, rfl⟩
      obtain ⟨g', hg'mem, hg'eq⟩ := lr7sv_conj_mem (θ := θ) (S := Set.range s')
        (T := Set.range s) hgen_s (ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i))
        (hgen'mem (ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) hz0)
      have hgr : g' = r i := by
        ext v
        change (g' : V →ₗ[ZMod 3] V) v = (r i : V →ₗ[ZMod 3] V) v
        rw [hg'eq, hconj_i i]
      rwa [← hgr]
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      have hza : ggDepARefl (θ ha) αa' ∈ S0 := Or.inr rfl
      obtain ⟨g', hg'mem, hg'eq⟩ := lr7sv_conj_mem (θ := θ) (S := Set.range s')
        (T := Set.range s) hgen_s (ggDepARefl (θ ha) αa')
        (hgen'mem (ggDepARefl (θ ha) αa') hza)
      have hgr : g' = ra := by
        ext v
        change (g' : V →ₗ[ZMod 3] V) v = (ra : V →ₗ[ZMod 3] V) v
        rw [hg'eq, hconj_a]
      rwa [← hgr]
  have hinj : Function.Injective (fun k => w k x) := by
    intro k l hkl
    apply hinj'
    have hk : w k x = θ.symm (w' k (ggDepAx 3 6)) := by
      change (w k : V →ₗ[ZMod 3] V) x = θ.symm (w' k (ggDepAx 3 6))
      rw [hw_conj k, lr7sv_conjHom_apply, hθx]
    have hl : w l x = θ.symm (w' l (ggDepAx 3 6)) := by
      change (w l : V →ₗ[ZMod 3] V) x = θ.symm (w' l (ggDepAx 3 6))
      rw [hw_conj l, lr7sv_conjHom_apply, hθx]
    exact θ.symm.injective (hk.symm.trans (hkl.trans hl))
  have hstab : ∃ H : Subgroup (V ≃ₗ[ZMod 3] V),
      H ≤ Subgroup.closure (Set.range r ∪ {ra}) ∧ (∀ g ∈ H, g x = x) ∧ 720 ≤ Nat.card H := by
    obtain ⟨H, hHle, hHfix, hHcard⟩ := hperm
    exact ⟨H, hHle.trans (Subgroup.closure_mono Set.subset_union_left), hHfix, hHcard⟩
  exact ggDepAThree_surv_weyl ι (Set.range r ∪ {ra}) hA x s w hs_mem hsr hrel hgen hw_mem hinj
    hstab

end CFSG.StandardType
