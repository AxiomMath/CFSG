module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGHLLines
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable def l05nKXconj {p N : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) :
    (V ≃ₗ[ZMod p] V) →* Module.End (ZMod p) (GGTWE p N) where
  toFun g := (θ : V →ₗ[ZMod p] GGTWE p N).comp
    ((g : V →ₗ[ZMod p] V).comp (θ.symm : GGTWE p N →ₗ[ZMod p] V))
  map_one' := by
    ext w
    simp [LinearMap.comp_apply]
  map_mul' f g := by
    ext w
    simp [LinearMap.comp_apply, LinearEquiv.mul_apply]

lemma l05nKXconj_apply {p N : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) (g : V ≃ₗ[ZMod p] V) (v : V) :
    l05nKXconj θ g (θ v) = θ (g v) := by
  simp [l05nKXconj, LinearMap.comp_apply]

lemma l05nKXconj_injective {p N : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) :
    Function.Injective (l05nKXconj θ) := by
  intro g h hgh
  ext v
  have h2 := congrArg (fun e => e (θ v)) hgh
  simp only [l05nKXconj_apply] at h2
  exact θ.injective h2

lemma l05nKXconj_rF {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    (i : Fin (N - 1)) :
    l05nKXconj θ (rF i) = ggTWRefl (ggTWh p N i) (ggTWα p N i) := by
  apply LinearMap.ext
  intro w
  rw [← θ.apply_symm_apply w, l05nKXconj_apply, hrF, θ.apply_symm_apply]

lemma l05nKXconj_rN {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (news : Set (GGTWE p N × GGTWE p N))
    (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v))
    (t : GGTWE p N × GGTWE p N) (ht : t ∈ news) :
    l05nKXconj θ (rN t) = ggTWRefl t.1 t.2 := by
  apply LinearMap.ext
  intro w
  rw [← θ.apply_symm_apply w, l05nKXconj_apply, hrN t ht, θ.apply_symm_apply]

lemma l05nKX_closure_forward {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N)
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    (news : Set (GGTWE p N × GGTWE p N)) (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v))
    {s : Module.End (ZMod p) (GGTWE p N)}
    (hs : s ∈ Submonoid.closure (ggTWGens p N news)) :
    ∃ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), l05nKXconj θ g = s := by
  refine Submonoid.closure_induction (motive := fun s _ => ∃ g ∈ Subgroup.closure
      (Set.range rF ∪ rN '' news), l05nKXconj θ g = s) ?_ ?_ ?_ hs
  · intro x hx
    rw [ggTWGens] at hx
    rcases hx with hx | hx
    · rw [ggTWFrameGens] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ⟨rF i, Subgroup.subset_closure (Set.mem_union_left _ ⟨i, rfl⟩),
        l05nKXconj_rF θ rF hrF i⟩
    · obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨rN t, Subgroup.subset_closure (Set.mem_union_right _ ⟨t, ht, rfl⟩),
        l05nKXconj_rN θ news rN hrN t ht⟩
  · exact ⟨1, Subgroup.one_mem _, map_one (l05nKXconj θ)⟩
  · intro a b _ _ ha hb
    obtain ⟨ga, hga, hga'⟩ := ha
    obtain ⟨gb, hgb, hgb'⟩ := hb
    exact ⟨ga * gb, Subgroup.mul_mem _ hga hgb, by rw [map_mul, hga', hgb']⟩

lemma l05nKX_frame_word {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N)
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    {w : Module.End (ZMod p) (GGTWE p N)}
    (hw : w ∈ Submonoid.closure (ggTWFrameGens p N)) :
    ∃ g ∈ Submonoid.closure (Set.range rF), l05nKXconj θ g = w := by
  refine Submonoid.closure_induction (motive := fun w _ =>
      ∃ g ∈ Submonoid.closure (Set.range rF), l05nKXconj θ g = w) ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨rF i, Submonoid.subset_closure ⟨i, rfl⟩, l05nKXconj_rF θ rF hrF i⟩
  · exact ⟨1, Submonoid.one_mem _, map_one (l05nKXconj θ)⟩
  · intro a b _ _ ha hb
    obtain ⟨ga, hga, hga'⟩ := ha
    obtain ⟨gb, hgb, hgb'⟩ := hb
    exact ⟨ga * gb, Submonoid.mul_mem _ hga hgb, by rw [map_mul, hga', hgb']⟩

lemma l05nKX_frame_mem {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N)
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    {w : V ≃ₗ[ZMod p] V} (hw : w ∈ Submonoid.closure (Set.range rF)) :
    l05nKXconj θ w ∈ Submonoid.closure (ggTWFrameGens p N) := by
  refine Submonoid.closure_induction (motive := fun w _ =>
      l05nKXconj θ w ∈ Submonoid.closure (ggTWFrameGens p N)) ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    rw [l05nKXconj_rF θ rF hrF i]
    exact Submonoid.subset_closure ⟨i, rfl⟩
  · rw [map_one]; exact Submonoid.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Submonoid.mul_mem _ ha hb

lemma l05nKX_form_apply {p N : ℕ} (f v : GGTWE p N) :
    ggDepAform f v = ggDepAdot f v := by
  simp [ggDepAform, ggDepAdot]

lemma l05nKX_form_ne_zero {p N : ℕ} (f : GGTWE p N) (hf : f ≠ 0) :
    ggDepAform f ≠ 0 := by
  intro h
  apply hf
  ext j
  have h1 := congrArg (fun g : GGTWE p N →ₗ[ZMod p] ZMod p => g (Pi.single j 1)) h
  rw [l05nKX_form_apply] at h1
  have h2 : ggDepAdot f (Pi.single j 1) = f j := by
    rw [ggDepAdot, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h2] at h1
  simpa using h1

lemma l05nKX_refl_apply {p N : ℕ} (c f v : GGTWE p N) :
    ggDepARefl c f v = v - ggDepAdot f v • c := by
  simp [ggDepARefl, l05nKX_form_apply]

lemma l05nKX_dot_sub {p N : ℕ} (a v w : GGTWE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  rw [← l05nKX_form_apply a (v - w), map_sub, l05nKX_form_apply a v, l05nKX_form_apply a w]

lemma l05nKX_dot_smul {p N : ℕ} (a : GGTWE p N) (k : ZMod p) (v : GGTWE p N) :
    ggDepAdot a (k • v) = k * ggDepAdot a v := by
  rw [← l05nKX_form_apply a (k • v), map_smul, l05nKX_form_apply a v]
  simp

lemma l05nKX_refl_invol {p N : ℕ} (c f : GGTWE p N) (h : ggDepAdot f c = 2) :
    ggDepARefl c f * ggDepARefl c f = 1 := by
  apply LinearMap.ext; intro v
  ext j
  have hone : (1 : Module.End (ZMod p) (GGTWE p N)) v = v := rfl
  simp only [Module.End.mul_apply, l05nKX_refl_apply, Pi.sub_apply, Pi.smul_apply,
    l05nKX_dot_sub, l05nKX_dot_smul, h]
  rw [hone]
  ring

lemma l05nKX_range_refl {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {c f : GGTWE p N} (h : ggTWdot f c = 2) :
    LinearMap.range (ggTWRefl c f - LinearMap.id) = Submodule.span (ZMod p) {c} := by
  have hform : ggDepAform f c = 2 := by rw [l05nKX_form_apply]; exact h
  have hf0 : f ≠ 0 := by
    intro hf
    exact (ne_zero_of_apply_eq_two hp2 hform).2 (by rw [hf]; simp [ggDepAform])
  have hsub : ggTWRefl c f - LinearMap.id = -((ggDepAform f).smulRight c) := by
    apply LinearMap.ext; intro v
    simp [ggTWRefl, ggDepARefl]
  rw [hsub, LinearMap.range_neg, LinearMap.range_smulRight_apply (l05nKX_form_ne_zero f hf0)]

lemma l05nKX_conj_sub {p N : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (θ : V ≃ₗ[ZMod p] GGTWE p N) (g : V ≃ₗ[ZMod p] V) :
    l05nKXconj θ g - LinearMap.id =
      (θ : V →ₗ[ZMod p] GGTWE p N).comp
        (((g : V →ₗ[ZMod p] V) - LinearMap.id).comp (θ.symm : GGTWE p N →ₗ[ZMod p] V)) := by
  apply LinearMap.ext; intro w
  simp [l05nKXconj, LinearMap.sub_apply, LinearMap.comp_apply]

lemma l05nKX_range_conj {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) (g : V ≃ₗ[ZMod p] V) :
    LinearMap.range (l05nKXconj θ g - LinearMap.id) =
      Submodule.map (θ : V →ₗ[ZMod p] GGTWE p N)
        (LinearMap.range ((g : V →ₗ[ZMod p] V) - LinearMap.id)) := by
  rw [l05nKX_conj_sub, LinearMap.range_comp, LinearMap.range_comp]
  rw [show LinearMap.range (θ.symm : GGTWE p N →ₗ[ZMod p] V) = ⊤ from
    LinearMap.range_eq_top.mpr θ.symm.surjective, Submodule.map_top]

lemma l05nKX_tv_of_conj {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) {g : V ≃ₗ[ZMod p] V}
    (htv : GGTWIsTv (l05nKXconj θ g)) :
    Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w := by
  rw [GGTWIsTv, GGDepAIsTv] at htv
  constructor
  · have hfin := htv.1
    rw [l05nKX_range_conj] at hfin
    rw [LinearEquiv.finrank_map_eq] at hfin
    change Module.finrank (ZMod p)
      (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1
    exact hfin
  · intro v
    have h2 := htv.2 (θ v)
    rw [l05nKXconj_apply θ g v] at h2
    rw [← map_sub θ (g v) v] at h2
    rw [l05nKXconj_apply θ g (g v - v)] at h2
    exact θ.injective h2

lemma l05nKX_refl_of_conj {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N)
    {g : V ≃ₗ[ZMod p] V} (hr : GGTWIsRefl (l05nKXconj θ g)) : GGLinRefl g := by
  rw [GGTWIsRefl] at hr
  obtain ⟨c, f, hcf, hs⟩ := hr
  have hform : ggDepAform f c = 2 := by rw [l05nKX_form_apply]; exact hcf
  have hc0 : c ≠ 0 := (ne_zero_of_apply_eq_two hp2 hform).1
  constructor
  · apply l05nKXconj_injective θ
    rw [map_mul, hs, l05nKX_refl_invol c f hcf, map_one]
  · have h1 : Module.finrank (ZMod p)
        (LinearMap.range (ggTWRefl c f - LinearMap.id)) = 1 := by
      rw [l05nKX_range_refl hp2 hcf, finrank_span_singleton hc0]
    have h2 := h1
    rw [← hs, l05nKX_range_conj] at h2
    rw [LinearEquiv.finrank_map_eq] at h2
    change Module.finrank (ZMod p)
      (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1
    exact h2

lemma l05nKX_roots {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N)
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v)) :
    ggTWRoots (ggTWFrameGens p N) (Set.range (ggTWh p N)) =
      θ '' ggHLRoots rF (fun i => θ.symm (ggTWh p N i)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, c, hc, rfl⟩ := hv
    obtain ⟨i, rfl⟩ := hc
    obtain ⟨g, hg, hgs⟩ := l05nKX_frame_word θ rF hrF hw
    refine ⟨g (θ.symm (ggTWh p N i)), ⟨g, hg, i, rfl⟩, ?_⟩
    rw [← hgs, ← l05nKXconj_apply θ g (θ.symm (ggTWh p N i)), θ.apply_symm_apply]
  · intro hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨w, hw, i, rfl⟩ := hu
    exact ⟨l05nKXconj θ w, l05nKX_frame_mem θ rF hrF hw, ggTWh p N i, ⟨i, rfl⟩,
      by rw [← l05nKXconj_apply θ w (θ.symm (ggTWh p N i)), θ.apply_symm_apply]⟩


theorem ggTW_notKill_frame {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) {xV : V} (hx : θ xV = ggTWx p N)
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    (news : Set (GGTWE p N × GGTWE p N)) (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hHL : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g → g xV = xV →
      GGHLLines (ggHLRoots rF (fun i => θ.symm (ggTWh p N i))) xV g)
    (pos : GGTWPos) (y : GGTWE p N) : ¬ GGTWKill .frame p N pos news y := by
  intro hkill
  simp only [GGTWKill] at hkill
  rcases hkill with ⟨s, hs, htv⟩ | ⟨s, hs, hrefl, hmove⟩
  · obtain ⟨g, hg, hgs⟩ := l05nKX_closure_forward θ rF hrF news rN hrN hs
    rw [← hgs] at htv
    exact hnt g hg (l05nKX_tv_of_conj θ htv)
  · obtain ⟨g, hg, hgs⟩ := l05nKX_closure_forward θ rF hrF news rN hrN hs
    rw [← hgs] at hrefl hmove
    have hlinrefl : GGLinRefl g := l05nKX_refl_of_conj hp2 θ hrefl
    have hfx : g xV = xV := by
      have h0 : l05nKXconj θ g (ggTWx p N) = ggTWx p N := hmove.1
      rw [← hx] at h0
      rw [l05nKXconj_apply] at h0
      exact θ.injective h0
    have hlines := hHL g hg hlinrefl hfx
    have hroots := l05nKX_roots θ rF hrF
    obtain ⟨-, v, hv, hmv⟩ := hmove
    rw [hroots] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨w, hw, c, d, hc, hgu⟩ := hlines u hu
    refine hmv (θ w) ?_ c d hc ?_
    · rw [hroots]; exact ⟨w, hw, rfl⟩
    · rw [l05nKXconj_apply θ g u, hgu, map_add, map_smul, map_smul, hx]

end CFSG.StandardType
