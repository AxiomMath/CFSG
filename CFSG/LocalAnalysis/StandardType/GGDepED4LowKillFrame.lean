module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGTWKillXfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nKF_conj_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (g : V ≃ₗ[ZMod 3] V)
    (s : Module.End (ZMod 3) (GGDepAE 3 6))
    (hg : (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap.comp (s.comp θ.toLinearMap)) :
    l05nKXconj (p := 3) (N := 7) θ g = s := by
  apply LinearMap.ext; intro w
  conv_lhs => rw [← θ.apply_symm_apply w]
  rw [l05nKXconj_apply (p := 3) (N := 7) θ g (θ.symm w)]
  have h1 : g (θ.symm w) = θ.symm (s w) := by
    have h2 : (g : V →ₗ[ZMod 3] V) (θ.symm w) = θ.symm (s w) := by
      rw [hg, LinearMap.comp_apply, LinearMap.comp_apply]
      simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
    simpa using h2
  rw [h1, θ.apply_symm_apply]

private lemma l05nKFconj_rF {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v)) (i : Fin 6) :
    l05nKXconj (p := 3) (N := 7) θ (rF i) = ggDepELrefl i := by
  apply LinearMap.ext; intro w
  rw [← θ.apply_symm_apply w, l05nKXconj_apply (p := 3) (N := 7) θ (rF i) (θ.symm w),
    hrF, θ.apply_symm_apply]
  rfl

private lemma l05nKF_frame_word {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    {w : Module.End (ZMod 3) (GGDepAE 3 6)}
    (hw : w ∈ Submonoid.closure ggDepELFrameGens) :
    ∃ g ∈ Submonoid.closure (Set.range rF), l05nKXconj (p := 3) (N := 7) θ g = w := by
  refine Submonoid.closure_induction (motive := fun w _ =>
      ∃ g ∈ Submonoid.closure (Set.range rF), l05nKXconj (p := 3) (N := 7) θ g = w)
    ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact ⟨rF i, Submonoid.subset_closure ⟨i, rfl⟩, l05nKFconj_rF θ rF hrF i⟩
  · exact ⟨1, Submonoid.one_mem _, map_one (l05nKXconj (p := 3) (N := 7) θ)⟩
  · intro a b _ _ ha hb
    obtain ⟨ga, hga, hga'⟩ := ha
    obtain ⟨gb, hgb, hgb'⟩ := hb
    exact ⟨ga * gb, Submonoid.mul_mem _ hga hgb, by rw [map_mul, hga', hgb']⟩

private lemma l05nKF_frame_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    {w : V ≃ₗ[ZMod 3] V} (hw : w ∈ Submonoid.closure (Set.range rF)) :
    l05nKXconj (p := 3) (N := 7) θ w ∈ Submonoid.closure ggDepELFrameGens := by
  refine Submonoid.closure_induction (motive := fun w _ =>
      l05nKXconj (p := 3) (N := 7) θ w ∈ Submonoid.closure ggDepELFrameGens) ?_ ?_ ?_ hw
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    rw [l05nKFconj_rF θ rF hrF i]
    exact Submonoid.subset_closure ⟨i, rfl⟩
  · rw [map_one]; exact Submonoid.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Submonoid.mul_mem _ ha hb

private lemma l05nKF_roots {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v)) :
    ggDepELRoots ggDepELFrameGens (Set.range ggDepELh) =
      θ '' ggHLRoots rF (fun i => θ.symm (ggDepELh i)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, c, hc, rfl⟩ := hv
    obtain ⟨i, rfl⟩ := hc
    obtain ⟨g, hg, hgs⟩ := l05nKF_frame_word θ rF hrF hw
    refine ⟨g (θ.symm (ggDepELh i)), ⟨g, hg, i, rfl⟩, ?_⟩
    rw [← hgs, ← l05nKXconj_apply (p := 3) (N := 7) θ g (θ.symm (ggDepELh i)),
      θ.apply_symm_apply]
  · intro hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨w, hw, i, rfl⟩ := hu
    exact ⟨l05nKXconj (p := 3) (N := 7) θ w, l05nKF_frame_mem θ rF hrF hw, ggDepELh i,
      ⟨i, rfl⟩, by rw [← l05nKXconj_apply (p := 3) (N := 7) θ w (θ.symm (ggDepELh i)),
        θ.apply_symm_apply]⟩

theorem ggDepEL_notTv {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) :
    ¬ ∃ g ∈ Submonoid.closure (ggDepELGens news), GGDepAIsTv g := by
  rintro ⟨s, hs, htv⟩
  have hgen : ∀ z ∈ ggDepELGens news, ∃ g' ∈ Set.range rF ∪ rN '' news,
      (g' : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap.comp (z.comp θ.toLinearMap) := by
    intro z hz
    rw [ggDepELGens] at hz
    rcases hz with hz | hz
    · obtain ⟨i, rfl⟩ := hz
      refine ⟨rF i, Or.inl ⟨i, rfl⟩, ?_⟩
      apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply]
      show (rF i : V →ₗ[ZMod 3] V) v = θ.symm (ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
      rw [← hrF i v, θ.symm_apply_apply]
      rfl
    · obtain ⟨t, ht, rfl⟩ := hz
      refine ⟨rN t, Or.inr ⟨t, ht, rfl⟩, ?_⟩
      apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply]
      show (rN t : V →ₗ[ZMod 3] V) v = θ.symm (ggDepARefl t.1 t.2 (θ v))
      rw [← hrN t ht v, θ.symm_apply_apply]
      rfl
  obtain ⟨g, hg, hgeq⟩ := l05nD6_closure_conj (S := ggDepELGens news)
    (T := Set.range rF ∪ rN '' news) θ hgen s hs
  exact hnt g hg ⟨by
      rw [l05nPT_conj_finrank θ s g hgeq]
      exact htv.1,
    l05nPT_conj_move_fix θ s g hgeq htv.2⟩

theorem ggDepEL_notKill_frame {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) {xV : V} (hx : θ xV = ggDepELx)
    (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hHL : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g → g xV = xV →
      GGHLLines (ggHLRoots rF (fun i => θ.symm (ggDepELh i))) xV g)
    (y : GGDepAE 3 6) : ¬ GGDepELKill .frame news y := by
  intro hkill
  simp only [GGDepELKill] at hkill
  have hgen : ∀ z ∈ ggDepELGens news, ∃ g' ∈ Set.range rF ∪ rN '' news,
      (g' : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap.comp (z.comp θ.toLinearMap) := by
    intro z hz
    rw [ggDepELGens] at hz
    rcases hz with hz | hz
    · obtain ⟨i, rfl⟩ := hz
      refine ⟨rF i, Or.inl ⟨i, rfl⟩, ?_⟩
      apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply]
      show (rF i : V →ₗ[ZMod 3] V) v = θ.symm (ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
      rw [← hrF i v, θ.symm_apply_apply]
      rfl
    · obtain ⟨t, ht, rfl⟩ := hz
      refine ⟨rN t, Or.inr ⟨t, ht, rfl⟩, ?_⟩
      apply LinearMap.ext; intro v
      simp only [LinearMap.comp_apply]
      show (rN t : V →ₗ[ZMod 3] V) v = θ.symm (ggDepARefl t.1 t.2 (θ v))
      rw [← hrN t ht v, θ.symm_apply_apply]
      rfl
  rcases hkill with ⟨s, hs, htv⟩ | ⟨s, hs, hrefl, hmove⟩
  · obtain ⟨g, hg, hgeq⟩ := l05nD6_closure_conj (S := ggDepELGens news)
      (T := Set.range rF ∪ rN '' news) θ hgen s hs
    exact hnt g hg ⟨by
        rw [l05nPT_conj_finrank θ s g hgeq]
        exact htv.1,
      l05nPT_conj_move_fix θ s g hgeq htv.2⟩
  · obtain ⟨g, hg, hgeq⟩ := l05nD6_closure_conj (S := ggDepELGens news)
      (T := Set.range rF ∪ rN '' news) θ hgen s hs
    have hconj : l05nKXconj (p := 3) (N := 7) θ g = s := l05nKF_conj_eq θ g s hgeq
    have hlinrefl : GGLinRefl g :=
      l05nKX_refl_of_conj (p := 3) (N := 7) (by norm_num) θ (by rw [hconj]; exact hrefl)
    rw [← hconj] at hmove
    have hfx : g xV = xV := by
      have h0 : l05nKXconj (p := 3) (N := 7) θ g ggDepELx = ggDepELx := hmove.1
      rw [← hx] at h0
      rw [l05nKXconj_apply (p := 3) (N := 7) θ g xV] at h0
      exact θ.injective h0
    have hlines := hHL g hg hlinrefl hfx
    have hroots := l05nKF_roots θ rF hrF
    obtain ⟨-, v, hv, hmv⟩ := hmove
    rw [hroots] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨w, hw, c, d, hc, hgu⟩ := hlines u hu
    refine hmv (θ w) ?_ c d hc ?_
    · rw [hroots]; exact ⟨w, hw, rfl⟩
    · rw [l05nKXconj_apply (p := 3) (N := 7) θ g u, hgu, map_add, map_smul, map_smul, hx]

end CFSG.StandardType

end
