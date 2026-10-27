module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGTWKillXfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nKO_conj_rF {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v)) (i : Fin 6) :
    l05nKXconj (p := 3) (N := 7) θ (rF i) = ggDepELrefl i := by
  change l05nKXconj (p := 3) (N := 7) θ (rF i) =
    ggDepARefl (ggDepELh i) (ggDepELα i)
  apply LinearMap.ext
  intro w
  rw [← θ.apply_symm_apply w, l05nKXconj_apply (p := 3) (N := 7), hrF, θ.apply_symm_apply]

private lemma l05nKO_closure_forward {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v))
    {s : Module.End (ZMod 3) (GGDepAE 3 6)}
    (hs : s ∈ Submonoid.closure (ggDepELGens news)) :
    ∃ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      l05nKXconj (p := 3) (N := 7) θ g = s := by
  refine Submonoid.closure_induction (motive := fun s _ => ∃ g ∈ Subgroup.closure
      (Set.range rF ∪ rN '' news), l05nKXconj (p := 3) (N := 7) θ g = s) ?_ ?_ ?_ hs
  · intro x hx
    rw [ggDepELGens] at hx
    rcases hx with hx | hx
    · rw [ggDepELFrameGens] at hx
      obtain ⟨i, rfl⟩ := hx
      exact ⟨rF i, Subgroup.subset_closure (Set.mem_union_left _ ⟨i, rfl⟩),
        l05nKO_conj_rF θ rF hrF i⟩
    · obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨rN t, Subgroup.subset_closure (Set.mem_union_right _ ⟨t, ht, rfl⟩),
        l05nKXconj_rN (p := 3) (N := 7) θ news rN hrN t ht⟩
  · exact ⟨1, Subgroup.one_mem _, map_one (l05nKXconj (p := 3) (N := 7) θ)⟩
  · intro a b _ _ ha hb
    obtain ⟨ga, hga, hga'⟩ := ha
    obtain ⟨gb, hgb, hgb'⟩ := hb
    exact ⟨ga * gb, Subgroup.mul_mem _ hga hgb, by rw [map_mul, hga', hgb']⟩

private lemma l05nKO_O_word {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v))
    {w : Module.End (ZMod 3) (GGDepAE 3 6)}
    (hw : w ∈ Submonoid.closure (ggDepELOGens news)) :
    ∃ g ∈ Submonoid.closure (Set.range (Sum.elim
        (fun i : {i : Fin 6 // GGDepED4In i} => rF i.1)
        (fun t : ↥news => rN t.1))),
      l05nKXconj (p := 3) (N := 7) θ g = w := by
  refine Submonoid.closure_induction (motive := fun w _ => ∃ g ∈ Submonoid.closure
      (Set.range (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => rF i.1)
        (fun t : ↥news => rN t.1))), l05nKXconj (p := 3) (N := 7) θ g = w) ?_ ?_ ?_ hw
  · intro x hx
    rw [ggDepELOGens] at hx
    rcases hx with hx | hx
    · obtain ⟨i, -, rfl⟩ := hx
      exact ⟨rF i.1, Submonoid.subset_closure ⟨Sum.inl i, rfl⟩,
        l05nKO_conj_rF θ rF hrF i.1⟩
    · obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨rN t, Submonoid.subset_closure ⟨Sum.inr ⟨t, ht⟩, rfl⟩,
        l05nKXconj_rN (p := 3) (N := 7) θ news rN hrN t ht⟩
  · exact ⟨1, Submonoid.one_mem _, map_one (l05nKXconj (p := 3) (N := 7) θ)⟩
  · intro a b _ _ ha hb
    obtain ⟨ga, hga, hga'⟩ := ha
    obtain ⟨gb, hgb, hgb'⟩ := hb
    exact ⟨ga * gb, Submonoid.mul_mem _ hga hgb, by rw [map_mul, hga', hgb']⟩

private lemma l05nKO_O_word_back {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v))
    {u : V ≃ₗ[ZMod 3] V}
    (hu : u ∈ Submonoid.closure (Set.range (Sum.elim
        (fun i : {i : Fin 6 // GGDepED4In i} => rF i.1)
        (fun t : ↥news => rN t.1)))) :
    l05nKXconj (p := 3) (N := 7) θ u ∈ Submonoid.closure (ggDepELOGens news) := by
  refine Submonoid.closure_induction (motive := fun u _ =>
      l05nKXconj (p := 3) (N := 7) θ u ∈ Submonoid.closure (ggDepELOGens news)) ?_ ?_ ?_ hu
  · intro x hx
    obtain ⟨s, rfl⟩ := hx
    cases s with
    | inl i =>
        rw [Sum.elim_inl, l05nKO_conj_rF θ rF hrF i.1]
        exact Submonoid.subset_closure (Set.mem_union_left _ ⟨i, trivial, rfl⟩)
    | inr t =>
        rw [Sum.elim_inr, l05nKXconj_rN (p := 3) (N := 7) θ news rN hrN t.1 t.2]
        exact Submonoid.subset_closure (Set.mem_union_right _ ⟨t.1, t.2, rfl⟩)
  · rw [map_one]; exact Submonoid.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Submonoid.mul_mem _ ha hb

private lemma l05nKO_roots {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6)
    (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v)) :
    ggDepELRoots (ggDepELOGens news) (ggDepELOCentres news) =
      θ '' ggHLRoots
        (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => rF i.1)
          (fun t : ↥news => rN t.1))
        (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => θ.symm (ggDepELh i.1))
          (fun t : ↥news => θ.symm t.1.1)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, c, hc, rfl⟩ := hv
    rw [ggDepELOCentres] at hc
    rcases hc with hc | hc
    · obtain ⟨i, -, rfl⟩ := hc
      obtain ⟨g, hg, hgs⟩ := l05nKO_O_word θ rF hrF news rN hrN hw
      refine ⟨g (θ.symm (ggDepELh i.1)), ⟨g, hg, Sum.inl i, rfl⟩, ?_⟩
      rw [← hgs, ← l05nKXconj_apply (p := 3) (N := 7) θ g (θ.symm (ggDepELh i.1)),
        θ.apply_symm_apply]
    · obtain ⟨t, ht, rfl⟩ := hc
      obtain ⟨g, hg, hgs⟩ := l05nKO_O_word θ rF hrF news rN hrN hw
      refine ⟨g (θ.symm t.1), ⟨g, hg, Sum.inr ⟨t, ht⟩, rfl⟩, ?_⟩
      rw [← hgs, ← l05nKXconj_apply (p := 3) (N := 7) θ g (θ.symm t.1),
        θ.apply_symm_apply]
  · intro hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨w, hw, s, rfl⟩ := hu
    cases s with
    | inl i =>
        refine ⟨l05nKXconj (p := 3) (N := 7) θ w,
          l05nKO_O_word_back θ rF hrF news rN hrN hw,
          ggDepELh i.1, Set.mem_union_left _ ⟨i, trivial, rfl⟩, ?_⟩
        change θ (w (θ.symm (ggDepELh i.1))) =
          l05nKXconj (p := 3) (N := 7) θ w (ggDepELh i.1)
        rw [← l05nKXconj_apply (p := 3) (N := 7) θ w (θ.symm (ggDepELh i.1)),
          θ.apply_symm_apply]
    | inr t =>
        refine ⟨l05nKXconj (p := 3) (N := 7) θ w,
          l05nKO_O_word_back θ rF hrF news rN hrN hw,
          t.1.1, Set.mem_union_right _ ⟨t.1, t.2, rfl⟩, ?_⟩
        change θ (w (θ.symm t.1.1)) = l05nKXconj (p := 3) (N := 7) θ w t.1.1
        rw [← l05nKXconj_apply (p := 3) (N := 7) θ w (θ.symm t.1.1),
          θ.apply_symm_apply]

theorem ggDepEL_notKill_other {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : V ≃ₗ[ZMod 3] GGDepAE 3 6) {yV : V}
    (rF : Fin 6 → V ≃ₗ[ZMod 3] V)
    (hrF : ∀ i v, θ (rF i v) = ggDepARefl (ggDepELh i) (ggDepELα i) (θ v))
    (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) (rN : GGDepAE 3 6 × GGDepAE 3 6 → V ≃ₗ[ZMod 3] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggDepARefl t.1 t.2 (θ v))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hHK : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g → g yV = yV →
      GGHLLines (ggHLRoots
        (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => rF i.1) (fun t : ↥news => rN t.1))
        (Sum.elim (fun i : {i : Fin 6 // GGDepED4In i} => θ.symm (ggDepELh i.1))
          (fun t : ↥news => θ.symm t.1.1))) yV g) :
    ¬ GGDepELKill .other news (θ yV) := by
  intro hkill
  simp only [GGDepELKill] at hkill
  rcases hkill with ⟨s, hs, htv⟩ | ⟨s, hs, hrefl, hmove⟩
  · obtain ⟨g, hg, hgs⟩ := l05nKO_closure_forward θ rF hrF news rN hrN hs
    rw [← hgs] at htv
    exact hnt g hg (l05nKX_tv_of_conj (p := 3) (N := 7) θ htv)
  · obtain ⟨g, hg, hgs⟩ := l05nKO_closure_forward θ rF hrF news rN hrN hs
    rw [← hgs] at hrefl hmove
    have hlinrefl : GGLinRefl g :=
      l05nKX_refl_of_conj (p := 3) (N := 7) (by decide) θ hrefl
    have hfy : g yV = yV := by
      have h0 : l05nKXconj (p := 3) (N := 7) θ g (θ yV) = θ yV := hmove.1
      rw [l05nKXconj_apply (p := 3) (N := 7)] at h0
      exact θ.injective h0
    have hlines := hHK g hg hlinrefl hfy
    have hroots := l05nKO_roots θ rF hrF news rN hrN
    obtain ⟨-, v, hv, hmv⟩ := hmove
    rw [hroots] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨w, hw, c, d, hc, hgu⟩ := hlines u hu
    refine hmv (θ w) ?_ c d hc ?_
    · rw [hroots]; exact ⟨w, hw, rfl⟩
    · rw [l05nKXconj_apply (p := 3) (N := 7) θ g u, hgu, map_add, map_smul, map_smul]

end CFSG.StandardType

end
