module

public import CFSG.LocalAnalysis.StandardType.GGTWKillXfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nD8_O_word {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) (pos : GGTWPos)
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    (news : Set (GGTWE p N × GGTWE p N)) (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v))
    {w : Module.End (ZMod p) (GGTWE p N)}
    (hw : w ∈ Submonoid.closure (ggTWOGens p N pos news)) :
    ∃ g ∈ Submonoid.closure (Set.range (Sum.elim
        (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => rF i.1)
        (fun t : ↥news => rN t.1))), l05nKXconj θ g = w := by
  refine Submonoid.closure_induction (motive := fun w _ => ∃ g ∈ Submonoid.closure
      (Set.range (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => rF i.1)
        (fun t : ↥news => rN t.1))), l05nKXconj θ g = w) ?_ ?_ ?_ hw
  · intro x hx
    rw [ggTWOGens] at hx
    rcases hx with hx | hx
    · obtain ⟨i, -, rfl⟩ := hx
      exact ⟨rF i.1, Submonoid.subset_closure ⟨Sum.inl i, rfl⟩,
        l05nKXconj_rF θ rF hrF i.1⟩
    · obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨rN t, Submonoid.subset_closure ⟨Sum.inr ⟨t, ht⟩, rfl⟩,
        l05nKXconj_rN θ news rN hrN t ht⟩
  · exact ⟨1, Submonoid.one_mem _, map_one (l05nKXconj θ)⟩
  · intro a b _ _ ha hb
    obtain ⟨ga, hga, hga'⟩ := ha
    obtain ⟨gb, hgb, hgb'⟩ := hb
    exact ⟨ga * gb, Submonoid.mul_mem _ hga hgb, by rw [map_mul, hga', hgb']⟩

private lemma l05nD8_O_word_back {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) (pos : GGTWPos)
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    (news : Set (GGTWE p N × GGTWE p N)) (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v))
    {u : V ≃ₗ[ZMod p] V}
    (hu : u ∈ Submonoid.closure (Set.range (Sum.elim
        (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => rF i.1)
        (fun t : ↥news => rN t.1)))) :
    l05nKXconj θ u ∈ Submonoid.closure (ggTWOGens p N pos news) := by
  refine Submonoid.closure_induction (motive := fun u _ =>
      l05nKXconj θ u ∈ Submonoid.closure (ggTWOGens p N pos news)) ?_ ?_ ?_ hu
  · intro x hx
    obtain ⟨s, rfl⟩ := hx
    cases s with
    | inl i =>
        rw [Sum.elim_inl, l05nKXconj_rF θ rF hrF i.1]
        exact Submonoid.subset_closure (Set.mem_union_left _ ⟨i, trivial, rfl⟩)
    | inr t =>
        rw [Sum.elim_inr, l05nKXconj_rN θ news rN hrN t.1 t.2]
        exact Submonoid.subset_closure (Set.mem_union_right _ ⟨t.1, t.2, rfl⟩)
  · rw [map_one]; exact Submonoid.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Submonoid.mul_mem _ ha hb

private lemma l05nD8_roots {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) (pos : GGTWPos)
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    (news : Set (GGTWE p N × GGTWE p N)) (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v)) :
    ggTWRoots (ggTWOGens p N pos news) (ggTWOCentres p N pos news) =
      θ '' ggHLRoots
        (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => rF i.1)
          (fun t : ↥news => rN t.1))
        (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => θ.symm (ggTWh p N i.1))
          (fun t : ↥news => θ.symm t.1.1)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, c, hc, rfl⟩ := hv
    rw [ggTWOCentres] at hc
    rcases hc with hc | hc
    · obtain ⟨i, -, rfl⟩ := hc
      obtain ⟨g, hg, hgs⟩ := l05nD8_O_word θ pos rF hrF news rN hrN hw
      refine ⟨g (θ.symm (ggTWh p N i.1)), ⟨g, hg, Sum.inl i, rfl⟩, ?_⟩
      rw [← hgs, ← l05nKXconj_apply θ g (θ.symm (ggTWh p N i.1)), θ.apply_symm_apply]
    · obtain ⟨t, ht, rfl⟩ := hc
      obtain ⟨g, hg, hgs⟩ := l05nD8_O_word θ pos rF hrF news rN hrN hw
      refine ⟨g (θ.symm t.1), ⟨g, hg, Sum.inr ⟨t, ht⟩, rfl⟩, ?_⟩
      rw [← hgs, ← l05nKXconj_apply θ g (θ.symm t.1), θ.apply_symm_apply]
  · intro hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨w, hw, s, rfl⟩ := hu
    cases s with
    | inl i =>
        refine ⟨l05nKXconj θ w, l05nD8_O_word_back θ pos rF hrF news rN hrN hw,
          ggTWh p N i.1, Set.mem_union_left _ ⟨i, trivial, rfl⟩, ?_⟩
        change θ (w (θ.symm (ggTWh p N i.1))) = l05nKXconj θ w (ggTWh p N i.1)
        rw [← l05nKXconj_apply θ w (θ.symm (ggTWh p N i.1)), θ.apply_symm_apply]
    | inr t =>
        refine ⟨l05nKXconj θ w, l05nD8_O_word_back θ pos rF hrF news rN hrN hw,
          t.1.1, Set.mem_union_right _ ⟨t.1, t.2, rfl⟩, ?_⟩
        change θ (w (θ.symm t.1.1)) = l05nKXconj θ w t.1.1
        rw [← l05nKXconj_apply θ w (θ.symm t.1.1), θ.apply_symm_apply]

theorem ggTW_notKill_other {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (θ : V ≃ₗ[ZMod p] GGTWE p N) {yV : V}
    (rF : Fin (N - 1) → V ≃ₗ[ZMod p] V)
    (hrF : ∀ i v, θ (rF i v) = ggTWRefl (ggTWh p N i) (ggTWα p N i) (θ v))
    (news : Set (GGTWE p N × GGTWE p N)) (rN : GGTWE p N × GGTWE p N → V ≃ₗ[ZMod p] V)
    (hrN : ∀ t ∈ news, ∀ v, θ (rN t v) = ggTWRefl t.1 t.2 (θ v))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (pos : GGTWPos)
    (hHK : ∀ g ∈ Subgroup.closure (Set.range rF ∪ rN '' news), GGLinRefl g → g yV = yV →
      GGHLLines (ggHLRoots
        (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => rF i.1)
          (fun t : ↥news => rN t.1))
        (Sum.elim (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => θ.symm (ggTWh p N i.1))
          (fun t : ↥news => θ.symm t.1.1))) yV g) :
    ¬ GGTWKill .other p N pos news (θ yV) := by
  intro hkill
  simp only [GGTWKill] at hkill
  rcases hkill with ⟨s, hs, htv⟩ | ⟨s, hs, hrefl, hmove⟩
  · obtain ⟨g, hg, hgs⟩ := l05nKX_closure_forward θ rF hrF news rN hrN hs
    rw [← hgs] at htv
    exact hnt g hg (l05nKX_tv_of_conj θ htv)
  · obtain ⟨g, hg, hgs⟩ := l05nKX_closure_forward θ rF hrF news rN hrN hs
    rw [← hgs] at hrefl hmove
    have hlinrefl : GGLinRefl g := l05nKX_refl_of_conj hp2 θ hrefl
    have hfy : g yV = yV := by
      have h0 : l05nKXconj θ g (θ yV) = θ yV := hmove.1
      rw [l05nKXconj_apply] at h0
      exact θ.injective h0
    have hlines := hHK g hg hlinrefl hfy
    have hroots := l05nD8_roots θ pos rF hrF news rN hrN
    obtain ⟨-, v, hv, hmv⟩ := hmove
    rw [hroots] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨w, hw, c, d, hc, hgu⟩ := hlines u hu
    refine hmv (θ w) ?_ c d hc ?_
    · rw [hroots]; exact ⟨w, hw, rfl⟩
    · rw [l05nKXconj_apply θ g u, hgu, map_add, map_smul, map_smul]

end CFSG.StandardType

end
