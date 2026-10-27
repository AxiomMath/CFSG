module

public import CFSG.LocalAnalysis.StandardType.GGNineDepDefs
import CFSG.LocalAnalysis.StandardType.GGNineDepRestrictAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleConnected
import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleFaithful
import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleAdj
import CFSG.LocalAnalysis.StandardType.GGDepARefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l04nD2_eqvGen_mem {α : Type*} {S : Set α} {R : α → α → Prop}
    (hR : ∀ {x y : α}, R x y → x ∈ S ∧ y ∈ S) :
    ∀ {x y : α}, Relation.EqvGen R x y → (x ∈ S ↔ y ∈ S) := by
  intro x y h
  exact Relation.EqvGen.rec (motive := fun a b _ => a ∈ S ↔ b ∈ S)
    (fun a b hab => ⟨fun _ => (hR hab).2, fun _ => (hR hab).1⟩)
    (fun a => Iff.rfl)
    (fun a b hab ih => ih.symm)
    (fun a b c hab hbc ihab ihbc => ihab.trans ihbc)
    h

private lemma l04nD2_eqvGen_subtype {α : Type*} {S : Set α} {R : α → α → Prop} {R' : S → S → Prop}
    (hR : ∀ {x y : α}, R x y → x ∈ S ∧ y ∈ S)
    (hstep : ∀ (a b : α) (ha : a ∈ S) (hb : b ∈ S), R a b → R' ⟨a, ha⟩ ⟨b, hb⟩)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (h : Relation.EqvGen R x y) :
    Relation.EqvGen R' ⟨x, hx⟩ ⟨y, hy⟩ := by
  exact Relation.EqvGen.rec (motive := fun a b _ =>
      ∀ (ha : a ∈ S) (hb : b ∈ S), Relation.EqvGen R' ⟨a, ha⟩ ⟨b, hb⟩)
    (fun a b hab ha hb => Relation.EqvGen.rel _ _ (hstep a b ha hb hab))
    (fun a ha hb => by
      have hsub : (⟨a, ha⟩ : S) = ⟨a, hb⟩ := Subtype.ext rfl
      rw [hsub]
      exact Relation.EqvGen.refl _)
    (fun a b hab ih ha hb => (ih hb ha).symm)
    (fun a b c hab hbc ihab ihbc ha hc => by
      have hb : b ∈ S := (l04nD2_eqvGen_mem hR hab).mp ha
      exact Relation.EqvGen.trans (⟨a, ha⟩ : S) (⟨b, hb⟩ : S) (⟨c, hc⟩ : S)
        (ihab ha hb) (ihbc hb hc))
    h hx hy

private structure L04fD2Setup {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x)
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) where
  O : Type
  g : O → (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))
  c : O → ↥(ggFixLineT r s)
  β : O → Module.Dual (ZMod p) ↥(ggFixLineT r s)
  hQ : (ggLargeRho r s hA).range = Subgroup.closure (Set.range g)
  hrefl : ∀ o, GGLinRefl (g o)
  hg : ∀ o w, g o w = w - β o w • c o
  hβ : ∀ o, β o (c o) = 2
  hspan : Submodule.span (ZMod p) (Set.range c) = ⊤
  hker : ∀ w, (∀ o, β o w = 0) → w = 0
  hconn : ∀ a b, Relation.ReflTransGen (fun a b => β a (c b) ≠ 0 ∧ β b (c a) ≠ 0) a b

private noncomputable def l04nD2_setup {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (hconn : GGLargeConnected r s)
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) : L04fD2Setup C hA := by
  classical
  haveI : Module.Finite (ZMod p) V := l04nD2_finite C
  let S : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ Set.range s
  have hSrefl : ∀ a ∈ S, GGLinRefl a := by
    rintro a (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · exact (ggDepA_linRefl_iff C.lin.p_ne_two (r i)).mpr
        ⟨h i, α i, l04nD2_pair_diag C i, C.lin.refl_form i⟩
    · exact C.lin.s_refl k
  have hex : ∀ a : ↥S, ∃ (c : V) (β : Module.Dual (ZMod p) V),
      β c = 2 ∧ ∀ v, (a : V ≃ₗ[ZMod p] V) v = v - β v • c :=
    fun a => (ggDepA_linRefl_iff C.lin.p_ne_two a.1).mp (hSrefl a.1 a.2)
  choose cV βV hβcV hformV using hex
  have hmoveV : ∀ a : ↥S, ggLinMove (a : V ≃ₗ[ZMod p] V) =
      Submodule.span (ZMod p) {cV a} :=
    fun a => l04nD2_move_eq_span C.lin.p_ne_two a.1 (hβcV a) (hformV a)
  have move_le_T : ∀ a : ↥S, ggLinMove (a : V ≃ₗ[ZMod p] V) ≤ ggFixLineT r s := by
    intro a
    obtain ⟨i, hi⟩ | ⟨k, hk⟩ := a.2
    · rw [← hi]
      exact (le_iSup (fun i => ggLinMove (r i)) i).trans le_sup_left
    · rw [← hk]
      exact (le_iSup (fun k => ggLinMove (s k)) k).trans le_sup_right
  have hcVmem : ∀ a : ↥S, cV a ∈ ggFixLineT r s := by
    intro a
    exact move_le_T a (by rw [hmoveV a]; exact Submodule.mem_span_singleton_self _)
  let cU : ↥S → ↥(ggFixLineT r s) := fun a => ⟨cV a, hcVmem a⟩
  let βU : ↥S → Module.Dual (ZMod p) ↥(ggFixLineT r s) :=
    fun a => (βV a).comp (ggFixLineT r s).subtype
  have hgenmem : ∀ a : ↥S, (a : V ≃ₗ[ZMod p] V) ∈ ggLargeGrp r s :=
    fun a => Subgroup.subset_closure a.2
  let g : ↥S → (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
    fun a => ggLargeRho r s hA ⟨a.1, hgenmem a⟩
  have hspanV : Submodule.span (ZMod p) (Set.range cV) = ggFixLineT r s := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact hcVmem a
    · rw [ggFixLineT]
      apply sup_le
      · apply iSup_le; intro i
        rw [hmoveV ⟨r i, Or.inl ⟨i, rfl⟩⟩]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨⟨r i, Or.inl ⟨i, rfl⟩⟩, rfl⟩)
      · apply iSup_le; intro k
        rw [hmoveV ⟨s k, Or.inr ⟨k, rfl⟩⟩]
        exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨⟨s k, Or.inr ⟨k, rfl⟩⟩, rfl⟩)
  have hspan : Submodule.span (ZMod p) (Set.range cU) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff (ggFixLineT r s) hcVmem).mpr hspanV
  have hβ : ∀ a : ↥S, βU a (cU a) = 2 := fun a => hβcV a
  have hg : ∀ a : ↥S, ∀ w : ↥(ggFixLineT r s), g a w = w - βU a w • cU a := by
    intro a w
    apply Subtype.ext
    show ((g a w : ↥(ggFixLineT r s)) : V) = (w : V) - βU a w • cV a
    have h1 : ((g a w : ↥(ggFixLineT r s)) : V) = (a : V ≃ₗ[ZMod p] V) (w : V) := by
      simp [g, ggLargeRho, l04nD2_restrict_apply, Subgroup.coe_inclusion]
    rw [h1, hformV a (w : V)]
    simp [βU, LinearMap.comp_apply]
  have hrefl : ∀ a : ↥S, GGLinRefl (g a) := by
    intro a
    have h' := l04nD2_restrict_refl C.lin.p_ne_two (ggFixLineT r s)
      (Subgroup.inclusion hA ⟨a.1, hgenmem a⟩) (hcVmem a) (hβcV a) (hformV a)
    simpa [g, ggLargeRho, Subgroup.coe_inclusion] using h'
  have hQ : (ggLargeRho r s hA).range = Subgroup.closure (Set.range g) := by
    have hImg : (ggLargeRho r s hA) '' {a : ↥(ggLargeGrp r s) | (a : V ≃ₗ[ZMod p] V) ∈ S}
        = Set.range g := by
      ext q
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨a.1, ha⟩, ?_⟩
        show ggLargeRho r s hA ⟨a.1, hgenmem ⟨a.1, ha⟩⟩ = ggLargeRho r s hA a
        exact congrArg (ggLargeRho r s hA) (Subtype.ext rfl)
      · rintro ⟨a, rfl⟩
        exact ⟨⟨a.1, hgenmem a⟩, a.2, rfl⟩
    have hSg : Subgroup.closure {a : ↥(ggLargeGrp r s) | (a : V ≃ₗ[ZMod p] V) ∈ S} = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [MonoidHom.range_eq_map, ← hSg, MonoidHom.map_closure, hImg]
  have hker : ∀ w : ↥(ggFixLineT r s), (∀ a : ↥S, βU a w = 0) → w = 0 := by
    intro w hw
    have hfix : (w : V) ∈ ggLinFix S := by
      intro a ha
      have hzero : βV ⟨a, ha⟩ (w : V) = 0 := by
        have h' := hw ⟨a, ha⟩
        simpa [βU, cU, LinearMap.comp_apply] using h'
      rw [hformV ⟨a, ha⟩ (w : V), hzero, zero_smul, sub_zero]
    have hbot : (w : V) ∈ (⊥ : Submodule (ZMod p) V) := by
      rw [← l04nD2_fix_A C]
      exact hfix
    exact Subtype.ext (by simpa using hbot)
  have hbeta_ne : ∀ (a b : ↥S) {v : V}, v ∈ ggLinMove (b : V ≃ₗ[ZMod p] V) →
      (a : V ≃ₗ[ZMod p] V) v ≠ v → βV a (cV b) ≠ 0 := by
    intro a b v hv hne h0
    apply hne
    have hv' : v ∈ Submodule.span (ZMod p) {cV b} := by rwa [hmoveV b] at hv
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hv'
    have hb0 : βV a v = 0 := by rw [← hlam, map_smul, h0, smul_zero]
    rw [hformV a v, hb0, zero_smul, sub_zero]
  let pairRel : ↥S → ↥S → Prop := fun a b => βU a (cU b) ≠ 0 ∧ βU b (cU a) ≠ 0
  have hpair_adj : ∀ a b : ↥S, GGLinAdj a.1 b.1 → pairRel a b := by
    intro a b hab
    obtain ⟨⟨v1, hv1, hne1⟩, ⟨v2, hv2, hne2⟩⟩ := hab
    refine ⟨?_, ?_⟩
    · have hb := hbeta_ne a b hv1 hne1
      simpa [pairRel, βU, cU, LinearMap.comp_apply] using hb
    · have hb := hbeta_ne b a hv2 hne2
      simpa [pairRel, βU, cU, LinearMap.comp_apply] using hb
  have hconn' : ∀ a b : ↥S, Relation.ReflTransGen pairRel a b := by
    intro a b
    have h0 := hconn a.1 a.2 b.1 b.2
    have h' : Relation.EqvGen pairRel a b :=
      l04nD2_eqvGen_subtype (S := S)
        (R := fun x y : V ≃ₗ[ZMod p] V => x ∈ S ∧ y ∈ S ∧ GGLinAdj x y)
        (R' := pairRel)
        (fun hab => ⟨hab.1, hab.2.1⟩)
        (fun x y hx hy hxy => hpair_adj ⟨x, hx⟩ ⟨y, hy⟩ hxy.2.2)
        a.2 b.2 h0
    have : Std.Symm pairRel := ⟨fun a b h => ⟨h.2, h.1⟩⟩
    rwa [Relation.EqvGen.eqvGen_eq_reflTransGen] at h'
  exact ⟨↥S, g, cU, βU, hQ, hrefl, hg, hβ, hspan, hker, hconn'⟩

private lemma l04nD2_absIrred {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (hconn : GGLargeConnected r s)
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) :
    ZS.AbsIrred p (ggLargeRho r s hA).range := by
  have D := l04nD2_setup C hconn hA
  exact ggRC_absIrred_of_connected C.lin.p_ne_two D.g D.c D.β D.hg D.hβ D.hspan D.hker D.hconn
    (ggLargeRho r s hA).range D.hQ

private lemma l04nD2_reflGen {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (hconn : GGLargeConnected r s)
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) :
    (ggLargeRho r s hA).range =
      Subgroup.closure {q | q ∈ (ggLargeRho r s hA).range ∧ GGLinRefl q} := by
  have D := l04nD2_setup C hconn hA
  apply le_antisymm
  · rw [D.hQ]
    apply Subgroup.closure_mono
    rintro q ⟨o, rfl⟩
    exact ⟨Subgroup.subset_closure (Set.mem_range_self o), D.hrefl o⟩
  · rw [Subgroup.closure_le]
    rintro q ⟨hq, _⟩
    exact hq

private lemma l04nD2_hirr {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (hconn : GGLargeConnected r s)
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) :
    ∀ W : Submodule (ZMod p) V, W ≤ ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ ggLargeGrp r s, ∀ w ∈ W, a w ∈ W) →
      W = ⊥ ∨ W = ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)) := by
  rw [l04nD2_com_eq_T C]
  intro W hWU hWstab
  let W' : Submodule (ZMod p) ↥(ggFixLineT r s) := W.comap (ggFixLineT r s).subtype
  have hW'map : W'.map (ggFixLineT r s).subtype = W := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hu
    · intro z hz
      exact ⟨⟨z, hWU hz⟩, hz, rfl⟩
  have hinv : ∀ a ∈ (ggLargeRho r s hA).range, ∀ w ∈ W', a w ∈ W' := by
    rintro a ⟨a₀, rfl⟩ w hw
    change (((ggLargeRho r s hA a₀) w : ↥(ggFixLineT r s)) : V) ∈ W
    have h1 : (((ggLargeRho r s hA a₀) w : ↥(ggFixLineT r s)) : V) =
        (a₀ : V ≃ₗ[ZMod p] V) (w : V) := by
      simp [ggLargeRho, l04nD2_restrict_apply, Subgroup.coe_inclusion]
    rw [h1]
    exact hWstab a₀ a₀.2 (w : V) hw
  rcases (l04nD2_absIrred C hconn hA).1 W' hinv with h | h
  · left
    rw [← hW'map, h, Submodule.map_bot]
  · right
    rw [← hW'map, h, Submodule.map_top, Submodule.range_subtype]

private lemma l04nD2_hend {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (hconn : GGLargeConnected r s)
    (hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s)) :
    ∀ f : V →ₗ[ZMod p] V, LinearMap.range f ≤ ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ ggLargeGrp r s, ∀ u ∈ ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)),
        f (a u) = a (f u)) →
      ∃ c : ZMod p, ∀ u ∈ ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)), f u = c • u := by
  rw [l04nD2_com_eq_T C]
  intro f hfrange hfcomm
  let F : Module.End (ZMod p) ↥(ggFixLineT r s) :=
    { toFun := fun u => ⟨f u, hfrange (LinearMap.mem_range_self f u)⟩
      map_add' := by intro u v; ext; simp
      map_smul' := by intro c u; ext; simp }
  have hFcomm : ∀ a ∈ (ggLargeRho r s hA).range,
      F ∘ₗ (a : ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s)) =
        (a : ↥(ggFixLineT r s) →ₗ[ZMod p] ↥(ggFixLineT r s)) ∘ₗ F := by
    rintro a ⟨a₀, rfl⟩
    ext u
    have hL : ((F ((ggLargeRho r s hA a₀) u) : ↥(ggFixLineT r s)) : V) =
        f ((a₀ : V ≃ₗ[ZMod p] V) (u : V)) := by
      simp [F, ggLargeRho, l04nD2_restrict_apply, Subgroup.coe_inclusion]
    have hR : ((((ggLargeRho r s hA a₀) (F u) : ↥(ggFixLineT r s))) : V) =
        (a₀ : V ≃ₗ[ZMod p] V) (f (u : V)) := by
      simp [F, ggLargeRho, l04nD2_restrict_apply, Subgroup.coe_inclusion]
    change ((F ((ggLargeRho r s hA a₀) u) : ↥(ggFixLineT r s)) : V) =
      (((ggLargeRho r s hA a₀) (F u) : ↥(ggFixLineT r s)) : V)
    rw [hL, hR, hfcomm a₀ a₀.2 (u : V) u.2]
  obtain ⟨c, hc⟩ := (l04nD2_absIrred C hconn hA).2 F hFcomm
  refine ⟨c, fun u hu => ?_⟩
  have h2 := congrArg (fun (g : Module.End (ZMod p) ↥(ggFixLineT r s)) => g ⟨u, hu⟩) hc
  have h3 : ((F ⟨u, hu⟩ : ↥(ggFixLineT r s)) : V) = c • u := by
    rw [h2]
    simp
  simpa [F] using h3

theorem ggNineDep_restrict {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (hconn : GGLargeConnected r s) :
    ∃ hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s),
      N - 2 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) ∧
        Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N ∧ GGLargeRestr r s hA := by
  have hA : ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s) := l04nD2_A_le_stab C
  have hnotr : ∀ g ∈ ggLargeGrp r s, g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
    intro g hg _ hcon
    exact C.lin.no_transv g hg ⟨hcon.1, fun w =>
      hcon.2 (LinearMap.mem_range_self (g.toLinearMap - LinearMap.id) w)
        g (Set.mem_singleton g)⟩
  have htriv : ∀ g ∈ ggLargeGrp r s, ∀ v : V,
      g v - v ∈ ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)) := by
    intro g hg v
    exact le_iSup₂ (f := fun a (_ : a ∈ (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V))) =>
      ggLinMove a) g hg (LinearMap.mem_range_self (g.toLinearMap - LinearMap.id) v)
  have hfaith : ∀ g ∈ ggLargeGrp r s,
      (∀ u ∈ ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)), g u = u) → g = 1 := by
    have : Module.Finite (ZMod p) V := l04nD2_finite C
    exact ggLin_faithful_on_com (ggLargeGrp r s) hnotr
      (l04nD2_hirr C hconn hA) (l04nD2_hend C hconn hA) htriv
  have hinj : Function.Injective (ggLargeRho r s hA) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    refine hfaith (a : V ≃ₗ[ZMod p] V) a.2 (fun u hu => ?_)
    have huT : u ∈ ggFixLineT r s := l04nD2_com_le_T C hu
    have h1 := congrArg
      (fun e : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s) => e ⟨u, huT⟩) ha
    have h2 : ((ggLargeRho r s hA a) ⟨u, huT⟩ : ↥(ggFixLineT r s)) = ⟨u, huT⟩ := by
      rw [h1]; rfl
    have h3 := congrArg Subtype.val h2
    simpa [ggLargeRho, l04nD2_restrict_apply, Subgroup.coe_inclusion] using h3
  refine ⟨hA, (l04nD2_finrank_bounds C).1, (l04nD2_finrank_bounds C).2,
    hinj, l04nD2_absIrred C hconn hA, l04nD2_reflGen C hconn hA⟩

end CFSG.StandardType

end
