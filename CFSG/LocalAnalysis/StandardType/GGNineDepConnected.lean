module

public import CFSG.LocalAnalysis.StandardType.GGNineDepDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleAdj
import CFSG.LocalAnalysis.StandardType.GGTBTorCartan
import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l04nD1_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private lemma l04nD1_cartanA_eq_two (m : ℕ) (i : Fin m) : CartanMatrix.A m i i = 2 := by
  rw [l04nD1_cartanA_entry, if_pos rfl]

private lemma l04nD1_cartanA_adj_up {m : ℕ} (i j : Fin m) (hij : j.val = i.val + 1) :
    CartanMatrix.A m j i = -1 := by
  rw [l04nD1_cartanA_entry]
  rw [if_neg (by intro hh; have hv := congrArg Fin.val hh; omega),
    if_pos (Or.inr (by omega))]

private lemma l04nD1_cartanA_adj_down {m : ℕ} (i j : Fin m) (hij : j.val = i.val + 1) :
    CartanMatrix.A m i j = -1 := by
  rw [l04nD1_cartanA_entry]
  rw [if_neg (by intro hh; have hv := congrArg Fin.val hh; omega),
    if_pos (Or.inl (by omega))]

private lemma l04nD1_cartanA_zero_up {m : ℕ} (i j : Fin m) (hij : j.val = i.val + 2) :
    CartanMatrix.A m i j = 0 := by
  rw [l04nD1_cartanA_entry]
  rw [if_neg (by intro hh; have hv := congrArg Fin.val hh; omega),
    if_neg (by intro hh; rcases hh with hh | hh <;> omega)]

private lemma l04nD1_two_ne_zero {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) : (2 : ZMod p) ≠ 0 :=
  zmod_two_ne_zero C.lin.p_ne_two

private lemma l04nD1_pair_diag {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (i : Fin (N - 1)) : α i (h i) = 2 := by
  rw [C.lin.pair i i, l04nD1_cartanA_eq_two (N - 1) i]
  norm_num

private lemma l04nD1_h_ne {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (i : Fin (N - 1)) : h i ≠ 0 := by
  intro h0
  have hh := l04nD1_pair_diag C i
  rw [h0, map_zero] at hh
  exact (l04nD1_two_ne_zero C) hh.symm

private lemma l04nD1_r_neg_self {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (i : Fin (N - 1)) : r i (h i) = -h i := by
  rw [C.lin.refl_form i (h i), l04nD1_pair_diag C i]
  module

private lemma l04nD1_h_mem_move {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (i : Fin (N - 1)) : h i ∈ ggLinMove (r i) := by
  have hmem : r i (h i) - h i ∈ ggLinMove (r i) := by
    rw [ggLinMove]
    simp
  have heq2 : -((2 : ZMod p)⁻¹) • (r i (h i) - h i) = h i := by
    rw [show r i (h i) - h i = (-2 : ZMod p) • h i by
      rw [l04nD1_r_neg_self C i]; module]
    rw [smul_smul]
    rw [show -((2 : ZMod p)⁻¹) * (-2 : ZMod p) = (2 : ZMod p) * (2 : ZMod p)⁻¹ by ring]
    rw [mul_inv_cancel₀ (l04nD1_two_ne_zero C), one_smul]
  rw [show h i = -((2 : ZMod p)⁻¹) • (r i (h i) - h i) from heq2.symm]
  exact Submodule.smul_mem _ _ hmem

private lemma l04nD1_move_eq_span {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (i : Fin (N - 1)) :
    ggLinMove (r i) = Submodule.span (ZMod p) ({h i} : Set V) := by
  apply le_antisymm
  · intro y hy
    rw [ggLinMove] at hy
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
    change r i v - v ∈ Submodule.span (ZMod p) ({h i} : Set V)
    have heq : r i v - v = (-(α i v)) • h i := by
      rw [C.lin.refl_form i v]; module
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (h i)))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact l04nD1_h_mem_move C i

private theorem l04nD1_r_refl {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (i : Fin (N - 1)) : GGLinRefl (r i) := by
  constructor
  · ext v
    rw [LinearEquiv.mul_apply]
    change r i (r i v) = v
    rw [C.lin.refl_form i (r i v),
      C.lin.refl_form i v, map_sub, map_smul, l04nD1_pair_diag C i]
    module
  · rw [l04nD1_move_eq_span C i, finrank_span_singleton (l04nD1_h_ne C i)]

private lemma l04nD1_move_le_fix_iff {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (g : V ≃ₗ[ZMod p] V) :
    ggLinMove g ≤ ggLinFix {g} ↔ ∀ w, g (g w - w) = g w - w := by
  constructor
  · intro h w
    exact h (LinearMap.mem_range_self (g.toLinearMap - LinearMap.id) w) g (Set.mem_singleton g)
  · intro h y hy
    rw [ggLinMove] at hy
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hy
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact h w

private lemma l04nD1_notr {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) {a b : V ≃ₗ[ZMod p] V}
    (ha : a ∈ Set.range r ∪ Set.range s) (hb : b ∈ Set.range r ∪ Set.range s) :
    ∀ g ∈ Subgroup.closure ({a, b} : Set (V ≃ₗ[ZMod p] V)), g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
  intro g hg hg1 hconj
  have hg' : g ∈ Subgroup.closure (Set.range r ∪ Set.range s) :=
    Subgroup.closure_mono (by
      intro z hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb) hg
  exact C.lin.no_transv g hg' ⟨hconj.1, (l04nD1_move_le_fix_iff g).mp hconj.2⟩

private lemma l04nD1_adj_symm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {a b : V ≃ₗ[ZMod p] V} (h : GGLinAdj a b) : GGLinAdj b a :=
  ⟨h.2, h.1⟩

private lemma l04nD1_eqvGen_of_reflTransGen {ι α : Type*} (f : ι → α) {rel : ι → ι → Prop}
    {p : α → α → Prop} (h : ∀ a b, rel a b → p (f a) (f b)) {a b : ι}
    (hab : Relation.ReflTransGen rel a b) : Relation.EqvGen p (f a) (f b) := by
  induction hab with
  | refl => exact Relation.EqvGen.refl _
  | tail hab hbc ih =>
      exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (h _ _ hbc))

private lemma l04nD1_move_of_adj {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) (i j : Fin (N - 1))
    (hij : CartanMatrix.A (N - 1) i j = -1) : r i (h j) ≠ h j := by
  intro heq
  have hform := C.lin.refl_form i (h j)
  rw [heq] at hform
  have hzero : α i (h j) • h i = 0 := sub_eq_self.mp hform.symm
  have hα : α i (h j) ≠ 0 := by
    intro h0
    rw [C.lin.pair i j, hij] at h0
    simp only [Int.cast_neg, Int.cast_one] at h0
    exact one_ne_zero (neg_eq_zero.mp h0)
  rcases smul_eq_zero.mp hzero with hh | hh
  · exact hα hh
  · exact (l04nD1_h_ne C i) hh

theorem ggNineDep_connected {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGNineDepCase p N h α r s x) : GGLargeConnected r s := by
  classical
  let Q : (V ≃ₗ[ZMod p] V) → (V ≃ₗ[ZMod p] V) → Prop :=
    fun a b => a ∈ Set.range r ∪ Set.range s ∧ b ∈ Set.range r ∪ Set.range s ∧ GGLinAdj a b
  have hmem_r : ∀ i : Fin (N - 1), r i ∈ Set.range r ∪ Set.range s :=
    fun i => Set.mem_union_left _ (Set.mem_range_self i)
  have hmem_s : ∀ k : T, s k ∈ Set.range r ∪ Set.range s :=
    fun k => Set.mem_union_right _ (Set.mem_range_self k)
  have hcross : ∃ (i : Fin (N - 1)) (k : T), GGLinAdj (r i) (s k) := by
    have hnc : ∃ (i : Fin (N - 1)) (k : T), r i * s k ≠ s k * r i := by
      by_contra hcomm
      push Not at hcomm
      have hx_s : x ∈ ggLinFix (Set.range s) := by
        rw [C.lin.fix_s]
        exact Submodule.subset_span (Set.mem_singleton x)
      have hsx : ∀ k : T, s k x = x := fun k => hx_s (s k) (Set.mem_range_self k)
      have hRx : ∀ i : Fin (N - 1), r i x ∈ Submodule.span (ZMod p) ({x} : Set V) := by
        intro i
        have hfix : r i x ∈ ggLinFix (Set.range s) := by
          intro a ha
          rcases ha with ⟨k, rfl⟩
          calc s k (r i x) = (s k * r i) x := rfl
            _ = (r i * s k) x := by rw [hcomm i k]
            _ = r i (s k x) := rfl
            _ = r i x := by rw [hsx k]
        rwa [C.lin.fix_s] at hfix
      have hmem_of_alpha : ∀ j : Fin (N - 1), α j x ≠ 0 →
          h j ∈ Submodule.span (ZMod p) ({x} : Set V) := by
        intro j hα
        obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp (hRx j)
        have hrel : α j x • h j = (1 - ν) • x := by
          have hh := C.lin.refl_form j x
          rw [← hν] at hh
          have h2 : α j x • h j = x - ν • x := by
            have hh' : x - α j x • h j = ν • x := hh.symm
            rw [← hh']; abel
          rw [h2, sub_smul, one_smul]
        rw [Submodule.mem_span_singleton]
        refine ⟨(α j x)⁻¹ * (1 - ν), ?_⟩
        have hc := congrArg (fun z => (α j x)⁻¹ • z) hrel
        simpa [smul_smul, inv_mul_cancel₀ hα] using hc.symm
      obtain ⟨i0, hi0⟩ : ∃ i : Fin (N - 1), r i x ≠ x := by
        by_contra h'
        push Not at h'
        exact C.lin.x_not_fix (by
          intro a ha
          rcases ha with ⟨i, rfl⟩
          exact h' i)
      have hαi0 : α i0 x ≠ 0 := by
        intro h0
        exact hi0 (by rw [C.lin.refl_form i0 x, h0, zero_smul, sub_zero])
      have hPi0 : h i0 ∈ Submodule.span (ZMod p) ({x} : Set V) := hmem_of_alpha i0 hαi0
      have hprop : ∀ i j : Fin (N - 1), CartanMatrix.A (N - 1) j i = -1 →
          h i ∈ Submodule.span (ZMod p) ({x} : Set V) →
          h j ∈ Submodule.span (ZMod p) ({x} : Set V) := by
        intro i j hji hi
        apply hmem_of_alpha j
        obtain ⟨aa, haa⟩ := Submodule.mem_span_singleton.mp hi
        have hval : aa * α j x = -1 := by
          have hh := C.lin.pair j i
          rw [← haa, map_smul, hji] at hh
          simpa [smul_eq_mul] using hh
        intro h0
        rw [h0, mul_zero] at hval
        exact (neg_ne_zero.mpr one_ne_zero) hval.symm
      have hcontra2 : ∀ i j : Fin (N - 1), CartanMatrix.A (N - 1) i j = 0 →
          h i ∈ Submodule.span (ZMod p) ({x} : Set V) →
          h j ∈ Submodule.span (ZMod p) ({x} : Set V) → False := by
        intro i j hij hi hj
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi
        obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hj
        have ha_ne : a ≠ 0 := by
          intro h0
          have hh := l04nD1_h_ne C i
          rw [← ha, h0, zero_smul] at hh
          exact hh rfl
        have hb_ne : b ≠ 0 := by
          intro h0
          have hh := l04nD1_h_ne C j
          rw [← hb, h0, zero_smul] at hh
          exact hh rfl
        have hdiag : a * α i x = 2 := by
          have hh := l04nD1_pair_diag C i
          rw [← ha, map_smul] at hh
          simpa [smul_eq_mul] using hh
        have hpair0 : b * α i x = 0 := by
          have hh := C.lin.pair i j
          rw [← hb, map_smul, hij] at hh
          simpa [smul_eq_mul] using hh
        have hb2 : b * 2 = 0 := by
          calc b * 2 = b * (a * α i x) := by rw [hdiag]
            _ = (b * α i x) * a := by ring
            _ = 0 := by rw [hpair0]; ring
        have hb0 : b = 0 := by
          rcases mul_eq_zero.mp hb2 with hh | hh
          · exact hh
          · exact absurd hh (l04nD1_two_ne_zero C)
        exact hb_ne hb0
      have hN : 5 ≤ N := C.lin.N_ge
      by_cases hcase : i0.val + 2 ≤ N - 2
      · have h1 : i0.val + 1 < N - 1 := by omega
        let i1 : Fin (N - 1) := ⟨i0.val + 1, h1⟩
        have h2 : i1.val + 1 < N - 1 := by
          have hv : i1.val = i0.val + 1 := rfl
          omega
        let i2 : Fin (N - 1) := ⟨i1.val + 1, h2⟩
        have hA1 : CartanMatrix.A (N - 1) i1 i0 = -1 :=
          l04nD1_cartanA_adj_up i0 i1 rfl
        have hP1 : h i1 ∈ Submodule.span (ZMod p) ({x} : Set V) := hprop i0 i1 hA1 hPi0
        have hA2 : CartanMatrix.A (N - 1) i2 i1 = -1 :=
          l04nD1_cartanA_adj_up i1 i2 rfl
        have hP2 : h i2 ∈ Submodule.span (ZMod p) ({x} : Set V) := hprop i1 i2 hA2 hP1
        have hA0 : CartanMatrix.A (N - 1) i0 i2 = 0 :=
          l04nD1_cartanA_zero_up i0 i2 (by
            have hv1 : i1.val = i0.val + 1 := rfl
            have hv2 : i2.val = i1.val + 1 := rfl
            omega)
        exact hcontra2 i0 i2 hA0 hPi0 hP2
      · have h4 : i0.val - 1 < N - 1 := by omega
        let j1 : Fin (N - 1) := ⟨i0.val - 1, h4⟩
        have h5 : i0.val - 2 < N - 1 := by omega
        let j2 : Fin (N - 1) := ⟨i0.val - 2, h5⟩
        have hA1 : CartanMatrix.A (N - 1) j1 i0 = -1 :=
          l04nD1_cartanA_adj_down j1 i0 (by
            have hv : j1.val = i0.val - 1 := rfl
            omega)
        have hP1 : h j1 ∈ Submodule.span (ZMod p) ({x} : Set V) := hprop i0 j1 hA1 hPi0
        have hA2 : CartanMatrix.A (N - 1) j2 j1 = -1 :=
          l04nD1_cartanA_adj_down j2 j1 (by
            have hv : j2.val = i0.val - 2 := rfl
            have hv1 : j1.val = i0.val - 1 := rfl
            omega)
        have hP2 : h j2 ∈ Submodule.span (ZMod p) ({x} : Set V) := hprop j1 j2 hA2 hP1
        have hA0 : CartanMatrix.A (N - 1) j2 i0 = 0 :=
          l04nD1_cartanA_zero_up j2 i0 (by
            have hv : j2.val = i0.val - 2 := rfl
            omega)
        exact hcontra2 j2 i0 hA0 hP2 hPi0
    obtain ⟨i0, k0, hnc0⟩ := hnc
    exact ⟨i0, k0, ggLin_adj_of_not_commute C.lin.p_ne_two (r i0) (s k0)
      (l04nD1_r_refl C i0) (C.lin.s_refl k0) hnc0
      (l04nD1_notr C (hmem_r i0) (hmem_s k0))⟩
  have hrConn : ∀ i j : Fin (N - 1), Relation.EqvGen Q (r i) (r j) := by
    have hadj_val : ∀ (m : ℕ) (hm : m < N - 1) (hm1 : m + 1 < N - 1),
        GGLinAdj (r ⟨m, hm⟩) (r ⟨m + 1, hm1⟩) := by
      intro m hm hm1
      constructor
      · refine ⟨h ⟨m + 1, hm1⟩, ?_, l04nD1_move_of_adj C ⟨m, hm⟩ ⟨m + 1, hm1⟩ ?_⟩
        · rw [l04nD1_move_eq_span C ⟨m + 1, hm1⟩]
          exact Submodule.subset_span (Set.mem_singleton _)
        · exact l04nD1_cartanA_adj_down ⟨m, hm⟩ ⟨m + 1, hm1⟩ rfl
      · refine ⟨h ⟨m, hm⟩, ?_, l04nD1_move_of_adj C ⟨m + 1, hm1⟩ ⟨m, hm⟩ ?_⟩
        · rw [l04nD1_move_eq_span C ⟨m, hm⟩]
          exact Submodule.subset_span (Set.mem_singleton _)
        · exact l04nD1_cartanA_adj_up ⟨m, hm⟩ ⟨m + 1, hm1⟩ rfl
    have hz : (0 : ℕ) < N - 1 := by have hN := C.lin.N_ge; omega
    let z : Fin (N - 1) := ⟨0, hz⟩
    have hchain : ∀ j : Fin (N - 1), Relation.EqvGen Q (r z) (r j) := by
      intro j
      have hstep : ∀ m (hm : m < N - 1), Relation.EqvGen Q (r z) (r ⟨m, hm⟩) := by
        intro m
        induction m with
        | zero =>
            intro hm
            exact Relation.EqvGen.refl _
        | succ m ih =>
            intro hm
            have hm' : m < N - 1 := by omega
            exact Relation.EqvGen.trans _ _ _ (ih hm') (Relation.EqvGen.rel _ _
              ⟨hmem_r ⟨m, hm'⟩, hmem_r ⟨m + 1, hm⟩, hadj_val m hm' hm⟩)
      exact hstep j.val j.isLt
    intro i j
    exact Relation.EqvGen.trans _ _ _ (hchain i).symm (hchain j)
  have hsConn : ∀ k l : T, Relation.EqvGen Q (s k) (s l) := by
    have hadjS : ∀ a b : T, s a * s b ≠ s b * s a → GGLinAdj (s a) (s b) := by
      intro a b hab
      exact ggLin_adj_of_not_commute C.lin.p_ne_two (s a) (s b) (C.lin.s_refl a) (C.lin.s_refl b)
        hab (l04nD1_notr C (hmem_s a) (hmem_s b))
    intro k l
    have hreach := C.lin.conn.preconnected k l
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    refine l04nD1_eqvGen_of_reflTransGen s ?_ hreach
    intro a b hab
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab with ⟨_, hne | hne⟩
    · exact ⟨hmem_s a, hmem_s b, hadjS a b hne⟩
    · exact ⟨hmem_s a, hmem_s b, l04nD1_adj_symm (hadjS b a hne)⟩
  intro a ha b hb
  change Relation.EqvGen Q a b
  rcases ha with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · rcases hb with ⟨j, rfl⟩ | ⟨l, rfl⟩
    · exact hrConn i j
    · obtain ⟨i0, k0, hik0⟩ := hcross
      exact Relation.EqvGen.trans _ _ _ (hrConn i i0)
        (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ ⟨hmem_r i0, hmem_s k0, hik0⟩) (hsConn k0 l))
  · rcases hb with ⟨j, rfl⟩ | ⟨l, rfl⟩
    · obtain ⟨i0, k0, hik0⟩ := hcross
      exact Relation.EqvGen.trans _ _ _ (hsConn k k0)
        (Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.rel _ _ ⟨hmem_s k0, hmem_r i0, l04nD1_adj_symm hik0⟩) (hrConn i0 j))
    · exact hsConn k l

end CFSG.StandardType

end
