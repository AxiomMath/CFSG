module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleConnected
import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleAdj
import CFSG.LocalAnalysis.StandardType.GGDepARefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma l04fD2_pair_diag {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) (i : Fin (N - 1)) : α i (h i) = 2 := by
  rw [C.lin.pair i i]
  simp [CartanMatrix.A]

lemma l04fD2_mem_T_r {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {T : Type} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : T → (V ≃ₗ[ZMod p] V)} (i : Fin (N - 1)) (v : V) :
    r i v - v ∈ ggFixLineT r s := by
  have hm : r i v - v ∈ ggLinMove (r i) := by
    rw [ggLinMove]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  exact Submodule.mem_sup_left ((le_iSup (fun j => ggLinMove (r j)) i) hm)

lemma l04fD2_mem_T_s {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} (k : ι) (v : V) :
    s k v - v ∈ ggFixLineT r s := by
  have hm : s k v - v ∈ ggLinMove (s k) := by
    rw [ggLinMove]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  exact Submodule.mem_sup_right ((le_iSup (fun j => ggLinMove (s j)) k) hm)

lemma l04fD2_rsq {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) (i : Fin (N - 1)) (v : V) : r i (r i v) = v := by
  rw [C.lin.refl_form i (r i v), C.lin.refl_form i v, map_sub, map_smul, l04fD2_pair_diag C i]
  module

lemma l04fD2_rsymm {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) (i : Fin (N - 1)) : (r i).symm = r i := by
  ext v
  have h := l04fD2_rsq C i ((r i).symm v)
  have h' : r i v = (r i).symm v := by simpa using h
  exact h'.symm

lemma l04fD2_ssymm {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) (k : T) : (s k).symm = s k := by
  have hsq : s k * s k = 1 := (C.lin.s_refl k).1
  ext v
  have h2 : s k (s k v) = v := by
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hsq
    simpa using h
  have h3 := congrArg (s k).symm h2
  have h4 : s k v = (s k).symm v := by simpa using h3
  exact h4.symm

lemma l04fD2_mem_fix {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (A : Set (V ≃ₗ[ZMod p] V)) (v : V) :
    v ∈ ggLinFix A ↔ ∀ a ∈ A, a v = v := Iff.rfl

lemma l04fD2_restrict_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (T : Submodule (ZMod p) V) (g : ↥(ggLinStab T)) (v : ↥T) :
    (((ggLinRestrictHom T g) v : ↥T) : V) = (g : V ≃ₗ[ZMod p] V) (v : V) := by
  simp [ggLinRestrictHom]

lemma l04fD2_finite {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) : Module.Finite (ZMod p) V := by
  have : Finite T := C.lin.finT
  exact ggFixLine_finite s C.lin.s_refl C.lin.fix_s

lemma l04fD2_h_mem_T {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) (i : Fin (N - 1)) : h i ∈ ggFixLineT r s := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero C.lin.p_ne_two
  have hc2 : (-(2 : ZMod p)⁻¹) * 2 = -1 := by
    rw [neg_mul, inv_mul_cancel₀ h2]
  have heq : h i = (-(2 : ZMod p)⁻¹) • (r i (h i) - h i) := by
    rw [C.lin.refl_form i (h i), l04fD2_pair_diag C i, smul_sub, smul_sub, smul_smul, hc2,
      neg_one_smul]
    module
  rw [heq]
  exact (ggFixLineT r s).smul_mem _ (l04fD2_mem_T_r i (h i))

lemma l04fD2_A_le_stab {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) :
    ggLargeGrp r s ≤ ggLinStab (ggFixLineT r s) := by
  rw [ggLargeGrp, Subgroup.closure_le]
  rintro g (hg | hg)
  · obtain ⟨i, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v hv
      have hm : r i v - v ∈ ggFixLineT r s := l04fD2_mem_T_r i v
      have hrv : r i v = v + (r i v - v) := by abel
      rw [hrv]
      exact (ggFixLineT r s).add_mem hv hm
    · intro v hv
      rw [l04fD2_rsymm C i]
      have hm : r i v - v ∈ ggFixLineT r s := l04fD2_mem_T_r i v
      have hrv : r i v = v + (r i v - v) := by abel
      rw [hrv]
      exact (ggFixLineT r s).add_mem hv hm
  · obtain ⟨k, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v hv
      have hm : s k v - v ∈ ggFixLineT r s := l04fD2_mem_T_s k v
      have hrv : s k v = v + (s k v - v) := by abel
      rw [hrv]
      exact (ggFixLineT r s).add_mem hv hm
    · intro v hv
      rw [l04fD2_ssymm C k]
      have hm : s k v - v ∈ ggFixLineT r s := l04fD2_mem_T_s k v
      have hrv : s k v = v + (s k v - v) := by abel
      rw [hrv]
      exact (ggFixLineT r s).add_mem hv hm

lemma l04fD2_disp {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (_C : GGLargeDepCase p N h α r s x) :
    ∀ g ∈ ggLargeGrp r s, ∀ v, g v - v ∈ ggFixLineT r s := by
  intro g hg
  rw [ggLargeGrp] at hg
  induction hg using Subgroup.closure_induction with
  | one => intro v; simp
  | mem a ha =>
      intro v
      rcases ha with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · exact l04fD2_mem_T_r i v
      · exact l04fD2_mem_T_s k v
  | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
      intro v
      have h1 := ih₁ (g₂ v)
      have h2 := ih₂ v
      have heq : g₁ (g₂ v) - v = (g₁ (g₂ v) - g₂ v) + (g₂ v - v) := by abel
      rw [LinearEquiv.mul_apply, heq]
      exact (ggFixLineT r s).add_mem h1 h2
  | inv g hg ih =>
      intro v
      have h1 := ih ((g⁻¹) v)
      have hfun : g ((g⁻¹) v) = v := by simp
      rw [hfun] at h1
      have heq : (g⁻¹) v - v = -(v - (g⁻¹) v) := by abel
      rw [heq]
      exact (ggFixLineT r s).neg_mem h1

lemma l04fD2_com_eq_T {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) :
    ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)) = ggFixLineT r s := by
  apply le_antisymm
  · rw [ggLinCom]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha v hv
    rw [ggLinMove] at hv
    obtain ⟨w, rfl⟩ := hv
    exact l04fD2_disp C a ha w
  · rw [ggFixLineT]
    apply sup_le
    · apply iSup_le; intro i
      exact le_iSup₂ (f := fun a (_ : a ∈ (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V))) =>
        ggLinMove a) (r i) (Subgroup.subset_closure (Or.inl ⟨i, rfl⟩))
    · apply iSup_le; intro k
      exact le_iSup₂ (f := fun a (_ : a ∈ (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V))) =>
        ggLinMove a) (s k) (Subgroup.subset_closure (Or.inr ⟨k, rfl⟩))

lemma l04fD2_com_le_T {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) :
    ggLinCom (ggLargeGrp r s : Set (V ≃ₗ[ZMod p] V)) ≤ ggFixLineT r s :=
  (l04fD2_com_eq_T C).le

lemma l04fD2_fix_A {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) : ggLinFix (Set.range r ∪ Set.range s) = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    have hvs : v ∈ ggLinFix (Set.range s) := by
      rw [l04fD2_mem_fix]
      intro a ha
      exact (l04fD2_mem_fix _ v).mp hv a (Set.mem_union_right _ ha)
    rw [C.lin.fix_s] at hvs
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvs
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · have hx : x ∈ ggLinFix (Set.range r) := by
        rw [l04fD2_mem_fix]
        intro a ha
        obtain ⟨i, rfl⟩ := ha
        have hv' : r i (c • x) = c • x :=
          (l04fD2_mem_fix _ _).mp hv (r i) (Set.mem_union_left _ (Set.mem_range_self i))
        have h1 : c • r i x = c • x := by rw [← map_smul, hv']
        have h2 := congrArg (fun y => c⁻¹ • y) h1
        rw [smul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, one_smul] at h2
        exact h2
      exact absurd hx C.lin.x_not_fix
  · intro v hv
    rw [Submodule.mem_bot] at hv
    rw [hv]
    exact Submodule.zero_mem _

lemma l04fD2_move_eq_span {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (a : V ≃ₗ[ZMod p] V) {c : V}
    {β : Module.Dual (ZMod p) V} (hβc : β c = 2) (hform : ∀ v, a v = v - β v • c) :
    ggLinMove a = Submodule.span (ZMod p) {c} := by
  have hβ0 : β ≠ 0 := by
    intro hzero
    rw [hzero] at hβc
    exact (zmod_two_ne_zero hp2) hβc.symm
  have hL : a.toLinearMap - LinearMap.id = (-β).smulRight c := by
    ext v
    change a v - v = (-β) v • c
    rw [hform v]
    simp only [LinearMap.neg_apply, neg_smul]
    abel
  rw [ggLinMove, hL, LinearMap.range_smulRight_apply (neg_ne_zero.mpr hβ0)]

lemma l04fD2_restrict_refl {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (T : Submodule (ZMod p) V) (g : ↥(ggLinStab T))
    {c : V} (hcT : c ∈ T) {β : Module.Dual (ZMod p) V} (hβc : β c = 2)
    (hform : ∀ v, (g : V ≃ₗ[ZMod p] V) v = v - β v • c) :
    GGLinRefl (ggLinRestrictHom T g) := by
  have hform_t : ∀ w : ↥T, ggLinRestrictHom T g w =
      w - (β.comp T.subtype) w • (⟨c, hcT⟩ : ↥T) := by
    intro w
    apply Subtype.ext
    show ((ggLinRestrictHom T g w : ↥T) : V) = (w : V) - (β.comp T.subtype w) • c
    rw [l04fD2_restrict_apply, hform]
    simp [LinearMap.comp_apply, Submodule.subtype_apply]
  have hβ'c' : (β.comp T.subtype) (⟨c, hcT⟩ : ↥T) = 2 := by
    simp [LinearMap.comp_apply, Submodule.subtype_apply, hβc]
  exact (ggDepA_linRefl_iff hp2 (ggLinRestrictHom T g)).mpr
    ⟨⟨c, hcT⟩, β.comp T.subtype, hβ'c', hform_t⟩

lemma l04fD2_span_h_finrank {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) :
    N - 2 ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h)) := by
  let Φ : (Fin (N - 1) → ZMod p) →ₗ[ZMod p] V :=
    { toFun := fun c => ∑ k : Fin (N - 1), c k • h k
      map_add' := by intro c d; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply] }
  have hrange : LinearMap.range Φ = Submodule.span (ZMod p) (Set.range h) := by
    ext v
    rw [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
    exact Iff.rfl
  let dvec : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  have hd : ∀ j : Fin (N - 1),
      ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) j k : ZMod p) * dvec k = 0 := by
    intro j
    simpa [dvec] using l6aF_A_mul_d (p := p) (N := N) C.lin.p_dvd j
  have hd_ne : dvec ≠ 0 := by
    intro h0
    have := congr_fun h0 ⟨0, by have := C.lin.N_ge; omega⟩
    simp [dvec] at this
  have hker_le : LinearMap.ker Φ ≤ Submodule.span (ZMod p) {dvec} := by
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hcA : ∀ j : Fin (N - 1),
        ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) j k : ZMod p) * c k = 0 := by
      intro j
      have h1 : α j (∑ k : Fin (N - 1), c k • h k) = 0 := by
        have h0 : α j (Φ c) = 0 := by rw [hc]; simp
        simpa [Φ] using h0
      rw [map_sum] at h1
      simp only [map_smul, smul_eq_mul, C.lin.pair] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    obtain ⟨l, hl⟩ :=
      ggCartanA_ker_le_one (p := p) (N := N - 1) dvec c hd hcA hd_ne
    rw [Submodule.mem_span_singleton]
    exact ⟨l, hl.symm⟩
  have hkerdim : Module.finrank (ZMod p) ↥(LinearMap.ker Φ) ≤ 1 := by
    calc Module.finrank (ZMod p) ↥(LinearMap.ker Φ)
        ≤ Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {dvec}) :=
          Submodule.finrank_mono hker_le
      _ = 1 := finrank_span_singleton hd_ne
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hdom : Module.finrank (ZMod p) (Fin (N - 1) → ZMod p) = N - 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [hrange, hdom] at hrn
  omega

lemma l04fD2_finrank_bounds {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {T : Type} {s : T → (V ≃ₗ[ZMod p] V)} {x : V}
    (C : GGLargeDepCase p N h α r s x) :
    N - 2 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) ∧
      Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N := by
  have : Module.Finite (ZMod p) V := l04fD2_finite C
  have hspan : Submodule.span (ZMod p) (Set.range h) ≤ ggFixLineT r s := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact l04fD2_h_mem_T C i
  have hlow : N - 2 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) :=
    (l04fD2_span_h_finrank C).trans (Submodule.finrank_mono hspan)
  have hup : Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N :=
    (Submodule.finrank_le (ggFixLineT r s)).trans C.lin.dim_le
  exact ⟨hlow, hup⟩

end CFSG.StandardType

end
