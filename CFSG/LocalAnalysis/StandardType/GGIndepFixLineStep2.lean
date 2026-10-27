module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2Defs
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6f2_pair_diag {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} (S : GGFixLineHyp p N h α r s x)
    (i : Fin (N - 1)) : α i (h i) = 2 := by
  rw [S.pair i i]
  simp [CartanMatrix.A]

private lemma l6f2_rsq {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} (S : GGFixLineHyp p N h α r s x)
    (i : Fin (N - 1)) (v : V) : r i (r i v) = v := by
  rw [S.r_form i (r i v), S.r_form i v, map_sub, map_smul, l6f2_pair_diag S i]
  module

private lemma l6f2_rsymm {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} (S : GGFixLineHyp p N h α r s x)
    (i : Fin (N - 1)) : (r i).symm = r i := by
  ext v
  have h := l6f2_rsq S i ((r i).symm v)
  have h' : r i v = (r i).symm v := by simpa using h
  exact h'.symm

private lemma l6f2_ssymm {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} (S : GGFixLineHyp p N h α r s x)
    (k : ι) : (s k).symm = s k := by
  have hsq : s k * s k = 1 := (S.s_refl k).1
  ext v
  have h2 : s k (s k v) = v := by
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hsq
    simpa using h
  have h3 := congrArg (s k).symm h2
  have h4 : s k v = (s k).symm v := by simpa using h3
  exact h4.symm

private lemma l6f2_mem_T_r {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} (i : Fin (N - 1)) (v : V) :
    r i v - v ∈ ggFixLineT r s := by
  have hm : r i v - v ∈ ggLinMove (r i) := by
    rw [ggLinMove]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  exact Submodule.mem_sup_left ((le_iSup (fun j => ggLinMove (r j)) i) hm)

private lemma l6f2_mem_T_s {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} (k : ι) (v : V) :
    s k v - v ∈ ggFixLineT r s := by
  have hm : s k v - v ∈ ggLinMove (s k) := by
    rw [ggLinMove]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  exact Submodule.mem_sup_right ((le_iSup (fun j => ggLinMove (s j)) k) hm)

theorem ggFixLine_A_le_stab {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Subgroup.closure (Set.range r ∪ Set.range s) ≤ ggLinStab (ggFixLineT r s) := by
  rw [Subgroup.closure_le]
  rintro g (hg | hg)
  · obtain ⟨i, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v hv
      have hm : r i v - v ∈ ggFixLineT r s := l6f2_mem_T_r i v
      have hrv : r i v = v + (r i v - v) := by abel
      rw [hrv]
      exact (ggFixLineT r s).add_mem hv hm
    · intro v hv
      rw [l6f2_rsymm S i]
      have hm : r i v - v ∈ ggFixLineT r s := l6f2_mem_T_r i v
      have hrv : r i v = v + (r i v - v) := by abel
      rw [hrv]
      exact (ggFixLineT r s).add_mem hv hm
  · obtain ⟨k, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · intro v hv
      have hm : s k v - v ∈ ggFixLineT r s := l6f2_mem_T_s k v
      have hrv : s k v = v + (s k v - v) := by abel
      rw [hrv]
      exact (ggFixLineT r s).add_mem hv hm
    · intro v hv
      rw [l6f2_ssymm S k]
      have hm : s k v - v ∈ ggFixLineT r s := l6f2_mem_T_s k v
      have hrv : s k v = v + (s k v - v) := by abel
      rw [hrv]
      exact (ggFixLineT r s).add_mem hv hm

@[expose] noncomputable def ggFixLineQ {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) :=
  MonoidHom.range ((ggLinRestrictHom (ggFixLineT r s)).comp (Subgroup.inclusion (ggFixLine_A_le_stab S)))

private lemma l6f2_mem_fix {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (A : Set (V ≃ₗ[ZMod p] V)) (v : V) :
    v ∈ ggLinFix A ↔ ∀ a ∈ A, a v = v := by
  rfl

private lemma l6f2_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
  have hp2 : p = 2 := by
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact hp hp2

private lemma l6f2_h_mem_T {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} (S : GGFixLineHyp p N h α r s x)
    (i : Fin (N - 1)) : h i ∈ ggFixLineT r s := by
  have h2 : (2 : ZMod p) ≠ 0 := l6f2_two_ne_zero S.odd
  have hc2 : (-(2 : ZMod p)⁻¹) * 2 = -1 := by
    rw [neg_mul, inv_mul_cancel₀ h2]
  have heq : h i = (-(2 : ZMod p)⁻¹) • (r i (h i) - h i) := by
    rw [S.r_form i (h i), l6f2_pair_diag S i, smul_sub, smul_sub, smul_smul, hc2,
      neg_one_smul]
    module
  rw [heq]
  exact (ggFixLineT r s).smul_mem _ (l6f2_mem_T_r i (h i))

theorem ggFixLine_T_props {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    (∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s), ∀ v, g v - v ∈ ggFixLineT r s) ∧
      Submodule.span (ZMod p) (Set.range h) ≤ ggFixLineT r s ∧
      N - 1 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) ∧
      Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N := by
  haveI : Finite ι := S.finite_family
  haveI : Module.Finite (ZMod p) V :=
    ggFixLine_finite (p := p) s S.s_refl S.fix_H
  have hA : ∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s), ∀ v,
      g v - v ∈ ggFixLineT r s := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | one =>
        intro v
        simp
    | mem a ha =>
        intro v
        rcases ha with ⟨i, rfl⟩ | ⟨k, rfl⟩
        · exact l6f2_mem_T_r i v
        · exact l6f2_mem_T_s k v
    | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
        intro v
        have hmul : (g₁ * g₂) v = g₁ (g₂ v) := rfl
        rw [hmul]
        have h1 := ih₁ (g₂ v)
        have h2 := ih₂ v
        have heq : g₁ (g₂ v) - v = (g₁ (g₂ v) - g₂ v) + (g₂ v - v) := by abel
        rw [heq]
        exact (ggFixLineT r s).add_mem h1 h2
    | inv g hg ih =>
        intro v
        have h1 := ih ((g⁻¹) v)
        have hfun : g ((g⁻¹) v) = v := by simp
        rw [hfun] at h1
        have heq : (g⁻¹) v - v = -(v - (g⁻¹) v) := by abel
        rw [heq]
        exact (ggFixLineT r s).neg_mem h1
  have hspan : Submodule.span (ZMod p) (Set.range h) ≤ ggFixLineT r s := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact l6f2_h_mem_T S i
  have hdim : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h)) = N - 1 := by
    rw [finrank_span_eq_card (R := ZMod p) (b := h) S.indep, Fintype.card_fin]
  have hle : N - 1 ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := by
    calc N - 1 = Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range h)) :=
          hdim.symm
      _ ≤ Module.finrank (ZMod p) ↥(ggFixLineT r s) := Submodule.finrank_mono hspan
  have hleN : Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤ N :=
    (Submodule.finrank_le (ggFixLineT r s)).trans S.dim_le
  exact ⟨hA, hspan, hle, hleN⟩

theorem ggFixLine_fix_A {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) : ggLinFix (Set.range r ∪ Set.range s) = ⊥ := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_bot]
    have hvs : v ∈ ggLinFix (Set.range s) := by
      rw [l6f2_mem_fix]
      intro a ha
      exact (l6f2_mem_fix _ v).mp hv a (Set.mem_union_right _ ha)
    rw [S.fix_H] at hvs
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvs
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · have hx : x ∈ ggLinFix (Set.range r) := by
        rw [l6f2_mem_fix]
        intro a ha
        obtain ⟨i, rfl⟩ := ha
        have hv' : r i (c • x) = c • x :=
          (l6f2_mem_fix _ _).mp hv (r i) (Set.mem_union_left _ (Set.mem_range_self i))
        have h1 : c • r i x = c • x := by
          rw [← map_smul, hv']
        have h2 := congrArg (fun y => c⁻¹ • y) h1
        rw [smul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, one_smul] at h2
        exact h2
      exact absurd hx S.x_not_fix
  · intro v hv
    rw [Submodule.mem_bot] at hv
    rw [hv]
    exact Submodule.zero_mem _

theorem ggFixLine_cross_pair {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) : ∃ (k : ι) (i : Fin (N - 1)), s k * r i ≠ r i * s k := by
  by_contra h
  have hcomm : ∀ k i, s k * r i = r i * s k := by
    intro k i
    by_contra hne
    exact h ⟨k, i, hne⟩
  have hpres : ∀ i (v : V), v ∈ ggLinFix (Set.range s) → r i v ∈ ggLinFix (Set.range s) := by
    intro i v hv
    rw [l6f2_mem_fix] at hv ⊢
    intro a ha
    obtain ⟨k, rfl⟩ := ha
    have hc := hcomm k i
    have hfix := hv (s k) (Set.mem_range_self k)
    calc s k (r i v) = (s k * r i) v := rfl
      _ = (r i * s k) v := by rw [hc]
      _ = r i (s k v) := rfl
      _ = r i v := by rw [hfix]
  have hxS : x ∈ ggLinFix (Set.range s) := by
    rw [S.fix_H]
    exact Submodule.subset_span (Set.mem_singleton x)
  have hw : ∀ i, ∃ c : ZMod p, r i x = c • x := by
    intro i
    have hmem : r i x ∈ Submodule.span (ZMod p) {x} := by
      rw [← S.fix_H]
      exact hpres i x hxS
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  have hline := ggFixLine_invariant_line S.odd S.five_le S.indep S.pair S.r_form hw
  have hxr : x ∈ ggLinFix (Set.range r) := by
    rw [l6f2_mem_fix]
    intro a ha
    obtain ⟨i, rfl⟩ := ha
    exact hline i
  exact S.x_not_fix hxr

private lemma l6f2_restrict_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (T : Submodule (ZMod p) V) (g : ↥(ggLinStab T)) (v : ↥T) :
    (((ggLinRestrictHom T g) v : ↥T) : V) = (g : V ≃ₗ[ZMod p] V) (v : V) := by
  simp [ggLinRestrictHom, LinearEquiv.ofSubmodules_apply]

theorem ggFixLine_restrict_injective {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Function.Injective ((ggLinRestrictHom (ggFixLineT r s)).comp
      (Subgroup.inclusion (ggFixLine_A_le_stab S))) := by
  haveI : Finite ι := S.finite_family
  haveI : Module.Finite (ZMod p) V :=
    ggFixLine_finite (p := p) s S.s_refl S.fix_H
  rw [injective_iff_map_eq_one]
  intro a ha
  have hT := ggFixLine_T_props S
  have hTfix : ∀ v : V, v ∈ ggFixLineT r s → (a : V ≃ₗ[ZMod p] V) v = v := by
    intro v hv
    have h1 : (ggLinRestrictHom (ggFixLineT r s))
        (Subgroup.inclusion (ggFixLine_A_le_stab S) a) = 1 := ha
    have h3 : ((ggLinRestrictHom (ggFixLineT r s))
        (Subgroup.inclusion (ggFixLine_A_le_stab S) a)) ⟨v, hv⟩ = ⟨v, hv⟩ := by
      rw [h1]
      rfl
    have h4 := congrArg Subtype.val h3
    rw [l6f2_restrict_apply] at h4
    simpa [Subgroup.coe_inclusion] using h4
  have hsq : ∀ w, (a : V ≃ₗ[ZMod p] V) ((a : V ≃ₗ[ZMod p] V) w - w) =
      (a : V ≃ₗ[ZMod p] V) w - w := by
    intro w
    exact hTfix _ (hT.1 a.1 a.2 w)
  let φ : V →ₗ[ZMod p] V := (a : V ≃ₗ[ZMod p] V).toLinearMap - LinearMap.id
  have hker : ggFixLineT r s ≤ LinearMap.ker φ := by
    intro v hv
    rw [LinearMap.mem_ker]
    change (a : V ≃ₗ[ZMod p] V) v - v = 0
    exact sub_eq_zero.mpr (hTfix v hv)
  have hle1 : Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) ≤ 1 := by
    have hmove : ggLinMove (a : V ≃ₗ[ZMod p] V) = LinearMap.range φ := rfl
    rw [hmove]
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have hkerle : Module.finrank (ZMod p) ↥(ggFixLineT r s) ≤
        Module.finrank (ZMod p) ↥(LinearMap.ker φ) := Submodule.finrank_mono hker
    have hdimT := hT.2.2.1
    have hdimV := S.dim_le
    omega
  have hnt := S.no_transvection a.1 a.2
  have hne : Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) ≠ 1 := by
    intro h1
    exact hnt ⟨h1, hsq⟩
  have hzero : Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) = 0 := by
    omega
  have hbot : ggLinMove (a : V ≃ₗ[ZMod p] V) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    have hspan : Submodule.span (ZMod p) {v} ≤ ggLinMove (a : V ≃ₗ[ZMod p] V) := by
      rw [Submodule.span_le]
      rintro w rfl
      exact hv
    have h1 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {v}) ≤
        Module.finrank (ZMod p) (ggLinMove (a : V ≃ₗ[ZMod p] V)) :=
      Submodule.finrank_mono hspan
    rw [finrank_span_singleton hv0, hzero] at h1
    omega
  have hb : LinearMap.range φ = ⊥ := by simpa [φ, ggLinMove] using hbot
  have hφ : φ = 0 := LinearMap.range_eq_bot.mp hb
  have ha1 : (a : V ≃ₗ[ZMod p] V) = 1 := by
    ext v
    have hv : (a : V ≃ₗ[ZMod p] V) v - v = 0 := by
      have h := congrArg (fun f : V →ₗ[ZMod p] V => f v) hφ
      simpa [φ] using h
    simpa using sub_eq_zero.mp hv
  exact Subtype.ext ha1

end CFSG.StandardType

end
