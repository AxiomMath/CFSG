module

public import CFSG.LocalAnalysis.StandardType.GGTBFix
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResI_mem_ggInduced_top {G : Type} [Group G] {L Bs K : Subgroup G}
    {ψ : MulAut ↥Bs} (h : ψ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs) : ψ ∈ ggInduced ⊤ Bs := by
  have hsub : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs := by
    apply sup_le <;> apply Subgroup.closure_mono <;> rintro φ ⟨g, -, hgN, hg⟩ <;>
      exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  exact mem_ggAutomizer_iff.mp (hsub h)

theorem ggResI_automizer_fix {G : Type} [Group G] {Bs X : Subgroup G} {z : G}
    (hzBs : z ∈ Bs) (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) :
    ∀ φ ∈ ggAutomizer X Bs, φ ⟨z, hzBs⟩ = ⟨z, hzBs⟩ := by
  intro φ hφ
  obtain ⟨g, hgX, _, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  apply Subtype.ext
  rw [hφg]
  have hzg : z * g = g * z :=
    (Subgroup.mem_centralizer_iff.mp (hXz hgX)) z (Set.mem_singleton z)
  rw [← hzg]
  group

theorem ggResI_alpha_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {r : V ≃ₗ[ZMod p] V} {hv w : V}
    {αv : Module.Dual (ZMod p) V} (hr : ∀ w, r w = w - αv w • hv) (h2 : αv hv = 2)
    (hfix : r w = w) : αv w = 0 := by
  have hne : hv ≠ 0 := by
    rintro rfl
    rw [map_zero] at h2
    exact zmod_two_ne_zero hp2 h2.symm
  rw [hr, sub_eq_self] at hfix
  exact (smul_eq_zero.mp hfix).resolve_right hne

theorem ggResI_sup_eq_closure {G : Type} [Group G] {Bs L K : Subgroup G} {Λ : Type} {b : Λ}
    {φ : Option Λ → MulAut ↥Bs}
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none})) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) := by
  rw [hAL, hAK, ← Subgroup.closure_union]
  congr 1
  ext γ
  constructor
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl)
    · exact ⟨some i, rfl⟩
    · exact ⟨some j, rfl⟩
    · exact ⟨none, rfl⟩
  · rintro ⟨o, rfl⟩
    cases o with
    | none => exact Or.inr (Or.inr rfl)
    | some i => exact Or.inl ⟨i, rfl⟩

theorem ggResI_map_sup {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs L K : Subgroup G}
    {Λ : Type}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Option Λ → MulAut ↥Bs}
    (hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)) := by
  rw [hA, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem ggResI_false_of_transvection {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L K : Subgroup G} (hNT : GGNoTransvection p Bs) {Λ : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) {φ : Option Λ → MulAut ↥Bs}
    (hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    {t : V ≃ₗ[ZMod p] V}
    (ht : t ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)))
    (htv : Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w) : False := by
  rw [← ggResI_map_sup ι hA] at ht
  obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp ht
  exact hNT ψ (ggResI_mem_ggInduced_top hψA) (ggRC_isTransvection_of_lin ι ψ htv)

section Basis

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {y : G} {K : Subgroup G} {Λ : Type} {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V}

omit [Finite G] [Fact p.Prime] in
theorem ggResI_fix_zpowers_of_fixed
    (hfixed : ∀ bb : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb) →
      (bb : G) ∈ Subgroup.zpowers x)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (bb : ↥Bs) (hgen : ∀ i : Λ, φ (some i) bb = bb) : (bb : G) ∈ Subgroup.zpowers x := by
  have hall : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
    rw [hAL]
    exact ggFixed_of_mem_closure (fun i : Λ => φ (some i)) bb hgen
  exact hfixed bb hall

omit [Finite G] in
theorem ggResI_fixSpan_of_fixed
    (hfixed : ∀ bb : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb) →
      (bb : G) ∈ Subgroup.zpowers x)
    (hxBs : x ∈ Bs) (ι : Additive ↥Bs ≃+ V)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i))) :
    ∀ w : V, (∀ i : Λ, α (some i) w = 0) →
      w ∈ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hxBs⟩)} := by
  intro w hw
  set bb : ↥Bs := Additive.toMul (ι.symm w) with hbb
  have hwbb : ι (Additive.ofMul bb) = w := by simp [hbb]
  have hgen : ∀ i : Λ, φ (some i) bb = bb := by
    intro i
    rw [ggLin_fix_iff (p := p) ι, hwbb, hφ, hw i, zero_smul, sub_zero]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (ggResI_fix_zpowers_of_fixed hfixed hAL bb hgen)
  have hbk : bb = (⟨x, hxBs⟩ : ↥Bs) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
  rw [← hwbb, hbk, ofMul_zpow, map_zsmul]
  exact Submodule.mem_span_singleton.mpr ⟨(k : ZMod p), by rw [Int.cast_smul_eq_zsmul]⟩

theorem ggResI_fixSpan (hFix : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (hxBs : x ∈ Bs) (ι : Additive ↥Bs ≃+ V)
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i))) :
    ∀ w : V, (∀ i : Λ, α (some i) w = 0) →
      w ∈ Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hxBs⟩)} :=
  ggResI_fixSpan_of_fixed
    (fun bb hall => hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
      hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hall)
    hxBs ι hφ hAL

theorem ggResI_span_top_of_fixed [Fintype Λ]
    (hfixed : ∀ bb : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb) →
      (bb : G) ∈ Subgroup.zpowers x)
    (hH : GGResHyp p B Bs x L D J y K)
    (ι : Additive ↥Bs ≃+ V) (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hind : LinearIndependent (ZMod p) h) :
    Submodule.span (ZMod p) (Set.range h) = ⊤ := by
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx : x ^ p = 1 := hH.1.tableB_facts.2.1.2 x hxBs
  have hfam : ggOptFam (h none) (fun i : Λ => h (some i)) = h := by
    funext o
    cases o <;> rfl
  have hspan := ggTBSpan_of_fix_le hx ι (fun i : Λ => φ (some i)) (fun i => h (some i))
    (fun i => α (some i)) (h none) (fun i w => hφ (some i) w) (by rw [hfam]; exact hind)
    (ggResI_fix_zpowers_of_fixed hfixed hAL)
  rwa [hfam] at hspan

theorem ggResI_span_top [Fintype Λ] (hFix : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    (ι : Additive ↥Bs ≃+ V) (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hind : LinearIndependent (ZMod p) h) :
    Submodule.span (ZMod p) (Set.range h) = ⊤ :=
  ggResI_span_top_of_fixed
    (fun bb hall => hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
      hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hall)
    hH ι hφ hAL hind

theorem ggResI_finrank [Fintype Λ] (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤)
    (hind : LinearIndependent (ZMod p) h) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
  rw [← finrank_top (ZMod p) V, ← hspan, finrank_span_eq_card hind, Fintype.card_option]

theorem ggResI_three_le_card [Fintype Λ] (hH : GGResHyp p B Bs x L D J y K)
    (ι : Additive ↥Bs ≃+ V) (hdim : Module.finrank (ZMod p) V = Fintype.card Λ + 1) :
    3 ≤ Fintype.card Λ := by
  obtain ⟨hp, -, -, -, h4⟩ := hH.1.tableB_facts
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hcard : Nat.card ↥Bs = Nat.card V := Nat.card_congr (Additive.ofMul.trans ι.toEquiv)
  have hV := FiniteField.pow_finrank_eq_natCard p V
  rw [hdim] at hV
  have hle : p ^ 4 ≤ p ^ (Fintype.card Λ + 1) := by
    rw [hV, ← hcard]
    exact h4
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  omega

end Basis

theorem ggRes_raw_commonKernel_le_xline
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hFix : GGTBFixInput) (hH : GGResHyp p B Bs x L D J y K)
    {Λ Λa : Type} (a0 : Λa)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V)
    (hlin : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hclosL : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i))) :
    ∀ w : V, (∀ i : Λ, α (Sum.inl i) w = 0) →
      ∃ lam : ZMod p,
        w = lam • ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) := by
  let node : Option Λ → Λ ⊕ Λa := fun o => match o with
    | none => Sum.inr a0
    | some i => Sum.inl i
  have hlinO : ∀ o w,
      ggLin (p := p) ι ((φ ∘ node) o) w =
        w - (α ∘ node) o w • (h ∘ node) o := by
    intro o w
    exact hlin (node o) w
  have hclosO : ggAutomizer L Bs =
      Subgroup.closure (Set.range fun i : Λ => (φ ∘ node) (some i)) := hclosL
  intro w hw
  have hspan := ggResI_fixSpan (p := p) (Λ := Λ) (V := V)
    (φ := φ ∘ node) (h := h ∘ node) (α := α ∘ node)
    hFix hH hH.1.tableB_facts.2.2.1 ι hlinO hclosO w hw
  rw [Submodule.mem_span_singleton] at hspan
  obtain ⟨lam, hlam⟩ := hspan
  exact ⟨lam, hlam.symm⟩

end CFSG.StandardType
