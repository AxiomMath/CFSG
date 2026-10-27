module

public import CFSG.LocalAnalysis.StandardType.GGForkIndefLattice
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggAutomizer_fixes_mem_normalizer (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hx : x ∈ Bs) {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs) (hfix : φ ⟨x, hx⟩ = ⟨x, hx⟩) :
    φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) := by
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hI : GGThmIHyp p B x L := hcfg.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hnc := ha₀ G p B x L hI
  have hgx : g * x * g⁻¹ ∈ Subgroup.zpowers x := by
    have h1 : g * x * g⁻¹ = x := by
      have h2 := hφg ⟨x, hx⟩
      rw [hfix] at h2
      simpa using h2.symm
    rw [h1]
    exact Subgroup.mem_zpowers x
  have hgL : g ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_sstar' hS hnc
      (CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem hgx)
  have hφi := inv_apply_of_forall hφg
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
    refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgL l).mp hl,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN), fun b => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hψl, hφi]
    group
  · intro hψ
    obtain ⟨l, hl, hlN, hψl⟩ := mem_ggAutomizer_iff.mp hψ
    have hgL' := Subgroup.inv_mem _ hgL
    have hgN' := Subgroup.inv_mem _ hgN
    refine mem_ggAutomizer_iff.mpr ⟨g⁻¹ * l * g, ?_, ?_, fun b => ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp hgL' l).mp hl
    · simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN' hlN) hgN
    · have hψeq : ψ = φ⁻¹ * (φ * ψ * φ⁻¹) * φ := by group
      rw [hψeq, MulAut.mul_apply, MulAut.mul_apply, hφi, hψl, hφg]
      group

theorem ggAutomizer_preserves_span_coroot (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hx : x ∈ Bs)
    {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer ⊤ Bs) (hfix : t ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ v ∈ Submodule.span (ZMod p) (Set.range h),
      ggLin (p := p) ι t v ∈ Submodule.span (ZMod p) (Set.range h) :=
  l6tr_normalizer_span (p := p) hφ hrefl hAL
    (ggAutomizer_fixes_mem_normalizer ha₀ hcfg hx ht hfix)

private theorem p3ln_alpha_eq_zero {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {N : Type}
    {ι : Additive ↥Bs ≃+ V} {X : Matrix N N ℤ} {φ' : N → MulAut ↥Bs} {h' : N → V}
    {α' : N → Module.Dual (ZMod p) V} (hD : GGExtDatum ι X φ' h' α') {x : G} (hx : x ∈ Bs)
    {H : Subgroup G} (hH : H ≤ Subgroup.centralizer ({x} : Set G)) {o : N}
    (hφ : φ' o ∈ ggAutomizer H Bs) :
    α' o (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) = 0 := by
  obtain ⟨g, hgH, -, hgval⟩ := mem_ggAutomizer_iff.mp hφ
  have hcomm : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hH hgH)
  have hgx : g * x * g⁻¹ = x := by
    rw [hcomm]
    group
  have hfix : φ' o ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply Subtype.ext
    rw [hgval ⟨x, hx⟩, hgx]
  have hlin := hD.lin o (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)))
  have hfix' : ggLin (p := p) ι (φ' o) (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) =
      ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) :=
    (ggLin_fix_iff ι (φ' o) ⟨x, hx⟩).mp hfix
  rw [hfix'] at hlin
  have hzero : α' o (ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))) • h' o = 0 :=
    sub_eq_self.mp hlin.symm
  rcases smul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd h (hD.indep.ne_zero o)

private theorem p3ln_word_fixes_x {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V}
    {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α') {x : G} (hxBs : x ∈ Bs)
    (hx : ∀ i : Λ, α' (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0)
    (ψ : List (Option Λ)) (k : Option Λ)
    (ha : ((ggSWordR X ψ (Pi.single k 1) none : ℤ) : ZMod p) = 0) :
    ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹)
      (ι (Additive.ofMul ⟨x, hxBs⟩)) = ι (Additive.ofMul ⟨x, hxBs⟩) := by
  set xv : V := ι (Additive.ofMul ⟨x, hxBs⟩) with hxv
  have hsum : (∑ o, ((ggSWordR X ψ (Pi.single k 1) o : ℤ) : ZMod p) * α' o xv) = 0 := by
    rw [Fintype.sum_option]
    have h1 : ((ggSWordR X ψ (Pi.single k 1) none : ℤ) : ZMod p) * α' none xv = 0 := by
      rw [ha, zero_mul]
    have h2 : ∀ i : Λ,
        ((ggSWordR X ψ (Pi.single k 1) (some i) : ℤ) : ZMod p) * α' (some i) xv = 0 := by
      intro i
      rw [hx i, mul_zero]
    rw [h1, Finset.sum_eq_zero (fun i _ => h2 i), add_zero]
  have hfix : ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) xv = xv := by
    have h3 := (ggExtDatum_word hD ψ k).2.2 xv
    rw [h3, hsum, zero_smul, sub_zero]
  simpa [hxv] using hfix

theorem ggExtDatum_lin_mem_normalizer (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {ι : Additive ↥Bs ≃+ V} {X : Matrix (Option Λ) (Option Λ) ℤ}
    {φ' : Option Λ → MulAut ↥Bs} {h' : Option Λ → V} {α' : Option Λ → Module.Dual (ZMod p) V}
    (hD : GGExtDatum ι X φ' h' α')
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ' (some i)))
    (ψ : List (Option Λ)) (k : Option Λ)
    (ha : ((ggSWordR X ψ (Pi.single k 1) none : ℤ) : ZMod p) = 0) :
    ggLin (p := p) ι ((ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹) ∈
      Subgroup.normalizer (Subgroup.closure (Set.range fun i : Λ =>
        ggLin (p := p) ι (φ' (some i))) : Set (V ≃ₗ[ZMod p] V)) := by
  obtain ⟨-, -, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hx : ∀ i : Λ, α' (some i) (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0 := by
    intro i
    exact p3ln_alpha_eq_zero hD hxBs hLx (by
      rw [hAL]
      exact Subgroup.subset_closure ⟨i, rfl⟩)
  set t : MulAut ↥Bs := (ψ.map φ').prod * φ' k * ((ψ.map φ').prod)⁻¹ with ht
  have hψ : (ψ.map φ').prod ∈ ggAutomizer ⊤ Bs :=
    Subgroup.list_prod_mem (ggAutomizer ⊤ Bs) (fun z hz => by
      rw [List.mem_map] at hz
      obtain ⟨o, -, rfl⟩ := hz
      exact Subgroup.subset_closure (hD.mem o))
  have hk : φ' k ∈ ggAutomizer ⊤ Bs := Subgroup.subset_closure (hD.mem k)
  have htA : t ∈ ggAutomizer ⊤ Bs := by
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hψ hk) (Subgroup.inv_mem _ hψ)
  have hfixv : ggLin (p := p) ι t (ι (Additive.ofMul ⟨x, hxBs⟩)) =
      ι (Additive.ofMul ⟨x, hxBs⟩) := by
    rw [ht]
    exact p3ln_word_fixes_x hD hxBs hx ψ k ha
  have hfix : t ⟨x, hxBs⟩ = ⟨x, hxBs⟩ :=
    (ggLin_fix_iff (p := p) ι t ⟨x, hxBs⟩).mpr hfixv
  have htN : t ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggAutomizer_fixes_mem_normalizer ha₀ hcfg hxBs htA hfix
  have htarget : ggLin (p := p) ι t ∈
      Subgroup.normalizer ((ggAutomizer L Bs).map (ggLin (p := p) ι)) :=
    Subgroup.le_normalizer_map (ggLin (p := p) ι) ⟨t, htN, rfl⟩
  have hmap : (ggAutomizer L Bs).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ' (some i))) := by
    rw [hAL, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [hmap] at htarget
  exact htarget

end CFSG.StandardType
