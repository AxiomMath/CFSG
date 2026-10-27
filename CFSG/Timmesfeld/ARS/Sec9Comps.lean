module

public import CFSG.Timmesfeld.ARS.CaseD4Collinear
public import CFSG.Timmesfeld.ARS.Sec8Components

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def leviComps (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Set (Set (Subgroup G)) :=
  {S | ∃ E ∈ leviSet R A A₀, S = comp R A A₀ E}

@[expose] def IsSL2Comp (Δ : Set (Subgroup G)) : Prop :=
  ∃ E ∈ Δ, ∃ F ∈ Δ, Opposite E F ∧ gen Δ = E ⊔ F

theorem IsSL2Comp.opposite_of_ne [Finite G] (hR : IsRootClass R) {Δ : Set (Subgroup G)}
    (hS : IsSL2Comp Δ) (hΔR : Δ ⊆ R) {X Y : Subgroup G} (hX : X ∈ Δ) (hY : Y ∈ Δ) (hXY : X ≠ Y) :
    Opposite X Y ∧ X ⊔ Y = gen Δ := by
  obtain ⟨E, hE, F, hF, hEF, hgen⟩ := hS
  have hsup : X ⊔ Y = E ⊔ F := sup_eq_of_le hR (hΔR hX) (hΔR hY) (hΔR hE) hEF hXY
    (sup_le (hgen ▸ le_gen hX) (hgen ▸ le_gen hY))
  refine ⟨?_, hsup.trans hgen.symm⟩
  have hno2 : ¬ IsPGroup 2 ↥(X ⊔ Y) := fun hP =>
    Sec3.not_opposite_of_isPGroup_sup hR (hΔR hE) (hΔR hF) (hsup ▸ hP) hEF
  rcases hR.rel X (hΔR hX) Y (hΔR hY) hXY with hc | ho | hs
  · exact absurd (isPGroup_sup_of_commuting (hR.isPGroup (hΔR hX)) (hR.isPGroup (hΔR hY)) hc)
      hno2
  · exact ho
  · exact absurd (hs.isPGroup_sup hR (hΔR hX) (hΔR hY)) hno2

namespace Sec9

theorem comp_mem_leviComps {A A₀ E : Subgroup G} (hE : E ∈ leviSet R A A₀) :
    comp R A A₀ E ∈ leviComps R A A₀ :=
  ⟨E, hE, rfl⟩

theorem self_mem_comp (A A₀ E : Subgroup G) : E ∈ comp R A A₀ E :=
  Relation.ReflTransGen.refl

theorem comp_eq_comp {A A₀ E F X : Subgroup G} (hXE : X ∈ comp R A A₀ E)
    (hXF : X ∈ comp R A A₀ F) : comp R A A₀ E = comp R A A₀ F :=
  (comp_eq_of_mem hXE).symm.trans (comp_eq_of_mem hXF)

section Comps

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hA₀

theorem mem_leviSet_of_mem_leviComps {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀)
    {X : Subgroup G} (hX : X ∈ Δ) : X ∈ leviSet R A A₀ := by
  obtain ⟨E, hE, rfl⟩ := hΔ
  exact comp_subset h hA hAne hA₀ hE hX

theorem commuting_of_ne {Δ Δ' : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀)
    (hΔ' : Δ' ∈ leviComps R A A₀) (hne : Δ ≠ Δ') {X Y : Subgroup G} (hX : X ∈ Δ) (hY : Y ∈ Δ') :
    Commuting X Y := by
  obtain ⟨E, hE, rfl⟩ := hΔ
  obtain ⟨F, hF, rfl⟩ := hΔ'
  refine commuting_of_notMem_comp h hA hAne hA₀ (comp_subset h hA hAne hA₀ hE hX)
    (comp_subset h hA hAne hA₀ hF hY) fun hYX => hne ?_
  exact (comp_eq_of_mem hX).symm.trans ((comp_eq_of_mem hYX).symm.trans (comp_eq_of_mem hY))

theorem commuting_gen_of_ne {Δ Δ' : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀)
    (hΔ' : Δ' ∈ leviComps R A A₀) (hne : Δ ≠ Δ') : Commuting (gen Δ) (gen Δ') :=
  commuting_gen_gen fun _ hX _ hY => commuting_of_ne h hA hAne hA₀ hΔ hΔ' hne hX hY

omit hA hAne hA₀ in
theorem exists_conjSub_eq {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) {X Y : Subgroup G}
    (hX : X ∈ Δ) (hY : Y ∈ Δ) : ∃ g ∈ gen Δ, conjSub X g = Y := by
  obtain ⟨E, hE, rfl⟩ := hΔ
  have hXY : Relation.ReflTransGen (oppGraph (leviSet R A A₀)) X Y :=
    (Sec3.reflTransGen_oppGraph_symm hX).trans hY
  obtain ⟨g, hg, hgY⟩ := Sec3.exists_conjSub_eq_of_reflTransGen h.root (fun Z hZ => hZ.1.1) hXY
  refine ⟨g, ?_, hgY⟩
  have e : (⨆ D ∈ {D | Relation.ReflTransGen (oppGraph (leviSet R A A₀)) X D}, D) =
      gen (comp R A A₀ E) := by
    change gen (comp R A A₀ X) = gen (comp R A A₀ E)
    rw [comp_eq_of_mem hX]
  exact e ▸ hg

theorem exists_opposite_mem {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) {X : Subgroup G}
    (hX : X ∈ Δ) : ∃ Y ∈ Δ, Opposite X Y := by
  obtain ⟨E, hE, rfl⟩ := hΔ
  obtain ⟨Y, hY, hXY⟩ := exists_opposite_mem_leviSet h hA hAne hA₀
    (comp_subset h hA hAne hA₀ hE hX)
  exact ⟨Y, hX.tail ⟨comp_subset h hA hAne hA₀ hE hX, hY, hXY⟩, hXY⟩

theorem mem_of_opposite {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) {X Y : Subgroup G}
    (hX : X ∈ Δ) (hY : Y ∈ leviSet R A A₀) (hXY : Opposite X Y) : Y ∈ Δ := by
  obtain ⟨E, hE, rfl⟩ := hΔ
  exact hX.tail ⟨comp_subset h hA hAne hA₀ hE hX, hY, hXY⟩

theorem conjSub_mem {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) {X : Subgroup G}
    (hX : X ∈ Δ) {g : G} (hg : g ∈ levi R A A₀) : conjSub X g ∈ Δ := by
  have := h.finite
  have hR := h.root
  obtain ⟨E, hE, rfl⟩ := hΔ
  exact Sec3.reflTransGen_conjSub hR h.noIsolated (fun Z hZ => hZ.1.1)
    (fun g hg _ hB => conjSub_mem_leviSet_of_mem_levi hR hB hg) hE
    (exists_opposite_mem_leviSet h hA hAne hA₀ hE) hX hg

omit h hA hAne hA₀ in
theorem mem_comp_self {X : Subgroup G} (hX : X ∈ leviSet R A A₀) :
    ∃ Δ ∈ leviComps R A A₀, X ∈ Δ :=
  ⟨comp R A A₀ X, comp_mem_leviComps hX, self_mem_comp A A₀ X⟩

theorem not_forall_commuting (hmax : IsSigmaMaximal R (centralGroup R A))
    {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) {X : Subgroup G}
    (hX : X ∈ lambdaStar R A A₀) (hall : ∀ Y ∈ Δ, Commuting Y X) : False := by
  have := h.finite
  have hR := h.root
  set W := gen Δ with hW
  have hWX : Commuting W X := commuting_iff_le_centralizer.2 ((gen_le fun Y hY =>
    commuting_iff_le_centralizer.1 (hall Y hY).symm).trans le_rfl) |>.symm
  have key : ∀ v ∈ levi R A A₀, ∀ Y : Subgroup G, Commuting W Y → Commuting W (conjSub Y v) := by
    intro v hv
    refine gen_induction (p := fun v => ∀ Y : Subgroup G, Commuting W Y →
      Commuting W (conjSub Y v)) hv (fun B hB x hx Y hY => ?_) (fun Y hY => by rwa [conjSub_one])
      (fun x y hx hy Y hY => by rw [conjSub_mul]; exact hx _ (hy Y hY))
    obtain ⟨Δ', hΔ', hBΔ'⟩ := mem_comp_self hB
    by_cases hΔΔ' : Δ = Δ'
    · subst hΔΔ'
      rw [conjSub_of_forall_commute fun y hy => hY x (le_gen hBΔ' hx) y hy]
      exact hY
    · have h1 := hY.conjSub x
      rwa [conjSub_of_forall_commute fun w hw =>
        ((commuting_gen_of_ne h hA hAne hA₀ hΔ hΔ' hΔΔ').symm x (le_gen hBΔ' hx) w hw)] at h1
  obtain ⟨E, hE, rfl⟩ := hΔ
  have hEM : Commuting E (M R A) := by
    rw [M_eq_gen_lambdaStar h hA hA₀, commuting_iff_le_centralizer]
    refine gen_le fun Y hY => ?_
    obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hX hY
    exact commuting_iff_le_centralizer.1
      ((key v hv X hWX).mono (le_gen (self_mem_comp A A₀ E)) le_rfl)
  have hmem : E ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨hE.1.1, hEM⟩
  rw [(Q_eq_M h hA).2.2.2.1, Set.mem_singleton_iff] at hmem
  exact hE.1.2.1 hmem

theorem not_commuting_and_commuting (hmax : IsSigmaMaximal R (centralGroup R A))
    {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) (hS : IsSL2Comp Δ) {Y Y' X : Subgroup G}
    (hY : Y ∈ Δ) (hY' : Y' ∈ Δ) (hYY' : Y ≠ Y') (hX : X ∈ lambdaStar R A A₀)
    (h1 : Commuting Y X) (h2 : Commuting Y' X) : False := by
  have := h.finite
  have hsup := (hS.opposite_of_ne h.root (fun Z hZ => (mem_leviSet_of_mem_leviComps h hA hAne hA₀
    hΔ hZ).1.1) hY hY' hYY').2
  refine not_forall_commuting h hA hAne hA₀ hmax hΔ hX fun Z hZ => ?_
  have hc : Commuting (Y ⊔ Y') X := Commuting.sup_left h1 h2
  rw [hsup] at hc
  exact hc.mono (le_gen hZ) le_rfl

theorem mem_lambdaSet_of_commuting (hmax : IsSigmaMaximal R (centralGroup R A))
    {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) (hS : IsSL2Comp Δ) {Y X : Subgroup G}
    (hY : Y ∈ Δ) (hX : X ∈ lambdaStar R A A₀) (hYX : Commuting Y X) : X ∈ lambdaSet R Y := by
  have := h.finite
  obtain ⟨Y', hY', hYY'⟩ := exists_opposite_mem h hA hAne hA₀ hΔ hY
  exact CaseD4.mem_lambdaSet_of_commuting_of_not h hA hAne hA₀
    (mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hY)
    (mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hY') hYY'
    (fun T hT h1 h2 => not_commuting_and_commuting h hA hAne hA₀ hmax hΔ hS hY hY' hYY'.ne hT h2 h1)
    hX hYX

end Comps

end Sec9

end CFSG.Timmesfeld.ARS
