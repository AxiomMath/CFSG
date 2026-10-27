module

public import CFSG.Timmesfeld.ARS.Sec9Lines
public import CFSG.Timmesfeld.ARS.CaseD4Frame
public import CFSG.Timmesfeld.ARS.Sec9Comps

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

abbrev orbit (Δ : Set (Subgroup G)) (X : Subgroup G) : Set (Subgroup G) :=
  (fun y => conjSub X y) '' (gen Δ : Set G)

theorem mem_orbit_self (Δ : Set (Subgroup G)) (X : Subgroup G) : X ∈ orbit Δ X :=
  ⟨1, Subgroup.one_mem _, conjSub_one X⟩

theorem conjSub_mem_orbit {Δ : Set (Subgroup G)} {X Y : Subgroup G} (hY : Y ∈ orbit Δ X) {g : G}
    (hg : g ∈ gen Δ) : conjSub Y g ∈ orbit Δ X := by
  obtain ⟨y, hy, rfl⟩ := hY
  exact ⟨g * y, Subgroup.mul_mem _ hg hy, conjSub_mul X g y⟩

theorem orbit_eq_of_mem {Δ : Set (Subgroup G)} {X Y : Subgroup G} (hY : Y ∈ orbit Δ X) :
    orbit Δ Y = orbit Δ X := by
  obtain ⟨y, hy, rfl⟩ := hY
  ext Z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * y, Subgroup.mul_mem _ hg hy, conjSub_mul X g y⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g * y⁻¹, Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hy), ?_⟩
    change conjSub (conjSub X y) (g * y⁻¹) = conjSub X g
    rw [← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem orbit_eq_of_mem_of_mem {Δ : Set (Subgroup G)} {X Y Z : Subgroup G}
    (hX : Z ∈ orbit Δ X) (hY : Z ∈ orbit Δ Y) : orbit Δ X = orbit Δ Y :=
  (orbit_eq_of_mem hX).symm.trans (orbit_eq_of_mem hY)

theorem exists_conjSub_eq_of_mem_orbit {Δ : Set (Subgroup G)} {X Y Z : Subgroup G}
    (hY : Y ∈ orbit Δ X) (hZ : Z ∈ orbit Δ X) : ∃ g ∈ gen Δ, conjSub Y g = Z := by
  rw [← orbit_eq_of_mem hY] at hZ
  obtain ⟨g, hg, rfl⟩ := hZ
  exact ⟨g, hg, rfl⟩

theorem conjSub_mem_orbit_conjSub {Δ : Set (Subgroup G)} {X Y : Subgroup G}
    (hY : Y ∈ orbit Δ X) {h : G} (hh : ∀ g ∈ gen Δ, Commute h g) :
    conjSub Y h ∈ orbit Δ (conjSub X h) := by
  obtain ⟨y, hy, rfl⟩ := hY
  refine ⟨y, hy, ?_⟩
  change conjSub (conjSub X h) y = conjSub (conjSub X y) h
  rw [← conjSub_mul, ← conjSub_mul, (hh y hy).eq]

theorem gen_le_levi {A A₀ : Subgroup G} {Δ : Set (Subgroup G)} (hΔ : Δ ⊆ leviSet R A A₀) :
    gen Δ ≤ levi R A A₀ :=
  gen_mono hΔ

theorem orbit_subset_lambdaStar (hR : IsRootClass R) {A A₀ : Subgroup G} {Δ : Set (Subgroup G)}
    (hΔ : Δ ⊆ leviSet R A A₀) {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) :
    orbit Δ X ⊆ lambdaStar R A A₀ := by
  rintro _ ⟨g, hg, rfl⟩
  exact conjSub_mem_lambdaStar_of_mem_levi hR hX (gen_le_levi hΔ hg)

section Two

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hmax hA₀

theorem exists_special {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) {X : Subgroup G}
    (hX : X ∈ lambdaStar R A A₀) : ∃ F ∈ Δ, Special R X F := by
  have := h.finite
  have hR := h.root
  by_contra! hall
  refine not_forall_commuting h hA hAne hA₀ hmax hΔ hX fun F hF => ?_
  have hFl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hF
  by_contra hnc
  have hne : X ≠ F := fun e => hnc (e ▸ hR.commuting_self hX.1.1.1)
  rcases hR.rel X hX.1.1.1 F hFl.1.1 hne with hc | ho | hs
  · exact hnc hc.symm
  · exact CaseD4.not_opposite_of_mem_leviSet hR hA hX hFl ho.symm
  · exact hall F hF hs

theorem exists_mem_lambdaSet {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀)
    {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) : ∃ E ∈ Δ, X ∈ lambdaSet R E := by
  obtain ⟨F, hF, hXF⟩ := exists_special h hA hAne hmax hA₀ hΔ hX
  obtain ⟨-, D, hD, hFD, hXD⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀
    (mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hF) hX hXF
  exact ⟨D, mem_of_opposite h hA hAne hA₀ hΔ hF hD hFD, hXD⟩

omit hAne hmax in
theorem ne_of_mem_leviSet {X E : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    (hE : E ∈ leviSet R A A₀) : E ≠ X := by
  have := h.finite
  intro e
  subst e
  have hle : E ≤ M R A ⊓ levi R A A₀ := le_inf (QD.le_M hX.1) (le_gen hE)
  rw [M_inf_levi_eq_bot h hA hA₀] at hle
  exact h.root.ne_bot E hE.1.1 (le_bot_iff.1 hle)

theorem exists_mem_orbit_mem_lambdaSet {Δa Δb : Set (Subgroup G)} (hΔa : Δa ∈ leviComps R A A₀)
    (hΔb : Δb ∈ leviComps R A A₀) (hab : Δa ≠ Δb) {B X : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hX : X ∈ lambdaStar R A A₀) :
    ∃ Y ∈ orbit (Δa ∪ Δb) X, Y ∈ lambdaSet R B := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBlkl : Δa ∪ Δb ⊆ leviSet R A A₀ := Set.union_subset
    (fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔa hY)
    (fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔb hY)
  have hga : gen Δa ≤ gen (Δa ∪ Δb) := gen_mono Set.subset_union_left
  have hgb : gen Δb ≤ gen (Δa ∪ Δb) := gen_mono Set.subset_union_right
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hBR : B ∈ R := hB.1.1.1
  obtain ⟨Y, hY, hBY⟩ := exists_special h hA hAne hmax hA₀ hΔb hB
  have hYl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔb hY
  obtain ⟨D, hD, hYD, hpts⟩ := natural_points h hA hAne hA₀ hYl hB hBY
  have hDb : D ∈ Δb := mem_of_opposite h hA hAne hA₀ hΔb hY hD hYD
  have hDYb : D ⊔ Y ≤ gen Δb := sup_le (le_gen hDb) (le_gen hY)
  set B' := ⁅B, Y⁆ with hB'def
  have hB'R : B' ∈ R := hBY.1
  obtain ⟨hB'st, g, hg, hBg⟩ := hpts B' hB'R le_sup_right
  have hB'l : B' ∈ lambdaSet R B :=
    mem_lambdaSet_comm hB'R (mem_lambdaSet_commutator hR hiso hBR hYl.1.1 hBY).1
  have hBO : B ∉ orbit (Δa ∪ Δb) X := by
    intro hBO
    refine hno B' ?_ hB'l
    rw [← orbit_eq_of_mem hBO]
    exact ⟨g, hgb (hDYb hg), hBg⟩
  obtain ⟨E, hE, hBE⟩ := exists_mem_lambdaSet h hA hAne hmax hA₀ hΔa hB
  have hEl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔa hE
  have hER : E ∈ R := hEl.1.1
  have hEb : ∀ k ∈ gen Δb, conjSub E k = E := fun k hk => conjSub_of_forall_commute fun e he =>
    ((commuting_gen_of_ne h hA hAne hA₀ hΔa hΔb hab) e (le_gen hE he) k hk).symm
  have hPE : ∀ P ∈ R, P ≤ B ⊔ B' → P ∈ lambdaSet R E := by
    intro P hP hPle
    have hB'E : B' ∈ lambdaSet R E := by
      have := conjSub_mem_lambdaSet hR hBE g
      rwa [hEb g (hDYb hg), hBg] at this
    have hmem : P ∈ {Z | Z ∈ R ∧ Z ≤ M R E} :=
      ⟨hP, hPle.trans (sup_le (QD.le_M hBE) (QD.le_M hB'E))⟩
    rw [(Q_eq_M h hER).2.1] at hmem
    refine hmem.resolve_left fun e => ?_
    exact ne_of_mem_leviSet h hA hA₀ (hpts P hP hPle).1 hEl e.symm
  have hcomm : ∀ Z ∈ orbit (Δa ∪ Δb) X, Commuting E Z := by
    intro Z hZ
    have hZst : Z ∈ lambdaStar R A A₀ := orbit_subset_lambdaStar hR hBlkl hX hZ
    have hZR : Z ∈ R := hZst.1.1.1
    obtain ⟨P, hP, hPle, hZP⟩ := exists_commuting_of_le_M h hA hBR hB'l
      (sup_le (QD.le_M hB.1) (QD.le_M hB'st.1)) hZR (QD.le_M hZst.1)
    obtain ⟨-, g', hg', hPg'⟩ := hpts P hP hPle
    have hEP : E ∈ lambdaSet R P := mem_lambdaSet_comm hER (hPE P hP hPle)
    by_contra hEZ
    have hZE : Special R E Z := by
      have hne : E ≠ Z := ne_of_mem_leviSet h hA hA₀ hZst hEl
      rcases hR.rel E hER Z hZR hne with hc | ho | hs
      · exact absurd hc hEZ
      · exact absurd ho (CaseD4.not_opposite_of_mem_leviSet hR hA hZst hEl)
      · exact hs
    obtain ⟨z, hz, hz1⟩ := hR.exists_ne_one hZR
    have hPz : conjSub P z = P := conjSub_of_forall_commute fun p hp => hZP z hz p hp
    have hEzP : conjSub E z ∈ lambdaSet R P := by
      have := conjSub_mem_lambdaSet hR hEP z
      rwa [hPz] at this
    have hWM : ⁅E, Z⁆ ≤ M R P := (commutator_le_sup_conjSub hR hiso hER hZR hZE hz hz1).trans
      (sup_le (QD.le_M hEP) (QD.le_M hEzP))
    obtain ⟨D'', hD'', hED'', hpts''⟩ := natural_points h hA hAne hA₀ hEl hZst hZE.symm
    obtain ⟨-, g'', hg'', hZg''⟩ := hpts'' ⁅Z, E⁆ hZE.symm.1 le_sup_right
    have hD''a : D'' ∈ Δa := mem_of_opposite h hA hAne hA₀ hΔa hE hD'' hED''
    have hWO : ⁅E, Z⁆ ∈ orbit (Δa ∪ Δb) X := by
      rw [Subgroup.commutator_comm, ← hZg'']
      exact conjSub_mem_orbit hZ (hga (sup_le (le_gen hD''a) (le_gen hE) hg''))
    have hmem : ⁅E, Z⁆ ∈ {W | W ∈ R ∧ W ≤ M R P} := ⟨hZE.1, hWM⟩
    rw [(Q_eq_M h hP).2.1] at hmem
    rcases hmem with hWP | hWl
    ·
      apply hBO
      rw [hWP] at hWO
      have := conjSub_mem_orbit hWO (hgb (hDYb (Subgroup.inv_mem _ hg')))
      rwa [← hPg', Plane.conjSub_conjSub_inv] at this
    ·
      refine hno _ (conjSub_mem_orbit hWO (hgb (hDYb (Subgroup.inv_mem _ hg')))) ?_
      have := conjSub_mem_lambdaSet hR hWl g'⁻¹
      rwa [← hPg', Plane.conjSub_conjSub_inv] at this
  refine not_forall_commuting h hA hAne hA₀ hmax hΔa hX fun E' hE' => ?_
  obtain ⟨k, hk, hkE⟩ := exists_conjSub_eq h hΔa hE hE'
  have h1 := (hcomm (conjSub X k⁻¹) ⟨k⁻¹, hga (Subgroup.inv_mem _ hk), rfl⟩).conjSub k
  rwa [hkE, Plane.conjSub_inv_conjSub] at h1

end Two

end Sec9

end CFSG.Timmesfeld.ARS
