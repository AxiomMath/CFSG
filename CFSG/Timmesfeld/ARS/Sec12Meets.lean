module

public import CFSG.Timmesfeld.ARS.Sec12Perp

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem exists_mem_deltaSet {X : Subgroup G} (hX : X ∈ leviSet R A A₀) :
    ∃ D ∈ lambdaStar R A A₀, X ∈ deltaSet R A A₀ D := by
  obtain ⟨E, hE, -⟩ := hS.exists_special_lambdaStar
  rcases hS.mem_deltaSet_or_special hE hX with h | hs
  · exact ⟨E, hE, h⟩
  · obtain ⟨hD, -, hDX⟩ := commutator_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hE hX hs
    exact ⟨_, hD, hS.mem_deltaSet_of_commuting hD hX hDX.1.2.2.symm⟩

theorem exists_mem_deltaSet_two {X Y : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (hY : Y ∈ leviSet R A A₀) (hXY : Commuting X Y) :
    ∃ D ∈ lambdaStar R A A₀, X ∈ deltaSet R A A₀ D ∧ Y ∈ deltaSet R A A₀ D := by
  obtain ⟨D₀, hD₀, hXD₀⟩ := hS.exists_mem_deltaSet hX
  rcases hS.mem_deltaSet_or_special hD₀ hY with h | hs
  · exact ⟨D₀, hD₀, hXD₀, h⟩
  · obtain ⟨hD, -, hDY⟩ := commutator_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hD₀ hY hs
    exact ⟨_, hD, (hS.commuting_iff_mem_deltaSet_commutator hD₀ hY hs hXD₀).1 hXY,
      hS.mem_deltaSet_of_commuting hD hY hDY.1.2.2.symm⟩

theorem exists_special_of_mem_lambdaStar {D : Subgroup G} (hD : D ∈ lambdaStar R A A₀) :
    ∃ D' ∈ lambdaStar R A A₀, Special R D D' := by
  have hR := hS.hyp.root
  obtain ⟨E, hE, C, hC, hEC, -⟩ := hS.exists_special_lambdaStar
  obtain ⟨v, hv, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hS.mem hS.sec8.2
    hS.max hS.opp hE hD
  exact ⟨conjSub C v, conjSub_mem_lambdaStar_of_mem_levi hR hC hv, Sec3.special_conjSub hR hEC v⟩

theorem exists_line_through {D X X' : Subgroup G} (hD : D ∈ lambdaStar R A A₀)
    (hX : X ∈ deltaSet R A A₀ D) (hX' : X' ∈ deltaSet R A A₀ D) :
    ∃ Y ∈ leviSet R A A₀, Special R D Y ∧ Commuting X Y ∧ Commuting X' Y := by
  have hA := hS.mem
  obtain ⟨D', hD', hDD'⟩ := hS.exists_special_of_mem_lambdaStar hD
  have hemp := hS.deltaSet_inter_eq_empty_of_special hD hD' hDD'
  have hnot : ∀ {Z : Subgroup G}, Z ∈ deltaSet R A A₀ D → Z ∉ deltaSet R A A₀ D' :=
    fun hZ hZ' => (Set.eq_empty_iff_forall_notMem.1 hemp) _ ⟨hZ, hZ'⟩
  have hnot' : ∀ {Z : Subgroup G}, Z ∈ deltaSet R A A₀ D' → Z ∉ deltaSet R A A₀ D :=
    fun hZ' hZ => (Set.eq_empty_iff_forall_notMem.1 hemp) _ ⟨hZ, hZ'⟩
  have hsX : Special R D' X := (hS.mem_deltaSet_or_special hD' hX.1).resolve_left (hnot hX)
  have hsX' : Special R D' X' := (hS.mem_deltaSet_or_special hD' hX'.1).resolve_left (hnot hX')
  obtain ⟨h1, h1D', -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hD' hX.1 hsX
  obtain ⟨h2, h2D', -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hD' hX'.1 hsX'
  obtain ⟨Y, ⟨hYD', hY1⟩, hY2⟩ := hS.deltaSet_inter_inter_nonempty hD' h1 h2 h1D' h2D'
  refine ⟨Y, hYD'.1, (hS.mem_deltaSet_or_special hD hYD'.1).resolve_left (hnot' hYD'),
    ((hS.commuting_iff_mem_deltaSet_commutator hD' hX.1 hsX hYD').2 hY1).symm,
    ((hS.commuting_iff_mem_deltaSet_commutator hD' hX'.1 hsX' hYD').2 hY2).symm⟩

theorem exists_commuting_mem_line {X X' W : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (hX' : X' ∈ leviSet R A A₀) (hXX' : X ≠ X') (hc : Commuting X X')
    (hW : W ∈ leviSet R A A₀) :
    ∃ Z ∈ leviSet R A A₀, Commuting Z W ∧
      ∀ U ∈ leviSet R A A₀, Commuting U X → Commuting U X' → Commuting U Z := by
  have hA := hS.mem
  obtain ⟨D, hD, hXD, hX'D⟩ := hS.exists_mem_deltaSet_two hX hX' hc
  have hline : ∀ Z ∈ deltaSet R A A₀ D, (∀ Y ∈ leviSet R A A₀, Special R D Y →
      Commuting X Y → Commuting X' Y → Commuting Z Y) →
      ∀ U ∈ leviSet R A A₀, Commuting U X → Commuting U X' → Commuting U Z := by
    intro Z hZ hZY U hU hUX hUX'
    rcases hS.mem_deltaSet_or_special hD hU with hUD | hs
    · exact hS.commuting_of_mem_deltaSet' hD hUD hZ
    · obtain ⟨Y, hY, hsY, hXY, hX'Y⟩ := hS.exists_line_through hD hXD hX'D
      exact (hS.commuting_of_two_commuting hD hU hY hs hsY hXD hX'D hXX' hUX.symm hXY
        hUX'.symm hX'Y hZ (hZY Y hY hsY hXY hX'Y)).symm
  rcases hS.mem_deltaSet_or_special hD hW with hWD | hsW
  · refine ⟨X, hX, hS.commuting_of_mem_deltaSet' hD hXD hWD, fun U _ hUX _ => hUX⟩
  obtain ⟨Y, hY, hsY, hXY, hX'Y⟩ := hS.exists_line_through hD hXD hX'D
  obtain ⟨hDY, hDYD, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hD hY hsY
  obtain ⟨hDW, hDWD, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hS.opp hD hW hsW
  obtain ⟨Z, ⟨hZD, hZY⟩, hZW⟩ := hS.deltaSet_inter_inter_nonempty hD hDY hDW hDYD hDWD
  have hZY' : Commuting Z Y := (hS.commuting_iff_mem_deltaSet_commutator hD hY hsY hZD).2 hZY
  refine ⟨Z, hZD.1, (hS.commuting_iff_mem_deltaSet_commutator hD hW hsW hZD).2 hZW,
    hline Z hZD fun Y' hY' hsY' hXY' hX'Y' => ?_⟩
  by_cases hY'Y : Commuting Z Y'
  · exact hY'Y
  exact hS.commuting_of_two_commuting hD hY' hY hsY' hsY hXD hX'D hXX' hXY' hXY hX'Y' hX'Y hZD
    hZY'

end Sec12

end CFSG.Timmesfeld.ARS
