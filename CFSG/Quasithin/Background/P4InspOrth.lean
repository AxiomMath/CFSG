module

public import CFSG.Quasithin.Background.P4InspectStmt
public import CFSG.Quasithin.Background.P4InspOrthRank
public import CFSG.Quasithin.Background.P4InspOrthSimple
public import CFSG.Quasithin.Background.P4InspOrthPlus4
public import CFSG.Quasithin.Background.P4InspOrthA5
public import CFSG.Quasithin.Background.P4InspOrthA8
public import CFSG.Quasithin.Background.P4InspOrthMinus6

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

open P4InspOrth CFSG.GroupTheory.WeirSylow

theorem inspectOrthCase : InspectOrthCase := by
  intro U _ _ _ f M K Q v hdata hex
  obtain ⟨q, hq, hM⟩ := hex
  have hf : IsSymplectic f := hdata.symp
  obtain ⟨n, hn⟩ := p4insporth_even_dim hf
  have hd2 : Module.finrank (ZMod 2) U = 2 * n := by omega
  have h3 := hdata.dim
  have h4 : 4 ≤ Module.finrank (ZMod 2) U := by omega
  have hJΩ := p4insporth_comm_le_omega hf h4 hq
  have hMO : M ≤ orthSub q ∧ ⁅orthSub q, orthSub q⁆ ≤ M := by
    rcases hM with rfl | rfl
    · exact ⟨le_rfl, p4insporth_comm_le_self _⟩
    · exact ⟨g12o_omegaSub_le_orthSub hq hf, hJΩ⟩
  have hK0 : K ≠ ⊥ := p4insporth_ne_bot hdata.K_irr (by omega)
  have key : IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ → K = ⁅orthSub q, orthSub q⁆ := fun hs =>
    p4insporth_eq_commutator hMO.1 hMO.2 hdata.K_le hdata.K_norm hdata.K_perf hK0 hs
  by_cases hplus : IsPlusType (p4insporth_quad hq)
  · rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
    · exact absurd (p4insporth_perfect_eq_bot (hdata.K_le.trans hMO.1)
        (p4insporth_solvable_plus_four hf hq (by omega) hplus) hdata.K_perf) hK0
    · obtain ⟨hs, hperm⟩ := p4insporth_plus_six hf hq (by omega) hplus
      have hK := key hs
      subst hK
      exact ⟨hs, fun _ => Or.inr (Or.inr (Or.inr hperm))⟩
    · have hs := p4insporth_simple_plus hf hq (by omega) hd2 hplus
      have hK := key hs
      subst hK
      exact ⟨hs, fun hsqt => absurd hsqt (p4insporth_not_sqt_plus hf hq hn4 hd2 hplus le_rfl)⟩
  · rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
    · obtain ⟨hs, hperm⟩ := p4insporth_minus_four hf hq (by omega) hplus
      have hK := key hs
      subst hK
      exact ⟨hs, fun _ => Or.inl hperm⟩
    · have hs := p4insporth_simple_minus_six hf hq (by omega) hplus
      have hK := key hs
      subst hK
      exact ⟨hs, fun hsqt =>
        absurd hsqt (p4insporth_not_sqt_minus hf hq (by omega) hd2 hplus le_rfl)⟩
    · have hs := p4insporth_simple_minus hf hq hn4 hd2 hplus
      have hK := key hs
      subst hK
      exact ⟨hs, fun hsqt =>
        absurd hsqt (p4insporth_not_sqt_minus hf hq (by omega) hd2 hplus le_rfl)⟩

end G11

end CFSG.Quasithin
