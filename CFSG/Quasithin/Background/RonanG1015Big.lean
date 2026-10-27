module

public import CFSG.Quasithin.Background.P4InspSp
public import CFSG.Quasithin.Background.RonanG1015Small
public import CFSG.Quasithin.Background.P4InspOrthA5
public import CFSG.Quasithin.Background.P4InspOrthA8
public import CFSG.Quasithin.Background.P4InspOrthMinus6
public import CFSG.Quasithin.Background.P4InspOrthPlus4
public import CFSG.Quasithin.Background.P4InspOrthSimple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth CFSG.Quasithin.G11.P4InspSp
  CFSG.GroupTheory.WeirSylow

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem big_cases [Finite U] {f : LinearMap.BilinForm (ZMod 2) U} {M K Q : Subgroup (GLV U)}
    {v : U} (hD : G121Data f M K Q v) (hns : ¬ CFSG.IsStronglyQuasithin ↥K) :
    (M = spSub f ∧ K = spSub f ∧ 6 ≤ Module.finrank (ZMod 2) U) ∨
    (∃ (q : U → ZMod 2) (hq : ∀ x y, q (x + y) = q x + q y + f x y),
      (M = orthSub q ∨ M = omegaSub f q) ∧ K = ⁅orthSub q, orthSub q⁆ ∧
      (∀ w, (∃ g ∈ M, w = g v) ↔ (w ≠ 0 ∧ q w = 0)) ∧
      ∃ n : ℕ, Module.finrank (ZMod 2) U = 2 * n ∧
        ((IsPlusType (p4insporth_quad hq) ∧ 4 ≤ n) ∨ (¬ IsPlusType (p4insporth_quad hq) ∧ 3 ≤ n))) := by
  rcases hD.concl with hM | ⟨q, hq, hM, horb⟩ | ⟨hd4, hM⟩
  ·
    subst hM
    have hsymp : IsSymplectic f := hD.symp
    have hdim : 2 < Module.finrank (ZMod 2) U := hD.dim
    have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
    have heven : Even (Module.finrank (ZMod 2) U) :=
      CFSG.ComponentClassification.CatalogueBAlternatingIsometry.even_finrank f hsymp.1
        (p4inspsp_nondeg hsymp)
    have hcases : Module.finrank (ZMod 2) U = 4 ∨ 6 ≤ Module.finrank (ZMod 2) U := by
      obtain ⟨k, hk⟩ := heven
      omega
    rcases hcases with h4 | h6
    · exfalso
      obtain ⟨-, hmod⟩ := p4inspsp_a6_case hsymp h4 (M := spSub f) (K := K)
        (Subgroup.commutator_le_self _) le_rfl hD.K_le hD.K_norm hD.K_irr hD.K_perf
      obtain ⟨φ, -⟩ := hmod
      exact hns (isStronglyQuasithin_of_alt (n := 6) (Or.inr (Or.inl rfl)) φ)
    · left
      have : IsSimpleGroup ↥(spSub f) := p4inspsp_isSimpleGroup_spSub hsymp h6
      have hKeq : K = spSub f := p4inspsp_eq_of_normalized hD.K_le hD.K_norm
        (p4inspsp_ne_bot hD.K_irr (by omega))
      exact ⟨rfl, hKeq, h6⟩
  ·
    right
    refine ⟨q, hq, hM, ?_, horb, ?_⟩
    all_goals
      have hf : IsSymplectic f := hD.symp
      obtain ⟨n, hn⟩ := p4insporth_even_dim hf
      have hd2 : Module.finrank (ZMod 2) U = 2 * n := by omega
      have h3 := hD.dim
      have h4 : 4 ≤ Module.finrank (ZMod 2) U := by omega
      have hJΩ := p4insporth_comm_le_omega hf h4 hq
      have hMO : M ≤ orthSub q ∧ ⁅orthSub q, orthSub q⁆ ≤ M := by
        rcases hM with rfl | rfl
        · exact ⟨le_rfl, p4insporth_comm_le_self _⟩
        · exact ⟨g12o_omegaSub_le_orthSub hq hf, hJΩ⟩
      have hK0 : K ≠ ⊥ := p4insporth_ne_bot hD.K_irr (by omega)
      have key : IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ → K = ⁅orthSub q, orthSub q⁆ := fun hs =>
        p4insporth_eq_commutator hMO.1 hMO.2 hD.K_le hD.K_norm hD.K_perf hK0 hs
    · by_cases hplus : IsPlusType (p4insporth_quad hq)
      · rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
        · exact absurd (p4insporth_perfect_eq_bot (hD.K_le.trans hMO.1)
            (p4insporth_solvable_plus_four hf hq (by omega) hplus) hD.K_perf) hK0
        · exfalso
          obtain ⟨hs, hperm⟩ := p4insporth_plus_six hf hq (by omega) hplus
          have hK := key hs
          subst hK
          obtain ⟨φ, -⟩ := hperm
          exact hns (isStronglyQuasithin_of_alt (n := 8) (Or.inr (Or.inr rfl)) φ)
        · exact key (p4insporth_simple_plus hf hq (by omega) hd2 hplus)
      · rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
        · exfalso
          obtain ⟨hs, hperm⟩ := p4insporth_minus_four hf hq (by omega) hplus
          have hK := key hs
          subst hK
          obtain ⟨φ, -⟩ := hperm
          exact hns (isStronglyQuasithin_of_alt (n := 5) (Or.inl rfl) φ)
        · exact key (p4insporth_simple_minus_six hf hq (by omega) hplus)
        · exact key (p4insporth_simple_minus hf hq hn4 hd2 hplus)
    · by_cases hplus : IsPlusType (p4insporth_quad hq)
      · rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
        · exact absurd (p4insporth_perfect_eq_bot (hD.K_le.trans hMO.1)
            (p4insporth_solvable_plus_four hf hq (by omega) hplus) hD.K_perf) hK0
        · exfalso
          obtain ⟨hs, hperm⟩ := p4insporth_plus_six hf hq (by omega) hplus
          have hK := key hs
          subst hK
          obtain ⟨φ, -⟩ := hperm
          exact hns (isStronglyQuasithin_of_alt (n := 8) (Or.inr (Or.inr rfl)) φ)
        · exact ⟨n, hd2, Or.inl ⟨hplus, hn4⟩⟩
      · rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | hn4
        · exfalso
          obtain ⟨hs, hperm⟩ := p4insporth_minus_four hf hq (by omega) hplus
          have hK := key hs
          subst hK
          obtain ⟨φ, -⟩ := hperm
          exact hns (isStronglyQuasithin_of_alt (n := 5) (Or.inl rfl) φ)
        · exact ⟨3, hd2, Or.inr ⟨hplus, le_rfl⟩⟩
        · exact ⟨n, hd2, Or.inr ⟨hplus, by omega⟩⟩
  ·
    exfalso
    rcases hM with hM | ⟨⟨e⟩, A, hAM, hA⟩
    · obtain ⟨-, hmod⟩ := p4inspsp_a6_case hD.symp hd4 (M := M) (K := K)
        (le_of_eq hM.symm) hD.M_le hD.K_le hD.K_norm hD.K_irr hD.K_perf
      obtain ⟨φ, -⟩ := hmod
      exact hns (isStronglyQuasithin_of_alt (n := 6) (Or.inr (Or.inl rfl)) φ)
    · obtain ⟨-, hL⟩ := p4inspsp_s5_case hd4 e hAM hA hD.K_le hD.K_norm hD.K_irr hD.K_perf
      obtain ⟨⟨φ⟩, -⟩ := hL
      exact hns (isStronglyQuasithin_of_alt (n := 5) (Or.inl rfl) φ)

end RonanG1015

end CFSG.Quasithin
