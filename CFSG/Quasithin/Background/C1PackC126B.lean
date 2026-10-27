module

public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S1412

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem minParabolic_ne_bot {H T M : Subgroup G} (h : MinParabolic H T M) : T ≠ ⊥ := by
  intro hT
  apply h.not_normal
  rw [hT]
  intro g _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp

theorem c126_of_commutator_eq_bot {C₁ C₂ : Subgroup G → Subgroup G} (hC : IsGNChoice C₁ C₂)
    {H T M : Subgroup G} (hmin : MinParabolic H T M) (hF : CharTwo H)
    (hJ : thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G)) :
    C₁ T ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ T : Set G) := by
  have hT : IsSylowTwoOf T H := hmin.isSylow
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair T hT.2.1 (minParabolic_ne_bot hmin)
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  by_cases hHV : H ≤ Subgroup.centralizer (VZ T H : Set G)
  · left
    have hC1V : C₁ T ≤ VZ T H := h1Z.trans (le_conjClosure _ H)
    refine le_inf ((h1Z.trans ?_).trans hT.1) ?_
    · exact (Subgroup.closure_le T).mpr fun x hx => hx.1.1
    · intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_iff.mp (hHV hh) c (hC1V hc)).symm
  · right
    have hredV : IsTwoReducedIn H (conjClosure (quasithinOmegaOneCenter T) H) := hred
    have htfae := MinParabolic.tfae_thompsonJ hmin hredV hHV
    have h1 : ⁅VZ T H, thompsonJ T⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJ
    have h3 : baum T = baum (pCoreOf 2 H) := (htfae.out 1 3).1 h1
    have hHN : H ≤ Subgroup.normalizer (baum T : Set G) := by
      rw [h3]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
        (normalizer_le_normalizer_baum _)
    exact hHN.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)

end CFSG.Quasithin.C1Pack
