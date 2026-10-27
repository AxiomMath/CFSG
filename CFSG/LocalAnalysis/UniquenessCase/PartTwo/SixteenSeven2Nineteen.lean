module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Glue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCase10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.Quasithin.EmptyFaithful.T1515C6Grp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r16_19_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h12 : R16_12 D) (h13 : R16_13_1 D) (h14 : R16_14 D) (h15 : R16_15 D)
    (h17 : R16_17 D) : R16_19 D := by
  intro V₀ V L hV hC
  by_contra hno
  have hn2 : ¬ Case168_2 D V₀ V hV L := fun h => hno (Or.inl h)
  have hn9 : ¬ Case168_9 D V₀ V hV L := fun h => hno (Or.inr h)
  obtain ⟨-, h0, h1⟩ := h12 V₀ V L hV hC
  subst h0
  obtain ⟨⟨A, hA⟩, hA13⟩ := h13 ⊥ V L hV hC
  obtain ⟨hAT, g, hAg, -⟩ := hA.1
  obtain ⟨Δ, hΔ⟩ := h17 ⊥ V L hV hC A hA g hAg
  obtain ⟨hVM, -⟩ := hA13 A hA g hAg
  obtain ⟨B, U, hBU⟩ := sixteen_seven2_hyperplane_exists' D hC.setting hV rfl h1 hA
  obtain ⟨hrkA, hcase⟩ := h15 ⊥ V L hV hC A hA
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  have hk3 : 3 ∈ D.sig → D.k = 1 := s15_Thirteen_k_eq_one_of_three_mem D hSg h1219
  have hsig3 : D.sig = {3} → D.k = 1 := fun h => hk3 (by rw [h]; exact Set.mem_singleton 3)
  have hI : Insp18 D ⊥ V hV L g Δ := by
    rcases hcase with h2 | h4 | h10 | h9
    · exact absurd h2 hn2
    · exact s16c167_insp18_case4 D (hk3 h4.2.2) hC.setting hC.conc hΔ hn2 h4
    · exact s16c167_insp18_case10 D (hsig3 h10.2.2.2.1) hC.setting hΔ hn2 h10
    · exact absurd h9 hn9
  have hUS : Unique19 D V g Δ ∧ Second19 V A := by
    rcases hcase with h2 | h4 | h10 | h9
    · exact absurd h2 hn2
    · exact s16c167_nineteen_case4 D hC.setting hC.conc hΔ h4 hAM hAel hrkA
    · exact s16c167_nineteen_case10 D hC.setting hΔ h10 hAM hAel hrkA
    · exact absurd h9 hn9
  exact s16c167_nineteen_core D hV hC.setting.hyp16 (h14 ⊥ V L hV hC) hA.1 hAg hΔ hI hVM
    hn2 hUS.1 hUS.2 hBU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
