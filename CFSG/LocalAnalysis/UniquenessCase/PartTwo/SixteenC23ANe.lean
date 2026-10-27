module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Gap64

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def C23Gap64Ne (D : Data G) : Prop :=
  UC6S846.SigmaStd D → DataExt D → UC6.R6_1 D → R127 D → R129_1 D → R1217 D → R119W D →
    Thm145 D → R16_63 D →
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Case167_2 D V₀ V hV L → Hyp154 D V₀ V L → V₀ ≠ ⊥ → v1Sub D.M V₀ V hV L ≠ ⊥ → False

theorem c23a_c23Gap64_of_ne (D : Data G) (h126 : R126 D) (h : C23Gap64Ne D) : C23Gap64 D := by
  intro hSig hExt h61 h127 h129 h1217 h119 h145 h63 V₀ V L hV hS hc h154 hne
  by_cases h0 : V₀ = ⊥
  · exact c23a_false_of_v0_bot D h126 h1217 h63 hS hc h154 h0 hne
  · exact h hSig hExt h61 h127 h129 h1217 h119 h145 h63 V₀ V L hV hS hc h154 h0 hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
