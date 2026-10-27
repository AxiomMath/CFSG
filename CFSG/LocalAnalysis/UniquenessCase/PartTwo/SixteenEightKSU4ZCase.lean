module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSU4ZCaseA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}


theorem s16k_su4z_case4 (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSU : IsSUn ↥(lBar V₀ V hV L) 4 1)
    (hN : NatSUn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 1)
    (hσ : 3 ∈ D.sig) (hV0 : V₀ = ⊥) : Case167_4 D V₀ V hV L := by
  subst hV0
  exact ⟨hSU, s16k_natSUn_lStar_of_lBar h hN, s16k_su4z_sig_eq_three h hN hσ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
