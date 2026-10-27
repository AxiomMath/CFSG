module

public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.S15221

open Equiv Equiv.Perm CFSG.Open CFSG.Quasithin

theorem isLnTwo_four_alt8 {X : Type} [Group X]
    (h : Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2))) :
    Nonempty (X ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := h
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  refine (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff X).mp ?_
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
    inferInstance, inferInstance, by rw [h2, pow_one], ⟨?_⟩⟩
  exact e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 (ZMod 2))

variable {G : Type} [Group G] [Finite G]

end CFSG.Quasithin.S15221
