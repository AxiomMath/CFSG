module

public import CFSG.LocalAnalysis.StandardType.FF81.CurtisA2Linear
import CFSG.ClassicalInvolution.WeakCT.FieldTwo
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogE
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.StandardType.FF81

theorem curtisA2_e6
    (X : Type) [Group X] (U : Fin 6 → Subgroup X) (hU : A2System adjE6 U ⊤) :
    CFSG.IsQuasisimple X ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
      CFSG.Assembly.LowTwoRank.StatedLieTag.E6 0 2 1 := by
  have hadm : CFSG.Open.StatedLieAdmissible .E6 0 2 1 := ⟨Nat.prime_two, le_rfl, rfl⟩
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hroot : ∃ c : Fin 6,
      CFSG.Timmesfeld.edgeE 6 ⟨0, by norm_num⟩ c ∨ CFSG.Timmesfeld.edgeE 6 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  have hcomm : ∀ i j : Fin 6, i ≠ j → ¬ CFSG.Timmesfeld.edgeE 6 i j →
      ¬ CFSG.Timmesfeld.edgeE 6 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    intro i j hij h1 h2
    exact hU.2.2.1 i j hij (fun h => h.elim h1 h2)
  have hpair : ∀ i j : Fin 6, CFSG.Timmesfeld.edgeE 6 i j →
      ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair (ZMod 2) W (U i) (U j) := by
    intro i j h
    exact hU.2.2.2 i j (Or.inl h)
  obtain ⟨ρ, hρ, hψ⟩ := CFSG.ClassicalInvolution.WeakCT.exists_frame_of_tree_two (K := ZMod 2) hF
    (CFSG.ClassicalInvolution.WeakCT.rootedTree_edgeE (r := 6) (by norm_num)) hroot hcomm hpair
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.weakCT_e6_of_frame (p := 2) (f := 1)
      hadm (F := ZMod 2) hF U hU.2.1 hcomm hρ hψ
  exact ⟨hqs, hmodel⟩

theorem curtisA2_holds :
    CurtisA2 :=
  ⟨fun m hm X _ U hU => curtisA2_linear m hm X U hU, fun X _ U hU => curtisA2_e6 X U hU⟩

end CFSG.StandardType.FF81
