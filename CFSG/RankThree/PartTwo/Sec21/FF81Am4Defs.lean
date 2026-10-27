module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSp)
open CFSG.LieType.Universal CFSG.LieType.CurtisTits
open CFSG.LieType.Universal.Symplectic.SpExtras (elt)
open CFSG.SeitzReduction.SymplecticPilot (complSp)

namespace Am4

noncomputable def tvec : StatedSp 4 (ZMod 2) := elt (.positiveLong (3 : Fin 4)) 1

noncomputable abbrev Pvec : Subgroup (StatedSp 4 (ZMod 2)) := Cen tvec

noncomputable abbrev Svec : Subgroup (StatedSp 4 (ZMod 2)) := complSp (ZMod 2) 3

theorem tvec_mem_Pvec : tvec ∈ Pvec :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

end Am4

open Am4

def KF_Sp6O7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) (t₀ : X), orderOf t₀ = 2 → L ≤ Cen t₀ →
    StatedClassicalModel ↥L .PSp 3 2 1 → setMul (Op 2 (Cen t₀)) L = Cen t₀ →
    IsElemAb 2 7 (Op 2 (Cen t₀)) → t₀ ∈ ⁅Cen t₀, Cen t₀⁆ →
    ∃ Θ : ↥Pvec ≃* ↥(Cen t₀), (Θ ⟨tvec, tvec_mem_Pvec⟩ : X) = t₀ ∧
      ∀ x : ↥Pvec, (x : StatedSp 4 (ZMod 2)) ∈ Svec ↔ (Θ x : X) ∈ L

end CFSG.RankThree.PartTwo.Sec21.FF81
