module

import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KP10LinearTwo
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof15Res3Inner

variable {G : Type} [Group G] [Finite G]

theorem exists_isPGroup_map_eq_of_le_map {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}
    [Fact p.Prime] (φ : A →* B) {H : Subgroup A} {Q : Subgroup B} (hQ : IsPGroup p Q)
    (hQH : Q ≤ H.map φ) : ∃ P : Subgroup A, P ≤ H ∧ IsPGroup p P ∧ P.map φ = Q := by
  set W := H ⊓ Q.comap φ
  let ψ : W →* Q := (φ.comp W.subtype).codRestrict Q fun w => w.2.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := hQH hq
    exact ⟨⟨a, ha, hq⟩, rfl⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p W))
  have htop : ((T.mapSurjective hψ : Sylow p Q) : Subgroup Q) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, (Subgroup.map_subtype_le _).trans inf_le_left,
    T.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2.2
  · intro q hq
    obtain ⟨w, hw, hwq⟩ : (⟨q, hq⟩ : Q) ∈ (T : Subgroup W).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwq⟩

end Proof15Res3Inner

open Proof15Res3Inner

end CFSG.RankThree.PartTwo.Sec15
