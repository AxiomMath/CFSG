module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.AutOnIndex

public section

namespace CFSG.Quasithin

namespace AutOn

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem isSylowTwoOf_autOn [Finite G] {V P S : Subgroup G} (hSP : IsSylowTwoOf S P)
    (hP : P ≤ Subgroup.normalizer (V : Set G)) : IsSylowTwoOf (autOn S V) (autOn P V) := by
  set C : Subgroup G := P ⊓ Subgroup.centralizer (V : Set G) with hC
  have hSN : S ≤ Subgroup.normalizer (V : Set G) := hSP.1.trans hP
  have hCP : C ≤ P := inf_le_left
  have hSC : S ⊓ Subgroup.centralizer (V : Set G) = S ⊓ C := by
    ext x
    simp only [hC, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, hSP.1 h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have e1 : Nat.card (autOn P V) * Nat.card C = Nat.card P := by
    rw [card_autOn_eq_relIndex hP]
    have := Subgroup.relIndex_mul_card C P
    rwa [inf_of_le_left hCP] at this
  have e2 : Nat.card (autOn S V) * Nat.card (S ⊓ C : Subgroup G) = Nat.card S := by
    rw [card_autOn_eq_relIndex hSN, hSC]
    have := Subgroup.relIndex_mul_card (S ⊓ C) S
    rwa [inf_of_le_left inf_le_left] at this
  have e3 : S.relIndex P * Nat.card S = Nat.card P := by
    have := Subgroup.relIndex_mul_card S P
    rwa [inf_of_le_left hSP.1] at this
  have hle : autOn S V ≤ autOn P V := autOn_mono hSP.1
  have e4 : (autOn S V).relIndex (autOn P V) * Nat.card (autOn S V) = Nat.card (autOn P V) := by
    have := Subgroup.relIndex_mul_card (autOn S V) (autOn P V)
    rwa [inf_of_le_left hle] at this
  have e5 : (S ⊓ C).relIndex C * Nat.card (S ⊓ C : Subgroup G) = Nat.card C := by
    have := Subgroup.relIndex_mul_card (S ⊓ C) C
    rwa [inf_of_le_left inf_le_right] at this
  have hTpos : 0 < Nat.card (autOn S V) := Nat.card_pos
  have hUpos : 0 < Nat.card (S ⊓ C : Subgroup G) := Nat.card_pos
  have hkey : (autOn S V).relIndex (autOn P V) * (S ⊓ C).relIndex C = S.relIndex P := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hTpos hUpos) ?_
    calc (autOn S V).relIndex (autOn P V) * (S ⊓ C).relIndex C *
          (Nat.card (autOn S V) * Nat.card (S ⊓ C : Subgroup G))
        = ((autOn S V).relIndex (autOn P V) * Nat.card (autOn S V)) *
            ((S ⊓ C).relIndex C * Nat.card (S ⊓ C : Subgroup G)) := by ring
      _ = Nat.card (autOn P V) * Nat.card C := by rw [e4, e5]
      _ = Nat.card P := e1
      _ = S.relIndex P * Nat.card S := e3.symm
      _ = S.relIndex P * (Nat.card (autOn S V) * Nat.card (S ⊓ C : Subgroup G)) := by rw [e2]
  have hTp : IsPGroup 2 (autOn S V) :=
    (hSP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm).map (conjAct V)
  refine ⟨hle, hTp, fun hdvd => hSP.2.2 ?_⟩
  exact hdvd.trans ⟨_, hkey.symm⟩

end AutOn

end CFSG.Quasithin
