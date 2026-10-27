module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

section Basic

variable {G : Type} [Group G] [Finite G]

theorem qTwoLMFrameC_perfect {B L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L) :
    commutator ↥L = ⊤ :=
  hG.2.2.2.2.2.2.1.2.2.2.1.2.2.1

theorem qTwoLMFrameC_le_centralizer {B L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L) :
    L ≤ Subgroup.centralizer ({x} : Set G) :=
  hG.2.2.2.2.2.2.1.2.2.2.1.1

theorem qTwoLMFrameC_four_le {m : ℕ} {X : Type} [Group X] (hL : LieModel X .PSU m 2 1) :
    4 ≤ m := by
  obtain ⟨_, _, h3, hne⟩ := hL.admissible
  have : m ≠ 3 := fun h => hne (by simp [h])
  omega

theorem qTwoLMFrameC_center_bot {B L : Subgroup G} {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m) :
    Subgroup.center ↥L = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ (hMul (↥L) (qTwoLMFrameC_perfect hG) hL)

theorem qTwoLMFrameC_x_not_mem {B L : Subgroup G} {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m) :
    x ∉ L := by
  intro hxL
  have hx1 : x ≠ 1 := hG.2.2.2.2.2.2.1.2.2.1
  have hc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    have := Subgroup.mem_centralizer_iff.mp (qTwoLMFrameC_le_centralizer hG l.2) x
      (Set.mem_singleton x)
    exact Subtype.ext this.symm
  rw [qTwoLMFrameC_center_bot hG hL hMul, Subgroup.mem_bot] at hc
  exact hx1 (congrArg Subtype.val hc)

end Basic

end CFSG.StandardType.QTwo

end
