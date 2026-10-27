module

public import CFSG.Timmesfeld.Transvection.FrameResidue

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Transvection.AssembleGen

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}

theorem perpSet_pred_eq_frameResidue (hr : 1 ≤ r) :
    perpSet Δ P Q (r - 1) =
      frameResidue Δ P Q ⟨r - 1, Nat.sub_one_lt_of_lt hr⟩ := by
  ext X
  simp only [perpSet, frameResidue, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hX, hc⟩
    refine ⟨hX, fun i hi => hc i ?_⟩
    have hlt : i.val < r := i.isLt
    have hne : i.val ≠ r - 1 := fun hv => hi (Fin.ext hv)
    omega
  · rintro ⟨hX, hc⟩
    refine ⟨hX, fun i hi => hc i ?_⟩
    intro h
    have hv : i.val = r - 1 := congrArg Fin.val h
    omega

end CFSG.Timmesfeld.Transvection
