module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1P
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Index
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinTrans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.JonesParshall CFSG.LieType.SpinGeom

theorem spinMu_Z1A_eq_B1A : Z1A spinMu = B1A spinMu := by
  refine le_antisymm (fun f hf => ?_) (B1A_le_Z1A _)
  haveI : Finite ↥spinH := Nat.finite_of_card_ne_zero (by rw [card_spinH]; norm_num)
  obtain ⟨x, hx⟩ := exists_cob_stab hf
  refine mem_B1A_of_restrict (μ := spinMu) (M := Fin 8 → ZMod 2) (G := ↥spinH)
    (H := MulAction.stabilizer ↥spinH
      (Multiplicative.ofAdd (frameE (ZMod 2) 0))) (m := x)
    (fun m => by funext i; exact CharTwo.add_self_eq_zero (m i)) ?_ hf ?_
  · rw [index_stabilizer_E0]
    exact ⟨67, by norm_num⟩
  · intro h hh
    have hfix : (h : MulAut SpinW) (Multiplicative.ofAdd (frameE (ZMod 2) 0)) =
        Multiplicative.ofAdd (frameE (ZMod 2) 0) := by
      simpa [Subgroup.smul_def] using (MulAction.mem_stabilizer_iff.mp hh)
    exact hx h hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
