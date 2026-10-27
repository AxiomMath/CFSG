module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusIsL2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSylow3
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus)

theorem even_clause {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : Even n) :
    ∃ B P₃ : Subgroup (Gom (quadMinus 3 F b c)), Nat.card B = 3 ∧ B ≤ P₃ ∧
      CFSG.ABGLocalTools.IsSylowOf 3 P₃ ⊤ ∧
      P₃ ≤ Subgroup.centralizer (B : Set (Gom (quadMinus 3 F b c))) ∧
      P₃ ≤ pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e ∧
      F08.KOf8103 ⊤ B ≤ pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e ∧
      IsL2 (Bar2 (F08.KOf8103 ⊤ B)) (2 * n) := by
  obtain ⟨B, P₃, t, ω, hω3, hω1, ht, hBt, hB3, hBP, hSyl, hab, hPS⟩ :=
    exists_sylow3_torus hirr hcard hn
  let X : Subgroup (Gom (quadMinus 3 F b c)) :=
    ⊤ ⊓ Subgroup.centralizer (B : Set (Gom (quadMinus 3 F b c)))
  have hLX : leviSub (stdP0 F b c) ≤ X := by
    refine le_inf le_top ?_
    rw [hBt]
    exact ht.leviSub_le_centralizer_zpowers
  have hXS : X ≤ pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e := by
    refine inf_le_right.trans ?_
    rw [hBt]
    exact ht.centralizer_zpowers_le_pointStabilizer hω3 hω1
  refine ⟨B, P₃, hB3, hBP, hSyl, ?_, hPS, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hab y (hBP hy) x hx
  · calc F08.KOf8103 ⊤ B = Hinf X := rfl
      _ ≤ X := uc22p21c_Hinf_le X
      _ ≤ pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e := hXS
  · exact isL2_bar2_derInf_std hcard hirr hLX hXS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
