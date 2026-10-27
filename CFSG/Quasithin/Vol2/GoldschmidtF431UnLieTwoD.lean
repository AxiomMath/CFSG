module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieNstC
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieTwoB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem centerOf_perfectCore_Pt (hf : 2 ≤ f) : centerOf (perfectCore (Pt h)) = ZX h := by
  rw [perfectCore_Pt h hf, centerOf_A2X_sup_N2X h hf]

theorem z_ZP_Xg (hf : 2 ≤ f) : z1X h ∈ centerOf (perfectCore (Pt h)) := by
  rw [centerOf_perfectCore_Pt h hf]
  exact z1X_mem_ZX h

theorem ZP_trans_Xg (hf : 2 ≤ f) {x : Xg h} (hx : x ∈ centerOf (perfectCore (Pt h)))
    (hx1 : x ≠ 1) : ∃ m ∈ Pt h, m * z1X h * m⁻¹ = x := by
  rw [centerOf_perfectCore_Pt h hf] at hx
  have hxZ : (x : GL (Fin 4) K) ∈ miyamotoZ h := hx
  have hxC := (centerIn_miyamotoP h).ge hxZ
  obtain ⟨b, hb, e⟩ := center_Xg h (w := x) (miyamotoZ_le_P h hxZ) (fun y hy =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC.2 (y : GL (Fin 4) K) hy)) hx1
  exact ⟨b, (Subgroup.mem_inf.1 hb).1, e⟩

end CFSG.Quasithin.H13.F431.Un.OL
