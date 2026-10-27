module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P510Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4NineMain

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem zz_arc_length (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h33 : Fan33 F)
    (h211 : Tutte.TutteTree) (T : Track Γ G) (hT : InPiStar T) {z : G} (hz : z ∈ T.line.ZZ)
    (hz1 : z ≠ 1) {tL tR : ℤ} (hfix : ∀ i, i ∈ T.line.fixIdx z ↔ tL ≤ i ∧ i ≤ tR) :
    tR - tL ≤ 8 ∧ tR - tL ≠ 7 := by
  have h48 : Fan48Two F := fan48_two F h40 h28 h211
  obtain ⟨hzz, i₀, hzs, hzc⟩ := hz
  have hnfix : z ∉ T.fixer := fun hzf =>
    hz1 (fan49 F h40 h28 h33 h48 T i₀ z hzf fun g hg => hzc g hg)
  have hi0 := (T.line.mem_edgeStab_iff).1 hzs
  have hLR : tL ≤ tR := by
    have := (hfix i₀).1 hi0.1
    omega
  have hzfix : ∀ c d : ℤ, tL ≤ c → d ≤ tR → z ∈ T.subFixer c d := fun c d hc hd =>
    (T.mem_subFixer).2 fun i h1 h2 => (hfix i).2 ⟨by omega, by omega⟩
  have hzmem : z ∈ omega1 (T.subFixer tL tR) :=
    Subgroup.subset_closure ⟨hzfix tL tR le_rfl le_rfl, hzz⟩
  have hpseg : PSeg T tL tR := ⟨hLR, fun hle => hnfix (hle hzmem)⟩
  obtain ⟨a, b, ha, hb, hp, hmax⟩ := T.exists_pseg_max F hpseg
  have hθ : IsTArc T a b := IsTArc.of_pseg_max T F h40 hp hmax
  have hmaxT : IsMaxTArc T a b := (fan42_2b T F h40 a b).2 ⟨hp, hmax⟩
  have hlen : b - a ≤ 8 := (fan48_concl F h40 h28 h211 T hT hθ).length
  have hev : (b - a) % 2 = 0 := fan_4_3_2 T F hT.1 hθ
  refine ⟨by omega, fun h7 => ?_⟩
  have hba : b - a = 8 := by omega
  have h44 := fan44_1 T F h40 hT.1.1 hT.1.2 hmaxT
  rcases (show (a = tL - 1 ∧ b = tR) ∨ (a = tL ∧ b = tR + 1) by omega) with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
  · have hmem : z ∈ omega1 (T.subFixer (a + 1) b) :=
      Subgroup.subset_closure ⟨hzfix (a + 1) b (by omega) (by omega), hzz⟩
    have hfa := (hfix a).1 (MulAction.mem_stabilizer_iff.1 (h44.2 hmem))
    omega
  · have hmem : z ∈ omega1 (T.subFixer a (b - 1)) :=
      Subgroup.subset_closure ⟨hzfix a (b - 1) (by omega) (by omega), hzz⟩
    have hfb := (hfix b).1 (MulAction.mem_stabilizer_iff.1 (h44.1 hmem))
    omega

end CFSG.Quasithin.Fan86
