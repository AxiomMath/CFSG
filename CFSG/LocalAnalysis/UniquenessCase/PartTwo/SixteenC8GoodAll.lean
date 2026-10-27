module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Good
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Fin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Conj
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Close
import CFSG.Quasithin.Background.C124Perf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Rechoice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c8_mem_centralizer_iff_fix (D : Data G) {V X : Subgroup G}
    {hV : IsElemAbelian 2 V} (hMs : D.M ≤ stabTil ⊥ V) (hXM : X ≤ D.M) {w : G} (hw : w ∈ V) :
    w ∈ centralizer (X : Set G) ↔
      ∀ φ ∈ barSub ⊥ V hV X,
        φ (mkTil ⊥ V hV (IntMod.mk hV ⟨w, hw⟩)) = mkTil ⊥ V hV (IntMod.mk hV ⟨w, hw⟩) := by
  constructor
  · intro hc φ hφ
    obtain ⟨g, hgX, rfl⟩ := (mem_barSub ⊥ V hV X φ).1 hφ
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
    have hgw : (g : G) * w = w * (g : G) :=
      Subgroup.mem_centralizer_iff.1 hc (g : G) hgX
    change (g : G) * w * (g : G)⁻¹ * w⁻¹ = 1
    rw [hgw]
    group
  · intro hfix
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have has : a ∈ stabTil ⊥ V := hMs (hXM ha)
    have h := hfix (actTil ⊥ V hV ⟨a, has⟩) (actTil_mem_barSub ⊥ V hV ha has)
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h
    have h1 : a * w * a⁻¹ * w⁻¹ = 1 := Subgroup.mem_bot.1 h
    have h2 : a * w * a⁻¹ = w := mul_inv_eq_one.1 h1
    calc a * w = a * w * a⁻¹ * a := by group
      _ = w * a := by rw [h2]

theorem c8_v1Sub_congr (D : Data G) {V₀ V L Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) (hLM : L ≤ D.M) (hYM : Y ≤ D.M)
    (hbar : barSub V₀ V hV Y = barSub V₀ V hV L) :
    v1Sub D.M V₀ V hV Y = v1Sub D.M V₀ V hV L := by
  by_cases h0 : V₀ = ⊥
  · subst h0
    rw [v1Sub_of_eq_bot D.M ⊥ V hV Y rfl, v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
    have hW : wSub ⊥ V hV Y = wSub ⊥ V hV L := by
      unfold wSub wTil
      rw [hbar]
    have hC : wSub ⊥ V hV Y ⊓ centralizer (Y : Set G) =
        wSub ⊥ V hV L ⊓ centralizer (L : Set G) := by
      rw [hW]
      refine le_antisymm ?_ ?_
      · rintro w ⟨hw, hc⟩
        have hwV : w ∈ V := preTil_le ⊥ V hV (wTil ⊥ V hV L) hw
        refine ⟨hw, (c8_mem_centralizer_iff_fix (hV := hV) D hMs hLM hwV).mpr ?_⟩
        intro φ hφ
        exact (c8_mem_centralizer_iff_fix (hV := hV) D hMs hYM hwV).mp hc φ (hbar.symm ▸ hφ)
      · rintro w ⟨hw, hc⟩
        have hwV : w ∈ V := preTil_le ⊥ V hV (wTil ⊥ V hV L) hw
        refine ⟨hw, (c8_mem_centralizer_iff_fix (hV := hV) D hMs hYM hwV).mpr ?_⟩
        intro φ hφ
        exact (c8_mem_centralizer_iff_fix (hV := hV) D hMs hLM hwV).mp hc φ (hbar ▸ hφ)
    exact iSup_congr fun m =>
      congrArg (fun Z : Subgroup G => conjSubgroup Z (m : G)) hC
  · rw [v1Sub_of_ne_bot D.M V₀ V hV Y h0, v1Sub_of_ne_bot D.M V₀ V hV L h0]

theorem c8_sect16_of_bar_all (D : Data G) (h1217 : R1217 D) (hSpA : RSp6SmallMod)
    (hSpC : RSp6SpinCent) {V₀ V L Y : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (h8 : Case167_8 D V₀ V hV L) (hYM : Y ≤ D.M) (hperf : ⁅Y, Y⁆ = Y)
    (hbar : barSub V₀ V hV Y = lBar V₀ V hV L) :
    Sect16 D V₀ V Y hV ∧ Case167_8 D V₀ V hV Y := by
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hM : Mbar D.M V₀ V hV = lBar V₀ V hV L := c8_mbar_eq_lbar D h1217 hSpA hSpC hS h8
  have hlb : lBar V₀ V hV Y = lBar V₀ V hV L := hbar
  have h151 : Hyp151 D V₀ V Y :=
    { hyp125 := hS.setting.hyp151.hyp125
      le := hYM
      twoResidual_eq := CFSG.Quasithin.C124.twoResidual_eq_self_of_perfect' hperf
      fstar_eq := by
        have := hS.setting.hyp151.fstar_eq
        change Fstar (lBar V₀ V hV Y) = lBar V₀ V hV Y
        rw [hlb]
        exact this
      commute := by
        intro g hg hgn
        exfalso
        apply hgn
        refine (mem_preBarSub D.M V₀ V hV _).2 ⟨hg, hMs hg, ?_⟩
        have hmem : actTil V₀ V hV ⟨g, hMs hg⟩ ∈ barSub V₀ V hV Y := by
          change actTil V₀ V hV ⟨g, hMs hg⟩ ∈ lBar V₀ V hV Y
          rw [hlb, ← hM]
          exact actTil_mem_barSub V₀ V hV hg (hMs hg)
        exact Subgroup.le_normalizer hmem }
  refine ⟨⟨⟨hS.setting.hyp16, h151⟩, ?_, ?_⟩, ?_⟩
  · rw [hbar]; exact hS.ne_bot
  · have h := hS.conc
    unfold Conc4_136 at h ⊢
    rw [hlb]; exact h
  · obtain ⟨h1, h2, h3, h4⟩ := h8
    refine ⟨hlb ▸ h1, ?_, h3, h4⟩
    have key : ∀ X X' : Subgroup G, X = X' → rk ↥(⊤ : Subgroup (Vtil X V hV)) = 8 →
        rk ↥(⊤ : Subgroup (Vtil X' V hV)) = 8 := by
      rintro X X' rfl h
      exact h
    exact key _ _ (c8_v1Sub_congr D hV hMs hS.setting.hyp151.le hYM hbar).symm h2

theorem c8_exists_good_all (D : Data G) (h127 : R127 D) (h119 : F11.R119 D) (h1217 : R1217 D)
    (hSpA : RSp6SmallMod) (hSpC : RSp6SpinCent) (hSchur : C8SchurSp6)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h8 : Case167_8 D V₀ V hV L) :
    ∃ Y : Subgroup G, Sect16 D V₀ V Y hV ∧ Case167_8 D V₀ V hV Y ∧
      lBar V₀ V hV Y = lBar V₀ V hV L ∧ C8Good D V₀ V Y := by
  obtain ⟨Y, hYM, hNY, hperf, hE, hinf, hbar⟩ := c8_exists_Y D h127 h119 h1217 hSpA hSpC hS h8
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨hSY, h8Y⟩ := c8_sect16_of_bar_all D h1217 hSpA hSpC hS h8 hYM hperf hbar
  exact ⟨Y, hSY, h8Y, hbar, hNY, c8_cTilde_isPGroup D hSchur hMs hYM hperf hE hinf h8Y.1⟩

theorem r16_27_4_of_good (D : Data G) (h61 : UC6.R6_1 D) (h129 : R129_1 D) (h22 : R1622 D)
    (h1217 : R1217 D) (hSpA : RSp6SmallMod) (hSpC : RSp6SpinCent) (hSpF : RSp6SpinForm)
    (hSpSt : RSp6SpinStab) (h127 : R127 D) (h119 : F11.R119 D) (hSchur : C8SchurSp6)
    (hle : C8TleKGood D) (hinv : C8InvThreePrimeGood D) : R16_27_4 D := by
  unfold R16_27_4
  intro V₀ V L hV hS h8 A hAT hA
  obtain ⟨Y, hSY, h8Y, hbar, hG⟩ :=
    c8_exists_good_all D h127 h119 h1217 hSpA hSpC hSchur hS h8
  have hP := hSY.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hM : Mbar D.M V₀ V hV = lBar V₀ V hV Y := c8_mbar_eq_lbar D h1217 hSpA hSpC hSY h8Y
  obtain ⟨ψ, hTP, hTR⟩ := c8_star_sylowT D hMs hM
    (c8_star_holds_of_good D h61 h129 h22 h1217 hSpA hSpC hSpF hSpSt hle hinv hSY h8Y hG)
  have key := c8_barSub_eq_bot_or_zpowers D hMs hM D.sylowM ψ hTP hTR hAT hA
  have res : barSub V₀ V hV A = ⊥ ∨
      ∃ a : ↥(lBar V₀ V hV Y), IsSp6Transvection a ∧
        barSub V₀ V hV A = Subgroup.zpowers (a : MulAut (Vtil V₀ V hV)) := by
    rcases key with h | ⟨a, ha, hAa⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ⟨ψ, ha⟩, hAa⟩
  clear key hTP hTR ψ hM
  revert res
  generalize lBar V₀ V hV Y = H at hbar
  subst hbar
  exact id

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
