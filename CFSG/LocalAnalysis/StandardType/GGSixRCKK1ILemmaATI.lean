module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLineChev
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLinePSL2All
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLinePSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLineOmM
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLineTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaH
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHBruhat

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)
open CFSG.StandardType.RCKC1

theorem rckLemmaHTI_of_scalars {M : LieUniversal} {β : Fin M.D.rank → ℤ} {Fq : Type} [Field Fq]
    {ε : Multiplicative Fq ≃* M.D.rootGroup β} (h1 : RCKRootLineScalars (M.D.rootGroup β) Fq ε)
    (hC : RCKLemmaHCent M β) : RCKLemmaHTI M β := by
  refine rckHB_TI_of_cent hC fun x hx hx1 y hy hy1 => ?_
  set a : Fq := Multiplicative.toAdd (ε.symm ⟨x, hx⟩) with ha
  set b : Fq := Multiplicative.toAdd (ε.symm ⟨y, hy⟩) with hb
  have hxa : (ε (Multiplicative.ofAdd a) : M.K) = x := by rw [ha, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hyb : (ε (Multiplicative.ofAdd b) : M.K) = y := by rw [hb, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hne : ∀ c : Fq, (ε (Multiplicative.ofAdd c) : M.K) ≠ 1 → c ≠ 0 := by
    intro c hc h0
    exact hc (by rw [h0, ofAdd_zero, map_one]; rfl)
  have ha0 : a ≠ 0 := hne a (by rw [hxa]; exact hx1)
  have hb0 : b ≠ 0 := hne b (by rw [hyb]; exact hy1)
  obtain ⟨h, hh⟩ := h1 (b * a⁻¹) (mul_ne_zero hb0 (inv_ne_zero ha0))
  refine ⟨h, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      set c : Fq := Multiplicative.toAdd (ε.symm ⟨z, hz⟩) with hc
      have hzc : (ε (Multiplicative.ofAdd c) : M.K) = z := by rw [hc, ofAdd_toAdd, MulEquiv.apply_symm_apply]
      rw [← hzc, hh c]
      exact (ε _).2
    · intro hz
      set c : Fq := Multiplicative.toAdd (ε.symm ⟨h * z * h⁻¹, hz⟩) with hc
      have hzc : (ε (Multiplicative.ofAdd c) : M.K) = h * z * h⁻¹ := by
        rw [hc, ofAdd_toAdd, MulEquiv.apply_symm_apply]
      have e1 : h * (ε (Multiplicative.ofAdd ((b * a⁻¹)⁻¹ * c)) : M.K) * h⁻¹ = h * z * h⁻¹ := by
        rw [hh, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hb0 (inv_ne_zero ha0)), one_mul, hzc]
      have e2 : (ε (Multiplicative.ofAdd ((b * a⁻¹)⁻¹ * c)) : M.K) = z := by
        simpa using e1
      rw [← e2]
      exact (ε _).2
  · rw [← hxa, hh a, mul_assoc, inv_mul_cancel₀ ha0, mul_one, hyb]

theorem rckK1I_lemmaHTI_ggU
    {t : StatedLieTag} {n f : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 f)
    {β : Fin (ggU t n f).D.rank → ℤ} (hβ : β ∈ (ggU t n f).D.roots) (hlong : GGLongRoot (ggU t n f).D β) :
    RCKLemmaHTI (ggU t n f) β := by
  have hall : RCKRootLineAll (ggU t n f) f := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hn : 3 ≤ n
      · exact (rckK1I_rootLine_chev (Or.inl ⟨rfl, hn⟩) hadm).2
      · obtain rfl : n = 2 := by have := hadm.2.2.1; omega
        exact (rckK1I_rootLineAll_PSL2 hadm).2
    · exact (rckK1I_rootLine_PSU hadm).2
    · exact (rckK1I_rootLine_chev (Or.inr (Or.inl rfl)) hadm).2
    · exact (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inl rfl))) hadm).2
    · exact (rckK1I_rootLine_POmegaMinus hadm).2
    · exact (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm).2
    · exact (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hadm).2
    · exact (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hadm).2
    · exact (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hadm).2
    · exact (rckK1I_rootLine_twistedE6 hadm).2
  obtain ⟨Fq, _, _, ε, -, hsc⟩ := hall β hβ hlong
  exact rckLemmaHTI_of_scalars hsc (rck_lemmaH_long.1 t n f β ht hadm.2.1 hlong)

end CFSG.StandardType.RCKK1I
