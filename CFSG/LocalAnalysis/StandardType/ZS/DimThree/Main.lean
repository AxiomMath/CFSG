module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.SL
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Orth
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.H3
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.J34
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.J35
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Hess
public import CFSG.RankThree.SubgroupLists.IrreducibleGL3
import CFSG.RankThree.PartOne.N1322.CaseCyclic
import CFSG.RankThree.PartOne.N1322.CoreHyp

public section

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne CFSG.RankThree.SubgroupLists
open CFSG.RankThree.PartOne.LIT (autGL)


theorem rows_of_finrank_eq_three {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hp : p ≠ 2) (h3 : Module.finrank (ZMod p) U = 3) (hR : ReflGen p A) (hI : AbsIrred p A)
    (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A) :
    (∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) ∨
      IsOrthType p A ∨
      (ExcData p .H3 A ∧ (p % 10 = 1 ∨ p % 10 = 9) ∧ (∀ g ∈ A, ∃ k ∈ A, k * g * k⁻¹ = g⁻¹) ∧
        H3Frame p A) ∨
      (ExcData p .J34 A ∧ J34Frame p A) ∨
      (ExcData p .J35 A ∧ ∃ g ∈ A, ∃ ζ : ZMod p, ζ * ζ ≠ 1 ∧ ∀ v, g v = ζ • v) := by
  obtain ⟨e⟩ : Nonempty (U ≃ₗ[ZMod p] (Fin 3 → ZMod p)) :=
    ⟨(Module.finBasisOfFinrankEq (ZMod p) U h3).equivFun⟩
  obtain ⟨H, hHG, hn, hirr, hcase⟩ :=
    bloom_mitchell_irreducible_gl_three hp (isIrreducibleMatrixRep_map e hI)
  rcases hcase with rfl | ⟨M, hMt, hMd, rfl⟩ | ⟨⟨e5⟩, hp10, hdec, -⟩ | ⟨⟨e32⟩, hp7⟩ |
      ⟨hperf, hZ3, ⟨e6⟩, hp30⟩ | ⟨hcyc, -, -⟩ | ⟨h27, hE, hp3⟩ | ⟨-, L, hL, h1, hperm, -⟩
  · exact Or.inl (mem_iff_det_of_statedSL_le hp e hR hI hHG)
  · exact Or.inr (Or.inl (isOrthType_of_omegaGL_le hp e hR hI hMt hMd hHG hn hirr))
  · refine Or.inr (Or.inr (Or.inl ⟨?_, hp10, ?_, ?_⟩))
    · exact excData_of_alternatingFive hp e hR hI hHG hirr e5 hp10 hdec
    · exact isConj_inv_of_alternatingFive hp e hR hI hHG hirr e5 hp10 hdec
    · exact h3Frame_of_alternatingFive hp e hR hI hHG hirr e5 hdec
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))
    · exact excData_of_glThreeTwo hp e hR hI hHG hn hirr e32 hp7
    · exact j34Frame_of_glThreeTwo hp e hR hI hHG hn hirr e32 (by
        rintro rfl
        rcases hp7 with h | h | h <;> norm_num at h)
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))
    · exact excData_of_threeAlternatingSix hp e hR hI hHG hn hirr hZ3 e6 hp30
    · exact exists_smul_of_threeAlternatingSix e hHG hirr hZ3 e6
  · obtain ⟨t, htG, ht⟩ := exists_isRefl_mem hp e hR hI
    exact (N1322.no_refl_normalizing_cyclic (four_ne_zero_of_ne_two hp) hirr hcyc ht
      fun x hx => hn t htG x hx).elim
  · exact (hprim (isImprimitiveOnV_of_extraspecial hp e hR hn hirr h27 hE hp3)).elim
  · exact (hprim (isImprimitiveOnV_of_lines e hL h1 hperm)).elim

theorem family_of_finrank_eq_three {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hp : p ≠ 2) (h3 : Module.finrank (ZMod p) U = 3) (hR : ReflGen p A) (hI : AbsIrred p A)
    (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A) : Family p A := by
  rcases rows_of_finrank_eq_three hp h3 hR hI hprim with h | ⟨Q, hQ, h | ⟨c, hc, h⟩⟩ |
      ⟨h, -, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Family.slpm h
  · exact Family.orth Q hQ h
  · exact Family.orthClass Q c hQ hc h
  all_goals exact family_of_excData h (by simp [ExcRow.needsModel])

end CFSG.StandardType.ZS.DimThree
