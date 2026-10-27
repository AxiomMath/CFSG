module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace GGE6ThreeData

theorem weylFrame
    {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
    {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}
    (h : GGE6ThreeData Z A Φ T w) :
    GGWeylFrame 3 A CoxeterMatrix.E₆ := by
  refine ⟨w, h.conj_w_mem_normalizer, h.torusWeylElt_w,
    h.conjAut_isReflection, ?_⟩
  refine ⟨ggE6Row_coxeterGroupEquiv.trans h.automizerEquivWeyl, fun i => ?_⟩
  change (h.automizerEquivWeyl
    (ggE6Row_coxeterGroupEquiv (CoxeterMatrix.E₆.simple i)) : MulAut ↥A) =
      ggConjAut A (h.conj_w_mem_normalizer i)
  rw [ggE6Row_coxeterGroupEquiv_simple]
  exact h.automizerEquivWeyl_simple i

end GGE6ThreeData

theorem sevenTwenty_le_card_ggAutomizer_of_e6_oneNode
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs K J : Subgroup G}
    (eK : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer K Bs))
    (hSide : GGResSideDatum p Bs K J) :
    720 ≤ Nat.card ↥(ggAutomizer J Bs) := by
  classical
  have hE6 : GGIsWeylMatrix CoxeterMatrix.E₆ := by
    refine Or.inr (Or.inl ⟨Equiv.refl _, ?_⟩)
    apply CoxeterMatrix.ext
    ext i j
    rw [CoxeterMatrix.reindex_apply]
    simp
  obtain ⟨Λ, instF, instD, b, M, C, MJ, V, instA, instM, ι, φ, h, α,
    hWM, hC, hWMJ, hMJ, hlin, hrefl, hpair, hXe, hXclos, hJe, hJclos, hJrefl⟩ := hSide
  obtain ⟨fK, -⟩ := hXe
  obtain ⟨fJ, -⟩ := hJe
  have hcardΛ : Fintype.card Λ = 6 := by
    have h := ggWeylTypeData_rank_eq_of_mulEquiv hWM hE6
      (fK.trans eK.symm)
    simpa using h
  have hcardJ : Fintype.card {j : Λ // j ≠ b} = 5 := by
    rw [Fintype.card_subtype_compl (fun j : Λ => j = b), Fintype.card_subtype_eq]
    omega
  have hdata : GGWeylTypeData 5 (Nat.card MJ.Group)
      (Nat.card ↥(Subgroup.center MJ.Group)) := by
    simpa only [hcardJ] using ggWeylTypeData_of_isWeylMatrix hWMJ
  have hMJcard : 720 ≤ Nat.card MJ.Group := by
    rcases hdata with hA | hB | hD | hE6 | hE7 | hE8 | hF4 | hG2
    · obtain ⟨-, hn, -⟩ := hA
      rw [hn]
      norm_num
    · obtain ⟨-, hn, -⟩ := hB
      rw [hn]
      norm_num
    · obtain ⟨-, hn, -⟩ := hD
      rw [hn]
      norm_num
    · obtain ⟨h6, -, -⟩ := hE6
      omega
    · obtain ⟨h7, -, -⟩ := hE7
      omega
    · obtain ⟨h8, -, -⟩ := hE8
      omega
    · obtain ⟨h4, -, -⟩ := hF4
      omega
    · obtain ⟨h2, -, -⟩ := hG2
      omega
  have hcard : Nat.card MJ.Group = Nat.card ↥(ggAutomizer J Bs) :=
    Nat.card_congr fJ.toEquiv
  simpa only [hcard] using hMJcard

end CFSG.StandardType

end
