module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_oTwoP (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (((Sec4.oTwoP p ↥X).map X.subtype : Subgroup G) : Set G) := by
  have hn : (Sec4.oTwoP p ↥X).Normal :=
    Subgroup.Normal.comap (CFSG.pCore_normal (p := p)) _
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, hn.conj_mem y hy ⟨x, hx⟩, by simp⟩
  · rintro ⟨y, hy, hyg⟩
    refine ⟨⟨x, hx⟩⁻¹ * y * ⟨x, hx⟩, ?_, ?_⟩
    · simpa using hn.conj_mem y hy ⟨x, hx⟩⁻¹
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyg ⊢
      rw [hyg]
      group

omit [Finite G] in
theorem le_oTwoP_of_pData {X : Subgroup G} {p : ℕ} {P : Subgroup G}
    (hchar : ∃ R : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype) ∧ P ≤ R ∧
        (P.subgroupOf R).Characteristic) :
    P ≤ (Sec4.oTwoP p ↥X).map X.subtype := by
  obtain ⟨R, ⟨R', hR'⟩, hPR, -⟩ := hchar
  exact hPR.trans (hR' ▸ Subgroup.map_subtype_le _)

end CFSG.RankThree.PartTwo.Sec15
