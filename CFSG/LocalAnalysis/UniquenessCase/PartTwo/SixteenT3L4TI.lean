module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open S18 (tilOf)

variable {G : Type} [Group G] [Finite G]

theorem s16t_l4_false_of_fix_or_uniqueMax (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} (h16 : Hyp16 D V₀ V)
    (hMst : D.M ≤ stabTil V₀ V) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpσ : p ∈ D.sig)
    {E : Subgroup G} (hEM : E ≤ D.M) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3)
    (hw : ∀ (w : G) (hwV : w ∈ V), w ∉ V₀ →
      (∃ B : Subgroup ↥D.M, IsPGroup p B ∧ ¬ IsCyclic ↥B ∧
        ∀ b ∈ B, barHom V₀ V hV hMst b (tilOf V₀ V hV w hwV) = tilOf V₀ V hV w hwV) ∨
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    False := by
  have hH : Hyp125 D V₀ V := h16.hyp125
  have hMn : D.M ≤ normalizer (V : Set G) := hH.pairFacts.le_normalizer
  have hMn₀ : D.M ≤ normalizer (V₀ : Set G) := hH.pairFacts.le_normalizer₀
  have hc4 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D h16
  refine r129_1_of_r127 D h127 V₀ V hH
    (s15_FiveTen_isTI_of_uniqueMax D hV hMn fun w hwV hw1 => ?_)
  by_cases hwV₀ : w ∈ V₀
  · exact c23_uniqueMax_of_mem_v0 D h61 hc4 hMn₀ hp hp3 hpσ hEM hE hEcard hwV₀ hw1
  · rcases hw w hwV hwV₀ with ⟨B, hBp, hBc, hBfix⟩ | hu
    · have hinj := D.M.subtype_injective
      have hBp' : IsPGroup p (B.map D.M.subtype) := hBp.map D.M.subtype
      have hBc' : ¬ IsCyclic ↥(B.map D.M.subtype) := fun hcyc =>
        hBc ((Subgroup.equivMapOfInjective B D.M.subtype hinj).isCyclic.2 hcyc)
      have hBw : B.map D.M.subtype ≤ F11.CElt D.M V₀ w := by
        rintro _ ⟨b, hb, rfl⟩
        refine ⟨b.2, hMn₀ b.2, ?_⟩
        exact (barHom_fix_iff V₀ V hV hMst b (IntMod.mk hV ⟨w, hwV⟩)).1 (hBfix b hb)
      exact c23_uniqueMax_of_le_cElt D h61 (Hyp125.hyp11 h127 hH) hc4 hp
        (by omega) hpσ hBp' hBc' hwV hwV₀ hBw
    · exact hu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
