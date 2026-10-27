module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4Points
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4Planes
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4Centralizer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLieChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace Case811L4

variable {c : Counterexample4 G} (t : Case811L4 c)

theorem normalizer_le_and_dvd_card
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN2 : Subgroup.normalizer ((Subgroup.zpowers t.a2 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {X : Subgroup G} (hXA : X ≤ t.A) (hX : Nat.card X = 3) :
    Subgroup.normalizer (X : Set G) ≤ c.S.M ∧
      t.r ∣ Nat.card (Subgroup.normalizer (X : Set G)) := by
  refine ⟨?_, (t.dvd_card_centralizer X hXA hX).trans (Subgroup.card_dvd_of_le
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer (X : Set G))))⟩
  obtain ⟨n, hnL, -, hXn⟩ := t.exists_conj_point hXA hX
  have hnM : n ∈ c.S.M := c.hyp81.1 hnL
  have hN : Subgroup.normalizer
      ((X.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) ≤ c.S.M := by
    rcases hXn with h | h | h <;> rw [h]
    exacts [hN1, hN2, hN3]
  intro g hg
  have hng : n * g * n⁻¹ ∈ c.S.M :=
    hN (by rw [← Subgroup.map_equiv_normalizer_eq]; exact ⟨g, hg, rfl⟩)
  have hg' : g = n⁻¹ * (n * g * n⁻¹) * n := by group
  rw [hg']
  exact c.S.M.mul_mem (c.S.M.mul_mem (c.S.M.inv_mem hnM) hng) hnM

end Case811L4

theorem Counterexample4.section8L4Residual (c : Counterexample4 G) (hK : KInputs811)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hS : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedSolvable)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) :
    Section8L4Residual c := by
  intro h r hlie _ hr _ hC
  obtain ⟨t, rfl, rfl⟩ := h.exists_case811L4 hK.k6c hK.k6d hK.k6L4 hlie hr hC
  have hN1 := t.normalizer_a1_le hSE hS
  have hN3 := t.normalizer_a3_le hSE hS
  exact t.false_of_forall_normalizer_le t.mem_sigma fun X hXA hX =>
    t.normalizer_le_and_dvd_card hN1 (t.normalizer_a2_le hK332 hN1 hN3) hN3 hXA hX

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
