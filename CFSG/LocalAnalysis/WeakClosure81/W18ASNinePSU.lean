module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineGap
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineT
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)

theorem noSocle185Factor_of_isPSUGp (hO : LieOrderFormulasInput) {Y : Type} [Group Y] {m n : ℕ}
    (h : IsPSUGp Y m n) : NoSocle185Factor Y := by
  have hadm : StatedLieAdmissible .PSU m 2 n := h.admissible
  have hcl : StatedClassicalModel Y .PSU m 2 n := h.statedClassicalModel (by decide)
  haveI : IsSimpleGroup Y := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y m 2 n hcl).2
  refine NoSocle185Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
  have hT' : CFSG.Blueprint.LieModel T .PSU m 2 n := h.of_mulEquiv e
  obtain ⟨-, hM, -⟩ := hO T .PSU m 2 n hadm hT'
  rcases hT.crossChar hO hadm hM with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · have : Nat.card T = 25920 := by
      have hd : lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by decide
      rw [hd, mul_one] at hM
      rw [hM]
      have h4 : Even (4 : ℕ) := by decide
      have h3 : ¬ Even (3 : ℕ) := by decide
      simp [lieOrderNumerator, show Finset.Icc 2 4 = {2, 3, 4} by decide, h4, h3]
    exact (hT.card_facts hO).2.2.2.1 this

end CFSG.LocalAnalysis.WeakClosure81

end
