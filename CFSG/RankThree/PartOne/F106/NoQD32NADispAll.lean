module

public import CFSG.RankThree.PartOne.F106.NoQD32NADisp
public import CFSG.RankThree.PartOne.F106.NoQD32NAL3U3

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.N143
open scoped commutatorElement

theorem false_classical_nonab {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hLie : LieModel X t n 2 f)
    (hsmall : SmallEvenParams t n f)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .twistedB2)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5) (hU6 : ¬ (q = 3 ∧ t = .PSU ∧ n = 6))
    {Y : Subgroup X} (hexp : ∀ y ∈ Y, y ^ q = 1)
    (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : False := by
  by_cases h3 : q = 3 ∧ ((t = .PSL ∧ n = 3) ∨ (t = .PSU ∧ n = 3))
  · obtain ⟨rfl, h⟩ := h3
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hLie with ⟨-, hmod⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact false_psl3_nonab hmod hexp hcl h4
      all_goals exact absurd ht' (by decide)
    · rcases hLie with ⟨-, hmod⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact false_psu3_nonab hmod hexp hcl h4
      all_goals exact absurd ht' (by decide)
  · refine false_classical_nonab_ne3 hadm hLie hsmall ht hq hq2 hq5 ?_ hexp hcl h4
    rintro ⟨hq3, h | ⟨hPSU, h | h⟩⟩
    · exact h3 ⟨hq3, Or.inl h⟩
    · exact h3 ⟨hq3, Or.inr ⟨hPSU, h⟩⟩
    · exact hU6 ⟨hq3, hPSU, h⟩

end CFSG.RankThree.PartOne.F106
