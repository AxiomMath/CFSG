module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0Z
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0L2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0L3c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0U6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

theorem r95_group_caseB {Q : Type} [Group Q] [Finite Q]
    (hQ : Shape92 Q) (hcyc : ∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P) {E : Subgroup Q}
    (hE : HasL32Quot E) {W : Subgroup Q} (hEW : E ≤ W)
    (hNW : ∀ D : Subgroup Q, D ≤ E → Nat.card D = 3 → normalizer (D : Set Q) ≤ W)
    (hW : W ≠ ⊤) :
    ∃ e : ℕ, 1 ≤ e ∧ LieModel Q .PSU 3 7 e ∧ IsSL2Cover ↥(Opp 3 W) 7 e ∧ ¬ 2 ∣ W.index := by
  rcases hQ with ⟨-, h3⟩ | hJ | ⟨p, f, h⟩ | ⟨p, f, hpf, h⟩ | ⟨p, f, hpf, h⟩
  · exact (r95_gB_not_three_group h3 hE).elim
  · exact (r95_gB_not_J1 hJ hE).elim
  · exact absurd (r95_gB_L2 h hcyc hE hEW hNW) hW
  · exact absurd (r95_gB_L3 hpf h hcyc hE hEW hNW) hW
  · obtain ⟨hp7, hcov, hodd⟩ := r95_gB_U3 hpf h hcyc hE hEW hNW hW
    rw [hp7] at h
    exact ⟨f, (LieModel.admissible h).2.1, h, hcov, hodd⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
