module

public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.RankThree.PartOne.OutStructure

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem outPNice_PSL_ge_three_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n r m : ℕ} (hn : 3 ≤ n) (h : StatedClassicalModel X .PSL n r m)
    (hdiag : ¬ p ∣ Nat.gcd n (r ^ m - 1)) : OutPNice p X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have e' : X ≃* projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  refine OutPNice.of_mulEquiv e' (outPNice_projectiveSL hp hp2 hn ?_)
  rwa [hK]

theorem outPNice_PSU_odd {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {n r m : ℕ}
    (h : StatedClassicalModel X .PSU n r m) (hdiag : ¬ p ∣ Nat.gcd n (r ^ m + 1)) :
    OutPNice p X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData r m K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ r ^ m = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨eT⟩ := nonempty_primeFormP_mulEquiv hU (isPrimeFormGram_one (n := n))
  have e' : X ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact OutPNice.of_mulEquiv e' (outPNice_primeFormP hU hn3 hq hp hdiag)

end CFSG.RankThree.PartOne.OutStructure
