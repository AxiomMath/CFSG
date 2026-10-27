module

public import CFSG.Milestones.ASVolI.F411.Cent
public import CFSG.Milestones.ASVolI.F411.aU5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem burnsideF411a_autCentSylow_hypU4 {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) : burnsideF411_AutCentSylow (hypPSU h 2 0) p :=
  fun α S hα => burnsideF411a_hyp_inner_of_fix_sylow h (by norm_num) (by norm_num)
    (burnsideF411a_hypU4_inner_of_fix h) α S hα

theorem burnsideF411a_autCentSylow_hypU5 {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) : burnsideF411_AutCentSylow (hypPSU h 2 1) p :=
  fun α S hα => burnsideF411a_hyp_inner_of_fix_sylow h (by norm_num) (by norm_num)
    (burnsideF411a_hypU5_inner_of_fix h) α S hα

theorem burnsideF411a_autCentSylow_U4 (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    burnsideF411_AutCentSylow (StatedProj (StatedSU 4 (p ^ f) K)) p := by
  have h := CFSG.LocalAnalysis.RankFourTheoremC.AutSU.unitaryFieldData_of_card hK
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  haveI : Finite (StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) :=
    Finite.of_equiv _ (hypPSUEquivStatedProj h hR (by norm_num)).toEquiv
  exact burnsideF411_autCentSylow_of_mulEquiv (hypPSUEquivStatedProj h hR (by norm_num))
    (burnsideF411a_autCentSylow_hypU4 h)

theorem burnsideF411a_autCentSylow_U5 (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    burnsideF411_AutCentSylow (StatedProj (StatedSU 5 (p ^ f) K)) p := by
  have h := CFSG.LocalAnalysis.RankFourTheoremC.AutSU.unitaryFieldData_of_card hK
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  haveI : Finite (StatedProj (StatedSU (2 * 2 + 1) (p ^ f) K)) :=
    Finite.of_equiv _ (hypPSUEquivStatedProj h hR (by norm_num)).toEquiv
  exact burnsideF411_autCentSylow_of_mulEquiv (hypPSUEquivStatedProj h hR (by norm_num))
    (burnsideF411a_autCentSylow_hypU5 h)

end CFSG.ASVolI
