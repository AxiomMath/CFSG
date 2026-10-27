module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkURow
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryDvdRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggKGUd_rank {p d : ℕ} (hpd : p ∣ d) : ggUnitaryTorusRank p d = d - 3 := by
  simp [ggUnitaryTorusRank, hpd]

private theorem recipeUnitary_rootSL2_dvd
    {d n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (hn : 2 ≤ n) (hd0 : 0 < d) (hpd : p ∣ d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have hd : 5 ≤ d := le_trans hp5 (Nat.le_of_dvd hd0 hpd)
  refine ⟨K, inferInstance, inferInstance, hK, hQ, d - 3, ?_, ?_⟩
  · have hdq : (d, 2 ^ n) ≠ (3, 2) := by
      intro heq
      have := congrArg Prod.fst heq
      simp only at this
      omega
    rw [← ggKGUd_rank hpd]
    exact ggTorusLift_unitary hK (by omega) (by omega) hdq hp hpq
  · have hp2 : p ≠ 2 := by omega
    have hle : d / p + 2 ≤ max (d - 3) 3 := by
      have hdp : d / p ≤ d / 5 := Nat.div_le_div_left hp5 (by norm_num)
      rcases le_total (d - 3) 3 with h | h
      · rw [max_eq_right h]
        omega
      · rw [max_eq_left h]
        omega
    exact ggTorusRootSL2_psu_dvd hK hn hd hp hp2 hle hpq hpd

private theorem recipeUnitary_lattice_dvd
    {d n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (hn : 2 ≤ n) (hd0 : 0 < d) (hpd : p ∣ d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have hd : 5 ≤ d := le_trans hp5 (Nat.le_of_dvd hd0 hpd)
  refine ⟨K, inferInstance, inferInstance, hK, hQ, d - 3, ?_, ?_⟩
  · have hdq : (d, 2 ^ n) ≠ (3, 2) := by
      intro heq
      have := congrArg Prod.fst heq
      simp only at this
      omega
    rw [← ggKGUd_rank hpd]
    exact ggTorusLift_unitary hK (by omega) (by omega) hdq hp hpq
  · exact ggTorusLattice_psu_dvd hK hn hd hp hp5 hpq hpd

theorem ggKGOneOn_unitaryDvd :
    GGKGOneOn fun p lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn, hpl⟩ := hs
  dsimp only at htag hpn hpl
  subst htag
  have hn : 2 ≤ n := by
    by_contra h
    have hn1 : n ≤ 1 := by omega
    have hn1' : 2 ^ n ≤ 2 := by
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
        _ = 2 := by norm_num
    have h2 := Nat.le_of_dvd (Nat.succ_pos _) hpn
    have := hl.1
    omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeUnitary_rootSL2_dvd hp hl.1 hpn hn (by omega) hpl hQ

theorem ggKGTwoOn_unitaryDvd :
    GGKGTwoOn fun p lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn, hpl⟩ := hs
  dsimp only at htag hpn hpl
  subst htag
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeUnitary_lattice_dvd hp hl.1 hpn hl.2.1 (by omega) hpl hQ

end CFSG.StandardType
