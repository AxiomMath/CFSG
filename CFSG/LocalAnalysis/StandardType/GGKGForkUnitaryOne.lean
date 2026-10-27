module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkURow
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem recipeUnitary_rootSL2
    {d n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hn2 : 2 ≤ n := by
    by_contra h
    have h1 : 2 ^ n ≤ 2 := by
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have h2 := Nat.le_of_dvd (Nat.succ_pos _) hpq
    omega
  have := (TableBU.unitaryFieldData_of_card hK hn).charP
  exact ⟨0, TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (by omega)),
    ggTorusRootSL2_psu_coprime hK hn2 hd hp hpq hpd⟩

theorem ggKGOneOn_unitary :
    GGKGOneOn fun p lab => GGUnitaryCoprimeLabel p lab := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hs with ⟨h, hpn, hpl⟩ | ⟨h, hl3, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl2 : 2 ≤ l := hlab.2.1
    exact recipeUnitary_rootSL2 hp hl.1 hpn hn (by omega) hpl hQ
  · dsimp only at h hl3 hpn
    subst h hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide), ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
    refine recipeUnitary_rootSL2 hp hl.1 hpn hn (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

end CFSG.StandardType
