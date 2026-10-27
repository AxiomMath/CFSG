module

public import CFSG.RankThree.PartOne.N143.Item613IdxDefs
public import CFSG.RankThree.PartOne.SPOR.I613Item3
public import CFSG.RankThree.PartOne.SPOR.I613Core
public import CFSG.RankThree.PartOne.CTP.SeitzExc

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.RankThree.PartOne.SPOR

theorem item613Idx_item3 :
    Item613IdxFor Census3.ThmThreeItem3 := by
  intro X _ _ _ hiso p hp hp7 E hE hcard _
  exfalso
  have := hE
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (IsElementaryAbelian.isPGroup p E)
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hk ▸ hcard)
  have hdvdE : p ^ 2 ∣ Nat.card E := hk ▸ pow_dvd_pow p hk2
  have hX := card_smallRee_model (f := 3) (ℓ := 3) rfl (CTP.reeTitsModel_reeG2 1 hiso)
  have hdvd : p ^ 2 ∣ 3 ^ 0 * ((3 ^ 3) ^ 3 * (3 ^ 3 - 1) * ((3 ^ 3) ^ 3 + 1)) := by
    rw [pow_zero, one_mul, ← hX]
    exact hdvdE.trans (Subgroup.card_subgroup_dvd_card E)
  exact CTP.not_sq_dvd_smallRee_aut hp (by omega) hdvd

theorem item613Idx_item6 :
    Item613IdxFor Census3.ThmThreeItem6 := by
  intro X _ _ hs h6 p hp hp7 E hE hcard hex
  obtain ⟨S, hS1, hS2, hEN, hSE⟩ := hex
  exfalso
  have := hs
  have := hE
  exact item613Item6_core h6 hp hp7 hcard hS1 hS2 hEN hSE

end CFSG.RankThree.PartOne.N143
