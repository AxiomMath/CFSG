module

public import CFSG.LocalAnalysis.StandardType.GGRealSgnDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthNsSgnLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
import CFSG.LocalAnalysis.StandardType.GGRealSgnTransfer
import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaSgn
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open CFSG.RankThree.Classical2 (orthDerived)

theorem ggTorusSgnComponents_rPlus
    {K : Type} [Field K] [Finite K] {n l p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1) (hl4 : 4 ≤ l) :
    GGTorusSgnComponents p 0 (OrthRest.RPlus K l) (LargeEvenInnSet _) := by
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  refine ggTorusSgnComponents_of_sgnComponentDatum hp (fun φ hφ _ => hφ) hZ hcp ?_
  let α := OrthTorus.rPlusEquiv K (by omega : 1 ≤ l)
  have : Finite ↥(orthDerived (TableBOrth.qPlusForm K l)) := Finite.of_equiv _ α.toEquiv
  refine ggKGSgnComponentDatum_of_mulEquiv α (RealKGOmega.ggKGSgnComponentDatum_orthDerived
    (TableBOrth.nondegenerate_qPlusForm (K := K) l) hp hp2 hpK (ℓ := l) ?_ hl4)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem ggTorusSgnComponents_rMinus
    {K : Type} [Field K] [Finite K] {n m p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1) (hm : 3 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusSgnComponents p 0 (OrthRest.RMinus K m b c) (LargeEvenInnSet _) := by
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
  refine ggTorusSgnComponents_of_sgnComponentDatum hp (fun φ hφ _ => hφ) hZ hcp ?_
  let α := OrthTorus.rMinusEquiv K m b c
  have : Finite ↥(orthDerived (TableBOrth.qMinusForm K m b c)) := Finite.of_equiv _ α.toEquiv
  refine ggKGSgnComponentDatum_of_mulEquiv α (RealKGOmega.ggKGSgnComponentDatum_orthDerived
    (TableBOrth.nondegenerate_qMinusForm m hbc) hp hp2 hpK (ℓ := m + 1) ?_ (by omega))
  simp only [Module.finrank_fintype_fun_eq_card, LargeEvenMinusIdx, Fintype.card_sum,
    Fintype.card_fin]
  ring

theorem ggRealSgnOn_orthNs :
    GGRealSgnOn GGOrthNsSgnLabel := by
  intro p lab hp hlab hs Q hQ
  obtain ⟨hp2, htag | htag, hpn, hl4⟩ := hs
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpn hl4
    subst htag
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      exact ⟨K, inferInstance, inferInstance, hK, hQ',
        ggTorusSgnComponents_rPlus hp hp2 hK hpn hl4⟩
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpn hl4
    subst htag
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
      exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ',
        ggTorusSgnComponents_rMinus hp hp2 hK hpn (by omega : 3 ≤ l - 1) hbc⟩

end CFSG.StandardType

end
