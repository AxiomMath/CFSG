module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrth
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRTransfer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB


theorem recipeOmegaPlus_torusGenTableB {l n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) (hl : 4 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F => Q R I F ∧ GGTorusGenTableB p R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 :=
    hpK.elim OrthTorus.ne_two_of_dvd_card_sub_one SpNS.ne_two_of_dvd_card_add_one
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggTorusGenTableB_of_torusGenR hp
    (fun _ h _ => h) hZ hcp (ggTorusGenR_of_mulEquiv (OrthTorus.rPlusEquiv K (by omega))
      (OrthTorusGen.ggTorusGenR_orthDerived hp hp2 hpK (TableBOrth.nondegenerate_qPlusForm _)
        (OrthTorus.exists_totallySingular_qPlusForm (by omega))))⟩

theorem recipeOmegaMinus_torusGenTableB {m n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) (hm : 3 ≤ m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧ GGTorusGenTableB p R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 :=
    hpK.elim OrthTorus.ne_two_of_dvd_card_sub_one SpNS.ne_two_of_dvd_card_add_one
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, ggTorusGenTableB_of_torusGenR hp
    (fun _ h _ => h) hZ hcp (ggTorusGenR_of_mulEquiv (OrthTorus.rMinusEquiv K m b c)
      (OrthTorusGen.ggTorusGenR_orthDerived hp hp2 hpK
        (TableBOrth.nondegenerate_qMinusForm m hbc) ((OrthTorus.charSum_qMinusForm m hbc).2 hm)))⟩

theorem largeEvenLabelAll_torusGenTableB_orth {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hl : 4 ≤ lab.rank)
    (hpn : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  intro Q hQ
  rcases htag with h | h <;> subst h <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_torusGenTableB hp hpn hl hQ
  · split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_torusGenTableB hp hpn (by omega) hQ

end CFSG.StandardType
