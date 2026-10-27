module

public import CFSG.Quasithin.Vol2.Ch10SecA312AR
public import CFSG.LieType.HighestRoot.CentTrialitySL2
public import CFSG.RankThree.ThinCatalog.FiveModels

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X]

theorem false_of_psl42_types {B : Subgroup X} (W : Subgroup ↥B)
    [W.Normal] (hW : IsPGroup 2 W) (hY : IsPSL 4 2 1 (↥B ⧸ W)) (h : A312Types B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥B ⧸ W) := isSimpleGroup_of_stated hY
  have hcard : Nat.card (↥B ⧸ W) = 20160 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hY).1 rfl]
    decide
  have hnp : ¬ IsPGroup 2 (↥B ⧸ W) := fun hp => by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [hcard] at hk
    have h5 : 5 ∣ 2 ^ k := hk ▸ (by norm_num : 5 ∣ 20160)
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5) (by norm_num)
  have heq := pCore_eq_of_isSimpleGroup W hW hs hnp
  let e₀ : ModO2 B ≃* ↥B ⧸ W := QuotientGroup.quotientMulEquivOfEq heq
  have hM : Nat.card (ModO2 B) = 20160 := by
    rw [Nat.card_congr e₀.toEquiv, hcard]
  rcases h with ⟨n, hn, F, _, _, hF, ⟨e⟩⟩ | he5 | he3 | ⟨n, hSz⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.LieType.HighestRoot.card_SL2, hF] at hM
    have h1 : 2 ^ n ≤ 20160 := Nat.le_of_dvd (by norm_num) ⟨_, hM.symm⟩
    have h2 : n < 15 := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
      have h15 : (2 : ℕ) ^ 15 = 32768 := by norm_num
      omega
    interval_cases n <;> norm_num at hM
  · obtain ⟨e⟩ := he5
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin] at hM
    norm_num [Nat.factorial] at hM
  · obtain ⟨e⟩ := he3
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field] at hM
    simp [Fin.prod_univ_three] at hM
  · exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hSz (by rw [hM]; norm_num)

theorem false_of_c14_rest {T B V : Subgroup X} (hB : B ∈ lFamily T)
    (hcase : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 4 2 1 Y) ∨
      IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
      IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))))
    (htypes : A312Types B) (hVB : V ≤ B) (hV : IsElemAbelian 2 V)
    (hBV : B ≤ Subgroup.normalizer (V : Set X)) (hcomm : ⁅V, B⁆ = V) (hV1 : V ≠ ⊥)
    (hc : pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X)) : False := by
  rcases hcase with ⟨W, hWn, hW, hY⟩ | ⟨W, hWn, hW, hY⟩ | ⟨W, hWn, hW, hY⟩
  · have hW2 : IsPGroup 2 W := fun w =>
      ⟨1, by rw [pow_one]; exact pow_eq_one_of_elemAbelian hW w⟩
    exact false_of_psl42_types W hW2 hY htypes
  · have : CFSG.IsExtraspecial 2 ↥W := hW.1
    have hW2 : IsPGroup 2 W := IsPGroup.of_card hW.2
    exact false_of_center_card_two W hW2 (CFSG.IsExtraspecial.center_order_p 2 ↥W)
      (isSimpleGroup_of_stated hY) (not_isPGroup_quotient hB W hW2) hVB hV hBV hcomm hV1 hc
  · have hW2 : IsPGroup 2 W := fun w =>
      ⟨1, by rw [pow_one]; exact pow_eq_one_of_elemAbelian hW w⟩
    exact false_of_hat_types W hW2 hY htypes

end CFSG.Quasithin.Vol2.Ch10.A312A
