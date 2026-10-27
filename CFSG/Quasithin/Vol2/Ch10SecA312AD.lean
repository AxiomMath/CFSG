module

public import CFSG.Quasithin.Vol2.Ch10SecA312AC
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.LieType.SteinbergBRSemidirectSLEven
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Quasithin.Vol2.Ch10SecA312AB

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X]

theorem isSimpleGroup_of_stated {Y : Type} [Group Y] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y t n p f) : IsSimpleGroup Y :=
  (CFSG.LieType.Simplicity.fam_classical_converse Y
    ((CFSG.Milestones.fam_classical_model_membership_alltags Y).2 ⟨t, n, p, f, h⟩)).2.2

theorem isSimpleGroup_alt {Y : Type} [Group Y] {n : ℕ} (hn : n = 5 ∨ n = 6) (h : IsAlt n Y) :
    IsSimpleGroup Y := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rcases hn with rfl | rfl <;> simp)
  exact e.isSimpleGroup

theorem isQuasisimple_of_isSL2 {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : IsSL2 p Y) : CFSG.IsQuasisimple Y := by
  obtain ⟨e⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have hq := CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le (K := ZMod p)
    (by rw [Nat.card_eq_fintype_card, ZMod.card]; omega)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq

theorem not_isPGroup_quotient {T B : Subgroup X} (hB : B ∈ lFamily T) (W : Subgroup ↥B)
    [W.Normal] (hW : IsPGroup 2 W) : ¬ IsPGroup 2 (↥B ⧸ W) := by
  intro hQ
  have hBc : quasithinIsCComponent B (B ⊔ T) := hB
  apply not_isPGroup_of_perfect hBc.2.1 hBc.1
  intro b
  obtain ⟨k, hk⟩ := hQ (QuotientGroup.mk b)
  have hmem : b ^ 2 ^ k ∈ W := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hk]
  obtain ⟨j, hj⟩ := hW ⟨_, hmem⟩
  refine ⟨k + j, ?_⟩
  have h1 : (b ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  rw [pow_add, pow_mul, h1]

theorem pow_eq_one_of_elemAbelian {Y : Type} [Group Y] {p n : ℕ} (h : IsElemAbelianOfRank p n Y)
    (y : Y) : y ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext i
  simp

omit [Finite X] in
theorem center_bot_or_top_of_types {B : Subgroup X} (h : A312Types B) :
    Subgroup.center (ModO2 B) = ⊥ ∨ Subgroup.center (ModO2 B) = ⊤ := by
  rcases h with ⟨n, hn, F, _, _, hF, ⟨e⟩⟩ | he5 | he3 | ⟨n, hSz⟩
  · left
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hZ := CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (F := F) (m := 2)
      (by norm_num) (Or.inl rfl)
    rw [← Subgroup.map_center_eq e.symm, hZ, Subgroup.map_bot]
  · have : IsSimpleGroup (ModO2 B) := isSimpleGroup_alt (Or.inl rfl) he5
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ModO2 B))
  · left
    obtain ⟨e⟩ := he3
    have hZ := CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (F := ZMod 2) (m := 3)
      (by norm_num) (Or.inr (by rw [Nat.card_eq_fintype_card, ZMod.card]))
    rw [← Subgroup.map_center_eq e.symm, hZ, Subgroup.map_bot]
  · have : IsSimpleGroup (ModO2 B) := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 n hSz).2
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ModO2 B))

theorem false_of_hat_types {B : Subgroup X} (W : Subgroup ↥B) [W.Normal] (hW : IsPGroup 2 W)
    (hH : IsHat (↥B ⧸ W) (alternatingGroup (Fin 6))) (h : A312Types B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hZ3, ⟨eA⟩⟩ := hH
  have hWle : W ≤ CFSG.pCore 2 ↥B :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup inferInstance hW
  have hle : CFSG.pCore 2 ↥B ≤ W := by
    set N := (CFSG.pCore 2 ↥B).map (QuotientGroup.mk' W) with hN
    have hn : N.Normal :=
      (inferInstance : (CFSG.pCore 2 ↥B).Normal).map _ (QuotientGroup.mk'_surjective W)
    have hNp : IsPGroup 2 N := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).map _
    have hbot : N = ⊥ := by
      rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hn with h | h
      · exfalso
        apply not_isPGroup_two_of_quasisimple hq
        rw [h] at hNp
        exact hNp.of_equiv Subgroup.topEquiv
      · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hNp
        have hdvd : Nat.card N ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le h
        rw [hk] at hdvd
        have hk0 : k = 0 := by
          by_contra hk0
          have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans hdvd
          omega
        rw [hk0, pow_zero] at hk
        exact Subgroup.eq_bot_of_card_eq N hk
    intro x hx
    have : (QuotientGroup.mk' W x) ∈ N := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  have heq : CFSG.pCore 2 ↥B = W := le_antisymm hle hWle
  let e₀ : ModO2 B ≃* ↥B ⧸ W := QuotientGroup.quotientMulEquivOfEq heq
  have hZB : Nat.card (Subgroup.center (ModO2 B)) = 3 := by
    rw [← Subgroup.map_center_eq e₀.symm, Subgroup.card_map_of_injective e₀.symm.injective, hZ3]
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hcardY : Nat.card (↥B ⧸ W) = 1080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (↥B ⧸ W)),
      Nat.card_congr eA.toEquiv, hcardA, hZ3]
  rcases center_bot_or_top_of_types h with h0 | h0
  · rw [h0, Subgroup.card_bot] at hZB
    omega
  · rw [h0, Subgroup.card_top, Nat.card_congr e₀.toEquiv, hcardY] at hZB
    omega

theorem false_of_list {T B V : Subgroup X} (hB : B ∈ lFamily T)
    (hcase : A312C6 B ⊤ ∨ A312C7 B ⊤ ∨ A312C8 B ⊤ ∨ A312C9 B ⊤ ∨ A312C10 B ⊤ ∨ A312C11 B ⊤ ∨
      A312C15 B ⊤ ∨ A312C16 B ⊤ ∨ A312C19 B ⊤) (htypes : A312Types B) (hVB : V ≤ B)
    (hV : IsElemAbelian 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set X)) (hcomm : ⁅V, B⁆ = V)
    (hV1 : V ≠ ⊥) (hc : pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X)) : False := by
  have hsimp : IsSimpleGroup ↥B → False := fun hs =>
    false_of_simple hB hs hVB hV hBV hcomm hV1 hc
  have hquas : CFSG.IsQuasisimple ↥B → False := fun hq =>
    false_of_quasisimple hq hVB hV hBV hcomm hV1
  rcases hcase with ⟨h5 | h32, -⟩ | (⟨h6, -⟩ | ⟨hH, -⟩) | (⟨p, -, -, h2, -⟩ | ⟨h5, -⟩) |
      (⟨-, p, hp, hp3, hSL, -⟩ | ⟨h6, -⟩ | ⟨hH, -⟩) | ⟨p, hp, hp3, ⟨W, hWn, hW, hY⟩, -⟩ |
      ⟨h6, -⟩ | ⟨h5, -⟩ | ⟨⟨W, hWn, hW, hY⟩, -⟩ | ⟨⟨W, hWn, hW, hY⟩ | ⟨W, hWn, hW, hY⟩, -⟩
  · exact hsimp (isSimpleGroup_alt (Or.inl rfl) h5)
  · exact hsimp (isSimpleGroup_of_stated h32)
  · exact hsimp (isSimpleGroup_alt (Or.inr rfl) h6)
  · exact hquas hH.1
  · exact hsimp (isSimpleGroup_of_stated h2)
  · exact hsimp (isSimpleGroup_alt (Or.inl rfl) h5)
  · exact hquas (isQuasisimple_of_isSL2 hp hp3 hSL)
  · exact hsimp (isSimpleGroup_alt (Or.inr rfl) h6)
  · exact hquas hH.1
  · exact false_of_quasisimple_quotient W hp (by omega)
      (fun w hw => congrArg Subtype.val (pow_eq_one_of_elemAbelian hW ⟨w, hw⟩))
      (isQuasisimple_of_isSL2 hp hp3 hY) hVB hV hBV hcomm hV1
  · exact hsimp (isSimpleGroup_alt (Or.inr rfl) h6)
  · exact hsimp (isSimpleGroup_alt (Or.inl rfl) h5)
  · have : CFSG.IsExtraspecial 2 ↥W := hW.1
    have hW2 : IsPGroup 2 W := IsPGroup.of_card hW.2
    exact false_of_center_card_two W hW2 (CFSG.IsExtraspecial.center_order_p 2 ↥W)
      (isSimpleGroup_alt (Or.inl rfl) hY) (not_isPGroup_quotient hB W hW2) hVB hV hBV hcomm hV1
      hc
  · have : CFSG.IsExtraspecial 2 ↥W := hW.1
    have hW2 : IsPGroup 2 W := IsPGroup.of_card hW.2
    exact false_of_center_card_two W hW2 (CFSG.IsExtraspecial.center_order_p 2 ↥W)
      (isSimpleGroup_of_stated hY) (not_isPGroup_quotient hB W hW2) hVB hV hBV hcomm hV1 hc
  · have hW2 : IsPGroup 2 W := fun w =>
      ⟨1, by rw [pow_one]; exact pow_eq_one_of_elemAbelian hW w⟩
    exact false_of_hat_types W hW2 hY htypes

end CFSG.Quasithin.Vol2.Ch10.A312A
