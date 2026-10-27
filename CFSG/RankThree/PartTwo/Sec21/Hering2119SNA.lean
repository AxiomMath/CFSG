module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End9ProofShare
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SNAGroup
import CFSG.RankThree.PartTwo.Sec21.Item2119End9ProofTools
import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofWeak

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

theorem item2119EndSharedNA_holds : Item2119EndSharedNA := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e₀ he₀ he₀d e₁ he₁
    he₁d P₀ P₁ hP₀ hP₁ hJ y hy3 hyN hyC hyc hye
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := q2127Of A d F with hQdef
  set Y := y2128Of (Lf e₀) (F e₀) Q with hYdef
  set D := CFSG.Open.thompsonSubgroup P₀ with hDdef
  obtain ⟨hDe, hD81, hYD, hFLD⟩ := hL e₀ he₀ he₀d P₀ hP₀
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hA3 : IsPGroup 3 A := Item2119End8Proof.isPGroup_of_pow hAe.2
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD3 : IsPGroup 3 D := Item2119End8Proof.isPGroup_of_pow hDe.2
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hAFQ : ∀ b ∈ A, b ∉ Subgroup.zpowers d → A ⊔ F b ≤ Q := fun b hb hbd =>
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      b ⟨hb, hbd⟩ le_rfl
  have hAQ : A ≤ Q := le_sup_left.trans (hAFQ e₀ he₀ he₀d)
  have hdc : ∀ q ∈ Q, q * d * q⁻¹ = d := by
    intro q hq
    have hQN : Q ≤ Subgroup.normalizer (A : Set G) := hQ.1.le
    have hmem : A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈ starOf A Q :=
      ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [hQ.2.2.1] at hmem
    have h := (mem_fixOn_iff.mp hmem.2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d)
    exact congrArg Subtype.val h
  have hFc : ∀ x ∈ F e₀, ∀ y ∈ F e₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((hF e₀ he₀ he₀d).1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF27 : Nat.card (F e₀) = 27 := (hF e₀ he₀ he₀d).2.1
  have he₀F : e₀ ∈ F e₀ := Item2119End8Proof.mem_F hAe hA27 h27 hQ hF he₀ he₀d
  have hdF : d ∈ F e₀ := Item2119End2Proof.mem_of_isQOf2127 hA27 hF27 hFc (hAFQ e₀ he₀ he₀d)
    (hQ.2.2.2.2 e₀ he₀ he₀d).1 hQ.2.1 hdA hdc
  have hdL : d ∈ Lf e₀ := (hLf e₀ he₀ he₀d).2.2.2.2.1
  set M := F e₀ ⊓ Lf e₀ with hMdef
  have hdM : d ∈ M := ⟨hdF, hdL⟩
  have hdD : d ∈ D := hFLD hdM
  have hMD : M ≤ D := hFLD
  have hYN_F : Y ≤ Subgroup.normalizer (F e₀ : Set G) := (h28 e₀ he₀ he₀d).1
  have hAY : A ≤ Y := le_sup_left.trans ((hAFQ e₀ he₀ he₀d).trans le_sup_right)
  have hQY : Q ≤ Y := le_sup_right
  have he₀Y : e₀ ∈ Y := hAY he₀
  have hrankd : ∀ b ∈ A, b ∉ Subgroup.zpowers d → ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card X ≤ 27 := fun b hb hbd X hX3 hXc hXC =>
    Item2119End8Proof.card_le_27_of_le_centralizer h27 hQ hA27 hb hbd hX3 hXc hXC
  have he₀D : e₀ ∉ D := by
    intro h
    have h27' := hrankd e₀ he₀ he₀d D hD3 hDc
      (Item2119End8Proof.le_centralizer_of_mem hDc h)
    rw [hD81] at h27'
    norm_num at h27'
  have hzD : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hdD
  have hrankD : ∀ b ∈ A, b ∉ D → ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card X ≤ 27 := fun b hb hbD => hrankd b hb (fun h => hbD (hzD h))
  obtain ⟨hM9, htr⟩ := Item2119End8Proof.facts_H (hF e₀ he₀ he₀d) (hLf e₀ he₀ he₀d) h26
    (h28 e₀ he₀ he₀d)
  have hMC : M ≤ D ⊓ Subgroup.centralizer ({e₀} : Set G) := le_inf hMD fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hFc m hm.1 e₀ he₀F)
  have hC9 : Nat.card (D ⊓ Subgroup.centralizer ({e₀} : Set G) : Subgroup G) ≤ 9 :=
    Item2119End8Proof.card_inf_centralizer_le_nine hA3 hDc hD3 hrankD he₀ he₀D
  have hCM : D ⊓ Subgroup.centralizer ({e₀} : Set G) = M :=
    (Subgroup.eq_of_le_of_card_ge hMC (by rw [hM9]; exact hC9)).symm
  have hconj : ∀ w ∈ Y, ∃ h ∈ M, w * e₀ * w⁻¹ = e₀ * h := by
    intro w hw
    have hσ : (F e₀).normalizerMonoidHom ⟨w, hYN_F hw⟩ ∈ Sec4.autIn Y (F e₀) :=
      Sec4.mem_autIn_iff.mpr ⟨w, hYN_F hw, hw, rfl⟩
    have h1 := (mem_trivOnQuot_iff.mp ((h28 e₀ he₀ he₀d).2.1 hσ)) ⟨e₀, he₀F⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe] at h1
    have h2 : e₀⁻¹ * (w * e₀ * w⁻¹) ∈ F e₀ := by
      have hyb : w * e₀ * w⁻¹ ∈ F e₀ := (Subgroup.mem_normalizer_iff.mp (hYN_F hw) e₀).mp he₀F
      exact (F e₀).mul_mem ((F e₀).inv_mem he₀F) hyb
    exact ⟨e₀⁻¹ * (w * e₀ * w⁻¹), ⟨h2, h1⟩, by group⟩
  have hquad : ∀ x ∈ D, e₀ * (e₀ * x * e₀⁻¹ * x⁻¹) = (e₀ * x * e₀⁻¹ * x⁻¹) * e₀ :=
    Item2119End8Proof.quadratic_of_normal hDe hD81 (hAe.2 e₀ he₀) he₀Y hYD he₀D
      (fun X hX3 hXc hXC => hrankD e₀ he₀ he₀D X hX3 hXc hXC) hFLD
      (fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hFc m hm.1 e₀ he₀F)) hM9
      (fun w hw => hconj w hw) (fun v hv w hw hv1 hw1 => by
        obtain ⟨m, hm, hmvw⟩ := htr v hv w hw hv1 hw1
        exact ⟨m, Subgroup.mem_sup_left hm, hmvw⟩)
  have hεM : ∀ x ∈ D, e₀ * x * e₀⁻¹ * x⁻¹ ∈ M := by
    intro x hx
    rw [← hCM]
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr (hquad x hx).symm⟩
    have h1 : e₀ * x * e₀⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hYD he₀Y) x).mp hx
    exact D.mul_mem h1 (D.inv_mem hx)
  have hkerM : ∀ x ∈ D, e₀ * x * e₀⁻¹ * x⁻¹ = 1 → x ∈ M := by
    intro x hx h1
    rw [← hCM]
    refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc x * e₀ = (e₀ * x * e₀⁻¹ * x⁻¹)⁻¹ * (e₀ * x) := by group
      _ = e₀ * x := by rw [h1]; group
  have hMc : ∀ m ∈ M, e₀ * m * e₀⁻¹ = m := fun m hm => by
    rw [hFc e₀ he₀F m hm.1]
    group
  have hMY : ∀ w ∈ Y, ∀ m ∈ M, w * m * w⁻¹ ∈ M := by
    intro w hw m hm
    have hwF := hYN_F hw
    have h1 : w * m * w⁻¹ ∈ F e₀ := (Subgroup.mem_normalizer_iff.mp hwF m).mp hm.1
    have hσ : (F e₀).normalizerMonoidHom ⟨w, hwF⟩ ∈ Sec4.autIn Y (F e₀) :=
      Sec4.mem_autIn_iff.mpr ⟨w, hwF, hw, rfl⟩
    have h2 := (mem_trivOnQuot_iff.mp ((h28 e₀ he₀ he₀d).2.1 hσ)) ⟨m, hm.1⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe] at h2
    refine ⟨h1, ?_⟩
    have : w * m * w⁻¹ = m * (m⁻¹ * (w * m * w⁻¹)) := by group
    rw [this]
    exact (Lf e₀).mul_mem hm.2 h2
  have htransY : ∀ v ∈ M, ∀ w ∈ M, v ≠ 1 → w ≠ 1 → ∃ m ∈ Y, m * v * m⁻¹ = w :=
    fun v hv w hw hv1 hw1 => by
      obtain ⟨m, hm, hmvw⟩ := htr v hv w hw hv1 hw1
      exact ⟨m, Subgroup.mem_sup_left hm, hmvw⟩
  have hMQ : M ≤ Q :=
    inf_le_left.trans ((le_sup_right : F e₀ ≤ A ⊔ F e₀).trans (hAFQ e₀ he₀ he₀d))
  have hq : ∃ q ∈ Y, q ^ 3 = 1 ∧ ∃ m ∈ M, q * m * q⁻¹ ≠ m := by
    by_contra hall
    push Not at hall
    have hle : M.subgroupOf Q ≤ Subgroup.center Q := by
      intro m hm
      rw [Subgroup.mem_center_iff]
      intro g
      have hg3 : (g : G) ^ 3 = 1 := by
        have := Monoid.pow_exponent_eq_one g
        rw [hQX.2.2] at this
        simpa using congrArg Subtype.val this
      have h := hall g (hQY g.2) hg3 m hm
      apply Subtype.ext
      change (g : G) * m = m * g
      calc (g : G) * m = (g * m * (g : G)⁻¹) * g := by group
        _ = m * g := by rw [h]
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMQ).toEquiv, hM9, hQX.1.2.2.2] at h1
    omega
  exact Hering2119S.na_group ⟨hDc, fun x hx => hDe.2 x hx⟩ hD81 hMD hM9 (hYD he₀Y)
    (hAe.2 e₀ he₀) hYD he₀Y hεM hkerM hMc hconj hMY htransY hq hyN hyC hyc hdM hd1 hye
    (fun X hX3 heX hcomm => Item2119End9Proof.card_le_mul_81 h27 hQ he₀ he₀d hX3 heX hcomm)

end CFSG.RankThree.PartTwo.Sec21
