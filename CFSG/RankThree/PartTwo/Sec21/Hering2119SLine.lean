module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SGrp
import CFSG.RankThree.PartTwo.Sec21.Item2119End9ProofTools
import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofWeak
public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofJ

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

structure LineAbs {G : Type} [Group G] (D M Y : Subgroup G) (e : G) : Prop where
  hMD : M ≤ D
  hM9 : Nat.card M = 9
  heN : e ∈ Subgroup.normalizer (D : Set G)
  he3 : e ^ 3 = 1
  hYN : Y ≤ Subgroup.normalizer (D : Set G)
  heY : e ∈ Y
  hεM : ∀ x ∈ D, e * x * e⁻¹ * x⁻¹ ∈ M
  hkerM : ∀ x ∈ D, e * x * e⁻¹ * x⁻¹ = 1 → x ∈ M
  hMc : ∀ m ∈ M, e * m * e⁻¹ = m
  hcent : ∀ w ∈ Y, ∃ h ∈ M, w * e * w⁻¹ = e * h
  hMY : ∀ w ∈ Y, ∀ m ∈ M, w * m * w⁻¹ ∈ M
  htrans : ∀ v ∈ M, ∀ w ∈ M, v ≠ 1 → w ≠ 1 → ∃ m ∈ Y, m * v * m⁻¹ = w
  hq : ∃ q ∈ Y, q ^ 3 = 1 ∧ ∃ m ∈ M, q * m * q⁻¹ ≠ m
  hbound : ∀ X : Subgroup G, IsPGroup 3 X → e ∈ X →
    (∀ x ∈ X, x * e * x⁻¹ * e⁻¹ ∈ Subgroup.centralizer (D : Set G)) →
      Nat.card X ≤ Nat.card (X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) * 81
  quat : ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ Y ∧ S ≤ Subgroup.centralizer ({e} : Set G) ∧
    ∃ a ∈ S, ∃ b ∈ S,
      (∀ m ∈ M, a * (a * m * a⁻¹) * a⁻¹ = m⁻¹) ∧ (∀ m ∈ M, b * (b * m * b⁻¹) * b⁻¹ = m⁻¹) ∧
      (∀ m ∈ M, a * (b * m * b⁻¹) * a⁻¹ = (b * (a * m * a⁻¹) * b⁻¹)⁻¹)

theorem lineAbs_of_config {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G}
    {L : Subgroup G} {d : G} {U₀ : Subgroup G} {a : G} {X : Subgroup G}
    (hE : Config2119End G A E U c L d U₀ a X) {Lf : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e))
    (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2))) {F : G → Subgroup G}
    (hF : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e))
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F) (hQX : IsExtra2127 (q2127Of A d F))
    (h28 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F))
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) {P : Subgroup G}
    (hL : Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P) :
    LineAbs (CFSG.Open.thompsonSubgroup P) (F e ⊓ Lf e)
      (y2128Of (Lf e) (F e) (q2127Of A d F)) e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := q2127Of A d F with hQdef
  set Y := y2128Of (Lf e) (F e) Q with hYdef
  set D := CFSG.Open.thompsonSubgroup P with hDdef
  obtain ⟨hDe, hD81, hYD, hFLD⟩ := hL
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hA3 : IsPGroup 3 A := Item2119End8Proof.isPGroup_of_pow hAe.2
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD3 : IsPGroup 3 D := Item2119End8Proof.isPGroup_of_pow hDe.2
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hAFQ : ∀ b ∈ A, b ∉ Subgroup.zpowers d → A ⊔ F b ≤ Q := fun b hb hbd =>
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      b ⟨hb, hbd⟩ le_rfl
  have hdc : ∀ q ∈ Q, q * d * q⁻¹ = d := by
    intro q hq
    have hQN : Q ≤ Subgroup.normalizer (A : Set G) := hQ.1.le
    have hmem : A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈ starOf A Q :=
      ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [hQ.2.2.1] at hmem
    have h := (mem_fixOn_iff.mp hmem.2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d)
    exact congrArg Subtype.val h
  have hFc : ∀ x ∈ F e, ∀ y ∈ F e, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((hF e he hed).1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF27 : Nat.card (F e) = 27 := (hF e he hed).2.1
  have heF : e ∈ F e := Item2119End8Proof.mem_F hAe hA27 h27 hQ hF he hed
  have hdF : d ∈ F e := Item2119End2Proof.mem_of_isQOf2127 hA27 hF27 hFc (hAFQ e he hed)
    (hQ.2.2.2.2 e he hed).1 hQ.2.1 hdA hdc
  have hdL : d ∈ Lf e := (hLf e he hed).2.2.2.2.1
  set M := F e ⊓ Lf e with hMdef
  have hdM : d ∈ M := ⟨hdF, hdL⟩
  have hdD : d ∈ D := hFLD hdM
  have hMD : M ≤ D := hFLD
  have hYN_F : Y ≤ Subgroup.normalizer (F e : Set G) := (h28 e he hed).1
  have hAY : A ≤ Y := le_sup_left.trans ((hAFQ e he hed).trans le_sup_right)
  have hQY : Q ≤ Y := le_sup_right
  have heY : e ∈ Y := hAY he
  have hrankd : ∀ b ∈ A, b ∉ Subgroup.zpowers d → ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card X ≤ 27 := fun b hb hbd X hX3 hXc hXC =>
    Item2119End8Proof.card_le_27_of_le_centralizer h27 hQ hA27 hb hbd hX3 hXc hXC
  have heD : e ∉ D := by
    intro h
    have h27' := hrankd e he hed D hD3 hDc
      (Item2119End8Proof.le_centralizer_of_mem hDc h)
    rw [hD81] at h27'
    norm_num at h27'
  have hzD : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hdD
  have hrankD : ∀ b ∈ A, b ∉ D → ∀ X : Subgroup G, IsPGroup 3 X →
      (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) → X ≤ Subgroup.centralizer ({b} : Set G) →
        Nat.card X ≤ 27 := fun b hb hbD => hrankd b hb (fun h => hbD (hzD h))
  obtain ⟨hM9, htr⟩ := Item2119End8Proof.facts_H (hF e he hed) (hLf e he hed) h26
    (h28 e he hed)
  have hMC : M ≤ D ⊓ Subgroup.centralizer ({e} : Set G) := le_inf hMD fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hFc m hm.1 e heF)
  have hC9 : Nat.card (D ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) ≤ 9 :=
    Item2119End8Proof.card_inf_centralizer_le_nine hA3 hDc hD3 hrankD he heD
  have hCM : D ⊓ Subgroup.centralizer ({e} : Set G) = M :=
    (Subgroup.eq_of_le_of_card_ge hMC (by rw [hM9]; exact hC9)).symm
  have hconj : ∀ w ∈ Y, ∃ h ∈ M, w * e * w⁻¹ = e * h := by
    intro w hw
    have hσ : (F e).normalizerMonoidHom ⟨w, hYN_F hw⟩ ∈ Sec4.autIn Y (F e) :=
      Sec4.mem_autIn_iff.mpr ⟨w, hYN_F hw, hw, rfl⟩
    have h1 := (mem_trivOnQuot_iff.mp ((h28 e he hed).2.1 hσ)) ⟨e, heF⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe] at h1
    have h2 : e⁻¹ * (w * e * w⁻¹) ∈ F e := by
      have hyb : w * e * w⁻¹ ∈ F e := (Subgroup.mem_normalizer_iff.mp (hYN_F hw) e).mp heF
      exact (F e).mul_mem ((F e).inv_mem heF) hyb
    exact ⟨e⁻¹ * (w * e * w⁻¹), ⟨h2, h1⟩, by group⟩
  have hMc : ∀ m ∈ M, e * m * e⁻¹ = m := fun m hm => by
    rw [hFc e heF m hm.1]
    group
  have hMY : ∀ w ∈ Y, ∀ m ∈ M, w * m * w⁻¹ ∈ M := by
    intro w hw m hm
    have hwF := hYN_F hw
    have h1 : w * m * w⁻¹ ∈ F e := (Subgroup.mem_normalizer_iff.mp hwF m).mp hm.1
    have hσ : (F e).normalizerMonoidHom ⟨w, hwF⟩ ∈ Sec4.autIn Y (F e) :=
      Sec4.mem_autIn_iff.mpr ⟨w, hwF, hw, rfl⟩
    have h2 := (mem_trivOnQuot_iff.mp ((h28 e he hed).2.1 hσ)) ⟨m, hm.1⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe] at h2
    refine ⟨h1, ?_⟩
    have : w * m * w⁻¹ = m * (m⁻¹ * (w * m * w⁻¹)) := by group
    rw [this]
    exact (Lf e).mul_mem hm.2 h2
  have hquad : ∀ x ∈ D, e * (e * x * e⁻¹ * x⁻¹) = (e * x * e⁻¹ * x⁻¹) * e :=
    Item2119End8Proof.quadratic_of_normal hDe hD81 (hAe.2 e he) heY hYD heD
      (fun X hX3 hXc hXC => hrankD e he heD X hX3 hXc hXC) hFLD
      (fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hFc m hm.1 e heF)) hM9
      (fun w hw => hconj w hw) (fun v hv w hw hv1 hw1 => by
        obtain ⟨m, hm, hmvw⟩ := htr v hv w hw hv1 hw1
        exact ⟨m, Subgroup.mem_sup_left hm, hmvw⟩)
  have hεM : ∀ x ∈ D, e * x * e⁻¹ * x⁻¹ ∈ M := by
    intro x hx
    rw [← hCM]
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr (hquad x hx).symm⟩
    have h1 : e * x * e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hYD heY) x).mp hx
    exact D.mul_mem h1 (D.inv_mem hx)
  have hkerM : ∀ x ∈ D, e * x * e⁻¹ * x⁻¹ = 1 → x ∈ M := by
    intro x hx h1
    rw [← hCM]
    refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc x * e = (e * x * e⁻¹ * x⁻¹)⁻¹ * (e * x) := by group
      _ = e * x := by rw [h1]; group
  have htransY : ∀ v ∈ M, ∀ w ∈ M, v ≠ 1 → w ≠ 1 → ∃ m ∈ Y, m * v * m⁻¹ = w :=
    fun v hv w hw hv1 hw1 => by
      obtain ⟨m, hm, hmvw⟩ := htr v hv w hw hv1 hw1
      exact ⟨m, Subgroup.mem_sup_left hm, hmvw⟩
  have hMQ : M ≤ Q :=
    inf_le_left.trans ((le_sup_right : F e ≤ A ⊔ F e).trans (hAFQ e he hed))
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
  obtain ⟨S, hS2, hSN, hquat⟩ := line_quat (hF e he hed) (hLf e he hed) h26 (h28 e he hed)
  have hSY : S ≤ Y := hSN.trans (le_sup_left : Lf e ⊓ Subgroup.normalizer (F e : Set G) ≤
    (Lf e ⊓ Subgroup.normalizer (F e : Set G)) ⊔ Q)
  have hSe : S ≤ Subgroup.centralizer ({e} : Set G) :=
    hSN.trans (inf_le_left.trans
      (Sec6.le_centralizer_of_mem_thetaComponentsAt (hLf e he hed).1))
  exact ⟨hMD, hM9, hYD heY, hAe.2 e he, hYD, heY, hεM, hkerM, hMc, hconj, hMY, htransY, hq,
    fun X hX3 heX hcomm => Item2119End9Proof.card_le_mul_81 h27 hQ he hed hX3 heX hcomm,
    S, hS2, hSY, hSe, hquat⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
