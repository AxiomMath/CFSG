module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End9ProofShare
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SSyl
import CFSG.RankThree.PartTwo.Sec21.Item2119End9ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item2119EndStep2Pair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)) →
        ∀ F : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d →
            CFSG.ABGLocalTools.IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G))) →
          IsQOf2127 A d F → IsExtra2127 (q2127Of A d F) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F)) →
          (∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ P : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P (y2128Of (Lf e) (F e) (q2127Of A d F)) →
            Concl2129Loc (Lf e) (F e) (y2128Of (Lf e) (F e) (q2127Of A d F)) P) →
          ∀ e₀ ∈ A, e₀ ∉ Subgroup.zpowers d → ∀ e₁ ∈ A,
            e₁ ∉ Subgroup.zpowers e₀ ⊔ Subgroup.zpowers d → ∀ P₀ P₁ : Subgroup G,
            CFSG.ABGLocalTools.IsSylowOf 3 P₀ (y2128Of (Lf e₀) (F e₀) (q2127Of A d F)) →
            CFSG.ABGLocalTools.IsSylowOf 3 P₁ (y2128Of (Lf e₁) (F e₁) (q2127Of A d F)) →
            CFSG.Open.thompsonSubgroup P₀ = CFSG.Open.thompsonSubgroup P₁ →
            ∃ (T : Subgroup G) (a₁ b₁ c₁ t : G), IsPGroup 2 T ∧
              T ≤ Subgroup.normalizer (CFSG.Open.thompsonSubgroup P₀ : Set G) ∧
              a₁ ∈ T ∧ b₁ ∈ T ∧ c₁ ∈ T ∧ t ∈ T ∧ e₀ * t = t * e₀ ∧
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀, t * x * t⁻¹ = x⁻¹) ∧
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀, a₁ * (a₁ * x * a₁⁻¹) * a₁⁻¹ = x⁻¹) ∧
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀, b₁ * (b₁ * x * b₁⁻¹) * b₁⁻¹ = x⁻¹) ∧
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀, c₁ * (c₁ * x * c₁⁻¹) * c₁⁻¹ = x⁻¹) ∧
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀,
                a₁ * (b₁ * x * b₁⁻¹) * a₁⁻¹ = (b₁ * (a₁ * x * a₁⁻¹) * b₁⁻¹)⁻¹) ∧
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀,
                a₁ * (c₁ * x * c₁⁻¹) * a₁⁻¹ = c₁ * (a₁ * x * a₁⁻¹) * c₁⁻¹) ∧
              (∀ x ∈ CFSG.Open.thompsonSubgroup P₀,
                b₁ * (c₁ * x * c₁⁻¹) * b₁⁻¹ = c₁ * (b₁ * x * b₁⁻¹) * c₁⁻¹)

theorem item2119EndSharedA_of_step2 (h2 : Item2119EndStep2Pair) : Item2119EndSharedA := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e₀ he₀ he₀d e₁ he₁
    he₁d P₀ P₁ hP₀ hP₁ hJ y hy3 hyC hyD
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, a₁, b₁, c₁, t, hT2, hTN, haT, hbT, hcT, htT, het, ht, ha, hb, hc, hab, hac, hbc⟩ :=
    h2 G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e₀ he₀ he₀d e₁ he₁
      he₁d P₀ P₁ hP₀ hP₁ hJ
  obtain ⟨hDe, hD81, hYD, hFLD⟩ := hL e₀ he₀ he₀d P₀ hP₀
  set Q := q2127Of A d F with hQdef
  set Y := y2128Of (Lf e₀) (F e₀) Q with hYdef
  set D := CFSG.Open.thompsonSubgroup P₀ with hDdef
  have hloc : CFSG.Assembly.RankThreeEven.localRank 3 G = 3 :=
    hE.cfg.pair.standing.localRank_three
  have hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD : Hering2119S.IsElem3 D := ⟨hDc, fun x hx => hDe.2 x hx⟩
  have hD3 : IsPGroup 3 D := Item2119End8Proof.isPGroup_of_pow hDe.2
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hAFQ : ∀ b ∈ A, b ∉ Subgroup.zpowers d → A ⊔ F b ≤ Q := fun b hb hbd =>
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      b ⟨hb, hbd⟩ le_rfl
  have hAY : A ≤ Y := le_sup_left.trans ((hAFQ e₀ he₀ he₀d).trans le_sup_right)
  have he₀Y : e₀ ∈ Y := hAY he₀
  have he₀N : e₀ ∈ Subgroup.normalizer (D : Set G) := hYD he₀Y
  have he₀3 : e₀ ^ 3 = 1 := hAe.2 e₀ he₀
  have hrankd : ∀ X : Subgroup G, IsPGroup 3 X → (∀ x ∈ X, ∀ y ∈ X, x * y = y * x) →
      X ≤ Subgroup.centralizer ({e₀} : Set G) → Nat.card X ≤ 27 := fun X hX3 hXc hXC =>
    Item2119End8Proof.card_le_27_of_le_centralizer h27 hQ hA27 he₀ he₀d hX3 hXc hXC
  have he₀C : e₀ ∉ Subgroup.centralizer (D : Set G) := by
    intro h
    have h27' := hrankd D hD3 hDc (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h x hx))
    rw [hD81] at h27'
    norm_num at h27'
  have hCt : ∀ z ∈ Subgroup.centralizer (D : Set G), t * z * t⁻¹ = z → z ^ 3 = 1 → z = 1 := by
    intro z hzD hzt hz3
    refine Item2119End9Proof.eq_one_of_mem_centralizer_of_inv (e := e₀) (t := t)
      (Hering2119S.isPGroup_zpowers_of_pow_three' he₀3) he₀N het ht ?_ hzD ?_ hz3
    · intro R hR3 hRe hRD
      exact (Item2119End9Proof.le_of_le_centralizer_of_le hE hLf h26 hF h27 hQ h28 he₀ he₀d hDc
        hFLD he₀C hR3 hRe hRD).trans hFLD
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * t = (t * z * t⁻¹) * t := by rw [hzt]
        _ = t * z := by group
  exact Hering2119S.false_of_triple hloc hD hD81 hT2 hTN haT hbT hcT htT ht ha hb hc hab hac hbc
    hCt hyC hyD hy3

end CFSG.RankThree.PartTwo.Sec21
