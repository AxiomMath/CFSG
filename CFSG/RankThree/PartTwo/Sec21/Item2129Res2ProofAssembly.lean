module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofJ
public import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofCore
import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofNormal
import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofWeak
public import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Item2129SO : Prop :=
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
          ∀ e ∈ A, e ∉ Subgroup.zpowers d →
            ∀ x ∈ y2128Of (Lf e) (F e) (q2127Of A d F) ⊓
                Subgroup.centralizer ((F e ⊓ Lf e : Subgroup G) : Set G),
              ∀ o ∈ y2128Of (Lf e) (F e) (q2127Of A d F) ⊓
                  Subgroup.centralizer ((F e : Subgroup G) : Set G),
                (∃ n : ℕ, x ^ 3 ^ n = 1) → Nat.Coprime (orderOf o) 3 → x * o = o * x

namespace Item2129Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_of {A L Le Fb Q : Subgroup G} {c d b : G} (hF : IsFOf2127 A Le Fb)
    (hL : IsLOf2125 L c d b Le) (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)))
    (h28 : Concl2128 Le Fb Q) :
    ∃ t ∈ Le ⊓ Subgroup.normalizer (Fb : Set G), ∀ h ∈ Fb ⊓ Le, t * h * t⁻¹ = h⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eL34⟩ := h26
  obtain ⟨hFe, hF27, -, -, ⟨eQ8⟩⟩ := hF
  obtain ⟨-, -, -, ⟨eLe⟩, -, -⟩ := hL
  obtain ⟨-, hYtriv, -⟩ := h28
  have hVc : ∀ x y : Fb, x * y = y * x := fun x y => hFe.1.is_comm.comm x y
  have hV3 : ∀ x : Fb, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hFe.2 x x.2)
  have hT : Le.subgroupOf Fb ≠ ⊤ := by
    intro h
    have hle : Fb ≤ Le := by
      intro x hx
      have hx' : (⟨x, hx⟩ : Fb) ∈ Le.subgroupOf Fb := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'
    apply Item2119End3Proof.not_dvd_card_of_lBar eLe eL34
    rw [← hF27]
    exact Subgroup.card_dvd_of_le hle
  have hQ8T : Sec4.autIn Le Fb ≤ Item2119End3Proof.fixQuot (Le.subgroupOf Fb) := by
    rw [← Item2119End3Proof.trivOnQuot_eq_fixQuot]
    refine le_trans (Item2119End3Proof.autIn_le_of_le ?_) hYtriv
    exact (le_sup_left : Le ⊓ Subgroup.normalizer (Fb : Set G) ≤
      (Le ⊓ Subgroup.normalizer (Fb : Set G)) ⊔ Q)
  have hT9 := Item2119End3Proof.card_eq_nine hV3 hF27 hT eQ8 hQ8T
  obtain ⟨z, hz, g, hg, hz1, hzz, hgg, -⟩ := Item2119End3Proof.quaternion_facts eQ8
  obtain ⟨t, htN, htL, htz⟩ := Sec4.mem_autIn_iff.mp hz
  refine ⟨t, ⟨htL, htN⟩, fun h hh => ?_⟩
  have h1 := Item2119End3Proof.apply_eq_inv_of_mem hVc hV3 hT9 (hQ8T hz) (hQ8T hg) hz1 hzz hgg
    (v := ⟨h, hh.1⟩) (Subgroup.mem_subgroupOf.mpr hh.2)
  rw [← htz] at h1
  have h2 := congrArg Subtype.val h1
  rwa [Sec4.normalizerMonoidHom_apply_coe] at h2

theorem loc2129_of {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) {Lf F : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e))
    (h26 : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 2)))
    (hF : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsFOf2127 A (Lf e) (F e))
    (h27 : ∀ e ∈ A, e ∉ Subgroup.zpowers d →
      IsSylowOf 3 (A ⊔ F e) (Subgroup.centralizer ({e} : Set G)))
    (hQ : IsQOf2127 A d F) (hQX : IsExtra2127 (q2127Of A d F))
    (h28 : ∀ e ∈ A, e ∉ Subgroup.zpowers d → Concl2128 (Lf e) (F e) (q2127Of A d F))
    {e : G} (he : e ∈ A) (hed : e ∉ Subgroup.zpowers d) :
    Loc2129 (F e) (F e ⊓ Lf e) (q2127Of A d F) (y2128Of (Lf e) (F e) (q2127Of A d F)) e d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hAFQ : A ⊔ F e ≤ q2127Of A d F :=
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      e ⟨he, hed⟩ le_rfl
  have hdA : d ∈ A := hE.mem_d.1
  have hQN : q2127Of A d F ≤ Subgroup.normalizer (A : Set G) := hQ.1.le
  have hstar : ∀ q (hq : q ∈ q2127Of A d F), A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈
      trivOnQuot A (Subgroup.zpowers d) ⊓ fixOn A (Subgroup.zpowers d) := by
    intro q hq
    have hmem : A.normalizerMonoidHom ⟨q, hQN hq⟩ ∈ starOf A (q2127Of A d F) :=
      ⟨⟨q, hQN hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rwa [hQ.2.2.1] at hmem
  have hdc : ∀ q ∈ q2127Of A d F, q * d * q⁻¹ = d := by
    intro q hq
    have h := (mem_fixOn_iff.mp (hstar q hq).2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d)
    exact congrArg Subtype.val h
  have hec : ∀ q ∈ q2127Of A d F, e⁻¹ * (q * e * q⁻¹) ∈ Subgroup.zpowers d := by
    intro q hq
    have h := (mem_trivOnQuot_iff.mp (hstar q hq).1) ⟨e, he⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe] at h
    exact h
  obtain ⟨hFe, hF27, -, -, -⟩ := hF e he hed
  have hFc : ∀ x ∈ F e, ∀ y ∈ F e, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hdF : d ∈ F e := Item2119End2Proof.mem_of_isQOf2127 hA27 hF27 hFc hAFQ
    (hQ.2.2.2.2 e he hed).1 hQ.2.1 hdA hdc
  have hLe : Lf e ∈ thetaComponentsAt 3 e := (hLf e he hed).1
  have hLC : Lf e ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLe
  have heL : e ∉ Lf e := by
    obtain ⟨eLe⟩ := (hLf e he hed).2.2.2.1
    obtain ⟨eL⟩ := h26
    have hZ : Subgroup.center (lBar (Lf e)) = ⊥ :=
      Item2119End3Proof.center_eq_bot_of_mulEquiv' (eLe.trans eL)
        (Item21Early2Proof.center_projSL_three_eq_bot (by norm_num) (by decide))
    have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
    exact Item2119End3Proof.not_mem_of_mem_thetaComponentsAt hLe hZ (hAe.2 e he) he1
  obtain ⟨hH9, htr⟩ := Item2119End8Proof.facts_H (hF e he hed) (hLf e he hed) h26 (h28 e he hed)
  obtain ⟨hYN, hYtriv, -⟩ := h28 e he hed
  refine
    { comm_F := hFc
      pow_F := hFe.2
      card_F := hF27
      le_H := inf_le_left
      card_H := hH9
      mem_e := Item2119End8Proof.mem_F hAe hA27 h27 hQ hF he hed
      not_mem_e := fun h => heL h.2
      mem_d := ⟨hdF, (hLf e he hed).2.2.2.2.1⟩
      ne_one_d := hE.ne_one_d
      le_Q := le_sup_right
      le_F_Q := le_sup_right.trans hAFQ
      card_Q := by rw [hQX.2.1]; norm_num
      extra_Q := hQX.1
      pow_Q := fun q hq => by
        have h := Monoid.pow_exponent_eq_one (⟨q, hq⟩ : q2127Of A d F)
        rw [hQX.2.2] at h
        simpa using congrArg Subtype.val h
      conj_d := hdc
      conj_e_Q := hec
      le_normalizer := hYN
      triv := fun y hy x hx => by
        have hσ : (F e).normalizerMonoidHom ⟨y, hYN hy⟩ ∈
            Sec4.autIn (y2128Of (Lf e) (F e) (q2127Of A d F)) (F e) :=
          Sec4.mem_autIn_iff.mpr ⟨y, hYN hy, hy, rfl⟩
        have h1 := (mem_trivOnQuot_iff.mp (hYtriv hσ)) ⟨x, hx⟩
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe] at h1
        have h2 : x⁻¹ * (y * x * y⁻¹) ∈ F e :=
          (F e).mul_mem ((F e).inv_mem hx) ((Subgroup.mem_normalizer_iff.mp (hYN hy) x).mp hx)
        exact ⟨h2, h1⟩
      trans := fun v hv w hw hv1 hw1 => by
        obtain ⟨m, hm, hmvw⟩ := htr v hv w hw hv1 hw1
        exact ⟨m, Subgroup.mem_sup_left hm,
          Subgroup.mem_centralizer_singleton_iff.mp (hLC hm.1), hmvw⟩
      le_F := fun X hX3 hXC =>
        Item2119End8Proof.le_F_of_le_centralizer hAe hA27 h27 hQ hF he hed hX3 hXC
      card_le_27 := fun X hX3 hXc hXC =>
        Item2119End8Proof.card_le_27_of_le_centralizer h27 hQ hA27 he hed hX3 hXc hXC
      card_le_729 := fun X hX3 hXY =>
        Item2119End8Proof.card_le_729 hAe hA27 h27 hQ hF (fun b hb hbd => h28 b hb hbd) he hed
          hX3 hXY
      exists_t := by
        obtain ⟨t, ht, htH⟩ := exists_inv_of (hF e he hed) (hLf e he hed) h26 (h28 e he hed)
        exact ⟨t, Subgroup.mem_sup_left ht, htH⟩ }

end Item2129Res2Proof

open Item2129Res2Proof

theorem item2129S_of_so (hSO : Item2129SO) : Item2129S := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 e he hed
  have hL := loc2129_of hE hLf h26 hF h27 hQ hQX h28 he hed
  obtain ⟨R, hR⟩ := hL.exists_R
    (hSO G A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 e he hed)
  exact hR.exists_S hL

end CFSG.RankThree.PartTwo.Sec21
