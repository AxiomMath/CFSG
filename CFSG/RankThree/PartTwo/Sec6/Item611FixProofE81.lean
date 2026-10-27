module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofInvol
public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofField
public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofMinus
public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofUPlus
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofThree
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLie
public import CFSG.RankThree.PartTwo.Sec6.Item641

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

open Res611Res4 Res611Res5 Res611Res6 Res611Res7 ThreeLocalSporProof
open scoped Pointwise

section CertsThree


theorem item611E81ThreeGroup_holdsFix (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) : Item611E81ThreeGroup := by
  intro G _ _ hst A hA hrank d hdA hd1 K hK hCAK h23 D hD hdD U hU hUd hUKC t ht1 ht2 htK hDt
    hUt
  by_contra hno
  push Not at hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d hK
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1 K hKd
  obtain ⟨hDE, hDA⟩ := hD
  have hDe : CFSG.Assembly.IsElemAbelian 3 D := hDE.1
  have hD3 : IsPGroup 3 D := Sec5.isPGroup_of_isElemAbelian hDe
  obtain ⟨hDU, hUab, hU4⟩ := mem_fourGroups_iff.mp hU.1
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hz2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have htU : Subgroup.zpowers t ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hUt hu)))
  set S := U ⊔ Subgroup.zpowers t with hS
  have hS2 : IsPGroup 2 S := by
    rw [hS, sup_comm]
    exact hz2.to_sup_of_normal_right' hU2 htU
  have hDzt : D ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxt : Commute t x := (Subgroup.mem_centralizer_singleton_iff.mp (hDt hx)).symm
    exact (hxt.zpow_left k).eq
  have hDS : D ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_sup U _ ⟨hDU hx, hDzt hx⟩
  have hCKN : thetaQuotCentralizer K ≤ Subgroup.normalizer (K : Set G) := fun z hz =>
    (mem_thetaQuotCentralizer_iff.mp hz).1
  have hUK : U ≤ Subgroup.normalizer (K : Set G) :=
    hUKC.trans (sup_le Subgroup.le_normalizer hCKN)
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := sup_le hUK (Subgroup.zpowers_le.mpr htK)
  have hDSK : D ⊔ S ≤ Subgroup.normalizer (K : Set G) := sup_le (hDA.trans hAK) hSK
  set Q := D ⊓ Subgroup.centralizer (U : Set G) with hQdef
  have hQ9 : Nat.card Q = 9 :=
    card_inf_centralizer_of_mem_fourGroupsMinus (Late.isE27_of_mem_partTwoE hDE) hU
  have hdQ : d ∈ Q := ⟨hdD, Subgroup.mem_centralizer_iff.mpr fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp (hUd hu)⟩
  set Q₀ := Q ⊓ K with hQ₀
  set θK := aschbacherSolvableCore 3 K with hθK
  set Qb := (Q₀.subgroupOf K).map (QuotientGroup.mk' θK) with hQb
  have hQe : CFSG.Assembly.IsElemAbelian 3 Q := Sec5.isElemAbelian_of_le hDe inf_le_left
  have hQ₀e : CFSG.Assembly.IsElemAbelian 3 Q₀ := Sec5.isElemAbelian_of_le hQe inf_le_left
  have hQ₀3 : IsPGroup 3 Q₀ := Sec5.isPGroup_of_isElemAbelian hQ₀e
  have hQbcard : Nat.card Qb = Nat.card Q₀ := card_map_mk_of_isPGroup hQ₀3 inf_le_right
  have hQbe : CFSG.Assembly.IsElemAbelian 3 Qb := by
    refine CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ ?_
    refine Item434Kit.isElemAbelian_of_map_injective K.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact hQ₀e
  have hQ₀3le : 3 ≤ Nat.card Q₀ := by
    rcases h23 with ⟨hAK', -⟩ | ⟨hdec, -, -⟩
    · have hQK : Q ≤ K := inf_le_left.trans (hDA.trans hAK')
      rw [hQ₀, inf_of_le_left hQK, hQ9]
      norm_num
    · have hQdec := eq_sup_inf_of_eq_sup (inf_le_left.trans hDA) hAK hdQ hdec
      have hle := Res611Res3.card_le_three_mul_card_inf hQe hdQ hd1 hQdec
      have hQ₀c : Nat.card Q₀ = Nat.card (Q ⊓ K : Subgroup G) := rfl
      omega
  have hQb1 : Qb ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQbcard
    omega
  have hQb9 : A ≤ K → 9 ≤ Nat.card Qb := by
    intro hAK'
    have hQK : Q ≤ K := inf_le_left.trans (hDA.trans hAK')
    rw [hQbcard, hQ₀, inf_of_le_left hQK, hQ9]
  set Cb := Subgroup.centralizer (Qb : Set (K ⧸ θK)) with hCb
  set P0 := inSubgroup (CFSG.pCore 3) Cb with hP0
  have hKX : Cb ⊓ Subgroup.centralizer (P0 : Set (K ⧸ θK)) ≤ P0 :=
    Res611Res7.inf_centralizer_le_of_case23 h23 hdA (hAe.2 d hdA) hd1 hQbe hQb9 hQb1
  have hQ₀D : Q₀ ≤ D := inf_le_left.trans inf_le_left
  have hJC : D ⊔ S ≤ Subgroup.centralizer (Q₀ : Set G) := by
    apply sup_le
    · intro y hy
      exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
        congrArg Subtype.val (hDe.1.is_comm.comm ⟨q, hQ₀D hq⟩ ⟨y, hy⟩)
    · apply sup_le
      · intro u hu
        refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
        have hqU : q ∈ Subgroup.centralizer (U : Set G) := hq.1.2
        exact (Subgroup.mem_centralizer_iff.mp hqU u hu).symm
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr fun q hq =>
          Subgroup.mem_centralizer_singleton_iff.mp (hDt (hQ₀D hq))
  have hJfix : D ⊔ S ≤ fixG K Qb := fun g hg => le_fixG_map K Q₀ ⟨hDSK hg, hJC hg⟩
  have hJinvC : D ⊔ S ≤ invG K Cb :=
    (hJfix.trans (fixG_le_invG K Qb)).trans (invG_le_invG_centralizer K Qb)
  have hJinvP : D ⊔ S ≤ invG K P0 := hJinvC.trans (invG_le_invG_pCore K Cb)
  have hP03 : IsPGroup 3 P0 := CFSG.pCore_isPGroup.map _
  have hθodd := Res611Res3.odd_card_theta_of_config h45 hst hA hrank hdA hd1 hKd
  obtain ⟨R, -, hR3, hRN, hsurj⟩ := exists_lift_invariant hθodd hD3 hS2 hDS hDSK hP03 hJinvP
  have hRU : R ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hno R hR3 hRN)
  have hUfixP : ∀ u ∈ U, ∀ hu : u ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ P0,
      thetaAct K ⟨u, hu⟩ x = x := by
    intro u huU hu x hx
    obtain ⟨r, hr, rfl⟩ := hsurj x hx
    rw [thetaAct_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe]
    have h := Subgroup.mem_centralizer_iff.mp (hRU hr) u huU
    rw [h, mul_inv_cancel_right]
  have hbotU := Res611Fix.inf_thetaQuotCentralizer_eq_bot h45 h41 h413 hst hA hrank hdA hd1 hK
    hCAK hUab
  have hKCK : K ≤ Subgroup.normalizer (thetaQuotCentralizer K : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thetaQuotCentralizer K)
  have hU1 : ∀ u ∈ U, u = 1 := by
    intro u huU
    have hu := hUK huU
    have huJ : u ∈ D ⊔ S := Subgroup.mem_sup_right (Subgroup.mem_sup_left huU)
    set τ := thetaAct K ⟨u, hu⟩ with hτ
    have hττ : τ * τ = 1 := by
      rw [hτ, ← map_mul]
      have h1 : (⟨u, hu⟩ * ⟨u, hu⟩ : Subgroup.normalizer (K : Set G)) = 1 :=
        Subtype.ext (by simpa [pow_two] using hUab.2 u huU)
      rw [h1, map_one]
    obtain ⟨hg1, hstab⟩ := mem_invG_iff.mp (hJinvC huJ)
    obtain ⟨hg2, hfixQ⟩ := mem_fixG_iff.mp (hJfix huJ)
    have hfixC : ∀ x ∈ Cb, τ x = x :=
      fix_of_fix_pCore τ hττ (fun x hx => (hstab x).mpr hx) (hUfixP u huU hu) hKX
    have huKC : u ∈ (K : Set G) * (thetaQuotCentralizer K : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K _ hKCK]
      exact hUKC huU
    obtain ⟨k, hk, z, hz, hkz⟩ := huKC
    have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
    have hzN : z ∈ Subgroup.normalizer (K : Set G) := hCKN hz
    set kb := QuotientGroup.mk' θK ⟨k, hk⟩ with hkb
    have hτeq : τ = MulAut.conj kb := by
      have h1 : (⟨u, hu⟩ : Subgroup.normalizer (K : Set G)) = ⟨k, hkN⟩ * ⟨z, hzN⟩ :=
        Subtype.ext hkz.symm
      have h2 : thetaAct K ⟨z, hzN⟩ = 1 :=
        (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hzN).mp hz
      have h3 : thetaAct K ⟨k, hkN⟩ = MulAut.conj kb := Sec12.thetaBarAct_of_mem hk
      rw [hτ, h1, map_mul, h2, mul_one, h3]
    have hkbC : kb ∈ Cb := by
      rw [hCb, Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : τ q = q := hfixQ q hq
      rw [hτeq, MulAut.conj_apply] at h1
      calc q * kb = (kb * q * kb⁻¹) * kb := by rw [h1]
        _ = kb * q := by group
    have hkbCC : kb ∈ Subgroup.centralizer (P0 : Set (K ⧸ θK)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyC : y ∈ Cb := (Subgroup.map_subtype_le _) hy
      have h1 : τ y = y := hfixC y hyC
      rw [hτeq, MulAut.conj_apply] at h1
      calc y * kb = (kb * y * kb⁻¹) * kb := by rw [h1]
        _ = kb * y := by group
    have hkbP : kb ∈ P0 := hKX ⟨hkbC, hkbCC⟩
    obtain ⟨n, hn⟩ := hP03 ⟨kb, hkbP⟩
    have hkbn : kb ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hτn : τ ^ 3 ^ n = 1 := by rw [hτeq, ← map_pow, hkbn, map_one]
    have hτ2 : τ ^ 2 = 1 := by rw [pow_two]; exact hττ
    have hτ1 : τ = 1 := by
      have hdvd : orderOf τ ∣ Nat.gcd (3 ^ n) 2 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτn) (orderOf_dvd_of_pow_eq_one hτ2)
      have hg : Nat.gcd (3 ^ n) 2 = 1 := Nat.Coprime.pow_left n (by norm_num)
      rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
      exact hdvd
    have huC : u ∈ thetaQuotCentralizer K :=
      (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct hu).mpr hτ1
    have hmem : u ∈ U ⊓ thetaQuotCentralizer K := ⟨huU, huC⟩
    rw [hbotU] at hmem
    exact hmem
  have hUbot : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr hU1
  rw [hUbot, Subgroup.card_bot] at hU4
  norm_num at hU4

end CertsThree

section Certs


theorem item611E81Core_ofFix (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9)
    (h41 : Sec4.Item4_1LargePrime) (h413 : Sec4.Item4_13_forwardFix) (hF : Item611FieldL2T)
    (hI : Item611InvolNormal) (hT : Item611E81ThreeGroup) : Item611E81Core := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT' hTL hTθ hcase t htL htN ht1 ht2
    hD V hVt hVN hVab hV4 U hU hUV d hdA hd1 K hK hCAK hKD R hR hRK hRθ hCR
  set D := A ⊓ Subgroup.centralizer ({t} : Set G) with hDdef
  have hDE : D ∈ collectionIn (partTwoE G) A := ⟨hD, inf_le_left⟩
  have hdD : d ∈ D := Res611Field.mem_of_mem_lZero hA.1.1 inf_le_left hd1 hCAK hKD
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hK.1
  have hdR : d ∈ D ⊓ Subgroup.centralizer (R : Set G) := by
    refine ⟨hdD, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hKd (hRK hr)))
  rw [hCR] at hdR
  have hUd : U ≤ Subgroup.centralizer ({d} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hdR.2 u hu)
  have htd : t ∈ Subgroup.centralizer ({d} : Set G) := by
    have := (inf_le_right : D ≤ Subgroup.centralizer ({t} : Set G)) hdD
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have htK : t ∈ Subgroup.normalizer (K : Set G) :=
    hI G hst A hA hrank d hdA hd1 K hK hCAK t htd ht2
  have hUKC : U ≤ K ⊔ thetaQuotCentralizer K :=
    le_sup_thetaQuotCentralizer h45 h49 hst hA.1.1 hdA hd1 hK.1 hD inf_le_left hdD hU hUd
  have hUt : U ≤ Subgroup.centralizer ({t} : Set G) := hUV.trans hVt
  have hDt : D ≤ Subgroup.centralizer ({t} : Set G) := inf_le_right
  rcases Res611Fix.cases413 h45 h41 h413 hst hA hrank hdA hd1 hK hCAK with h1 | h2 | h3 | h4
  · exact hF G hst A hA hrank d hdA hd1 K hK hCAK D hDE hKD R hR hRK hRθ h1
  · obtain ⟨P, hP, hPN, hPU⟩ := hT G hst A hA hrank d hdA hd1 K hK hCAK (Or.inl h2) D hDE hdD U
      hU hUd hUKC t ht1 ht2 htK hDt hUt
    exact false_of_threeGroup hst.evenRank_eq hD hU.1 ht1 ht2 hDt hUt hP hPN hPU
  · obtain ⟨P, hP, hPN, hPU⟩ := hT G hst A hA hrank d hdA hd1 K hK hCAK (Or.inr h3) D hDE hdD U
      hU hUd hUKC t ht1 ht2 htK hDt hUt
    exact false_of_threeGroup hst.evenRank_eq hD hU.1 ht1 ht2 hDt hUt hP hPN hPU
  ·
    exact item611NotG2CoverT_holds G hst A hA hrank d hdA hd1 K hK hCAK D hDE hKD R hR hRK hRθ h4

theorem item611E81Inv_of_res5Fix (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hKf : KFacts.KS6OuterIndex) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) (hC : Item611UPlusCent) (hV : Item611E81V)
    (hCore : Item611E81Core) : Item611E81Inv := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ hcase t htL htN ht1 ht2 hD
  obtain ⟨V, hVt, hVN, hVab, hV4⟩ :=
    hV G hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ hcase t htL htN ht1 ht2 hD
  have hDV : A ⊓ Subgroup.centralizer {t} ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_right.trans hVN
  obtain ⟨U, hU, hUV⟩ := exists_mem_fourGroups_le hD.1 hD.2.1 hVab hV4 hDV
  have hUm : U ∈ fourGroupsMinus (A ⊓ Subgroup.centralizer {t}) := by
    rcases Sec21.Item211Res2Proof.mem_fourGroupsPlus_or_mem_fourGroupsMinus hD.1.2 hU with
      hP | hM
    · exact (Res611Fix.false_of_mem_fourGroupsPlus h45 h48 h49 hKf h41 h413 hC hst hA hrank
        hcA hc1 hL hCA ⟨hD, inf_le_left⟩ (mem_thetaComponentFamily_inf hcA hc1 hL.1 htL)
        hP).elim
    · exact hM
  obtain ⟨d, hdA, hd1, K, hK, hCAK, hKD, R, hR, hRK, hRθ, hCR⟩ :=
    item611ChooseMinus_holdsFix h45 h48 h49 hKf h41 h413 G hst A hA hrank c hcA hc1 L hL hCA
      (A ⊓ Subgroup.centralizer {t}) ⟨hD, inf_le_left⟩ U hUm
  exact hCore G hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ hcase t htL htN ht1 ht2
    hD V hVt hVN hVab hV4 U hUm hUV d hdA hd1 K hK hCAK hKD R hR hRK hRθ hCR

end Certs

section CertsCore


theorem item611E81Core_of_res7Fix (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9)
    (h41 : Sec4.Item4_1LargePrime) (h413 : Sec4.Item4_13_forwardFix) (hF : Item611FieldL2T) :
    Item611E81Core :=
  item611E81Core_ofFix h45 h49 h41 h413 hF (item611InvolNormal_holdsFix h45 h41 h413)
    (item611E81ThreeGroup_holdsFix h45 h41 h413)

theorem item611E81Core_holdsFix (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (h41 : Sec4.Item4_1LargePrime) (h413 : Sec4.Item4_13_forwardFix) : Item611E81Core :=
  item611E81Core_of_res7Fix h45 h49 h41 h413 (item611FieldL2T_holdsFix h45 h48 h49 h41 h413)

end CertsCore

end CFSG.RankThree.PartTwo.Sec6
