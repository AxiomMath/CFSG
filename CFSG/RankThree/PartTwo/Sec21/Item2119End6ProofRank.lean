module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127C
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofTools
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

namespace Item2119End6Proof

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_sup_of_commute {B S : Subgroup G} (hB : IsElemAbelian 3 B)
    (hS : IsElemAbelian 3 S) (hc : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b) (hBS : B ⊓ S = ⊥) :
    IsElemAbelian 3 (B ⊔ S) ∧ Nat.card (B ⊔ S : Subgroup G) = Nat.card B * Nat.card S := by
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B S hc
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hS.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hmem : ∀ u ∈ (B ⊔ S : Subgroup G), ∃ b ∈ B, ∃ s ∈ S, u = b * s := by
    intro u hu
    have hu' : u ∈ ((B ⊔ S : Subgroup G) : Set G) := hu
    rw [hset] at hu'
    obtain ⟨b, hb, s, hs, rfl⟩ := hu'
    exact ⟨b, hb, s, hs, rfl⟩
  refine ⟨⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩, ?_⟩
  · obtain ⟨b, hb, s, hs, hu⟩ := hmem u u.2
    obtain ⟨b', hb', s', hs', hv⟩ := hmem v v.2
    apply Subtype.ext
    change (u : G) * v = v * u
    rw [hu, hv]
    have h1 : Commute b b' := hBc b hb b' hb'
    have h2 : Commute b s' := hc b hb s' hs'
    have h3 : Commute s b' := (hc b' hb' s hs).symm
    have h4 : Commute s s' := hSc s hs s' hs'
    exact (Commute.mul_left (h1.mul_right h2) (h3.mul_right h4)).eq
  · obtain ⟨b, hb, s, hs, rfl⟩ := hmem u hu
    have hbs : Commute b s := hc b hb s hs
    rw [hbs.mul_pow, hB.2 b hb, hS.2 s hs, one_mul]
  · rw [hBS, Subgroup.card_bot, mul_one] at hcard
    exact hcard

theorem mem_normalizer_of_mem_centralizer {T : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (T : Set G)) : g ∈ Subgroup.normalizer (T : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  have h := Subgroup.mem_centralizer_iff.mp hg t ht
  rw [← h, mul_inv_cancel_right]
  exact ht

end Item2119End6Proof

open Item2119End6Proof

theorem item2127Rank_holds : Item2127Rank := by
  intro G _ _ A E U c L d hP y hy hy3
  by_contra hyc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := hP.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  obtain ⟨eL⟩ := hP.l34
  have hZ : Subgroup.center (lBar L) = ⊥ :=
    Item2119End3Proof.center_eq_bot_of_mulEquiv' eL
      (Item21Early2Proof.center_projSL_three_eq_bot (by norm_num) (by decide))
  obtain ⟨⟨hyC, -⟩, hyT⟩ := hy
  have hyc' : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
  set B := Subgroup.zpowers c ⊔ Subgroup.zpowers y with hBdef
  obtain ⟨hBe, hBcard⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers
    (Item2119End3Proof.isElemAbelian_zpowers' hc3) hy3 (fun b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (show Commute y c from hyc') k).eq)
  have hB9 : Nat.card B = 9 := by
    rw [hBcard hyc, Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hcC : c ∈ Sec4.thetaQuotCentralizer L :=
    Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc
  have hBC : B ≤ Sec4.thetaQuotCentralizer L :=
    sup_le (Subgroup.zpowers_le.mpr hcC) (Subgroup.zpowers_le.mpr hyT)
  set D := Subgroup.zpowers y with hDdef
  have hD3 : IsPGroup 3 D := by
    rintro ⟨g, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hDC : D ≤ Sec4.thetaQuotCentralizer L := Subgroup.zpowers_le.mpr hyT
  set K := L ⊓ Subgroup.centralizer (D : Set G) with hKdef
  have hKL : K ≤ L := inf_le_left
  have hcov := Sec6.le_inf_centralizer_sup_theta_of_isPGroup hD3 hDC
  set φ : K →* lBar L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL) with hφdef
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) z
    have hl : (l : G) ∈ (K : Set G) * (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K _
        (hKL.trans (Sec6.le_normalizer_theta L))]
      exact hcov l.2
    obtain ⟨k, hk, t, ht, hkt⟩ := hl
    refine ⟨⟨k, hk⟩, ?_⟩
    change QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hKL ⟨k, hk⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) l
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t', ht', rfl⟩ := ht
    have : (Subgroup.inclusion hKL ⟨k, hk⟩)⁻¹ * l = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hkt]
      simp
    rw [this]
    exact ht'
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    intro h3k
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 3 h3k
    have hwθ : Subgroup.inclusion hKL (w : K) ∈ aschbacherSolvableCore 3 L := by
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hKL (w : K)) =
          1 := MonoidHom.mem_ker.mp w.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨_, hwθ⟩ : aschbacherSolvableCore 3 L) = 3 := by
      rw [Subgroup.orderOf_mk, orderOf_injective _ (Subgroup.inclusion_injective hKL),
        Subgroup.orderOf_coe, hw]
    have h1 := orderOf_dvd_natCard (⟨_, hwθ⟩ : aschbacherSolvableCore 3 L)
    rw [hord] at h1
    exact three_not_dvd_card_aschbacherSolvableCore h1
  set e' := eL.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  obtain ⟨xb, hxb3, hxb1, R, hR1, hR2, hxbR⟩ := exists_normalizer_two_of_localRank
    (KFacts.L34.localRank_three_of_mulEquiv KFacts.L34.card_galoisField_two_two e')
  have hzx3 : IsPGroup 3 (Subgroup.zpowers xb) := by
    rintro ⟨g, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxb3, one_zpow]
  obtain ⟨Eb, hEb⟩ := hzx3.exists_le_sylow
  have hEb9 : Nat.card (Eb : Subgroup (lBar L)) = 9 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr eL.toEquiv, KFacts.L34.card_projSL,
      CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
        (show 20160 = 3 ^ 2 * 2240 by norm_num) (by norm_num)]
    norm_num
  have hEbe : IsElemAbelian 3 (Eb : Subgroup (lBar L)) := by
    have h9 : Nat.card ((Eb : Subgroup (lBar L)).map e'.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective e'.injective, hEb9]
    have hEA := KFacts.L34.isElementaryAbelian_of_card_eq_nine
      KFacts.L34.card_galoisField_two_two h9
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
    · apply Subtype.ext
      apply e'.injective
      have h := congrArg Subtype.val (hEA.toIsMulCommutative.is_comm.comm
        ⟨e' u, Subgroup.mem_map_of_mem _ u.2⟩ ⟨e' v, Subgroup.mem_map_of_mem _ v.2⟩)
      simpa only [Subgroup.coe_mul, map_mul] using h
    · apply e'.injective
      rw [map_pow, map_one]
      exact @CFSG.elemPow_eq_one_of_isElementaryAbelian 3 _ _ _ hEA (e' u)
        (Subgroup.mem_map_of_mem _ hu)
  obtain ⟨S, hSE, hSinj⟩ := exists_lift_of_isPGroup hsurj hker Eb.isPGroup'
  have hxbE : xb ∈ (Eb : Subgroup (lBar L)) := hEb (Subgroup.mem_zpowers xb)
  rw [← hSE] at hxbE
  obtain ⟨q, hqS, hφq⟩ := hxbE
  have hSmul : ∀ s ∈ S, ∀ t ∈ S, φ s = φ t → s = t := by
    intro s hs t ht hst
    have h1 := hSinj (s⁻¹ * t) (S.mul_mem (S.inv_mem hs) ht) (by rw [map_mul, map_inv, hst,
      inv_mul_cancel])
    exact (inv_mul_eq_one.mp h1)
  have hq3 : q ^ 3 = 1 := hSinj _ (S.pow_mem hqS 3) (by rw [map_pow, hφq, hxb3])
  have hq1 : q ≠ 1 := fun h => hxb1 (by rw [← hφq, h, map_one])
  obtain ⟨T, hT1, hT2, hqT⟩ :=
    exists_normalized_two hsurj hker hq3 hR1 hR2 (by rw [hφq]; exact hxbR)
  have hSe : IsElemAbelian 3 S := by
    have hEbc : ∀ u ∈ (Eb : Subgroup (lBar L)), ∀ v ∈ (Eb : Subgroup (lBar L)), u * v = v * u :=
      fun u hu v hv => congrArg Subtype.val (hEbe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    have hφS : ∀ s ∈ S, φ s ∈ (Eb : Subgroup (lBar L)) := fun s hs => by
      rw [← hSE]
      exact Subgroup.mem_map_of_mem _ hs
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun u hu => ?_⟩
    · refine hSmul _ (S.mul_mem u.2 v.2) _ (S.mul_mem v.2 u.2) ?_
      show φ ((u : K) * v) = φ ((v : K) * u)
      rw [map_mul, map_mul, hEbc _ (hφS _ u.2) _ (hφS _ v.2)]
    · exact hSinj _ (S.pow_mem hu 3) (by rw [map_pow, hEbe.2 _ (hφS u hu)])
  have hS9 : Nat.card S = 9 := by
    have hinj : Function.Injective (φ.comp S.subtype) := by
      intro s t hst
      exact Subtype.ext (hSmul s s.2 t t.2 hst)
    have hrange : (φ.comp S.subtype).range = S.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hrange, hSE, hEb9]
  set qG : G := (q : G) with hqG
  set TG : Subgroup G := T.map K.subtype with hTG
  set SG : Subgroup G := S.map K.subtype with hSG
  have hqL : qG ∈ L := q.2.1
  have hqC : qG ∈ Subgroup.centralizer (D : Set G) := q.2.2
  have hqG3 : qG ^ 3 = 1 := by rw [hqG, ← Subgroup.coe_pow, hq3, Subgroup.coe_one]
  have hqG1 : qG ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hTGK : TG ≤ K := Subgroup.map_subtype_le T
  have hSGK : SG ≤ K := Subgroup.map_subtype_le S
  have hBK : ∀ b ∈ B, ∀ k ∈ K, b * k = k * b := by
    intro b hb k hk
    have hkB : B ≤ Subgroup.centralizer ({k} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hLC hk.1)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hk.2 y (Subgroup.mem_zpowers y))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hkB hb)
  have hqB : qG ∉ B := by
    intro hqB
    exact hqG1 (Item2119End3Proof.eq_one_of_mem_thetaQuotCentralizer hZ hqL (hBC hqB) hqG3)
  obtain ⟨hE0e, hE0card⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers hBe hqG3
    (fun b hb => (hBK b hb qG q.2).symm)
  have hE027 : Nat.card (B ⊔ Subgroup.zpowers qG : Subgroup G) = 27 := by
    rw [hE0card hqB, hB9]
  have hTG1 : TG ≠ ⊥ := by
    intro hbot
    apply hT1
    rw [eq_bot_iff]
    intro t ht
    have : (t : G) ∈ TG := ⟨t, ht, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hTG2 : IsPGroup 2 TG := hT2.map _
  have hqTG : qG ∈ Subgroup.normalizer (TG : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    obtain ⟨t', ht', rfl⟩ := ht
    have h1 := (Subgroup.mem_normalizer_iff.mp hqT t').mp ht'
    exact ⟨_, h1, rfl⟩
  have hBTG : B ≤ Subgroup.normalizer (TG : Set G) := fun b hb =>
    mem_normalizer_of_mem_centralizer (Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (hBK b hb t (hTGK ht)).symm)
  have hE0N : B ⊔ Subgroup.zpowers qG ≤ Subgroup.normalizer (TG : Set G) :=
    sup_le hBTG (Subgroup.zpowers_le.mpr hqTG)
  have hE0E : B ⊔ Subgroup.zpowers qG ∈ partTwoE G :=
    ⟨hE0e, hE027, TG, hTG1, hTG2, hE0N⟩
  have hSGe : IsElemAbelian 3 SG := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
    · obtain ⟨u', hu', hu''⟩ := u.2
      obtain ⟨v', hv', hv''⟩ := v.2
      apply Subtype.ext
      change (u : G) * v = v * u
      rw [← hu'', ← hv'']
      have h := congrArg Subtype.val (hSe.1.is_comm.comm ⟨u', hu'⟩ ⟨v', hv'⟩)
      simpa using congrArg Subtype.val h
    · obtain ⟨u', hu', rfl⟩ := hu
      have h := hSe.2 u' hu'
      simpa using congrArg Subtype.val h
  have hBSG : B ⊓ SG = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Item2119End3Proof.eq_one_of_mem_thetaQuotCentralizer hZ (hKL (hSGK hx.2))
      (hBC hx.1) (hBe.2 x hx.1)
  obtain ⟨hA0e, hA0card⟩ := isElemAbelian_sup_of_commute hBe hSGe
    (fun b hb s hs => hBK b hb s (hSGK hs)) hBSG
  have hSG9 : Nat.card SG = 9 := by
    rw [hSG, Subgroup.card_map_of_injective K.subtype_injective, hS9]
  have hqSG : qG ∈ SG := ⟨q, hqS, rfl⟩
  have hle : B ⊔ Subgroup.zpowers qG ≤ B ⊔ SG :=
    sup_le le_sup_left ((Subgroup.zpowers_le.mpr hqSG).trans le_sup_right)
  have hAE : A ∈ partTwoE G := by
    obtain ⟨-, -, E₀, hE₀, hE₀A⟩ := hpair.mem_S.1
    have hA27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
    have hEq : E₀ = A := Subgroup.eq_of_le_of_card_ge hE₀A (by rw [hA27, hE₀.2.1])
    rw [← hEq]
    exact hE₀
  have hEF := hpair.side hAE
  rw [hEF] at hE0E
  have heq := hE0E.2.1 _ hA0e hle
  have hc81 := congrArg (fun H : Subgroup G => Nat.card H) heq
  rw [hA0card, hB9, hSG9, hE027] at hc81
  norm_num at hc81

end CFSG.RankThree.PartTwo.Sec21
