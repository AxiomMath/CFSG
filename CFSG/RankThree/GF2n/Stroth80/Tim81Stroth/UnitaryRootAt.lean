module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmtUnRoot
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Pin
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.RootSylowSp
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Sec7MaxLocalTI
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.MovingConj
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.PSUModel
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Sec7TailMovingEquiv
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.UnitaryReduction
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.WeakClosure

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Tim81
open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem unitaryRootAt_of_unitaryConclusion
    {Z0 : Subgroup G} {f m : ℕ} (hf : 2 ≤ f) (hm : 4 ≤ m)
    (hcardV : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = 2 ^ f)
    (hVZ : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = Nat.card Z)
    {Φ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m →* Hbar M Q Z}
    (hΦker : Φ.ker = Subgroup.center _)
    (hconj : ∀ U : Subgroup (Hbar M Q Z),
      (∃ g : Hbar M Q Z, U = conjSubgroup g
        ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))) ↔
      ∃ x, U = (conjSub ((Unitary.rootDatum
        (card_galoisField_two_mul (by omega : 1 ≤ f)) m).rootGroup
        (unitaryLongRoot m (by omega))) x).map Φ) :
    UnitaryRootAt M Q Z Z0 m := by
  refine ⟨f, hf, hVZ.symm.trans hcardV, hm, Φ, hΦker, ?_⟩
  exact (hconj _).mp ⟨1, (CFSG.RankThree.GF2n.conjSubgroup_one _).symm⟩

theorem tim81Stroth_of_hwc_un_root
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (h712 : Stroth712Statement) (h713 : Stroth713Statement) (hZc : Sec7CentreStatement)
    (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hZt : Sec7ZtStatement)
    (hzcard : Sec7ZCardStatement) (hpin : UnitaryConclusionPin)
    (hc : Ctx M Q Z B) {N : ℕ} {t : G} (hs : Sec7Hyp hc N t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {n : ℕ}
    (hn : Nat.card ↥(Pc (MbarPrime M Q Z Z0) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))))
        = Nat.card Z ^ n)
    (hmaxAb : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hElt : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hNL : ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0)
    (hwc : WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0))) :
    (∃ m, 2 * m - 3 = n ∧
      IsPSUModel m (Nat.card Z) ↥(generalizedFitting (Hbar M Q Z)) ∧
      UnitaryRootAt M Q Z Z0 m) ∨
      ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0 := by
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0 hc hs hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hcardV' : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card ↥(bar M Q Z0) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarZ0H).toEquiv
  have h4 : 4 ≤ Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
    rw [hcardV']; exact four_le_card_bar_Z0 hc hs hzcard hZ0
  have hyp : Hyp (MbarPrime M Q Z Z0) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) :=
    { o2 := pCore_two_bar_H0_eq_bot hc
      maxLocal := isMaximalTwoLocal_of_isMaxTwoLocalSubgroup
        (isMaxTwoLocal_MbarPrime_of_ti h34 h311a hZt hzcard hZc hc hs hZ0 hmaxAb hElt hF)
      fitting := generalizedFitting_MbarPrime hc hs hZ0 h712
      maxAb := maxAb_bar_Z0_comm (Z0 := Z0) hmaxAb
        ((isElemAbelian_bar_Z0 hc hs hZc hZ0).subgroupOf (bar M Q (H0 M Z)))
      elem := (isElemAbelian_bar_Z0 hc hs hZc hZ0).subgroupOf (bar M Q (H0 M Z))
      ti := isTI_bar_Z0 hc hs hZ0 hElt }
  haveI hFinH : Finite (Hbar M Q Z) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  rcases h1 (Hbar M Q Z) (MbarPrime M Q Z Z0)
    ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) hyp h4 hwc with hwcM | hUC | hH
  · exact absurd hwcM (not_weaklyClosed_bar_Z0 hc hs hZ0 hZc hNL)
  · obtain ⟨f, hf, hcardV, hNC, m, hm, Φ, hΦrange, hΦker, hconj⟩ := hUC
    have hpin' : Nat.card ↥(Pc (MbarPrime M Q Z Z0)
          ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))) =
        Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ^ (2 * m - 3) :=
      hpin (Hbar M Q Z) (MbarPrime M Q Z Z0) _ f hf m hm Φ hyp hcardV hΦrange hΦker hconj
    have hVZ : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = Nat.card Z :=
      hcardV'.trans (card_bar_Z0 hc hs hzcard hZ0)
    have hbase : 2 ≤ Nat.card Z := by rw [← hVZ]; omega
    have hpow : Nat.card Z ^ (2 * m - 3) = Nat.card Z ^ n := by
      rw [← hVZ, ← hpin', hn, hVZ]
    have hmn : 2 * m - 3 = n := Nat.pow_right_injective hbase hpow
    have hZq : Nat.card Z = 2 ^ f := hVZ.symm.trans hcardV
    refine Or.inl ⟨m, hmn, ?_, ?_⟩
    · rw [hZq]
      have hgrange : Φ.range = generalizedFitting (Hbar M Q Z) := hΦrange.trans hNC
      have hker' : Φ.rangeRestrict.ker = Subgroup.center
          ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) := by
        rw [MonoidHom.ker_rangeRestrict]
        exact hΦker
      exact IsPSUModel.congr (MulEquiv.subgroupCongr hgrange)
        (isPSUModel_of_su_surjective (n := m) (f := f) (by omega) Φ.rangeRestrict
          Φ.rangeRestrict_surjective hker')
    · exact unitaryRootAt_of_unitaryConclusion hf hm hcardV hVZ hΦker hconj
  ·
    by_cases hn4 : ¬ OmegaPlusNat hc t 4
    · obtain ⟨Hw, hmem⟩ := exists_isHMember hc hs hZ0 h34 h712 h713 hn4 hNL
      exact absurd hmem (hH Hw)
    · obtain ⟨Hw, hmem⟩ := exists_isHMember_of_fitting hc hs hZ0 h34 h712 hF hNL
      exact absurd hmem (hH Hw)

theorem tim81StrothSp_of_hwc_un_root
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (hF2 : Step85F2Statement) (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (h34 : Stroth34Statement) (hpin : UnitaryConclusionPin)
    (hc : Ctx M Q Z B) {N : ℕ} {t : G} (hs : Sec8Hyp hc N t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {n : ℕ}
    (hn : Nat.card ↥(Pc (MbarPrime M Q Z Z0) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))))
        = Nat.card Z ^ n)
    (hmaxAb : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hElt : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hNL : ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0)
    (hwc : WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0))) :
    ∃ m, 2 * m - 3 = n ∧
      IsPSUModel m (Nat.card Z) ↥(generalizedFitting (Hbar M Q Z)) ∧
      UnitaryRootAt M Q Z Z0 m := by
  have hZ0H : Z0 ≤ H0 M Z := isCentrePre_le_H0_sp hc hZ0
  have hbarZ0H : bar M Q Z0 ≤ bar M Q (H0 M Z) :=
    Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (Subgroup.subgroupOf_mono M hZ0H)
  have hcardV' : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card ↥(bar M Q Z0) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarZ0H).toEquiv
  have h4 : 4 ≤ Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
    rw [hcardV']; exact four_le_card_bar_Z0_sp h51 hA hc hs hZ0
  have hyp : Hyp (MbarPrime M Q Z Z0) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) :=
    { o2 := pCore_two_bar_H0_eq_bot hc
      maxLocal := isMaximalTwoLocal_MbarPrime_sp_maxLocal h51 hA hc hs hZ0 hElt hmaxAb hF2 hF
      fitting := generalizedFitting_MbarPrime_sp hc hs hZ0 hF2
      maxAb := maxAb_bar_Z0_comm (Z0 := Z0) hmaxAb
        ((isElemAbelian_bar_Z0_sp h51 hA hc hs hZ0).subgroupOf (bar M Q (H0 M Z)))
      elem := (isElemAbelian_bar_Z0_sp h51 hA hc hs hZ0).subgroupOf (bar M Q (H0 M Z))
      ti := isTI_bar_Z0_sp hc hs hZ0 hElt }
  haveI hFinH : Finite (Hbar M Q Z) :=
    Finite.of_injective (Subtype.val) Subtype.val_injective
  rcases h1 (Hbar M Q Z) (MbarPrime M Q Z Z0)
    ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) hyp h4 hwc with hwcM | hUC | hH
  · exact absurd hwcM (not_weaklyClosed_bar_Z0_sp h51 hA hc hs hZ0 hNL)
  · obtain ⟨f, hf, hcardV, hNC, m, hm, Φ, hΦrange, hΦker, hconj⟩ := hUC
    have hpin' : Nat.card ↥(Pc (MbarPrime M Q Z Z0)
          ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))) =
        Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) ^ (2 * m - 3) :=
      hpin (Hbar M Q Z) (MbarPrime M Q Z Z0) _ f hf m hm Φ hyp hcardV hΦrange hΦker hconj
    have hVZ : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = Nat.card Z :=
      hcardV'.trans (card_bar_Z0_sp h51 hA hc hs hZ0)
    have hbase : 2 ≤ Nat.card Z := by rw [← hVZ]; omega
    have hpow : Nat.card Z ^ (2 * m - 3) = Nat.card Z ^ n := by
      rw [← hVZ, ← hpin', hn, hVZ]
    have hmn : 2 * m - 3 = n := Nat.pow_right_injective hbase hpow
    have hZq : Nat.card Z = 2 ^ f := hVZ.symm.trans hcardV
    refine ⟨m, hmn, ?_, ?_⟩
    · rw [hZq]
      have hgrange : Φ.range = generalizedFitting (Hbar M Q Z) := hΦrange.trans hNC
      have hker' : Φ.rangeRestrict.ker = Subgroup.center
          ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) := by
        rw [MonoidHom.ker_rangeRestrict]
        exact hΦker
      exact IsPSUModel.congr (MulEquiv.subgroupCongr hgrange)
        (isPSUModel_of_su_surjective (n := m) (f := f) (by omega) Φ.rangeRestrict
          Φ.rangeRestrict_surjective hker')
    · exact unitaryRootAt_of_unitaryConclusion hf hm hcardV hVZ hΦker hconj
  ·
    obtain ⟨Hw, hmem⟩ := exists_isHMember_sp hc hs hZ0 h34 hF2 hF hNL
    exact absurd hmem (hH Hw)

theorem tim81StrothSpStatement_of_inputs_un_root
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (hF2 : Step85F2Statement) (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (h34 : Stroth34Statement) (hpin : UnitaryConclusionPin)
    (hc : Ctx M Q Z B) {N : ℕ} {t : G} (hs : Sec8Hyp hc N t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {n : ℕ}
    (hn : Nat.card ↥(Pc (MbarPrime M Q Z Z0) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))))
        = Nat.card Z ^ n)
    (hmaxAb : IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q)
    (hElt : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
      g ∈ Subgroup.normalizer (Z0 : Set G))
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    (hNL : ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0) :
    (∃ m, 2 * m - 3 = n ∧
      IsPSUModel m (Nat.card Z) ↥(generalizedFitting (Hbar M Q Z)) ∧
      UnitaryRootAt M Q Z Z0 m) ∨
      ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0 := by
  by_cases hwc : WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0))
  · obtain ⟨m, h3, hmodel, hroot⟩ :=
      tim81StrothSp_of_hwc_un_root h1 hF2 h51 hA h34 hpin hc hs hZ0 hn hmaxAb hElt hF hNL hwc
    exact Or.inl ⟨m, h3, hmodel, hroot⟩
  · exact Or.inr (exists_conj_le_CN_of_fitting_of_not_weaklyClosed_sp hc hs hZ0 h51 hA hF hwc)

theorem tim81StrothUnRootStatement_holds
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (h712 : Stroth712Statement) (h713 : Stroth713Statement) (hZc : Sec7CentreStatement)
    (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hZt : Sec7ZtStatement)
    (hzcard : Sec7ZCardStatement)
    (hpin : UnitaryConclusionPin) :
    Tim81StrothUnRootStatement := by
  intro G _ _ M Q Z B hQN hc n t hs Z0 hZ0 hmaxAb hElt hF hNL k hk
  haveI := hQN
  have hO2 : inSubgroup (pCore 2) (MbarPrime M Q Z Z0) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) :=
    inSubgroup_pCore_eq_bar_CN hc hs.toSec5.mem hZ0
      (pCore_two_MbarPrime_eq_CN_subgroupOf_of_fitting hc hs hZ0 h712 hF)
  by_cases hwc : WeaklyClosedIn ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      (inSubgroup (pCore 2) (MbarPrime M Q Z Z0))
  · exact tim81Stroth_of_hwc_un_root h1 h712 h713 hZc h34 h311a hZt hzcard hpin
      hc hs hZ0 (card_Pc_eq_pow hc hs.toSec5.mem hZ0 hO2 hk) hmaxAb hElt hF hNL hwc
  · exact Or.inr (exists_conj_le_CN_of_fitting_of_not_weaklyClosed hc hs hZ0 hZc hF hwc)

theorem tim81StrothSpUnRootStatement_holds
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (hF2 : Step85F2Statement) (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (h34 : Stroth34Statement)
    (hpin : UnitaryConclusionPin) :
    Tim81StrothSpUnRootStatement := by
  intro G _ _ M Q Z B hQN hc n t hs Z0 hZ0 hmaxAb hElt hF hNL k hk
  haveI := hQN
  have hO2sub : pCore 2 (MbarPrime M Q Z Z0) =
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0) := by
    rw [← generalizedFitting_MbarPrime_sp hc hs hZ0 hF2]
    exact generalizedFitting_MbarPrime_eq_of_fitting (N := hc.CN t) hF
  have hO2 : inSubgroup (pCore 2) (MbarPrime M Q Z Z0) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) :=
    inSubgroup_pCore_eq_bar_CN hc hs.toSec5.mem hZ0 hO2sub
  exact tim81StrothSpStatement_of_inputs_un_root h1 hF2 h51 hA h34 hpin hc hs hZ0
    (card_Pc_eq_pow hc hs.toSec5.mem hZ0 hO2 hk) hmaxAb hElt hF hNL

theorem tim81StrothUnRootStatement_holds_of_inputs
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (h712 : Stroth712Statement) (h713 : Stroth713Statement) (hZc : Sec7CentreStatement)
    (h34 : Stroth34Statement)
    (h311a : Stroth311aStatement) (hZt : Sec7ZtStatement)
    (hzcard : Sec7ZCardStatement) :
    Tim81StrothUnRootStatement :=
  tim81StrothUnRootStatement_holds h1 h712 h713 hZc h34 h311a hZt hzcard
    unitaryConclusionPin_holds

theorem tim81StrothSpUnRootStatement_holds_of_inputs
    (h1 : CFSG.RankThree.GF2n.Tim81.Theorem1Statement)
    (hF2 : Step85F2Statement) (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (h34 : Stroth34Statement) :
    Tim81StrothSpUnRootStatement :=
  tim81StrothSpUnRootStatement_holds h1 hF2 h51 hA h34 unitaryConclusionPin_holds

end CFSG.RankThree.GF2n.Stroth80
