module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section9

universe v
universe w
universe u

public theorem subgroupCentralizerIn_W1_eq_W2_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      subgroupCentralizerIn MF W1 = W2 := by
  classical
  intro h92
  have h92W1 : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := by
    exact hypothesis_9_2_with_card_W1_sec9 h92
  have hW1prime : Nat.Prime (Nat.card W1) :=
    nat_card_W1_prime_of_hypothesis_9_2_sec9 M MF U W1 W2 h92W1
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, hMFleDer, _hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, hW2le, _hW2ne, _hW2cyc,
      hcentralizer, _hhat, _hprimeCentralizer⟩
  have hW1_ne_bot : W1 ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card W1 = 1 := by
      simp [hbot]
    exact hW1prime.ne_one hcard1
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW1_ne_bot with ⟨x, hx_ne⟩
  let xG : G := (x : G)
  have hxW1 : xG ∈ W1 := x.property
  have hxG_ne : xG ≠ 1 := by
    intro hxG
    apply hx_ne
    ext
    exact hxG
  have hxcent : elementCentralizerIn (ambientDerivedSubgroup M) xG = W2 :=
    hcentralizer xG hxW1 hxG_ne
  have hgen : Subgroup.zpowers x = ⊤ :=
    zpowers_eq_top_of_prime_card_of_ne_one hW1prime hx_ne
  apply le_antisymm
  · intro y hy
    have hy' : y ∈ MF ∧ y ∈ Subgroup.centralizer (W1 : Set G) := by
      simpa [subgroupCentralizerIn] using hy
    have hyDer : y ∈ ambientDerivedSubgroup M := hMFleDer hy'.1
    have hyCentX : y ∈ Subgroup.centralizer ({xG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hy' ⊢
      intro z hz
      have hz_eq : z = xG := by simpa using hz
      subst z
      exact hy'.2 xG hxW1
    have hyElem : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) xG := by
      simpa [elementCentralizerIn] using And.intro hyDer hyCentX
    simpa [hxcent] using hyElem
  · intro y hyW2
    have hyElem : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) xG := by
      simpa [hxcent] using hyW2
    have hyMF : y ∈ MF := hW2le hyW2
    have hyCentX : y ∈ Subgroup.centralizer ({xG} : Set G) := by
      simp [elementCentralizerIn] at hyElem
      exact hyElem.2
    have hy_comm_x : y * xG = xG * y := by
      rw [Subgroup.mem_centralizer_iff] at hyCentX
      exact (hyCentX xG (by simp [xG])).symm
    have hyCentW1 : y ∈ Subgroup.centralizer (W1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      let wW1 : W1 := ⟨w, hw⟩
      have hw_mem_z : wW1 ∈ Subgroup.zpowers x := by
        simp [hgen]
      rcases (Subgroup.mem_zpowers_iff.mp hw_mem_z) with ⟨n, hn⟩
      have hw_eq : w = xG ^ n := by
        calc
          w = (wW1 : G) := rfl
          _ = ((x : W1) ^ n : W1) := by rw [← hn]
          _ = xG ^ n := by simp [xG]
      subst w
      exact (Commute.zpow_right (hy_comm_x : Commute y xG) n).eq.symm
    simpa [subgroupCentralizerIn] using And.intro hyMF hyCentW1

private theorem subgroupCentralizerIn_W1_eq_Kstar_of_typeCommon_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF V W1 Kstar : Subgroup G)
    (hW1prime : Nat.Prime (Nat.card W1))
    (hCommon : section16TypeCommon M MF V W1 Kstar) :
    subgroupCentralizerIn MF W1 = Kstar := by
  classical
  rcases hCommon with
    ⟨_hHallD, hMFleDer, _hComp, _hVnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hSecond, _hFitting, _hFittingLeDer, hKstarle, hKstarne, _hKstarcyc,
      hcentralizer, _hHatW, _hT6, _hKstarSecond⟩
  have hW1_ne_bot : W1 ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card W1 = 1 := by
      simp [hbot]
    exact hW1prime.ne_one hcard1
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW1_ne_bot with ⟨x, hx_ne⟩
  let xG : G := (x : G)
  have hxW1 : xG ∈ W1 := x.property
  have hxG_ne : xG ≠ 1 := by
    intro hxG
    apply hx_ne
    ext
    exact hxG
  have hxcent : elementCentralizerIn (ambientDerivedSubgroup M) xG = Kstar :=
    hcentralizer xG hxW1 hxG_ne
  have hgen : Subgroup.zpowers x = ⊤ :=
    zpowers_eq_top_of_prime_card_of_ne_one hW1prime hx_ne
  apply le_antisymm
  · intro y hy
    have hy' : y ∈ MF ∧ y ∈ Subgroup.centralizer (W1 : Set G) := by
      simpa [subgroupCentralizerIn] using hy
    have hyDer : y ∈ ambientDerivedSubgroup M := hMFleDer hy'.1
    have hyCentX : y ∈ Subgroup.centralizer ({xG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hy' ⊢
      intro z hz
      have hz_eq : z = xG := by simpa using hz
      subst z
      exact hy'.2 xG hxW1
    have hyElem : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) xG := by
      simpa [elementCentralizerIn] using And.intro hyDer hyCentX
    simpa [hxcent] using hyElem
  · intro y hyKstar
    have hyElem : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) xG := by
      simpa [hxcent] using hyKstar
    have hyMF : y ∈ MF := hKstarle hyKstar
    have hyCentX : y ∈ Subgroup.centralizer ({xG} : Set G) := by
      simp [elementCentralizerIn] at hyElem
      exact hyElem.2
    have hy_comm_x : y * xG = xG * y := by
      rw [Subgroup.mem_centralizer_iff] at hyCentX
      exact (hyCentX xG (by simp [xG])).symm
    have hyCentW1 : y ∈ Subgroup.centralizer (W1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      let wW1 : W1 := ⟨w, hw⟩
      have hw_mem_z : wW1 ∈ Subgroup.zpowers x := by
        simp [hgen]
      rcases (Subgroup.mem_zpowers_iff.mp hw_mem_z) with ⟨n, hn⟩
      have hw_eq : w = xG ^ n := by
        calc
          w = (wW1 : G) := rfl
          _ = ((x : W1) ^ n : W1) := by rw [← hn]
          _ = xG ^ n := by simp [xG]
      subst w
      exact (Commute.zpow_right (hy_comm_x : Commute y xG) n).eq.symm
    simpa [subgroupCentralizerIn] using And.intro hyMF hyCentW1

public theorem theorem_9_3_action_normalizes_and_solvable_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
  hypothesis_9_2_statement M MF U W1 W2 q →
      (U ⊔ W1 ≤ Subgroup.normalizer (MF : Set G)) ∧ Group.IsSolvable MF := by
  intro h92
  have hMF := h92.mf
  rcases hMF.1 with ⟨hMFleM, hMFnormalM, hMFnil, _hMFhall⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhall, _hMFder, hcomp, _hnil, hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  have hderM : ambientDerivedSubgroup M ≤ M := hhall.1
  have hUM : U ≤ M := (hcomp.2.1).trans hderM
  have hW1M : W1 ≤ M := hW1norm.trans inf_le_right
  have hMnorm : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  constructor
  · exact (sup_le hUM hW1M).trans hMnorm
  · haveI : Group.IsNilpotent MF := hMFnil
    exact inferInstance

public theorem ambientDerived_disjoint_W1_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
  hypothesis_9_2_statement M MF U W1 W2 q →
      Disjoint (ambientDerivedSubgroup M) W1 := by
  intro h92
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhall, _hMFder, _hcomp, _hnil, _hW1norm, _hW1cyc, hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  rcases hhall with ⟨hDleM, hHallD⟩
  have hcopDsub :
      Nat.Coprime (Nat.card ((ambientDerivedSubgroup M).subgroupOf M))
        ((ambientDerivedSubgroup M).subgroupOf M).index :=
    hHallD.card_coprime_index
  have hindex : ((ambientDerivedSubgroup M).subgroupOf M).index = Nat.card W1 := by
    simpa [Subgroup.relIndex] using hW1card.symm
  have hcop : Nat.Coprime (Nat.card (ambientDerivedSubgroup M)) (Nat.card W1) := by
    simpa [natCard_subgroupOf_eq (ambientDerivedSubgroup M) M hDleM, hindex] using
      hcopDsub
  exact Subgroup.disjoint_of_coprime_natCard hcop

public theorem section12ComplementIn_U_sup_W1_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
  hypothesis_9_2_statement M MF U W1 W2 q →
      section12ComplementIn (U ⊔ W1) U W1 := by
  intro h92
  have h92full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhall, _hMFder, hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  have hUleD : U ≤ ambientDerivedSubgroup M := hcomp.2.1
  have hDdisj : Disjoint (ambientDerivedSubgroup M) W1 :=
    ambientDerived_disjoint_W1_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92full
  have hUW1disj : Disjoint U W1 := by
    rw [disjoint_iff] at hDdisj ⊢
    apply le_antisymm
    · exact (inf_le_inf_right W1 hUleD).trans (le_of_eq hDdisj)
    · exact bot_le
  exact ⟨le_sup_left, le_sup_right, rfl, hUW1disj⟩

public theorem nat_card_MF_coprime_U_sup_W1_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
  hypothesis_9_2_statement M MF U W1 W2 q →
      Nat.Coprime (Nat.card MF) (Nat.card (U ⊔ W1 : Subgroup G)) := by
  intro h92
  have hMF := h92.mf
  have h92full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  rcases hMF.1 with ⟨hMFleM, hMFnormalM, _hMFnil, hMFhall⟩
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, hMFleD, hcompD, _hnil, hW1norm, _hW1cyc, hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne, _hW2cyc,
      _hcentralizer, _hhat, _hprimeCentralizer⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  rcases hcompD with ⟨_hMFleD_comp, hUleD, hD_eq, hMFUdisj⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hW1leNormU : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).1
  have hUnormalUW : (U.subgroupOf (U ⊔ W1)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := U) (K := U ⊔ W1) le_sup_left).2
    exact sup_le Subgroup.le_normalizer hW1leNormU
  have hUWcomp : section12ComplementIn (U ⊔ W1) U W1 :=
    section12ComplementIn_U_sup_W1_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92full
  have hUWdisj : Disjoint U W1 := hUWcomp.2.2.2
  have hUWdisjSub : Disjoint (U.subgroupOf (U ⊔ W1)) (W1.subgroupOf (U ⊔ W1)) := by
    rw [disjoint_iff] at hUWdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ W1 := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hUWdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hUWsupTop :
      U.subgroupOf (U ⊔ W1) ⊔ W1.subgroupOf (U ⊔ W1) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := W1) (B := U ⊔ W1)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hUWcompSub : (U.subgroupOf (U ⊔ W1)).IsComplement' (W1.subgroupOf (U ⊔ W1)) := by
    letI : (U.subgroupOf (U ⊔ W1)).Normal := hUnormalUW
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf (U ⊔ W1)) (W1.subgroupOf (U ⊔ W1)) hUWdisjSub hUWsupTop
  have hcardUW : Nat.card (U ⊔ W1 : Subgroup G) = Nat.card U * Nat.card W1 := by
    have hmul := hUWcompSub.card_mul
    simpa [natCard_subgroupOf_eq U (U ⊔ W1) le_sup_left,
      natCard_subgroupOf_eq W1 (U ⊔ W1) le_sup_right] using hmul.symm
  have hMleNormMF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleM).1 hMFnormalM
  have hMFnormalD : (MF.subgroupOf D).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (H := MF) (K := D) hMFleD).2
    exact hDleM.trans hMleNormMF
  have hMFUdisjSub : Disjoint (MF.subgroupOf D) (U.subgroupOf D) := by
    rw [disjoint_iff] at hMFUdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ MF ⊓ U := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf, D] using hx.1,
          by simpa [Subgroup.mem_subgroupOf, D] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hMFUdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hMFUsupTop : MF.subgroupOf D ⊔ U.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := MF) (A' := U) (B := D) hMFleD hUleD]
    apply Subgroup.subgroupOf_eq_top.2
    intro x hxD
    change x ∈ D at hxD
    simpa [D, hD_eq] using hxD
  have hMFUcompSub : (MF.subgroupOf D).IsComplement' (U.subgroupOf D) := by
    letI : (MF.subgroupOf D).Normal := hMFnormalD
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (MF.subgroupOf D) (U.subgroupOf D) hMFUdisjSub hMFUsupTop
  have hindexMF_D : (MF.subgroupOf D).index = Nat.card U := by
    have hidx := hMFUcompSub.symm.index_eq_card
    simpa [natCard_subgroupOf_eq U D hUleD] using hidx
  have hMFsubM_le_DsubM : MF.subgroupOf M ≤ D.subgroupOf M := by
    intro x hx
    simpa [Subgroup.mem_subgroupOf, D] using
      hMFleD (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hrel_eq :
      (MF.subgroupOf M).relIndex (D.subgroupOf M) = (MF.subgroupOf D).index := by
    rw [Subgroup.relIndex_subgroupOf (H := MF) (K := D) (L := M) hDleM]
    rw [← Subgroup.relIndex_subgroupOf (H := MF) (K := D) (L := D) le_rfl]
    have hDsubtop : D.subgroupOf D = ⊤ := Subgroup.subgroupOf_eq_top.2 le_rfl
    rw [hDsubtop]
    exact Subgroup.relIndex_top_right (MF.subgroupOf D)
  have hcardU_dvd_indexMF : Nat.card U ∣ (MF.subgroupOf M).index := by
    refine ⟨(D.subgroupOf M).index, ?_⟩
    rw [← hindexMF_D, ← hrel_eq]
    exact (Subgroup.relIndex_mul_index hMFsubM_le_DsubM).symm
  have hDindex_eq_cardW1 : (D.subgroupOf M).index = Nat.card W1 := by
    simpa [D, Subgroup.relIndex] using hW1card.symm
  have hcardW1_dvd_indexMF : Nat.card W1 ∣ (MF.subgroupOf M).index := by
    refine ⟨(MF.subgroupOf M).relIndex (D.subgroupOf M), ?_⟩
    rw [← hDindex_eq_cardW1, Nat.mul_comm]
    exact (Subgroup.relIndex_mul_index hMFsubM_le_DsubM).symm
  have hcopMFindex : Nat.Coprime (Nat.card MF) (MF.subgroupOf M).index := by
    simpa [natCard_subgroupOf_eq MF M hMFleM] using hMFhall.card_coprime_index
  have hcopU : Nat.Coprime (Nat.card MF) (Nat.card U) :=
    Nat.Coprime.coprime_dvd_right hcardU_dvd_indexMF hcopMFindex
  have hcopW1 : Nat.Coprime (Nat.card MF) (Nat.card W1) :=
    Nat.Coprime.coprime_dvd_right hcardW1_dvd_indexMF hcopMFindex
  have hcopProd : Nat.Coprime (Nat.card MF) (Nat.card U * Nat.card W1) :=
    hcopU.mul_right hcopW1
  simpa [hcardUW] using hcopProd

private theorem theorem_9_3_frobenius_action_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      section12FrobeniusJoinWithKernel U W1 := by
  classical
  intro h92
  have h92full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  have h92W1 : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := by
    exact hypothesis_9_2_with_card_W1_sec9 h92
  have hW1prime : Nat.Prime (Nat.card W1) :=
    nat_card_W1_prime_of_hypothesis_9_2_sec9 M MF U W1 W2 h92W1
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhallD, hMFleD, hcompD, _hnil, hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, hW2le, _hW2ne, _hW2cyc,
      hcentralizer, _hhat, _hprimeCentralizer⟩
  rcases hcompD with ⟨_hMFleDcomp, hUleD, _hD_eq, hMFUdisj⟩
  rcases h92.typeIIToIVSourceCondition with ⟨hUneBot, _hW1primeOrder, _hTI⟩
  let S : Subgroup G := U ⊔ W1
  have hW1leNormU : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).1
  have hUnormalS : (U.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := U) (K := S) (by simp [S])).2
    simpa [S] using sup_le Subgroup.le_normalizer hW1leNormU
  have hUWcomp : section12ComplementIn S U W1 := by
    simpa [S] using
      section12ComplementIn_U_sup_W1_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92full
  have hUWdisj : Disjoint U W1 := hUWcomp.2.2.2
  have hUWdisjSub : Disjoint (U.subgroupOf S) (W1.subgroupOf S) := by
    rw [disjoint_iff] at hUWdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ W1 := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf, S] using hx.1,
          by simpa [Subgroup.mem_subgroupOf, S] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hUWdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hUWsupTop :
      U.subgroupOf S ⊔ W1.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := W1) (B := S)
      (by simp [S]) (by simp [S])]
    exact Subgroup.subgroupOf_eq_top.2 (by simp [S])
  have hUWcompSub : (U.subgroupOf S).IsComplement' (W1.subgroupOf S) := by
    letI : (U.subgroupOf S).Normal := hUnormalS
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf S) (W1.subgroupOf S) hUWdisjSub hUWsupTop
  have hUsub_ne : U.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hUneBot
    have hcard :
        Nat.card (U.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := U.subgroupOf S)).1 hbot
    have hcardU : Nat.card U = 1 := by
      rw [natCard_subgroupOf_eq U S (by simp [S])] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := U)).2 hcardU
  have hW1_ne_bot : W1 ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card W1 = 1 := by
      simp [hbot]
    exact hW1prime.ne_one hcard1
  have hW1sub_ne : W1.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hW1_ne_bot
    have hcard :
        Nat.card (W1.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := W1.subgroupOf S)).1 hbot
    have hcardW1 : Nat.card W1 = 1 := by
      rw [natCard_subgroupOf_eq W1 S (by simp [S])] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := W1)).2 hcardW1
  have hcent :
      ∀ x : W1.subgroupOf S, x ≠ 1 →
        elementCentralizerIn (U.subgroupOf S) (x : S) = ⊥ := by
    intro x hxne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyParts :
        y ∈ U.subgroupOf S ∧
          y ∈ Subgroup.centralizer ({(x : S)} : Set S) := by
      simpa [elementCentralizerIn] using hy
    let xG : G := ((x : S) : G)
    have hxW1 : xG ∈ W1 := by
      simpa [xG] using (Subgroup.mem_subgroupOf.mp x.property : ((x : S) : G) ∈ W1)
    have hxGne : xG ≠ 1 := by
      intro hxG
      apply hxne
      ext
      exact hxG
    have hyU : (y : G) ∈ U := by
      simpa [Subgroup.mem_subgroupOf, S] using hyParts.1
    have hyDer : (y : G) ∈ ambientDerivedSubgroup M := hUleD hyU
    have hcentx : elementCentralizerIn (ambientDerivedSubgroup M) xG = W2 :=
      hcentralizer xG hxW1 hxGne
    have hyCommS : (y : S) * (x : S) = (x : S) * (y : S) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyParts.2
    have hyCommG : (y : G) * xG = xG * (y : G) := by
      simpa [xG] using congrArg Subtype.val hyCommS
    have hyCentX : (y : G) ∈ Subgroup.centralizer ({xG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz_eq : z = xG := by simpa using hz
      subst z
      exact hyCommG.symm
    have hyElem : (y : G) ∈ elementCentralizerIn (ambientDerivedSubgroup M) xG := by
      simpa [elementCentralizerIn] using And.intro hyDer hyCentX
    have hyW2 : (y : G) ∈ W2 := by
      simpa [hcentx] using hyElem
    have hyMF : (y : G) ∈ MF := hW2le hyW2
    have hyBot : (y : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hMFUdisj) hyMF hyU
    ext
    simpa using hyBot
  exact (lemma_3_1 (G := S) (K := U.subgroupOf S) (R := W1.subgroupOf S)
    hUsub_ne hW1sub_ne hUnormalS hUWcompSub).2 hcent

private theorem theorem_9_3_typeIIIIV_centralizer_eq_bot_of_W2_prime_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      Nat.Prime (Nat.card W2) →
        subgroupCentralizerIn MF (U ⊔ W1) = ⊥ := by
  classical
  intro h92 hW2prime
  by_contra hCUE_ne_bot
  let CUE : Subgroup G := subgroupCentralizerIn MF (U ⊔ W1)
  have hCW1 : subgroupCentralizerIn MF W1 = W2 :=
    subgroupCentralizerIn_W1_eq_W2_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hCUE_le_W2 : CUE ≤ W2 := by
    intro x hx
    have hxCW1 : x ∈ subgroupCentralizerIn MF W1 :=
      subgroupCentralizerIn_sup_le_right_sec9 MF U W1 (by simpa [CUE] using hx)
    simpa [hCW1] using hxCW1
  have hCUE_eq_W2 : CUE = W2 := by
    let Csub : Subgroup W2 := CUE.subgroupOf W2
    haveI : Fact (Nat.card W2).Prime := ⟨hW2prime⟩
    have hCsub_ne_bot : Csub ≠ ⊥ := by
      intro hbot
      apply hCUE_ne_bot
      apply le_antisymm
      · intro x hxCUE
        have hxCsub : (⟨x, hCUE_le_W2 hxCUE⟩ : W2) ∈ Csub := by
          simpa [Csub, Subgroup.mem_subgroupOf] using hxCUE
        have hxBot : (⟨x, hCUE_le_W2 hxCUE⟩ : W2) ∈ (⊥ : Subgroup W2) := by
          simpa [hbot] using hxCsub
        simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxBot)
      · exact bot_le
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card Csub with hbot | htop
    · exact False.elim (hCsub_ne_bot hbot)
    · apply le_antisymm
      · exact hCUE_le_W2
      · intro x hxW2
        have hxCsub : (⟨x, hxW2⟩ : W2) ∈ Csub := by
          simp [htop]
        simpa [Csub, CUE, Subgroup.mem_subgroupOf] using hxCsub
  have hCUEeq : subgroupCentralizerIn MF (U ⊔ W1) = W2 := by
    simpa [CUE] using hCUE_eq_W2
  have hfrobUW1 : section12FrobeniusJoinWithKernel U W1 :=
    theorem_9_3_frobenius_action_source_core_sec9 M MF U W1 W2 q h92
  have hcompUW1 : section12ComplementIn (U ⊔ W1) U W1 :=
    section12ComplementIn_U_sup_W1_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hcop : Nat.Coprime (Nat.card MF) (Nat.card (U ⊔ W1 : Subgroup G)) :=
    nat_card_MF_coprime_U_sup_W1_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  rcases theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92 with
    ⟨hnormMF, hsolvMF⟩
  have haction : frobeniusActionData (U ⊔ W1) U W1 MF :=
    ⟨hcompUW1, hfrobUW1, hnormMF, hsolvMF, hcop⟩
  have h91 := theorem_9_1 (U ⊔ W1) U W1 MF haction
  have hcard_eq :
      Nat.card W2 ^ Nat.card W1 * Nat.card MF =
        Nat.card W2 ^ Nat.card W1 * Nat.card (subgroupCentralizerIn MF U) := by
    simpa [hCUEeq, hCW1] using h91.1
  have hfactor_pos : 0 < Nat.card W2 ^ Nat.card W1 :=
    pow_pos (Nat.card_pos (α := W2)) (Nat.card W1)
  have hCU_card_eq :
      Nat.card (subgroupCentralizerIn MF U) = Nat.card MF :=
    (Nat.eq_of_mul_eq_mul_left hfactor_pos hcard_eq).symm
  have hCUMF : subgroupCentralizerIn MF U = MF :=
    subgroupCentralizerIn_eq_left_of_card_eq_sec9 MF U hCU_card_eq
  have hPsource := h92.typePDefinitionData
  have hIItoIV := h92.typeIIToIVSourceCondition
  have hPsource_full : Section8.typePDefinitionData M MF U W1 W2 := hPsource
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hUM : U ≤ M :=
    hUleD.trans (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hU_le_CMF : U ≤ subgroupCentralizerIn M MF := by
    intro u hu
    have huM : u ∈ M := hUM hu
    have huCentMF : u ∈ Subgroup.centralizer (MF : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hzMF
      have hzCU : z ∈ subgroupCentralizerIn MF U := by
        simpa [hCUMF] using hzMF
      have hzParts : z ∈ MF ∧ z ∈ Subgroup.centralizer (U : Set G) := by
        simpa [subgroupCentralizerIn] using hzCU
      have hzCentU : z ∈ Subgroup.centralizer (U : Set G) := hzParts.2
      rw [Subgroup.mem_centralizer_iff] at hzCentU
      exact (hzCentU u hu).symm
    simpa [subgroupCentralizerIn] using And.intro huM huCentMF
  exact ((Section8.theorem_8_5_b M MF U W1 W2 hPsource_full).2 hIItoIV.1)
    hU_le_CMF

private theorem section16NonidentityElements_nonempty_of_subgroup_ne_bot_sec9
    {G : Type u} [Group G] [Finite G]
    {U : Subgroup G} :
    U ≠ ⊥ → (section16NonidentityElements (U : Set G)).Nonempty := by
  intro hUne
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hUne with ⟨u, hu_ne⟩
  exact ⟨(u : G), u.property, by
    intro h
    exact hu_ne (Subtype.ext h)⟩

private theorem section16CentralizerInSet_nonidentity_ne_bot_of_subgroupCentralizerIn_ne_bot_sec9
    {G : Type u} [Group G] [Finite G]
    (MF U : Subgroup G) :
    subgroupCentralizerIn MF U ≠ ⊥ →
      section16CentralizerInSet MF (section16NonidentityElements (U : Set G)) ≠ ⊥ := by
  intro hCU
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCU with ⟨y, hy_ne⟩
  let yX : section16CentralizerInSet MF (section16NonidentityElements (U : Set G)) :=
    ⟨(y : G), by
      have hyMF : (y : G) ∈ MF := y.property.1
      have hyCentU : (y : G) ∈ Subgroup.centralizer (U : Set G) := y.property.2
      have hyCentNonid :
          (y : G) ∈ Subgroup.centralizer (section16NonidentityElements (U : Set G)) := by
        rw [Subgroup.mem_centralizer_iff] at hyCentU ⊢
        intro z hz
        exact hyCentU z hz.1
      exact ⟨hyMF, hyCentNonid⟩⟩
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨yX, ?_⟩
  intro hyX
  exact hy_ne (Subtype.ext (by simpa [yX] using congrArg Subtype.val hyX))

private theorem normalizer_nonidentityElements_le_of_subgroup_sec9
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (section16NonidentityElements (U : Set G)) := by
  intro g hg
  change ∀ y : G, y ∈ section16NonidentityElements (U : Set G) ↔
    g * y * g⁻¹ ∈ section16NonidentityElements (U : Set G)
  intro y
  constructor
  · intro hy
    rcases hy with ⟨hyU, hyne⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg y).1 hyU, ?_⟩
    intro h1
    apply hyne
    have h : g⁻¹ * (g * y * g⁻¹) * g = g⁻¹ * 1 * g := by rw [h1]
    simpa [mul_assoc] using h
  · intro hy
    rcases hy with ⟨hyU, hyne⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg y).2 hyU, ?_⟩
    intro h1
    exact hyne (by simp [h1])

private theorem maximal_normalizer_eq_self_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    Subgroup.normalizer (M : Set G) = M := by
  classical
  have hMsigma_ne : section10Msigma M ≠ ⊥ := theorem_10_2_e (G := G) hM
  have hMsigmaSub_ne : section10MsigmaSubgroup M ≠ ⊥ := by
    intro hbot
    exact hMsigma_ne (by simp [section10Msigma, hbot])
  have hnorm :=
    section10_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
      (G := G) hM (N := section10MsigmaSubgroup M) hMsigmaSub_ne
  have hnormSigma :
      Subgroup.normalizer (section10Msigma M : Set G) = M := by
    simpa [section10Msigma] using hnorm
  apply le_antisymm
  · intro g hgNormM
    have hle :
        Subgroup.normalizer (M : Set G) ≤
          Subgroup.normalizer
            (((section10MsigmaSubgroup M : Subgroup M).map M.subtype : Subgroup G) : Set G) :=
      section9_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) (H := M) (K := section10MsigmaSubgroup M)
    have hgNormSigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) := by
      simpa [section10Msigma] using hle hgNormM
    simpa [hnormSigma] using hgNormSigma
  · exact Subgroup.le_normalizer

private theorem theorem_9_3_typeII_canonical_unique_maximal_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF K U : Subgroup G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeII M MF) :
    ∀ X : Subgroup G, X ≤ U → X ≠ ⊥ →
      subgroupCentralizerIn MF X ≠ ⊥ →
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (X : Set G)) = {M} := by
  have hTypeData :=
    section16_typeII_canonical_caseP2_data
      (G := G) hM hMF hKU hType
  rcases hTypeData with
    ⟨_hCommon, _hExtra, _hUcomm, _hUne, _hNormNotLe, hMF_eq_msigma⟩
  have hB4 :=
    (theorem_16_B (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU).2.2.2.1
  intro X hXU hXne hCentXne
  have hCentXneSigma :
      subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
    simpa [hMF_eq_msigma] using hCentXne
  exact hB4 X hXU hXne hCentXneSigma

private theorem theorem_9_3_typeII_normalizer_of_fixed_source_condition_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U : Subgroup G)
    (hUne : U ≠ ⊥)
    (hUleD : U ≤ ambientDerivedSubgroup M)
    (hsource : ∀ A : Set G, A.Nonempty → A ⊆ ambientDerivedSubgroup M →
      A ⊆ section16NonidentityElements (U : Set G) →
        section16CentralizerInSet MF A ≠ ⊥ → Subgroup.normalizer A ≤ M) :
    subgroupCentralizerIn MF U ≠ ⊥ →
      Subgroup.normalizer (U : Set G) ≤ M := by
  intro hCU
  have hXne : (section16NonidentityElements (U : Set G)).Nonempty :=
    section16NonidentityElements_nonempty_of_subgroup_ne_bot_sec9 hUne
  have hXleD : section16NonidentityElements (U : Set G) ⊆ ambientDerivedSubgroup M := by
    intro x hx
    exact hUleD hx.1
  have hCXne :
      section16CentralizerInSet MF (section16NonidentityElements (U : Set G)) ≠ ⊥ :=
    section16CentralizerInSet_nonidentity_ne_bot_of_subgroupCentralizerIn_ne_bot_sec9
      MF U hCU
  exact (normalizer_nonidentityElements_le_of_subgroup_sec9 U).trans
    (hsource (section16NonidentityElements (U : Set G)) hXne hXleD subset_rfl hCXne)

private theorem theorem_9_3_typeII_fixed_subset_normalizer_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      section16TypeII M MF →
        ∀ A : Set G, A.Nonempty →
          A ⊆ ambientDerivedSubgroup M →
            A ⊆ section16NonidentityElements (U : Set G) →
              section16CentralizerInSet MF A ≠ ⊥ → Subgroup.normalizer A ≤ M := by
  intro h92 hII A hAne _hAD hAnon hCentNe
  have hM := h92.maximal
  have hMF := h92.mf
  have hPsource := h92.typePDefinitionData
  have hPsource_full := hPsource
  rcases hPsource with
    ⟨_hMFsrc, _hW1cyc, _hW1ne, _hW1hall, _hCompMW1, _hUleD, _hUnil,
      _hW1normU, hCompU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hHatW⟩
  rcases Section8.sourceTypeP_exists_KUData_of_aligned_complement
      (G := G) hM hPsource_full with ⟨Uc, hKU⟩
  have hCaseP2 : section16CaseP2 W1 Uc :=
    ((proposition_16_1 (G := G) (M := M) (MF := MF) (K := W1) (U := Uc)
      hM hMF hKU).2.1).mp hII
  rcases hCaseP2 with ⟨hW1ne, hUcne⟩
  have hTypeData :=
    section16_typeII_canonical_caseP2_data
      (G := G) hM hMF hKU hII
  rcases hTypeData with
    ⟨_hCommon, _hExtra, _hUcomm, _hUcne, _hNormNotLe, hMF_eq_msigma⟩
  rcases section16_conjugate_ambient_complement_of_caseP2
      (G := G) (M := M) (MF := MF) (K := W1) (U := Uc) (V := U)
      hM hMF hKU hW1ne hUcne hCompU with
    ⟨d, hUconj⟩
  have hdM : (d : G) ∈ M :=
    (section12_ambientDerivedSubgroup_le (G := G) (E := M)) d.property
  let X : Subgroup G := Subgroup.closure A
  have hXU : X ≤ U := by
    refine (Subgroup.closure_le (K := U)).2 ?_
    intro x hxA
    exact (hAnon hxA).1
  have hXne : X ≠ ⊥ := by
    rcases hAne with ⟨x, hxA⟩
    have hxne : x ≠ 1 := (hAnon hxA).2
    have hxX : x ∈ X := Subgroup.subset_closure hxA
    intro hXbot
    exact hxne (by simpa [X, hXbot] using hxX)
  have hCentXne : subgroupCentralizerIn MF X ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCentNe with ⟨yC, hyCne⟩
    let y : G := yC
    have hyMF : y ∈ MF := yC.property.1
    have hyCentA : y ∈ Subgroup.centralizer A := yC.property.2
    have hyCentX : y ∈ Subgroup.centralizer (X : Set G) := by
      simpa [X, Subgroup.centralizer_closure] using hyCentA
    let yX : subgroupCentralizerIn MF X := ⟨y, hyMF, hyCentX⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨yX, ?_⟩
    intro hyXone
    exact hyCne (Subtype.ext (by
      simpa [yX, y] using congrArg Subtype.val hyXone))
  let Y : Subgroup G := X.conjBy (d : G)⁻¹
  have hUc_back : U.conjBy (d : G)⁻¹ = Uc := by
    rw [hUconj]
    exact Subgroup.conjBy_inv Uc (d : G)
  have hYUc : Y ≤ Uc := by
    intro y hy
    have hyUconj : y ∈ U.conjBy (d : G)⁻¹ := by
      rcases Subgroup.mem_map.mp hy with ⟨x, hxX, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, hXU hxX, rfl⟩
    simpa [Y, hUc_back] using hyUconj
  have hYne : Y ≠ ⊥ := by
    simpa [Y] using
      (section11_conjBy_ne_bot (G := G) (H := X) (g := (d : G)⁻¹) hXne)
  have hdNormSigma : (d : G) ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section12_le_normalizer_msigma (M := M) hdM
  have hdinvNormSigma :
      (d : G)⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    (Subgroup.normalizer _).inv_mem hdNormSigma
  have hCentYSigma :
      subgroupCentralizerIn (section10Msigma M) Y ≠ ⊥ := by
    change subgroupCentralizerIn (section10Msigma M) (X.conjBy (d : G)⁻¹) ≠ ⊥
    rw [section11_subgroupCentralizerIn_conjBy_eq_self_of_mem_normalizer
      hdinvNormSigma]
    have hCentXneSigma :
        subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
      simpa [hMF_eq_msigma] using hCentXne
    exact section11_conjBy_ne_bot (G := G)
      (H := subgroupCentralizerIn (section10Msigma M) X) (g := (d : G)⁻¹)
      hCentXneSigma
  have hCentY : subgroupCentralizerIn MF Y ≠ ⊥ := by
    simpa [hMF_eq_msigma] using hCentYSigma
  have huniqY :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer (Y : Set G)) = {M} :=
    theorem_9_3_typeII_canonical_unique_maximal_sec9
      M MF W1 Uc hM hMF hKU hII Y hYUc hYne hCentY
  have hYconj : Y.conjBy (d : G) = X := by
    simpa [Y] using (Subgroup.conjBy_inv' X (d : G))
  have hMconj : M.conjBy (d : G) = M :=
    section11_conjBy_eq_of_mem_normalizer (H := M) (Subgroup.le_normalizer hdM)
  have huniqX :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer (X : Set G)) = {M} := by
    have hConj :=
      section16_maximalSubgroupsContaining_centralizer_conjBy
        (G := G) (X := Y) (M := M) hM (d : G) huniqY
    simpa [hYconj, hMconj] using hConj
  intro g hgNormA
  have hconj_le_of_mem_normalizer :
      ∀ {g : G}, g ∈ Subgroup.normalizer A → X.conjBy g ≤ X := by
    intro g hgNorm
    change ∀ z : G, z ∈ A ↔ g * z * g⁻¹ ∈ A at hgNorm
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hzX, rfl⟩
    change g * z * g⁻¹ ∈ X
    exact
      Subgroup.closure_induction (k := A)
        (p := fun z _hz => g * z * g⁻¹ ∈ X)
        (mem := by
          intro z hzA
          exact Subgroup.subset_closure ((hgNorm z).1 hzA))
        (one := by simp [X])
        (mul := by
          intro z w _hzA _hwA hzX hwX
          simpa [mul_assoc] using X.mul_mem hzX hwX)
        (inv := by
          intro z _hzA hzX
          simpa [mul_assoc] using X.inv_mem hzX)
        hzX
  have hgX : X.conjBy g = X := by
    apply le_antisymm
    · exact hconj_le_of_mem_normalizer hgNormA
    · have hginv : g⁻¹ ∈ Subgroup.normalizer A := Subgroup.inv_mem _ hgNormA
      simpa using
        (section10_le_conjBy_inv_of_conjBy_le
          (H := X) (K := X) (a := g⁻¹)
          (hconj_le_of_mem_normalizer hginv))
  have huniqX_from_g :
      section9MaximalSubgroupsContaining
        (Subgroup.centralizer (X : Set G)) = {M.conjBy g} := by
    have hConj :=
      section16_maximalSubgroupsContaining_centralizer_conjBy
        (G := G) (X := X) (M := M) hM g huniqX
    simpa [hgX] using hConj
  have hMg_mem :
      M.conjBy g ∈
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (X : Set G)) := by
    simp [huniqX_from_g]
  have hMg_eq_M : M.conjBy g = M := by
    have hsingle : M.conjBy g ∈ ({M} : Set (Subgroup G)) := by
      simpa [huniqX] using hMg_mem
    simpa using hsingle
  have hgNormM : g ∈ Subgroup.normalizer M :=
    section10_mem_normalizer_of_conjBy_eq (G := G) hMg_eq_M
  simpa [maximal_normalizer_eq_self_sec9 (G := G) hM] using hgNormM

private theorem theorem_9_3_nat_prime_card_of_section16HasPrimeOrder_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    section16HasPrimeOrder H → Nat.Prime (Nat.card H) := by
  rintro ⟨p, hp⟩
  rw [hp]
  exact p.property

private theorem theorem_9_3_typeIIIIV_W2_prime_order_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (section16TypeIII M MF ∨ section16TypeIV M MF) →
        section16HasPrimeOrder W2 := by
  intro h92 hIIIIV
  have h92_fixed := h92
  have h92W1 : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) := by
    exact hypothesis_9_2_with_card_W1_sec9 h92
  have hW1prime : Nat.Prime (Nat.card W1) :=
    nat_card_W1_prime_of_hypothesis_9_2_sec9 M MF U W1 W2 h92W1
  have hM := h92.maximal
  have hMF := h92.mf
  have hPsource := h92.typePDefinitionData
  have hW1ne : W1 ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card W1 = 1 := by
      simp [hbot]
    exact hW1prime.ne_one hcard1
  rcases Section8.sourceTypeP_exists_KUData_of_aligned_complement
      (G := G) hM hPsource with ⟨Uc, hKU⟩
  have hCaseP1 :
      section16CaseP1 W1 Uc ∧ MF ≠ section10Msigma M :=
    ((proposition_16_1 (G := G) (M := M) (MF := MF) (K := W1) (U := Uc)
      hM hMF hKU).2.2.1).mp hIIIIV
  have hUc_bot : Uc = ⊥ := hCaseP1.1.2
  have hC : section16TheoremCConclusions M MF W1 Uc :=
    theorem_16_C (G := G) hM hMF hKU hCaseP1.1.1
  rcases hC with
    ⟨_hUcomm, _hNormUNotLeM, _hKstarCyclic, _hKstarPos, _hKstarMF,
      _hMFnotCyclic, _hDerEq, _hKstarSecond, _Mstar, _hMstarP, _hUnique, _hKeq,
      _hKstarHall, _hPrimeX, _hPrimeY, _hInter, _hProd, _hZcyc, _hCase,
      _hCover, _hHatTI, _hHatEq, _hHatTISubset, _hKprimeIfUne,
      hKstarPrimeIfBot⟩
  have hCommon :
      ∃ V : Subgroup G, section16TypeCommon M MF V W1 (section16Kstar M W1) :=
    section16_exists_typeCommon_of_K_ne_bot (G := G) hM hMF hKU hCaseP1.1.1
  rcases hCommon with ⟨V, hCommon⟩
  have hCW1_kstar :
      subgroupCentralizerIn MF W1 = section16Kstar M W1 :=
    subgroupCentralizerIn_W1_eq_Kstar_of_typeCommon_sec9
      M MF V W1 (section16Kstar M W1) hW1prime hCommon
  have hCW1_fixed :
      subgroupCentralizerIn MF W1 = W2 :=
    subgroupCentralizerIn_W1_eq_W2_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92_fixed
  have hKstar_eq_W2 : section16Kstar M W1 = W2 := by
    rw [← hCW1_kstar, hCW1_fixed]
  simpa [hKstar_eq_W2] using hKstarPrimeIfBot hUc_bot

private theorem theorem_9_3_typeIIIIV_W2_prime_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (section16TypeIII M MF ∨ section16TypeIV M MF) →
        Nat.Prime (Nat.card W2) := by
  intro h92 hIIIIV
  exact theorem_9_3_nat_prime_card_of_section16HasPrimeOrder_sec9 W2
    (theorem_9_3_typeIIIIV_W2_prime_order_source_bridge_sec9
      M MF U W1 W2 q h92 hIIIIV)

private theorem theorem_9_3_branch_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      ((section16TypeII M MF → ∀ A : Set G, A.Nonempty →
          A ⊆ ambientDerivedSubgroup M →
            A ⊆ section16NonidentityElements (U : Set G) →
              section16CentralizerInSet MF A ≠ ⊥ → Subgroup.normalizer A ≤ M) ∧
        ((section16TypeIII M MF ∨ section16TypeIV M MF) →
          Nat.Prime (Nat.card W2))) := by
  intro h92
  exact
    ⟨theorem_9_3_typeII_fixed_subset_normalizer_source_bridge_sec9
        M MF U W1 W2 q h92,
      theorem_9_3_typeIIIIV_W2_prime_source_bridge_sec9
        M MF U W1 W2 q h92⟩

private theorem theorem_9_3_branch_centralizer_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (section16TypeII M MF → subgroupCentralizerIn MF U = ⊥) ∧
      ((section16TypeIII M MF ∨ section16TypeIV M MF) →
        ∃ p : ℕ,
          Nat.Prime p ∧
            Nat.card W2 = p ∧
            subgroupCentralizerIn MF (U ⊔ W1) = ⊥) := by
  classical
  intro h92
  have h92full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  have hPsource := h92.typePDefinitionData
  have hIIsource := h92.typeIISource
  rcases h92.typeIIToIVSourceCondition with ⟨hUne, _hW1prime, _hTIfit⟩
  rcases hPsource with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD, _hUnil, _hW1normU,
      _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  rcases theorem_9_3_branch_source_bridge_sec9 M MF U W1 W2 q h92full with
    ⟨hII812b, hIIIIV⟩
  constructor
  · intro hII
    rcases hIIsource hII with ⟨_hUcomm, hnotNormalizer, _hTypeF⟩
    by_contra hcentralizer_ne_bot
    exact hnotNormalizer
      (theorem_9_3_typeII_normalizer_of_fixed_source_condition_sec9 M MF U
        hUne hUleD (hII812b hII) hcentralizer_ne_bot)
  · intro hIIIIVbranch
    have hW2prime : Nat.Prime (Nat.card W2) := hIIIIV hIIIIVbranch
    exact ⟨Nat.card W2, hW2prime, rfl,
      theorem_9_3_typeIIIIV_centralizer_eq_bot_of_W2_prime_sec9
        M MF U W1 W2 q h92full hW2prime⟩

public theorem theorem_9_3_source_action_and_branch_facts_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      frobeniusActionData (U ⊔ W1) U W1 MF ∧
      (section16TypeII M MF → subgroupCentralizerIn MF U = ⊥) ∧
      ((section16TypeIII M MF ∨ section16TypeIV M MF) →
        ∃ p : ℕ,
          Nat.Prime p ∧
            Nat.card W2 = p ∧
            subgroupCentralizerIn MF (U ⊔ W1) = ⊥) := by
  intro h92
  have hfrobUW1 : section12FrobeniusJoinWithKernel U W1 :=
    theorem_9_3_frobenius_action_source_core_sec9 M MF U W1 W2 q h92
  have hcompUW1 : section12ComplementIn (U ⊔ W1) U W1 :=
    section12ComplementIn_U_sup_W1_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hcop : Nat.Coprime (Nat.card MF) (Nat.card (U ⊔ W1 : Subgroup G)) :=
    nat_card_MF_coprime_U_sup_W1_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  rcases theorem_9_3_action_normalizes_and_solvable_sec9
      M MF U W1 W2 q h92 with
    ⟨hnormMF, hsolvMF⟩
  rcases theorem_9_3_branch_centralizer_source_core_sec9
      M MF U W1 W2 q h92 with
    ⟨hII, hIIIIV⟩
  exact ⟨⟨hcompUW1, hfrobUW1, hnormMF, hsolvMF, hcop⟩, hII, hIIIIV⟩

public theorem theorem_9_3_source_facts_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (frobeniusActionData (U ⊔ W1) U W1 MF ∧
        subgroupCentralizerIn MF W1 = W2) ∧
      (section16TypeII M MF → subgroupCentralizerIn MF U = ⊥) ∧
      ((section16TypeIII M MF ∨ section16TypeIV M MF) →
        ∃ p : ℕ,
          Nat.Prime p ∧
            Nat.card W2 = p ∧
            subgroupCentralizerIn MF (U ⊔ W1) = ⊥) := by
  intro h92
  rcases theorem_9_3_source_action_and_branch_facts_sec9 M MF U W1 W2 q h92 with
    ⟨haction, hII, hIIIIV⟩
  exact ⟨⟨haction,
    subgroupCentralizerIn_W1_eq_W2_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92⟩,
    hII, hIIIIV⟩

public theorem theorem_9_3
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
    ((section16TypeII M MF →
      subgroupCentralizerIn MF U = ⊥ ∧ Nat.card MF = Nat.card W2 ^ q) ∧
    ((section16TypeIII M MF ∨ section16TypeIV M MF) →
      ∃ p : ℕ,
        Nat.Prime p ∧
          Nat.card W2 = p ∧
          subgroupCentralizerIn MF (U ⊔ W1) = ⊥ ∧
          Nat.card MF = p ^ q * Nat.card (subgroupCentralizerIn MF U))) := by
  intro h92
  have h92full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  rcases theorem_9_3_source_facts_sec9 M MF U W1 W2 q h92full with
    ⟨⟨haction, hCW1⟩, hII_CU, hIIIIV_facts⟩
  have h91 := theorem_9_1 (U ⊔ W1) U W1 MF haction
  constructor
  · intro hII
    have hCU : subgroupCentralizerIn MF U = ⊥ := hII_CU hII
    have hcard :
        Nat.card MF = Nat.card (subgroupCentralizerIn MF W1) ^ Nat.card W1 :=
      h91.2.2 hCU
    have hcardW2 : Nat.card MF = Nat.card W2 ^ Nat.card W1 := by
      simpa [hCW1] using hcard
    exact ⟨hCU, by simpa [h92.q_eq] using hcardW2⟩
  · intro hIIIIV
    rcases hIIIIV_facts hIIIIV with ⟨p, hp, hW2, hCUW1⟩
    have hcard :
        Nat.card MF =
          Nat.card W2 ^ Nat.card W1 * Nat.card (subgroupCentralizerIn MF U) := by
      simpa [hCUW1, hCW1] using h91.1
    exact ⟨p, hp, hW2, hCUW1, by simpa [hW2, h92.q_eq] using hcard⟩

end CFSG.Section9
