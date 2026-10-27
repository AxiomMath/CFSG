module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.Quasithin.Background.BlueprintB2Thompson
public import CFSG.Walter.Bender1970.S2.OddFitting
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.Walter.Bender1970.S2.Subnormal
public import CFSG.Walter.Bender1970.S2.TwoSubgroup
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate43

public section

namespace CFSG

open CFSG CFSG.Open CFSG.Quasithin.BlueprintB2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hasNormalPComplement_of_elementary_selfcentralizing
    {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (E : Subgroup H) (hE : IsElemAbelian p E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set H), g ^ p = 1 → g ∈ E)
    (hNC : Subgroup.normalizer (E : Set H) = Subgroup.centralizer (E : Set H)) :
    HasNormalPComplement p H := by
  classical
  have hNHNP : HasNormalPComplement p ↥(Subgroup.normalizer (E : Set H)) := by
    let N : Subgroup H := Subgroup.normalizer (E : Set H)
    have hcen : ∀ x : N, orderOf x = p → x ∈ Subgroup.center N := by
      intro x hxord
      rw [Subgroup.mem_center_iff]
      intro y
      have hxN : (x : H) ∈ Subgroup.centralizer (E : Set H) := by
        rw [← hNC]
        exact x.2
      have hxpow : x ^ p = 1 := by
        rw [← hxord]
        exact pow_orderOf_eq_one x
      have hxpowH : (x : H) ^ p = 1 := by
        simpa using congrArg (fun z : N => (z : H)) hxpow
      have hxE : (x : H) ∈ E := hSC (x : H) hxN hxpowH
      have hyN : (y : H) ∈ Subgroup.centralizer (E : Set H) := by
        rw [← hNC]
        exact y.2
      have hyx : (x : H) * (y : H) = (y : H) * (x : H) :=
        (Subgroup.mem_centralizer_iff.mp hyN) (x : H) hxE
      exact Subtype.ext hyx.symm
    exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.hasNormalPComplement_of_central_order_p
      (K := N) hp2 hcen
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  let P0 : Subgroup H := (P : Subgroup H)
  let EP : Subgroup P0 := E.subgroupOf P0
  let C : Subgroup P0 := Subgroup.centralizer (EP : Set P0)
  have hEP' : E ≤ P0 := by simpa [P0] using hEP
  have hEPelem : IsElemAbelian p EP := hE.subgroupOf P0
  have hEPclass : CFSG.IsElementaryAbelian p EP :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hEPelem
  have hEPleC : EP ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxE : (x : H) ∈ E := Subgroup.mem_subgroupOf.mp hx
    have hyE : (y : H) ∈ E := Subgroup.mem_subgroupOf.mp hy
    have hcomm : (x : H) * (y : H) = (y : H) * (x : H) :=
      congrArg (fun z : E => (z : H))
        (hE.1.is_comm.comm ⟨(x : H), hxE⟩ ⟨(y : H), hyE⟩)
    exact Subtype.ext hcomm.symm
  have hEPchar : (EP.subgroupOf C).Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ x hx
    obtain ⟨y, hyH, rfl⟩ := Subgroup.mem_map.mp hx
    have hyEP : ((y : C) : P0) ∈ EP := Subgroup.mem_subgroupOf.mp hyH
    have hyE : (((y : C) : P0) : H) ∈ E := Subgroup.mem_subgroupOf.mp hyEP
    have hypowC : y ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hE.2 (((y : C) : P0) : H) hyE
    have hφpow : (φ y) ^ p = 1 := by
      rw [← map_pow, hypowC, map_one]
    have hφcentE : (((φ y : C) : P0) : H) ∈ Subgroup.centralizer (E : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have heEP : (⟨e, hEP' he⟩ : P0) ∈ EP := Subgroup.mem_subgroupOf.mpr he
      have hcent := (Subgroup.mem_centralizer_iff.mp (φ y).2)
        (⟨e, hEP' he⟩ : P0) heEP
      exact congrArg (fun z : P0 => (z : H)) hcent
    have hφE : (((φ y : C) : P0) : H) ∈ E :=
      hSC _ hφcentE (by
        simpa using congrArg (fun z : C => (((z : P0) : H))) hφpow)
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hφE)
  have hnormC_le : Subgroup.normalizer (C : Set P0) ≤ C := by
    have hcharMove := CFSG.Walter.normalizer_le_normalizer_map_of_characteristic
      (A := C) (D := EP.subgroupOf C)
    have hmap : (EP.subgroupOf C).map C.subtype = EP :=
      Subgroup.map_subgroupOf_eq_of_le hEPleC
    rw [hmap] at hcharMove
    refine hcharMove.trans ?_
    intro n hn
    have hnNormE : (n : H) ∈ Subgroup.normalizer (E : Set H) := by
      have hnSub : n ∈ (Subgroup.normalizer (E : Set H)).subgroupOf P0 := by
        rw [Subgroup.subgroupOf_normalizer_eq hEP']
        simpa [EP] using hn
      exact Subgroup.mem_subgroupOf.mp hnSub
    have hnCentE : (n : H) ∈ Subgroup.centralizer (E : Set H) := by
      rw [← hNC]
      exact hnNormE
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hcent := (Subgroup.mem_centralizer_iff.mp hnCentE) (e : H)
      (Subgroup.mem_subgroupOf.mp he)
    exact Subtype.ext hcent
  have hCtop : C = ⊤ := by
    haveI : Group.IsNilpotent P0 := IsPGroup.isNilpotent (P.isPGroup')
    have hnc : NormalizerCondition P0 := Group.normalizerCondition_of_isNilpotent
    by_contra hne
    have hlt : C < ⊤ := lt_top_iff_ne_top.mpr hne
    have hltN : C < Subgroup.normalizer (C : Set P0) := hnc C hlt
    exact (not_lt_of_ge hnormC_le) hltN
  have hpow_mem_EP : ∀ x : P0, x ^ p = 1 → x ∈ EP := by
    intro x hx
    have hxC : x ∈ C := by
      rw [hCtop]
      exact Subgroup.mem_top x
    have hxCentE : (x : H) ∈ Subgroup.centralizer (E : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have heEP : (⟨e, hEP' he⟩ : P0) ∈ EP := Subgroup.mem_subgroupOf.mpr he
      have hcent := (Subgroup.mem_centralizer_iff.mp hxC)
        (⟨e, hEP' he⟩ : P0) heEP
      exact congrArg (fun z : P0 => (z : H)) hcent
    have hxE : (x : H) ∈ E := hSC (x : H) hxCentE (by
      simpa using congrArg (fun z : P0 => (z : H)) hx)
    exact Subgroup.mem_subgroupOf.mpr hxE
  have hElem : elemThompson (P : Subgroup H) p = EP := by
    refine le_antisymm ?_ ?_
    · rw [elemThompson]
      refine sSup_le ?_
      intro A hA
      intro a ha
      have hAel : CFSG.IsElementaryAbelian p A := (mem_elemThompsonFamily_iff.mp hA).1
      letI : CFSG.IsElementaryAbelian p A := hAel
      exact hpow_mem_EP a (elemPow_eq_one_of_isElementaryAbelian a ha)
    · exact le_elemThompson (A := EP) (by
        rw [mem_elemThompsonFamily_iff]
        refine ⟨hEPclass, ?_⟩
        intro B hB
        have hBle : B ≤ EP := by
          letI : CFSG.IsElementaryAbelian p B := hB
          intro b hb
          exact hpow_mem_EP b (elemPow_eq_one_of_isElementaryAbelian b hb)
        exact Subgroup.card_le_of_le hBle)
  have hE_ZP : E ≤ (Subgroup.center P0).map P0.subtype := by
    intro e he
    refine Subgroup.mem_map.mpr ⟨⟨e, hEP' he⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro x
    have hxC : x ∈ C := by
      rw [hCtop]
      exact Subgroup.mem_top x
    have heEP : (⟨e, hEP' he⟩ : P0) ∈ EP := Subgroup.mem_subgroupOf.mpr he
    have hcent := (Subgroup.mem_centralizer_iff.mp hxC)
      (⟨e, hEP' he⟩ : P0) heEP
    exact hcent.symm
  let ZP : Subgroup H := (Subgroup.center P0).map P0.subtype
  have hC_HNP : HasNormalPComplement p ↥(Subgroup.centralizer (ZP : Set H)) := by
    have hle : Subgroup.centralizer (ZP : Set H) ≤ Subgroup.normalizer (E : Set H) := by
      intro x hx
      rw [hNC]
      exact Subgroup.centralizer_le (fun z hz => hE_ZP hz) hx
    exact CFSG.hasNormalPComplement_of_le p hle hNHNP
  have hN_HNP : HasNormalPComplement p ↥(Subgroup.normalizer
      (((elemThompson (P : Subgroup H) p).map P0.subtype : Subgroup H) : Set H)) := by
    have hmap : ((elemThompson (P : Subgroup H) p).map P0.subtype : Subgroup H) = E := by
      rw [hElem]
      exact Subgroup.map_subgroupOf_eq_of_le hEP'
    rw [hmap]
    exact hNHNP
  exact CFSG.RankThree.Coprime.thompson_elementary_normal_p_complement hp2 P hC_HNP hN_HNP

end CFSG
