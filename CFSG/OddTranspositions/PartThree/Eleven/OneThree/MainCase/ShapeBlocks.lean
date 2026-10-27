module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Coset
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.ShapeLocal
import CFSG.OddTranspositions.PartThree.EightSeven

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_conj_of_mem_dalphaStar (hC : HypothesisC D)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {p q k : G} (hp : p ∈ DalphaStar D hC.alpha)
    (hq : q ∈ DalphaStar D hC.alpha) (hpq : p ≠ q) (hc : Commute p q)
    (hk : k ∈ kBlock D hC.alpha) : Commute (k * p * k⁻¹) q := by
  let H := Halpha D hC.alpha
  let p' : H := ⟨p, Subgroup.subset_closure hp⟩
  let q' : H := ⟨q, Subgroup.subset_closure hq⟩
  have hpD : p ∈ D := (hC.DalphaStar_subset_commute hp).1
  have hqD : q ∈ D := (hC.DalphaStar_subset_commute hq).1
  have hp2 : p * p = 1 := hC.setup.oddT.mul_self_eq_one hpD
  obtain ⟨k', hk'K, hk'val⟩ := Subgroup.mem_map.mp hk
  have hk'val' : (k' : G) = k := hk'val
  have hQ : q' * p' ∉ CFSG.pCore 2 H := by
    intro hmem
    rw [hQ1] at hmem
    have h1 : q' * p' = 1 := Subgroup.mem_bot.mp hmem
    have h1' : q * p = 1 := by simpa [q', p'] using congrArg Subtype.val h1
    have hqp : q = p := by
      calc q = q * (p * p) := by rw [hp2, mul_one]
        _ = q * p * p := by group
        _ = p := by rw [h1', one_mul]
    exact hpq hqp.symm
  have hcp : Commute (q' : G) (p' : G) := by simpa [q', p'] using hc.symm
  have hcomm := commute_conj_of_mul_not_mem_pCore (hC := hC) (c := q') (v := p')
    hqD hpD hcp hQ hk'K
  simpa [q', p', hk'val'] using hcomm.symm

theorem not_commute_conj_of_mem_dalphaStar (hC : HypothesisC D)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {p k : G} (hp : p ∈ DalphaStar D hC.alpha)
    (hk : k ∈ kBlock D hC.alpha) (hne : k * p * k⁻¹ ≠ p) : ¬ Commute p (k * p * k⁻¹) := by
  intro hcomm
  let H := Halpha D hC.alpha
  let K := EightOne.twoOddCore H
  let p' : H := ⟨p, Subgroup.subset_closure hp⟩
  have hpD : p ∈ D := (hC.DalphaStar_subset_commute hp).1
  have hp2 : p' * p' = 1 := by
    apply Subtype.ext
    simpa [p'] using hC.setup.oddT.mul_self_eq_one hpD
  obtain ⟨k', hk'K, hk'val⟩ := Subgroup.mem_map.mp hk
  have hk'val' : (k' : G) = k := hk'val
  have hKnormal : K.Normal :=
    (CFSG.oddCore_normal (G := H ⧸ CFSG.pCore 2 H)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 H))
  let t : H := p' * (k' * p' * k'⁻¹)
  have htK : t ∈ K := by
    have h1 : p' * k' * p'⁻¹ ∈ K := hKnormal.conj_mem k' hk'K p'
    have h2 : k'⁻¹ ∈ K := K.inv_mem hk'K
    have h3 : (p' * k' * p'⁻¹) * k'⁻¹ ∈ K := K.mul_mem h1 h2
    convert h3 using 1
    rw [inv_eq_of_mul_eq_one_right hp2]
    simp only [t]
    group
  have htval : (t : G) = p * (k * p * k⁻¹) := by
    simp [t, p', hk'val']
  have hconjD : k * p * k⁻¹ ∈ D := by
    simpa [hk'val'] using hC.setup.normal k' p hpD
  have hord : orderOf (t : H) = 2 := by
    rw [← Subgroup.orderOf_coe t, htval]
    exact hC.setup.oddT.orderOf_mul_eq_two hpD hconjD hne.symm hcomm
  have hdvd : 2 ∣ Nat.card K := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard K htK
  exact (odd_card_twoOddCore hQ1).not_two_dvd_nat hdvd

section MemDalpha

variable {hC : HypothesisC D}


theorem MainHyp.mem_Dalpha_of_mem_of_commute (h : MainHyp hC) {β γ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha) {v c : G} (hv : v ∈ β)
    (hc : c ∈ γ) (hvc : v ≠ c) (hcomm : Commute v c) : γ ∈ Dalpha D β := by
  have hne : β ≠ γ := by
    intro heq
    have hcβ : c ∈ β := by rw [heq]; exact hc
    exact h.not_commute_of_mem_block hβ hv hcβ hvc hcomm
  exact mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha
    hβ.1 hγ.1 hne hv hc hcomm

end MemDalpha

theorem commute_of_four_point_dalphaStar (hC : HypothesisC D) {U : Type} [Group U] [Finite U]
    (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (φ : Halpha D hC.alpha ⧸ EightOne.twoOddCore (Halpha D hC.alpha) ≃*
      Multiplicative (ZMod 2) × U)
    (hQ1 : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {a a' b b' : G}
    (ha : a ∈ DalphaStar D hC.alpha) (ha' : a' ∈ DalphaStar D hC.alpha)
    (hb : b ∈ DalphaStar D hC.alpha) (hb' : b' ∈ DalphaStar D hC.alpha) (hab : Commute a b)
    (ha'b : Commute a' b) (hab' : Commute a b') (haa' : ¬ Commute a a')
    (hbb' : ¬ Commute b b') : Commute a' b' := by
  let H := Halpha D hC.alpha
  let aH : H := ⟨a, Subgroup.subset_closure ha⟩
  let aH' : H := ⟨a', Subgroup.subset_closure ha'⟩
  let bH : H := ⟨b, Subgroup.subset_closure hb⟩
  let bH' : H := ⟨b', Subgroup.subset_closure hb'⟩
  have haHF : aH ∈ DstarH hC := (mem_DstarH_iff hC).mpr ha
  have haH'F : aH' ∈ DstarH hC := (mem_DstarH_iff hC).mpr ha'
  have hbHF : bH ∈ DstarH hC := (mem_DstarH_iff hC).mpr hb
  have hbH'F : bH' ∈ DstarH hC := (mem_DstarH_iff hC).mpr hb'
  have habH : Commute aH bH := by
    show aH * bH = bH * aH
    exact Subtype.ext (by simpa [aH, bH] using hab.eq)
  have ha'bH : Commute aH' bH := by
    show aH' * bH = bH * aH'
    exact Subtype.ext (by simpa [aH', bH] using ha'b.eq)
  have hab'H : Commute aH bH' := by
    show aH * bH' = bH' * aH
    exact Subtype.ext (by simpa [aH, bH'] using hab'.eq)
  have haa'H : ¬ Commute aH aH' := fun hc => haa' (by simpa [aH, aH'] using hc.map H.subtype)
  have hbb'H : ¬ Commute bH bH' := fun hc => hbb' (by simpa [bH, bH'] using hc.map H.subtype)
  have hfour := commute_of_four_point (X := H) (F := DstarH hC) (p := shapeProj φ)
    (Nine.setup_DstarH hC) hU (shapeProj_surjective φ)
    (by rw [ker_shapeProj]; exact odd_card_twoOddCore hQ1)
    haHF haH'F hbHF hbH'F habH ha'bH hab'H haa'H hbb'H
  simpa [aH', bH'] using hfour.map H.subtype

end CFSG.OddTranspositions.PartThree.ElevenThree
