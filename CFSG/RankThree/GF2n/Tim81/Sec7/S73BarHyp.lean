module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S73BarIso
import CFSG.Adapters.WholeGroupLayer
import CFSG.GroupTheory.Fitting.MulEquiv
import CFSG.RankThree.GF2n.Tim81.FStarSimple
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Split

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem generalizedFitting_barY_rOf (hD : L2Datum M V A B h) (h73a : Sec7.Stmt73alpha M V)
    (hOY : inSubgroup (pPrimeCore 2) (yOf h) = oOf M h) :
    generalizedFitting ↥(barY h (rOf M h)) = pCore 2 ↥(barY h (rOf M h)) := by
  obtain ⟨e, -⟩ := exists_barQuotEquiv h (inf_le_right : rOf M h ≤ yOf h)
    (subgroupOf_rOf_of_oddCore_eq hOY)
  rw [← CFSG.WholeGroup.generalizedFitting_map_mulEquiv e,
    (h73a A B h hD).2.2.2.2.2.1, pCore_map_iso 2 e]

theorem inSubgroup_pCore_barY_rOf (hS : Sec6Hyp M V) (hD : L2Datum M V A B h)
    (h73a : Sec7.Stmt73alpha M V) (hOY : inSubgroup (pPrimeCore 2) (yOf h) = oOf M h) :
    inSubgroup (pCore 2) (barY h (rOf M h)) = barY h (p0Of M V (A ⊔ B)) := by
  have hRY : rOf M h ≤ yOf h := inf_le_right
  obtain ⟨e, he⟩ := exists_barQuotEquiv h hRY (subgroupOf_rOf_of_oddCore_eq hOY)
  have hp : pCore 2 ↥(barY h (rOf M h)) =
      (((p0Of M V (A ⊔ B)).subgroupOf (rOf M h)).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h)))).map e.toMonoidHom := by
    rw [← (h73a A B h hD).2.2.2.2.2.2, pCore_map_iso 2 e]
  have h1 : inSubgroup (pCore 2) (barY h (rOf M h)) =
      (((p0Of M V (A ⊔ B)).subgroupOf (rOf M h)).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h)))).map
        ((barY h (rOf M h)).subtype.comp e.toMonoidHom) := by
    rw [inSubgroup, hp, Subgroup.map_map]
  have hcomp : ((barY h (rOf M h)).subtype.comp e.toMonoidHom).comp
      (QuotientGroup.mk' (pPrimeCore 2 ↥(rOf M h))) = barMap h hRY :=
    MonoidHom.ext fun k => he k
  rw [h1, Subgroup.map_map, hcomp,
    ← barY_eq_map_barMap h (L2Datum.p0_le_rOf hS hD) hRY]

theorem EpsIn.isMaximalTwoLocal_barY (hE : EpsIn M V h) :
    IsMaximalTwoLocal (barY h (rOf M h)) := by
  refine ⟨⟨barY h V, ?_, isPGroup_barY h hE.root.isPGroup_V, hE.normalizer_barY.symm⟩, ?_⟩
  · intro hbot
    have h1 := hE.card_barY_self
    rw [hbot, Subgroup.card_bot] at h1
    have := hE.root.four_le_card
    omega
  · rintro H hlt ⟨P, hP1, hP2, hH⟩
    have hPH : P ≤ inSubgroup (pCore 2) H :=
      le_inSubgroup_pCore (Subgroup.le_normalizer.trans hH.symm.le) hH.le hP2
    have hK : pCore 2 ↥H ≠ ⊥ := by
      intro hbot
      apply hP1
      rw [inSubgroup, hbot, Subgroup.map_bot] at hPH
      exact le_bot_iff.mp hPH
    exact not_le_of_gt hlt (hE.le_of_pCore_ne_bot hlt.le hK)

theorem EpsIn.le_barY_of_le_barY_p0 (hE : EpsIn M V h) (hS : Sec6Hyp M V)
    (hD : L2Datum M V A B h) (h72 : Sec7.Stmt72 M V n f) (h73g : Sec7.Stmt73gamma M V)
    {U : Subgroup (YBar h)} (hVU : barY h V ≤ U) (hUP : U ≤ barY h (p0Of M V (A ⊔ B)))
    (hRU : barY h (rOf M h) ≤ Subgroup.normalizer (U : Set (YBar h)))
    (hUc : IsMulCommutative U) : U ≤ barY h V := by
  have h72' := h72 A B h hD
  have hP0Y : p0Of M V (A ⊔ B) ≤ yOf h := (L2Datum.p0_le_rOf hS hD).trans inf_le_right
  have hVN : V ≤ p0Of M V (A ⊔ B) ⊓ preimY h U :=
    le_inf (L2Datum.V_le_p0 hS hD) ((barY_le_iff_le_preimY h hE.le_yOf).mp hVU)
  have hKN : M ⊓ cenOf (A ⊔ B) ≤
      Subgroup.normalizer ((p0Of M V (A ⊔ B) ⊓ preimY h U : Subgroup G) : Set G) := by
    intro y hy
    have hyR : y ∈ rOf M h := L2Datum.inf_cenOf_le_rOf hD hy
    exact mem_normalizer_inf (L2Datum.rOf_le_normalizer_p0 hS hD h72'.1 hyR)
      (mem_normalizer_preimY h hyR.2 (hRU ⟨⟨y, hyR.2⟩, Subgroup.mem_subgroupOf.mpr hyR, rfl⟩))
  rcases (h73g A B h hD).1 _ hVN inf_le_left hKN with hNV | hNP0
  · intro u hu
    obtain ⟨⟨p, hpY⟩, hpP, rfl⟩ := hUP hu
    have hpN : p ∈ p0Of M V (A ⊔ B) ⊓ preimY h U :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hpP, (mem_preimY_iff h).mpr ⟨hpY, hu⟩⟩
    rw [hNV] at hpN
    exact ⟨⟨p, hpY⟩, Subgroup.mem_subgroupOf.mpr hpN, rfl⟩
  · exfalso
    have hPU : barY h (p0Of M V (A ⊔ B)) ≤ U :=
      (barY_le_iff_le_preimY h hP0Y).mpr (hNP0.symm.le.trans inf_le_right)
    haveI := hUc
    have hP2 : IsPGroup 2 (p0Of M V (A ⊔ B)) :=
      (inSubgroup_pCore_two M).1.to_le (inf_le_left.trans inf_le_left)
    have hinj := hE.barMap_injective_of_disjoint hP0Y (hE.disjoint_oddCore_of_isPGroup hP2)
    have hcomm : ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqU : barMap h hP0Y ⟨q, hq⟩ ∈ U :=
        hPU ⟨⟨q, hP0Y hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
      have hpU : barMap h hP0Y ⟨p, hp⟩ ∈ U :=
        hPU ⟨⟨p, hP0Y hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
      have hu := mul_comm' (⟨_, hqU⟩ : ↥U) ⟨_, hpU⟩
      have hqp : (⟨q, hq⟩ : ↥(p0Of M V (A ⊔ B))) * ⟨p, hp⟩ =
          ⟨p, hp⟩ * ⟨q, hq⟩ :=
        hinj (by rw [map_mul, map_mul]; exact congrArg Subtype.val hu)
      exact congrArg Subtype.val hqp
    exact hE.root.ne_bot (h72'.2.2.1.symm.trans hcomm)

theorem EpsIn.maximal_barY (hE : EpsIn M V h) (hS : Sec6Hyp M V) (hD : L2Datum M V A B h)
    (h72 : Sec7.Stmt72 M V n f) (h73g : Sec7.Stmt73gamma M V)
    (hF : generalizedFitting ↥(barY h (rOf M h)) = pCore 2 ↥(barY h (rOf M h)))
    (hP : inSubgroup (pCore 2) (barY h (rOf M h)) = barY h (p0Of M V (A ⊔ B))) :
    Maximal (fun U : Subgroup (YBar h) => U ≤ barY h (rOf M h) ∧
      barY h (rOf M h) ≤ Subgroup.normalizer (U : Set (YBar h)) ∧ IsMulCommutative U)
      (barY h V) := by
  refine ⟨⟨barY_mono h hE.le_rOf, hE.normalizer_barY.symm.le,
    (isElemAbelian_barY h hE.root.elem).1⟩, ?_⟩
  rintro U ⟨hUR, hRU, hUc⟩ hVU
  exact hE.le_barY_of_le_barY_p0 hS hD h72 h73g hVU
    ((le_of_isMulCommutative_normal hF hUR hRU hUc).trans hP.le) hRU hUc

theorem Hyp.centralizer_generalizedFitting_eq_bot (hH : Hyp M V) (hV : 4 ≤ Nat.card V) :
    Subgroup.centralizer (generalizedFitting G : Set G) = ⊥ :=
  CFSG.Adapters.centralizer_generalizedFitting_eq_bot_of_isSimpleGroup G
    (hH.isSimpleGroup_generalizedFitting hV).1 (hH.isSimpleGroup_generalizedFitting hV).2

theorem EpsIn.hyp_barY (hE : EpsIn M V h) (hS : Sec6Hyp M V) (hD : L2Datum M V A B h)
    (h72 : Sec7.Stmt72 M V n f) (h73a : Sec7.Stmt73alpha M V) (h73g : Sec7.Stmt73gamma M V)
    (hOY : inSubgroup (pPrimeCore 2) (yOf h) = oOf M h) :
    Hyp (barY h (rOf M h)) (barY h V) := by
  have hF := generalizedFitting_barY_rOf hD h73a hOY
  exact
    { o2 := hE.pCore_yBar_eq_bot
      maxLocal := hE.isMaximalTwoLocal_barY
      fitting := hF
      maxAb := hE.maximal_barY hS hD h72 h73g hF (inSubgroup_pCore_barY_rOf hS hD h73a hOY)
      elem := isElemAbelian_barY h hE.root.elem
      ti := hE.isTI_barY }

end CFSG.RankThree.GF2n.Tim81
