module

public import CFSG.Monster.GMS.CoTwoAutFinal
public import CFSG.Monster.GMS.ASegDefs
import CFSG.Monster.GMS.Griess13.ChecksUniqueness
import CFSG.Monster.GMS.Leech.Pairs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module hiding co1Act

namespace CoTwoAutSetup

variable {G : Type} [Group G] {t x : G}

theorem centInvAutInnerAt_of
    (L : LeechSystem t) (hx : x ∈ L.typeSet 0) (H : AutHyp x t)
    (hnorm : Co2NormalizerFact) : CentInvAutInnerAt x t := by
  show ∀ ψ : ↥(Xsub x t) ≃* ↥(Xsub x t), (∀ g : ↥(Xsub x t), (g : G) = x → ψ g = g) →
    (∀ g : ↥(Xsub x t), (g : G) = t → ψ g = g) →
      ∃ h ∈ Xsub x t, ∀ g : ↥(Xsub x t), (ψ g : G) = h * g * h⁻¹
  intro ψ hψx hψt
  have hxX : x ∈ Xsub x t := Rsub_le_Xsub L (x_mem_Rsub (t := t) hx.1)
  have htX : t ∈ Xsub x t := Rsub_le_Xsub L (t_mem_Rsub L hx.1)
  have hΨ := autOn_autMap (Xsub x t) ψ
  have hΨx : autMap (Xsub x t) ψ x = x := by
    rw [autMap_apply ψ hxX]
    exact congrArg Subtype.val (hψx ⟨x, hxX⟩ rfl)
  have hΨt : autMap (Xsub x t) ψ t = t := by
    rw [autMap_apply ψ htX]
    exact congrArg Subtype.val (hψt ⟨t, htX⟩ rfl)
  obtain ⟨h, hh, hΨh⟩ := inner_of_autOn L hx H hnorm hΨ hΨx hΨt
  refine ⟨h, hh, fun g => ?_⟩
  have h1 := hΨh g g.2
  rw [autMap_apply ψ g.2] at h1
  exact h1

end CoTwoAutSetup

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem centInvAutInnerTwoAB_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    CentInvAutInnerTwoAB a z₀ := by
  intro x t hx ht
  have ha : orderOf a = 2 := hG.1.1
  have hz : orderOf z₀ = 2 := hG.2.1
  have hcomm : x * t = t * x :=
    (mul_comm_of_mul_self (mul_self_eq_one_of_orderOf_two (orderOf_eq_two_of_isConj' ha hx))
      (mul_self_eq_one_of_orderOf_two (orderOf_eq_two_of_isConj' hz ht.1))
      (mul_self_eq_one_of_orderOf_two (orderOf_eq_two_of_isConj' ha ht.2))).symm
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨L⟩ := exists_leechSystem co1ModuleUniqueness (h.gms t ht.1)
  have hxQ : x ∈ leechQ t := h.mem_leechQ_of_isConj_mul hx ht.1 hcomm ht.2
  have hxL : x ∈ L.typeSet 0 := L.isLeechTwo_iff.mp (h.isLeechTwo_of_mem ht.1 hxQ hx)
  have hstruct := coTwoStructure_of I hG (coTwoPerfect_of I hG) x t hx ht.1 hcomm ht.2
  have hirr := coTwoIrreducible_of I hG x t hx ht.1 hcomm ht.2
  exact CoTwoAutSetup.centInvAutInnerAt_of L hxL ⟨hstruct.1, hstruct.2.1, hirr⟩ co2NormalizerFact

end CFSG.Monster.GMS
