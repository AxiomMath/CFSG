module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7SylowInComponent
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_involutions_in_component
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∀ x : G, x ∈ w.M → IsInvolution x → x ∈ d.E := by
  classical
  let M : Subgroup G := w.M
  let E : Subgroup G := d.E
  obtain ⟨SM, _hSMcard, hSMleE⟩ :=
    secondCase_a7_sylow_le_component hmin c w d hA7 hmodel
  let Ei : Subgroup M := E.subgroupOf M
  have hSMleEi : (SM : Subgroup M) ≤ Ei := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hSMleE
      (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩))
  have hdiv : Ei.index ∣ (SM : Subgroup M).index :=
    Subgroup.index_dvd_of_le hSMleEi
  have hnot2 : ¬ 2 ∣ Ei.index := by
    intro h2
    exact SM.not_dvd_index (dvd_trans h2 hdiv)
  have hnotEven : ¬ Even Ei.index := by
    intro he
    exact hnot2 (Even.two_dvd he)
  have hoddEi : Odd Ei.index := Nat.not_even_iff_odd.mp hnotEven
  let : Ei.Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact le_normalizer_of_isNormalIn d.E_normal
  have hquotOdd : Odd (Nat.card (M ⧸ Ei)) := by
    simpa only [Subgroup.index_eq_card] using hoddEi
  intro x hxM hxI
  let xM : M := ⟨x, hxM⟩
  let pi : M →* M ⧸ Ei := QuotientGroup.mk' Ei
  have hsq : (pi xM) ^ 2 = 1 := by
    have hxpow : xM ^ 2 = 1 := by
      apply Subtype.ext
      simpa [xM] using hxI.2
    exact congrArg pi hxpow
  have hone : pi xM = 1 :=
    eq_one_of_sq_eq_one_of_coprime_two hquotOdd.coprime_two_left hsq
  have hxEi : xM ∈ Ei :=
    (QuotientGroup.eq_one_iff (N := Ei) xM).mp hone
  exact Subgroup.mem_subgroupOf.mp hxEi

end CFSG.GorensteinWalter
