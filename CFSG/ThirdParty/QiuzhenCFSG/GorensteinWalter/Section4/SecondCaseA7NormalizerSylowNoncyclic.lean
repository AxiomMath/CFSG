module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7SylowInComponent
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow subgroups above the selected A7 component are noncyclic

The selected component contains an order-eight `2`-subgroup.  Its map into
the A7 central quotient is injective because the center has odd order.  A
cyclic image would contain an element of order eight, but cycle types on
seven letters rule that out.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open Equiv.Perm

/-- Every Sylow `2`-subgroup of a subgroup containing the selected A7
component is noncyclic. -/
public theorem secondCase_a7_sylow_not_cyclic_of_component_le
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (N : Subgroup G) (hEN : d.E ≤ N) :
    ∀ P : Sylow 2 N, ¬ IsCyclic P := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SM, hSMcard, hSME⟩ :=
    secondCase_a7_sylow_le_component hmin c w d hA7 hmodel
  let A : Subgroup G := (SM : Subgroup w.M).map w.M.subtype
  have hAcard : Nat.card A = 8 := by
    dsimp [A]
    rw [Subgroup.card_map_of_injective w.M.subtype_injective, hSMcard]
  have hAp : IsPGroup 2 A := SM.isPGroup'.map w.M.subtype
  have hAleE : A ≤ d.E := by simpa [A] using hSME
  have hno8 : ∀ x : alternatingGroup (Fin 7), orderOf x ≠ 8 := by
    intro x hx
    have hxperm : orderOf (x : Equiv.Perm (Fin 7)) = 8 :=
      (Subgroup.orderOf_coe x).trans hx
    have hlcm4 : (x : Equiv.Perm (Fin 7)).cycleType.lcm ∣ 4 := by
      rw [Multiset.lcm_dvd]
      intro n hn
      have hn2 : 2 ≤ n := two_le_of_mem_cycleType hn
      have hn7 : n ≤ 7 := by
        exact (le_card_support_of_mem_cycleType hn).trans
          ((x : Equiv.Perm (Fin 7)).support.card_le_univ.trans_eq
            (Fintype.card_fin 7))
      have hndvd8 : n ∣ 8 := by
        simpa [hxperm] using dvd_of_mem_cycleType hn
      have hndvdpow : n ∣ 2 ^ 3 := by simpa using hndvd8
      rcases (Nat.dvd_prime_pow Nat.prime_two).mp hndvdpow with
        ⟨k, hk, hnk⟩
      have hk0 : k ≠ 0 := by
        intro hkzero
        subst k
        norm_num at hnk
        omega
      have hk3 : k ≠ 3 := by
        intro hkthree
        subst k
        norm_num at hnk
        omega
      have hk12 : k = 1 ∨ k = 2 := by omega
      rcases hk12 with rfl | rfl
      · rw [hnk]
        norm_num
      · rw [hnk]
        norm_num
    rw [lcm_cycleType, hxperm] at hlcm4
    norm_num at hlcm4
  have hA_not_cyclic : ¬ IsCyclic A := by
    intro hAcyc
    obtain ⟨a, haorder⟩ :=
      isCyclic_iff_exists_orderOf_eq_natCard.mp hAcyc
    have haorder8 : orderOf a = 8 := haorder.trans hAcard
    let Z : Subgroup d.E := Subgroup.center d.E
    let q : d.E →* d.E ⧸ Z := QuotientGroup.mk' Z
    let iA : A →* d.E := Subgroup.inclusion hAleE
    let phi : A →* d.E ⧸ Z := q.comp iA
    have hiAinj : Function.Injective iA := Subgroup.inclusion_injective hAleE
    have hphi_ker : phi.ker = ⊥ := by
      apply le_antisymm
      · intro x hx
        have hqx : q (iA x) = 1 := MonoidHom.mem_ker.mp hx
        have hxZ : iA x ∈ Z :=
          (QuotientGroup.eq_one_iff (N := Z) (iA x)).mp hqx
        let z : Z := ⟨iA x, hxZ⟩
        have hordA : orderOf x ∣ Nat.card A := orderOf_dvd_natCard x
        have hordZ0 : orderOf z ∣ Nat.card Z := orderOf_dvd_natCard z
        have horderz : orderOf z = orderOf x := by
          calc
            orderOf z = orderOf (z : d.E) := (Subgroup.orderOf_coe z).symm
            _ = orderOf (iA x) := rfl
            _ = orderOf x := orderOf_injective iA hiAinj x
        have hordZ : orderOf x ∣ Nat.card Z := by
          rwa [horderz] at hordZ0
        have hcop : Nat.Coprime (Nat.card A) (Nat.card Z) := by
          rw [hAcard]
          have h2cop : Nat.Coprime 2 (Nat.card Z) :=
            Nat.coprime_two_left.mpr d.center_odd
          simpa using h2cop.pow_left 3
        have hord1 : orderOf x = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop hordA hordZ
        exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hord1)
      · exact bot_le
    have hphi_inj : Function.Injective phi :=
      (MonoidHom.ker_eq_bot_iff phi).mp hphi_ker
    let psi : A →* alternatingGroup (Fin 7) :=
      hA7.some.toMonoidHom.comp phi
    have hpsi_inj : Function.Injective psi :=
      hA7.some.injective.comp hphi_inj
    have hpsi_order : orderOf (psi a) = 8 := by
      rw [orderOf_injective psi hpsi_inj a, haorder8]
    exact hno8 (psi a) hpsi_order
  intro P hPcyc
  have hAleN : A ≤ N := hAleE.trans hEN
  let AN : Subgroup N := A.subgroupOf N
  have hANp : IsPGroup 2 AN := hAp.comap_subtype
  obtain ⟨Q, hANQ⟩ := hANp.exists_le_sylow
  have hQcyc : IsCyclic Q :=
    (MulEquiv.isCyclic (Sylow.equiv Q P)).mpr hPcyc
  have hANcyc : IsCyclic AN := by
    let : IsCyclic Q := hQcyc
    exact Subgroup.isCyclic_of_le hANQ
  let eAN : AN ≃* A := Subgroup.subgroupOfEquivOfLe hAleN
  have hAcyc : IsCyclic A := isCyclic_of_surjective eAN eAN.surjective
  exact hA_not_cyclic hAcyc

end CFSG.GorensteinWalter
