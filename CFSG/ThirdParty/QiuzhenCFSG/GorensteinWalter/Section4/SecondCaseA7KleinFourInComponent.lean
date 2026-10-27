module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UEQuotientCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralOddKernelKleinFourLift
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A Klein four centralizing the component part of U
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 component branch, an actual Klein four subgroup of `E`
centralizes `U ∩ E`. -/
public theorem secondCase_a7_exists_kleinFour_centralizing_U_inter_E
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ V : Subgroup d.E, IsKleinFour V ∧
      V ≤ Subgroup.centralizer
        (((c.U ⊓ d.E).subgroupOf d.E : Subgroup d.E) : Set d.E) ∧
      V ≤ Subgroup.centralizer
        ({(⟨c.t, d.t_mem_E⟩ : d.E)} : Set d.E) := by
  classical
  let E : Subgroup G := d.E
  let Z : Subgroup E := Subgroup.center E
  let : Z.Normal := by dsimp [Z]; infer_instance
  let q : E →* E ⧸ Z := QuotientGroup.mk' Z
  let UE : Subgroup E := (c.U ⊓ E).subgroupOf E
  let UEbar : Subgroup (E ⧸ Z) := UE.map q
  have hUEbarcard : Nat.card UEbar = 3 := by
    simpa [E, Z, q, UE, UEbar] using
      secondCase_a7_U_inter_E_quotient_card_eq_three
        hmin c w d hA7 hmodel
  let tE : E := ⟨c.t, d.t_mem_E⟩
  have htE : IsInvolution tE := by
    constructor
    · intro h
      exact c.t_involution.1 (by simpa [tE] using congrArg Subtype.val h)
    · exact Subtype.ext c.t_involution.2
  have hqt : IsInvolution (q tE) := by
    constructor
    · intro hq1
      have htZ : tE ∈ Z := (QuotientGroup.eq_one_iff (N := Z) tE).mp hq1
      have h2dvd : 2 ∣ Nat.card Z := by
        rw [← orderOf_eq_prime htE.2 htE.1]
        exact Subgroup.orderOf_dvd_natCard Z htZ
      exact d.center_odd.not_two_dvd_nat h2dvd
    · simpa [map_pow] using congrArg q htE.2
  have hUleH : c.U ≤ c.H :=
    Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hUEbarcent : UEbar ≤
      Subgroup.centralizer ({q tE} : Set (E ⧸ Z)) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxU : (x : G) ∈ c.U := (Subgroup.mem_subgroupOf.mp hx).1
    have hxH : (x : G) ∈ c.H := hUleH hxU
    rw [c.H_eq_centralizer] at hxH
    have hxcomm : x * tE = tE * x := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hxH
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg q hxcomm
  let eQ : (E ⧸ Z) ≃* A7 := hA7.some
  let t7 : A7 := eQ (q tE)
  have ht7 : IsInvolution t7 := by
    constructor
    · intro h
      apply hqt.1
      apply eQ.injective
      simpa [t7] using h
    · simpa [t7, map_pow] using congrArg eQ hqt.2
  let U7 : Subgroup A7 := UEbar.map eQ.toMonoidHom
  have hU7card : Nat.card U7 = 3 := by
    rw [Subgroup.card_map_of_injective eQ.injective, hUEbarcard]
  have hU7cent : U7 ≤ Subgroup.centralizer ({t7} : Set A7) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hUEbarcent hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [t7] using congrArg eQ hcomm
  obtain ⟨V7, hV7K, hV7cent, hV7centT⟩ :=
    aSeven_exists_kleinFour_centralizing_card_three_of_centralizes_involution
      t7 ht7 U7 hU7card hU7cent
  let Vbar : Subgroup (E ⧸ Z) := V7.map eQ.symm.toMonoidHom
  have hVbarK : IsKleinFour Vbar :=
    isKleinFour_map_mulEquiv_cross V7 hV7K eQ.symm
  have hVbarcent :=
    centralizer_map_le_of_mulEquiv eQ.symm U7 V7 hV7cent
  have hUback : U7.map eQ.symm.toMonoidHom = UEbar := by
    change (UEbar.map eQ.toMonoidHom).map eQ.symm.toMonoidHom = UEbar
    rw [Subgroup.map_map]
    have hid : eQ.symm.toMonoidHom.comp eQ.toMonoidHom =
        MonoidHom.id (E ⧸ Z) := by
      apply MonoidHom.ext
      intro x
      exact eQ.symm_apply_apply x
    rw [hid, Subgroup.map_id]
  rw [hUback] at hVbarcent
  have hVbarcentT : Vbar ≤
      Subgroup.centralizer ({q tE} : Set (E ⧸ Z)) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hvcomm :=
      Subgroup.mem_centralizer_singleton_iff.mp (hV7centT hv)
    apply eQ.injective
    rw [eQ.map_mul, eQ.map_mul]
    change eQ (eQ.symm v) * eQ (q tE) =
      eQ (q tE) * eQ (eQ.symm v)
    rw [eQ.apply_symm_apply]
    simpa [t7] using hvcomm
  let T : Subgroup E := Subgroup.zpowers tE
  let A : Subgroup E := UE ⊔ T
  have hTmap : T.map q = Subgroup.zpowers (q tE) := by
    simpa [T] using MonoidHom.map_zpowers q tE
  have hVbarcentTmap : Vbar ≤
      Subgroup.centralizer ((T.map q : Subgroup (E ⧸ Z)) : Set (E ⧸ Z)) := by
    rw [hTmap, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hVbarcentT
  have hVbarcentAmap : Vbar ≤
      Subgroup.centralizer ((A.map q : Subgroup (E ⧸ Z)) : Set (E ⧸ Z)) := by
    have hsup := le_centralizer_sup_of_le_centralizers
      hVbarcent hVbarcentTmap
    simpa [Vbar, A, UEbar, Subgroup.map_sup] using hsup
  obtain ⟨V, hVK, _hVmap, hVcent⟩ :=
    exists_kleinFour_lift_centralizing_of_odd_central_kernel
      Z A d.center_odd le_rfl Vbar hVbarK hVbarcentAmap
  have hVcentUE : V ≤ Subgroup.centralizer (UE : Set E) :=
    hVcent.trans (Subgroup.centralizer_le (SetLike.coe_mono le_sup_left))
  have hVcentTsub : V ≤ Subgroup.centralizer (T : Set E) :=
    hVcent.trans (Subgroup.centralizer_le (SetLike.coe_mono le_sup_right))
  have hVcentt : V ≤ Subgroup.centralizer ({tE} : Set E) := by
    simpa [T, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using
      hVcentTsub
  exact ⟨V, hVK, by simpa [E, UE] using hVcentUE,
    by simpa [E, tE] using hVcentt⟩

end CFSG.GorensteinWalter
