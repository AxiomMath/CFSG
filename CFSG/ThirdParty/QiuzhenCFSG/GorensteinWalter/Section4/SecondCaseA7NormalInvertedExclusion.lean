module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7DistinctInvertedConjugate
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7KCenter
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.HhatConjugateTI
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FUFittingContainment
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSix
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddInvertedCentralizesNormalInverted
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeOddFactor
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Excluding a normal inverted subgroup in the A7 second case

If the subgroup of `U` inverted by the selected reflection were normal in
`Hhat`, a distinct conjugate of its central order-three subgroup would
centralize `U`.  In the order-six quotient of `Hhat`, that conjugate and the
reflection generate structurally from their cards `3` and `2`; this avoids
finite enumeration.  The resulting common normal subgroup of `Hhat` and its
conjugate contradicts conjugate-TI control.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The subgroup of `U` inverted by the synchronized reflection cannot be
normal in `Hhat`. -/
public theorem secondCase_a7_inverted_subgroup_not_normal_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d)
    (I : Subgroup G)
    (hI : (I : Set G) = invertedElements c.U (od.s : G)) :
    ¬ IsNormalIn I c.Hhat := by
  classical
  intro hInormal
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have hUeqOdd : c.U = oddCoreOf c.Hhat := h26.1
  have hUnormal : IsNormalIn c.U c.Hhat := by
    rw [hUeqOdd]
    refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat), ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.Hhat) * x0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
        (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
          x0 hx0 ⟨h, hh⟩, by simp⟩
  have hUleHhat : c.U ≤ c.Hhat := hUnormal.1
  have hsHhat : (od.s : G) ∈ c.Hhat := c.H_le_Hhat od.s_mem_H
  have hsU : ∀ u : G, u ∈ c.U →
      (od.s : G) * u * (od.s : G)⁻¹ ∈ c.U :=
    fun u hu => hUnormal.2 (od.s : G) hsHhat u hu
  have hIleU : I ≤ c.U := by
    intro x hx
    have hx' : x ∈ invertedElements c.U (od.s : G) := by
      rw [← hI]
      exact hx
    exact hx'.1
  have hIinv : ∀ x : G, x ∈ I →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹ := by
    intro x hx
    have hx' : x ∈ invertedElements c.U (od.s : G) := by
      rw [← hI]
      exact hx
    exact hx'.2
  have hUp : IsPGroup 3 c.U :=
    secondCase_a7_U_isPGroup_three hmin c w d hA7 hmodel
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hIp : IsPGroup 3 I := by
    have hsubp : IsPGroup 3 (I.subgroupOf c.U) :=
      hUp.to_subgroup (I.subgroupOf c.U)
    obtain ⟨n, hn⟩ := hsubp.exists_card_eq
    apply IsPGroup.of_card (n := n)
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hIleU).toEquiv).symm.trans hn
  obtain ⟨e, Ke, hKeEq, heComm, heSqHhat, hKeNe, hKeLe, hKeInv⟩ :=
    secondCase_a7_exists_distinct_inverted_conjugate_in_Hhat_component
      hmin c w d hA7 hmodel od
  let eG : G := e
  have hKeCard : Nat.card Ke = 3 := by
    rw [hKeEq, Subgroup.card_map_of_injective (MulAut.conj eG).injective,
      od.K_card]
  have hKep : IsPGroup 3 Ke :=
    IsPGroup.of_card (n := 1) (by simp [hKeCard])
  have hJoinLeHhat : I ⊔ Ke ≤ c.Hhat :=
    sup_le (hIleU.trans hUleHhat) (fun _ hx => (hKeLe hx).1)
  have hKeNormI : Ke ≤ Subgroup.normalizer (I : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk x hx
    exact hInormal.2 k (hKeLe hk).1 x hx
  have hJoinp : IsPGroup 3 (I ⊔ Ke : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hIp hKep hKeNormI
  have hJoinOdd : Odd (Nat.card (I ⊔ Ke : Subgroup G)) := by
    obtain ⟨n, hn⟩ := hJoinp.exists_card_eq
    rw [hn]
    exact Odd.pow (by norm_num)
  have hsNI : (od.s : G) ∈ Subgroup.normalizer (I : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      change (od.s : G) * y * (od.s : G)⁻¹ ∈ I
      rw [hIinv y hy]
      exact I.inv_mem hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj (od.s : G)).injective]
  have hsNKe : (od.s : G) ∈ Subgroup.normalizer (Ke : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      change (od.s : G) * y * (od.s : G)⁻¹ ∈ Ke
      rw [hKeInv y hy]
      exact Ke.inv_mem hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj (od.s : G)).injective]
  have hsNJoin : (od.s : G) ∈
      Subgroup.normalizer ((I ⊔ Ke : Subgroup G) : Set G) :=
    Subgroup.normalizer_inf_normalizer_le_normalizer_sup I Ke ⟨hsNI, hsNKe⟩
  have hsJoin : ∀ x : G, x ∈ I ⊔ Ke →
      (od.s : G) * x * (od.s : G)⁻¹ ∈ I ⊔ Ke := by
    intro x hx
    exact ((Subgroup.mem_normalizer_iff.mp hsNJoin) x).1 hx
  have hInormalJoin : IsNormalIn I (I ⊔ Ke) := by
    refine ⟨le_sup_left, ?_⟩
    intro g hg x hx
    exact hInormal.2 g (hJoinLeHhat hg) x hx
  have hKeCentI : Ke ≤ Subgroup.centralizer (I : Set G) := by
    intro k hk
    exact inverted_element_centralizes_normal_inverted_subgroup
      (I ⊔ Ke) I (od.s : G) hJoinOdd hsJoin hInormalJoin hIinv
      ⟨(le_sup_right : Ke ≤ I ⊔ Ke) hk, hKeInv k hk⟩
  have hFUeqU : c.FU = c.U :=
    secondCase_a7_fitting_eq_U hmin c w d hA7 hmodel
  have hFleU : od.F ≤ c.U := by
    rw [← hFUeqU]
    exact le_sup_right.trans (od.FU_inter_M_eq.le.trans inf_le_left)
  have hB_eq_F : od.B = od.F :=
    secondCase_a7_fixed_subgroups_eq hmin c w d hA7 hmodel od
  have hUeqFI : od.F ⊔ I = c.U := by
    apply le_antisymm
    · exact sup_le hFleU hIleU
    · intro u hu
      obtain ⟨f, hf, i, hi, hui⟩ :=
        fact_1_5_ii_decomposition od.s_involution
          (Nat.coprime_two_left.mpr (by
            change Odd (Nat.card (oddCoreOf c.H))
            exact odd_card_oddCoreOf c.H)) hsU u hu
      have hfF : f ∈ od.F := by
        have hfB : f ∈ od.B := by
          rw [od.B_fixed]
          exact hf
        rwa [hB_eq_F] at hfB
      have hiI : i ∈ I := by
        change i ∈ (I : Set G)
        rw [hI]
        exact hi
      rw [hui]
      exact Subgroup.mul_mem_sup hfF hiI
  have hKeCentF : Ke ≤ Subgroup.centralizer (od.F : Set G) := by
    have hEcentF : d.E ≤ Subgroup.centralizer (od.F : Set G) :=
      Subgroup.le_centralizer_iff.mp od.F_centralizes_E
    intro x hx
    exact hEcentF (hKeLe hx).2
  have hKeCentU : Ke ≤ Subgroup.centralizer (c.U : Set G) := by
    rw [← hUeqFI]
    exact le_centralizer_sup_of_le_centralizers hKeCentF hKeCentI
  have hKleU : od.K ≤ c.U :=
    le_sup_left.trans (od.U_inter_M_eq.le.trans inf_le_left)
  have hKnormal : IsNormalIn od.K c.Hhat := by
    rw [secondCase_a7_K_eq_center_U hmin c w d hA7 hmodel od]
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := Subgroup.center c.U) (hKchar := Subgroup.centerCharacteristic)
      hUnormal
  have hKne : od.K ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card od.K = 1 := by rw [hbot]; simp
    rw [od.K_card] at hcard
    norm_num at hcard
  have hKleFHhat : od.K ≤ fittingSubgroupOf c.Hhat := by
    have hKleFU : od.K ≤ c.FU := by rwa [hFUeqU]
    exact hKleFU.trans
      (FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure c h26)
  have hHhatLeNK : c.Hhat ≤ Subgroup.normalizer (od.K : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    exact hKnormal.2 h hh k hk
  have hNK : Subgroup.normalizer (od.K : Set G) = c.Hhat := by
    exact normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) c.Hhat_maximal
      (hKleFHhat.trans (fittingSubgroupOf_isNormalIn c.Hhat).1) hKne
      (Subgroup.normal_subgroupOf_of_le_normalizer hHhatLeNK)
  have hNKe : Subgroup.normalizer (Ke : Set G) =
      conjugateSubgroup c.Hhat eG := by
    rw [hKeEq]
    calc
      Subgroup.normalizer
          ((od.K.map (MulAut.conj eG).toMonoidHom) : Set G) =
          (Subgroup.normalizer (od.K : Set G)).map
            (MulAut.conj eG).toMonoidHom :=
        (Subgroup.map_normalizer_eq_of_bijective od.K
          (MulAut.conj eG).bijective).symm
      _ = c.Hhat.map (MulAut.conj eG).toMonoidHom := by rw [hNK]
      _ = conjugateSubgroup c.Hhat eG := rfl
  let He : Subgroup G := conjugateSubgroup c.Hhat eG
  let Ue : Subgroup G := conjugateSubgroup c.U eG
  let X : Subgroup G := c.U ⊓ Ue
  have hUleHe : c.U ≤ He := by
    change c.U ≤ conjugateSubgroup c.Hhat eG
    rw [← hNKe]
    exact (Subgroup.le_centralizer_iff.mp hKeCentU).trans
      (Subgroup.centralizer_le_normalizer (Ke : Set G))
  have hUeNormalHe : IsNormalIn Ue He := by
    refine ⟨Subgroup.map_mono hUleHhat, ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hh with ⟨h0, hh0, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨h0 * x0 * h0⁻¹, hUnormal.2 h0 hh0 x0 hx0, ?_⟩
    change eG * (h0 * x0 * h0⁻¹) * eG⁻¹ =
      (eG * h0 * eG⁻¹) * (eG * x0 * eG⁻¹) *
        (eG * h0 * eG⁻¹)⁻¹
    group
  have hmap_twice (A : Subgroup G) :
      (conjugateSubgroup A eG).map (MulAut.conj eG).toMonoidHom =
        conjugateSubgroup A (eG ^ 2) := by
    dsimp [conjugateSubgroup]
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, pow_two, mul_assoc]
  have hSqNormHhat : conjugateSubgroup c.Hhat (eG ^ 2) = c.Hhat := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    exact Subgroup.le_normalizer (by simpa [eG] using heSqHhat)
  have hUeLeHhat : Ue ≤ c.Hhat := by
    calc
      Ue = c.U.map (MulAut.conj eG).toMonoidHom := rfl
      _ ≤ He.map (MulAut.conj eG).toMonoidHom := Subgroup.map_mono hUleHe
      _ = conjugateSubgroup c.Hhat (eG ^ 2) := hmap_twice c.Hhat
      _ = c.Hhat := hSqNormHhat
  have hSqNormU : conjugateSubgroup c.U (eG ^ 2) = c.U := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hUnormal.2 (eG ^ 2) heSqHhat u hu
    · intro hu
      have heInvSq : (eG ^ 2)⁻¹ ∈ c.Hhat := c.Hhat.inv_mem heSqHhat
      have hback := hUnormal.2 (eG ^ 2)⁻¹ heInvSq
        ((eG ^ 2) * u * (eG ^ 2)⁻¹) hu
      simpa [mul_assoc] using hback
  have hUeMap : Ue.map (MulAut.conj eG).toMonoidHom = c.U := by
    exact (hmap_twice c.U).trans hSqNormU
  have hXMap : X.map (MulAut.conj eG).toMonoidHom = X := by
    calc
      X.map (MulAut.conj eG).toMonoidHom =
          c.U.map (MulAut.conj eG).toMonoidHom ⊓
            Ue.map (MulAut.conj eG).toMonoidHom := by
              dsimp [X]
              rw [Subgroup.map_inf _ _ _ (MulAut.conj eG).injective]
      _ = Ue ⊓ c.U := by
        rw [hUeMap]
        rfl
      _ = X := by simp [X, inf_comm]
  have hFleUe : od.F ≤ Ue := by
    intro f hf
    apply Subgroup.mem_map.mpr
    refine ⟨f, hFleU hf, ?_⟩
    have hcomm : eG * f = f * eG :=
      (Subgroup.mem_centralizer_iff.mp (od.F_centralizes_E hf)) eG e.2
    change eG * f * eG⁻¹ = f
    calc
      eG * f * eG⁻¹ = (f * eG) * eG⁻¹ := by rw [hcomm]
      _ = f := by simp [mul_assoc]
  have hFleX : od.F ≤ X := fun f hf => ⟨hFleU hf, hFleUe hf⟩
  have hFne : od.F ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card od.F = 1 := by rw [hbot]; simp
    rw [od.F_card] at hcard
    norm_num at hcard
  have hXne : X ≠ ⊥ := by
    intro hbot
    apply hFne
    exact le_bot_iff.mp (hFleX.trans_eq hbot)
  have hXleHhat : X ≤ c.Hhat :=
    inf_le_left.trans hUleHhat
  have hXleFHhat : X ≤ fittingSubgroupOf c.Hhat := by
    have hXleFU : X ≤ c.FU := by
      rw [hFUeqU]
      exact inf_le_left
    exact hXleFU.trans
      (FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure c h26)
  have hUleNX : c.U ≤ Subgroup.normalizer (X : Set G) := by
    have hUleNUe : c.U ≤ Subgroup.normalizer (Ue : Set G) :=
      hUleHe.trans (le_normalizer_of_isNormalIn hUeNormalHe)
    exact (le_inf Subgroup.le_normalizer hUleNUe).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hKeLeUe : Ke ≤ Ue := by
    rw [hKeEq]
    exact Subgroup.map_mono hKleU
  have hKeLeNX : Ke ≤ Subgroup.normalizer (X : Set G) := by
    have hKeLeNU : Ke ≤ Subgroup.normalizer (c.U : Set G) :=
      hKeCentU.trans (Subgroup.centralizer_le_normalizer (c.U : Set G))
    have hKeLeNUe : Ke ≤ Subgroup.normalizer (Ue : Set G) :=
      hKeLeUe.trans Subgroup.le_normalizer
    exact (le_inf hKeLeNU hKeLeNUe).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hsHe : (od.s : G) ∈ He := by
    apply Subgroup.mem_map.mpr
    refine ⟨(od.s : G), hsHhat, ?_⟩
    change eG * (od.s : G) * eG⁻¹ = (od.s : G)
    calc
      eG * (od.s : G) * eG⁻¹ = ((od.s : G) * eG) * eG⁻¹ := by
        rw [heComm]
      _ = (od.s : G) := by simp [mul_assoc]
  have hsNX : (od.s : G) ∈ Subgroup.normalizer (X : Set G) := by
    have hsNU : (od.s : G) ∈ Subgroup.normalizer (c.U : Set G) :=
      le_normalizer_of_isNormalIn hUnormal hsHhat
    have hsNUe : (od.s : G) ∈ Subgroup.normalizer (Ue : Set G) :=
      le_normalizer_of_isNormalIn hUeNormalHe hsHe
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hsNU, hsNUe⟩
  let V : Subgroup G := twoCoreOf c.Hhat
  have hkleinBranch := secondCase_a7_klein_branch hmin c w d hA7 hmodel
  have hkleinCore : IsKleinFour (pCore 2 c.Hhat) := hkleinBranch.1
  have hVK : IsKleinFour V := by
    simpa [V] using firstCase_klein_V_klein c hkleinCore
  have hVnormal : IsNormalIn V c.Hhat := by
    dsimp [V, twoCoreOf]
    refine ⟨Subgroup.map_subtype_le (pCore 2 c.Hhat), ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.Hhat) * x0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
        (pCore_normal (p := 2) (G := c.Hhat)).conj_mem
          x0 hx0 ⟨h, hh⟩, by simp⟩
  have hVleHhat : V ≤ c.Hhat := hVnormal.1
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) := by
    dsimp [V]
    rw [← h26.2.1]
    exact inf_le_right
  have hVleNX : V ≤ Subgroup.normalizer (X : Set G) := by
    have hVcentX : V ≤ Subgroup.centralizer (X : Set G) :=
      hVcentU.trans (Subgroup.centralizer_le (SetLike.coe_mono inf_le_left))
    exact hVcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hVp : IsPGroup 2 V := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply IsPGroup.of_card (n := 2)
    simp
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hVUdisj : Disjoint V c.U := by
    have hcop : Nat.Coprime (Nat.card V) (Nat.card c.U) := by
      rw [hVK.card_four]
      exact (Nat.coprime_two_left.mpr hUodd).pow_left 2
    exact Subgroup.disjoint_of_coprime_natCard hcop
  have hVnormalVU : IsNormalIn V (V ⊔ c.U) := by
    refine ⟨le_sup_left, ?_⟩
    intro g hg v hv
    exact hVnormal.2 g (sup_le hVleHhat hUleHhat hg) v hv
  have hUnormalVU : IsNormalIn c.U (V ⊔ c.U) := by
    refine ⟨le_sup_right, ?_⟩
    intro g hg u hu
    exact hUnormal.2 g (sup_le hVleHhat hUleHhat hg) u hu
  have hVUcomm : ∀ v : G, v ∈ V → ∀ u : G, u ∈ c.U → v * u = u * v := by
    intro v hv u hu
    exact ((Subgroup.mem_centralizer_iff.mp (hVcentU hv)) u hu).symm
  let J : Subgroup G := Ke ⊓ (V ⊔ c.U)
  have hJodd : Odd (Nat.card J) := by
    have hdvd : Nat.card J ∣ Nat.card Ke :=
      Subgroup.card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat (by rw [hKeCard]; norm_num) hdvd
  have hJleU : J ≤ c.U := by
    exact odd_order_subgroup_le_of_le_sup_of_twoPGroup
      V c.U J hVnormalVU hUnormalVU hVUcomm inf_le_right hVp hJodd hVUdisj
  have hKeInfVUBot : Ke ⊓ (V ⊔ c.U) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxKe : x ∈ Ke := hx.1
    have hxU : x ∈ c.U := hJleU hx
    have hxCentU : x ∈ Subgroup.centralizer (c.U : Set G) :=
      hKeCentU hxKe
    have hxK : x ∈ od.K := by
      rw [secondCase_a7_K_eq_center_U hmin c w d hA7 hmodel od]
      apply Subgroup.mem_map.mpr
      refine ⟨(⟨x, hxU⟩ : c.U), ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hxCentU) y y.2
    by_cases hx1 : x = 1
    · exact Subgroup.mem_bot.mpr hx1
    · have hEq : od.K = Ke :=
        subgroup_eq_of_card_eq_prime_of_common_ne_one Nat.prime_three
          od.K Ke od.K_card hKeCard hxK hxKe hx1
      exact False.elim (hKeNe hEq.symm)
  have hUcentV : c.U ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff.mp hVcentU
  have hsNotVU : (od.s : G) ∉ V ⊔ c.U := by
    intro hsVU
    obtain ⟨v, hv, u, hu, hsu⟩ :=
      mem_sup_decompose_of_centralizes hsVU hUcentV
    have hv2 : v ^ 2 = 1 := by
      let vV : V := ⟨v, hv⟩
      simpa [vV, pow_two] using congrArg Subtype.val (hVK.mul_self vV)
    have hcomm : Commute v u := by
      exact (Subgroup.mem_centralizer_iff.mp (hUcentV hu)) v hv
    have hu2 : u ^ 2 = 1 := by
      have hs2 := od.s_involution.2
      rw [hsu, hcomm.mul_pow, hv2, one_mul] at hs2
      exact hs2
    let uU : c.U := ⟨u, hu⟩
    have huU2 : uU ^ 2 = 1 := Subtype.ext hu2
    have huU1 : uU = 1 :=
      eq_one_of_sq_eq_one_of_coprime_two
        (Nat.coprime_two_left.mpr hUodd) huU2
    have hu1 : u = 1 := congrArg Subtype.val huU1
    have hsV : (od.s : G) ∈ V := by
      rw [hsu, hu1, mul_one]
      exact hv
    let : Nontrivial od.K := (Subgroup.nontrivial_iff_ne_bot od.K).mpr hKne
    obtain ⟨k, hkne⟩ := exists_ne (1 : od.K)
    have hkInv : (od.s : G) * (k : G) * (od.s : G)⁻¹ = (k : G)⁻¹ := by
      have hkI : (k : G) ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
        rw [← od.K_inverted]
        exact k.2
      exact hkI.2
    have hskComm : (od.s : G) * (k : G) = (k : G) * (od.s : G) :=
      ((Subgroup.mem_centralizer_iff.mp (hVcentU hsV)) (k : G)
        (hKleU k.2)).symm
    have hkFix : (od.s : G) * (k : G) * (od.s : G)⁻¹ = (k : G) := by
      calc
        (od.s : G) * (k : G) * (od.s : G)⁻¹ =
            ((k : G) * (od.s : G)) * (od.s : G)⁻¹ := by rw [hskComm]
        _ = (k : G) := by simp [mul_assoc]
    have hk2 : k ^ 2 = 1 := by
      apply Subtype.ext
      have hkinveq : (k : G)⁻¹ = (k : G) := hkInv.symm.trans hkFix
      calc
        (k : G) ^ 2 = (k : G) * (k : G) := pow_two _
        _ = (k : G)⁻¹ * (k : G) := by rw [hkinveq]
        _ = 1 := by simp
    have hk1 : k = 1 :=
      eq_one_of_sq_eq_one_of_coprime_two (by rw [od.K_card]; norm_num) hk2
    exact hkne hk1
  let H : Subgroup G := c.Hhat
  let N : Subgroup H := pCore 2 H
  let O : Subgroup H := pPrimeCore 2 H
  let K0 : Subgroup H := N ⊔ O
  have : K0.Normal := by
    dsimp [K0, N, O]
    infer_instance
  let q : H →* H ⧸ K0 := QuotientGroup.mk' K0
  have hK0map : K0.map H.subtype = V ⊔ c.U := by
    dsimp [K0, N, O, H]
    rw [Subgroup.map_sup]
    simp [V, twoCoreOf, oddCoreOf, hUeqOdd]
  let KeH : Subgroup H := Ke.subgroupOf H
  let sH : H := ⟨(od.s : G), hsHhat⟩
  let S0 : Subgroup H := Subgroup.zpowers sH
  have hKeHcard : Nat.card KeH = 3 := by
    calc
      Nat.card KeH = Nat.card Ke :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (H := Ke) (K := H) (fun x hx => (hKeLe hx).1)).toEquiv
      _ = 3 := hKeCard
  have hsHorder : orderOf sH = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact od.s_involution.2
    · intro hs1
      apply od.s_involution.1
      exact congrArg Subtype.val hs1
  have hS0card : Nat.card S0 = 2 := by
    simpa [S0, Nat.card_zpowers] using hsHorder
  have hKeHInfK0 : KeH ⊓ K0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxKe : (x : G) ∈ Ke := Subgroup.mem_subgroupOf.mp hx.1
    have hxK0map : (x : G) ∈ K0.map H.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx.2, rfl⟩
    have hxVU : (x : G) ∈ V ⊔ c.U := by
      rwa [hK0map] at hxK0map
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hKeInfVUBot]
      exact ⟨hxKe, hxVU⟩
    exact Subgroup.mem_bot.mp hxbot
  have hsHNotK0 : sH ∉ K0 := by
    intro hsK0
    apply hsNotVU
    have hsmap : (od.s : G) ∈ K0.map H.subtype :=
      Subgroup.mem_map.mpr ⟨sH, hsK0, rfl⟩
    rwa [hK0map] at hsmap
  have hS0InfK0 : S0 ⊓ K0 = ⊥ := by
    by_contra hne
    have hcardne : Nat.card (S0 ⊓ K0 : Subgroup H) ≠ 1 := by
      intro hcard
      exact hne ((Subgroup.eq_bot_iff_card (H := S0 ⊓ K0)).mpr hcard)
    have hcarddvd : Nat.card (S0 ⊓ K0 : Subgroup H) ∣ 2 := by
      rw [← hS0card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcardeq : Nat.card (S0 ⊓ K0 : Subgroup H) = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hcarddvd).resolve_left hcardne
    have hinfeq : S0 ⊓ K0 = S0 :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardeq, hS0card])
    apply hsHNotK0
    have hsinf : sH ∈ S0 ⊓ K0 := by
      rw [hinfeq]
      exact Subgroup.mem_zpowers sH
    exact hsinf.2
  have hqker : q.ker = K0 := by
    simp [q]
  let QKe : Subgroup (H ⧸ K0) := KeH.map q
  let QS : Subgroup (H ⧸ K0) := S0.map q
  have hQKeCard : Nat.card QKe = 3 := by
    have hcard := card_map_eq_card_mul_card_ker q KeH
    rw [hqker, hKeHInfK0, Subgroup.card_bot, mul_one] at hcard
    exact hcard.symm.trans hKeHcard
  have hQSCard : Nat.card QS = 2 := by
    have hcard := card_map_eq_card_mul_card_ker q S0
    rw [hqker, hS0InfK0, Subgroup.card_bot, mul_one] at hcard
    exact hcard.symm.trans hS0card
  have hsNormKeH : sH ∈ Subgroup.normalizer (KeH : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    change (k : G) ∈ Ke ↔
      (od.s : G) * (k : G) * (od.s : G)⁻¹ ∈ Ke
    exact Subgroup.mem_normalizer_iff.mp hsNKe (k : G)
  have hS0NormKeH : S0 ≤ Subgroup.normalizer (KeH : Set H) :=
    Subgroup.zpowers_le.mpr hsNormKeH
  have hQSNormQKe : QS ≤ Subgroup.normalizer (QKe : Set (H ⧸ K0)) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz a ha
    rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, rfl⟩
    rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨z0 * a0 * z0⁻¹, ?_, by simp⟩
    exact (Subgroup.le_normalizer_iff.mp hS0NormKeH) z0 hz0 a0 ha0
  have hQdisj : Disjoint QKe QS := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hQKeCard, hQSCard]
    norm_num
  have hQjoinCard : Nat.card (QKe ⊔ QS : Subgroup (H ⧸ K0)) = 6 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer
      QKe QS hQSNormQKe hQdisj, hQKeCard, hQSCard]
  let qEquiv : (H ⧸ K0) ≃* DihedralGroup 3 := by
    simpa [H, N, O, K0] using hkleinBranch.2.some
  have hQcard : Nat.card (H ⧸ K0) = 6 := by
    calc
      Nat.card (H ⧸ K0) = Nat.card (DihedralGroup 3) :=
        Nat.card_congr qEquiv.toEquiv
      _ = 6 := by rw [DihedralGroup.nat_card]
  have hQjoinTop : QKe ⊔ QS = ⊤ :=
    Subgroup.eq_top_of_card_eq (QKe ⊔ QS) (hQjoinCard.trans hQcard.symm)
  let L : Subgroup H := (K0 ⊔ KeH) ⊔ S0
  have hK0mapBot : K0.map q = ⊥ := by
    apply le_antisymm
    · intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
      apply Subgroup.mem_bot.mpr
      exact (QuotientGroup.eq_one_iff (N := K0) x).mpr hx
    · exact bot_le
  have hLmap : L.map q = QKe ⊔ QS := by
    dsimp [L, QKe, QS]
    rw [Subgroup.map_sup, Subgroup.map_sup, hK0mapBot]
    simp
  have hkerLeL : q.ker ≤ L := by
    rw [hqker]
    exact le_sup_left.trans le_sup_left
  have hLtop : L = ⊤ := by
    calc
      L = Subgroup.comap q (L.map q) :=
        (Subgroup.comap_map_eq_self hkerLeL).symm
      _ = Subgroup.comap q (⊤ : Subgroup (H ⧸ K0)) := by
        rw [hLmap, hQjoinTop]
      _ = ⊤ := by simp
  let NXH : Subgroup H := (Subgroup.normalizer (X : Set G)).comap H.subtype
  have hK0leNXH : K0 ≤ NXH := by
    intro x hx
    change (x : G) ∈ Subgroup.normalizer (X : Set G)
    have hxmap : (x : G) ∈ K0.map H.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hxVU : (x : G) ∈ V ⊔ c.U := by
      rwa [hK0map] at hxmap
    exact sup_le hVleNX hUleNX hxVU
  have hKeHleNXH : KeH ≤ NXH := by
    intro x hx
    exact hKeLeNX (Subgroup.mem_subgroupOf.mp hx)
  have hS0leNXH : S0 ≤ NXH := by
    apply Subgroup.zpowers_le.mpr
    exact hsNX
  have hLleNXH : L ≤ NXH :=
    sup_le (sup_le hK0leNXH hKeHleNXH) hS0leNXH
  have hHhatLeNX : c.Hhat ≤ Subgroup.normalizer (X : Set G) := by
    intro h hh
    let hH : H := ⟨h, hh⟩
    have hmemL : hH ∈ L := by
      rw [hLtop]
      exact Subgroup.mem_top hH
    exact hLleNXH hmemL
  have hXnormalHhat : IsNormalIn X c.Hhat := by
    refine ⟨hXleHhat, ?_⟩
    intro h hh x hx
    exact ((Subgroup.mem_normalizer_iff.mp (hHhatLeNX hh)) x).mp hx
  have hXmapNormalHe :
      IsNormalIn (X.map (MulAut.conj eG).toMonoidHom) He := by
    refine ⟨Subgroup.map_mono hXnormalHhat.1, ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hh with ⟨h0, hh0, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨h0 * x0 * h0⁻¹, hXnormalHhat.2 h0 hh0 x0 hx0, ?_⟩
    change eG * (h0 * x0 * h0⁻¹) * eG⁻¹ =
      (eG * h0 * eG⁻¹) * (eG * x0 * eG⁻¹) *
        (eG * h0 * eG⁻¹)⁻¹
    group
  have hXnormalHe : IsNormalIn X He := by
    rw [← hXMap]
    exact hXmapNormalHe
  have heHhat : eG ∈ c.Hhat :=
    hhat_conjugate_TI_of_normal_in_both hmin c X hXne hXleFHhat eG
      hXnormalHhat hXnormalHe
  apply hKeNe
  rw [hKeEq]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHhatLeNK heHhat)

end CFSG.GorensteinWalter
