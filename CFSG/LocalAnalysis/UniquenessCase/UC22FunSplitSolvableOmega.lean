module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSolvableInvolution
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SectionIH
public import CFSG.ClassicalInvolution.Q3.TL4SepComm
public import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

theorem twoGenerated_of_hypOmegaGen_threePrime
    {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (h3 : ¬ 3 ∣ Nat.card Y) {K : Subgroup Y} (hK : K ∈ Ω) :
    Subgroup.closure {x : Y | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K := by
  rcases hΩ.omega2 K hK with hgen | he
  · exact hgen
  · obtain ⟨e⟩ := he
    have hcard : Nat.card (K ⧸ classicalInvolutionOddCore K) = 24 :=
      (Nat.card_congr e.toEquiv).trans CFSG.ClassicalInvolution.natCard_sl2Three
    have hthree : 3 ∣ Nat.card (K ⧸ classicalInvolutionOddCore K) := by
      rw [hcard]
      norm_num
    exact False.elim (h3 (hthree.trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card K))))

theorem le_centralizer_of_involution_not_mem_normal_of_threePrime
    {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (hO : classicalInvolutionOddCore Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    {K : Subgroup Y} (hK : K ∈ Ω) {z : Y} (hz : IsUniqueInvolution K z)
    {N : Subgroup Y} (hN : N.Normal) (hzN : z ∉ N) :
    K ≤ centralizer (N : Set Y) := by
  have hON : oddCoreOf N = ⊥ := by
    rw [oddCoreOf, CFSG.ClassicalInvolution.Q3.TL4.oddCore_eq_bot_of_normal hO hN,
      Subgroup.map_bot]
  rw [← twoGenerated_of_hypOmegaGen_threePrime hΩ h3 hK, Subgroup.closure_le]
  rintro x ⟨hxK, hx2⟩
  obtain ⟨R, hR, hRK, hxR⟩ := exists_mem_RSet_ge hK hx2 (Subgroup.zpowers_le.mpr hxK)
  have hRN : R ⊓ N = ⊥ := by
    by_contra hne
    exact hzN (CFSG.ClassicalInvolution.Q3.TL4.mem_of_isPGroup_of_ne_bot hz
      (inf_le_left.trans hRK.1) (hRK.2.1.to_le inf_le_left) hne).2
  have hc := CFSG.ClassicalInvolution.Q3.comm613Gen_normal hΩ hR hN hRN
  rw [hON, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  exact hc (hxR (Subgroup.mem_zpowers x))

theorem involution_mem_pCore_two_of_hypOmegaGen_solvable_threePrime
    {Y : Type} [Group Y] [Finite Y] [Group.IsSolvable Y]
    {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (hO : classicalInvolutionOddCore Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    {K : Subgroup Y} (hK : K ∈ Ω) {z : Y} (hz : IsUniqueInvolution K z) :
    z ∈ CFSG.pCore 2 Y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOp : CFSG.pPrimeCore 2 Y = ⊥ := by
    rw [← CFSG.ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]
    exact hO
  have hF : CFSG.fittingSubgroup Y = CFSG.pCore 2 Y := CFSG.Fitting_eq_pcore Y 2 hOp
  rw [← hF]
  by_contra hzF
  have hKC := le_centralizer_of_involution_not_mem_normal_of_threePrime hΩ hO h3 hK hz
    CFSG.fittingSubgroup_normal hzF
  have hKF := hKC.trans (CFSG.RankThree.PGroups.solvable_fitting_self_centralizing Y)
  exact hzF (hKF hz.mem)

theorem le_pCore_two_of_normal_hypOmegaGen_threePrime
    {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (hO : classicalInvolutionOddCore Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    {K : Subgroup Y} (hK : K ∈ Ω) (hKn : K.Normal) : K ≤ CFSG.pCore 2 Y := by
  obtain ⟨_, R, hRK, _⟩ := hΩ.omega1 K hK
  obtain ⟨k, hk, ⟨eR⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ
    (mem_RSet_of_isSylow2In hK hRK)
  let S : Sylow 2 K := AscL62.sylowOfIsSylow2In'' hRK
  let eS : (S : Subgroup K) ≃* QuaternionGroup (2 ^ k) :=
    (Subgroup.subgroupOfEquivOfLe hRK.1).trans eR
  have hKsub : CFSG.Open.IsSubnormal K ⊤ := by
    let := hKn
    exact IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
  exact le_pCore_two_of_subnormal_quaternion_of_threePrime hO h3 hKsub S hk eS

theorem isPGroup_two_of_generated_conjClass_non_normal_solvable_threePrime
    {Y : Type} [Group Y] [Finite Y] [Group.IsSolvable Y]
    {K : Subgroup Y} (hΩ : HypOmegaGen (CoreAssembly.conjClass K))
    (hO : classicalInvolutionOddCore Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    (hgen : (⨆ g : Y, conjSub g K) = ⊤)
    {z : Y} (hz : IsUniqueInvolution K z) (hz2 : z ∈ CFSG.pCore 2 Y)
    (hnotNormal : ¬ K.Normal) : IsPGroup 2 Y := by
  have _ := hnotNormal
  exact isPGroup_two_of_generated_conjClass_solvable_threePrime_of_involution_mem
    hΩ hO h3 hgen hz hz2

theorem isPGroup_two_of_generated_conjClass_solvable_threePrime
    {Y : Type} [Group Y] [Finite Y] [Group.IsSolvable Y]
    {K : Subgroup Y} (hΩ : HypOmegaGen (CoreAssembly.conjClass K))
    (hO : classicalInvolutionOddCore Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    (hgen : (⨆ g : Y, conjSub g K) = ⊤)
    {z : Y} (hz : IsUniqueInvolution K z) (hz2 : z ∈ CFSG.pCore 2 Y) :
    IsPGroup 2 Y := by
  by_cases hKn : K.Normal
  · have hK2 := le_pCore_two_of_normal_hypOmegaGen_threePrime hΩ hO h3
      (CoreAssembly.mem_conjClass_self K) hKn
    have htop : (⊤ : Subgroup Y) ≤ CFSG.pCore 2 Y := by
      rw [← hgen]
      refine iSup_le fun g => ?_
      have hconj := CFSG.ClassicalInvolution.Q3.conjSub_eq_self_of_normal hKn g
      rw [hconj]
      exact hK2
    have hY2 : IsPGroup 2 (⊤ : Subgroup Y) := CFSG.pCore_isPGroup.to_le htop
    exact hY2.of_equiv Subgroup.topEquiv
  · exact isPGroup_two_of_generated_conjClass_non_normal_solvable_threePrime
      hΩ hO h3 hgen hz hz2 hKn

theorem le_pCore_two_of_hypOmegaGen_solvable_threePrime
    {Y : Type} [Group Y] [Finite Y] [Group.IsSolvable Y]
    {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (hO : classicalInvolutionOddCore Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    {K : Subgroup Y} (hK : K ∈ Ω) : K ≤ CFSG.pCore 2 Y := by
  let H := subnormalClosure K
  have hKH : K ≤ H := le_subnormalClosure K
  have hHsub : CFSG.Open.IsSubnormal H ⊤ := isSubnormal_subnormalClosure K
  have hOH : classicalInvolutionOddCore H = ⊥ := by
    have hle := CFSG.ClassicalInvolution.Balance.oddCoreIn_le_of_isSubnormal hHsub
    have htop : CFSG.ClassicalInvolution.Balance.oddCoreIn (⊤ : Subgroup Y) = ⊥ :=
      (CFSG.ComponentClassification.OddCore.equiv_invariant
        (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)).trans hO
    rw [htop] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp (le_bot_iff.mp hle)
  have hΩH : HypOmegaGen (CoreAssembly.conjClass (K.subgroupOf H)) :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.hypOmegaGen_conjClass_section hΩ hK hKH
  have hH3 : ¬ 3 ∣ Nat.card H :=
    fun hdvd => h3 (hdvd.trans (Subgroup.card_subgroup_dvd_card H))
  have hKfam : K.subgroupOf H ∈ CoreAssembly.conjClass (K.subgroupOf H) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨z, hz⟩ := (hΩH.omega1 _ hKfam).1
  have hz2 := involution_mem_pCore_two_of_hypOmegaGen_solvable_threePrime hΩH hOH hH3 hKfam hz
  have hH2 : IsPGroup 2 H := isPGroup_two_of_generated_conjClass_solvable_threePrime
    hΩH hOH hH3
    (CFSG.ClassicalInvolution.Q3.iSup_conjSub_eq_top_of_subnormalClosure
      (subnormalClosure_subgroupOf_subnormalClosure K)) hz hz2
  have hHcore : CFSG.Open.pCoreOf 2 H = H := le_antisymm
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (CFSG.LieType.BorelTits.le_pCoreOf 2 le_rfl (by
      rw [Subgroup.subgroupOf_self]
      infer_instance) hH2)
  have hcore := CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hHsub
  have htop : CFSG.Open.pCoreOf 2 (⊤ : Subgroup Y) = CFSG.pCore 2 Y :=
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)
  rw [hHcore, htop] at hcore
  exact hKH.trans (hcore ▸ inf_le_right)

end CFSG.LocalAnalysis.UniquenessCase.UC22
