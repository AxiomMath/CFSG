module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.theorem_15_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 15 3 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Fixed-complement context, source `kappa_compl_context`: if `K` is
complemented by `U M_σ`, and `K` normalizes `U`, then the fixed product
`K U` is a complement to `M_σ`. -/
private theorem CFSG.section15_sigma_complement_of_kappa_um_sigma_complement
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKcomp : section12ComplementIn M K (U ⊔ section10Msigma M))
    (hUHall :
      section12HallSubgroupIn
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M)
    (hreg : section14ActsRegularlyOn K U) :
    section12ComplementIn M (section10Msigma M) (K ⊔ U) := by
  classical
  let S : Subgroup G := section10Msigma M
  have hSleM : S ≤ M := by
    simpa [S] using (section15_msigma_le (M := M))
  have hKUleM : K ⊔ U ≤ M := sup_le hK.1 hUHall.1
  have hS_U_disj : Disjoint S U := by
    have hSHall :
        IsHallSubgroup (section10SigmaPrimes M) (S.subgroupOf M) := by
      simpa [S, section15_msigma_subgroupOf_eq (G := G) (M := M)] using
        (theorem_10_2_b (G := G) hM).2
    have hπdisj :
        Disjoint (section10SigmaPrimes M)
          ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
      rw [Set.disjoint_left]
      intro p hpσ hpπ
      exact hpπ (Or.inr hpσ)
    have hsubDisj :
        Disjoint (S.subgroupOf M) (U.subgroupOf M) :=
      section15_disjoint_of_hall_disjoint_primes hSHall hUHall.2 hπdisj
    rw [Subgroup.disjoint_def]
    intro x hxS hxU
    have hxM : x ∈ M := hSleM hxS
    have hxSsub : (⟨x, hxM⟩ : M) ∈ S.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxS
    have hxUsub : (⟨x, hxM⟩ : M) ∈ U.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxU
    have hxbotSub : (⟨x, hxM⟩ : M) ∈ (⊥ : Subgroup M) :=
      Subgroup.disjoint_def.mp hsubDisj hxSsub hxUsub
    have hxone : x = 1 := by
      have hxoneSub : (⟨x, hxM⟩ : M) = 1 := by
        simpa using hxbotSub
      simpa using congrArg Subtype.val hxoneSub
    simp [hxone]
  refine ⟨hSleM, hKUleM, ?_, ?_⟩
  · have hprod : M = K ⊔ (U ⊔ S) := by
      simpa [S] using hKcomp.2.2.1
    simpa [S, sup_assoc, sup_comm, sup_left_comm] using hprod
  · rw [Subgroup.disjoint_def]
    intro x hxS hxKU
    have hxKU' : x ∈ U ⊔ K := by
      simpa [sup_comm] using hxKU
    have hKU_mul :
        ((U ⊔ K : Subgroup G) : Set G) = (U : Set G) * (K : Set G) := by
      exact Subgroup.coe_mul_of_right_le_normalizer_left
        (N := U) (H := K) hreg.1
    have hxKUset : x ∈ ((U ⊔ K : Subgroup G) : Set G) := hxKU'
    rw [hKU_mul, Set.mem_mul] at hxKUset
    rcases hxKUset with ⟨u, huU, k, hkK, huk⟩
    have hk_Uσ : k ∈ U ⊔ S := by
      have hk_eq : k = u⁻¹ * x := by
        rw [← huk]
        simp
      rw [hk_eq]
      exact (U ⊔ S).mul_mem
        (Subgroup.mem_sup_left (U.inv_mem huU))
        (Subgroup.mem_sup_right hxS)
    have hkbot : k ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hKcomp.2.2.2 hkK (by simpa [S] using hk_Uσ)
    have hkone : k = 1 := by
      simpa using hkbot
    have hxU : x ∈ U := by
      have hx_eq_u : x = u := by
        simpa [hkone] using huk.symm
      simpa [hx_eq_u] using huU
    exact Subgroup.disjoint_def.mp hS_U_disj hxS hxU

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_bot_actsRegularlyOn
    (U : Subgroup G) :
    section14ActsRegularlyOn (⊥ : Subgroup G) U := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxone : x = 1 := by
      simpa using hx
    subst x
    simp
  · intro x hx hxne
    have hxone : x = 1 := by
      simpa using hx
    exact False.elim (hxne hxone)

public theorem CFSG.section15_KUData_of_proposition14_2AData
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hU : section14Proposition14_2AData M K U) :
    section15KUData M K U := by
  rcases hU with ⟨_hprime, _hcomm, hUHall, hreg, hnormComp⟩
  have hKcomp : section12ComplementIn M K (U ⊔ section10Msigma M) := hnormComp.1
  have hKUcomp : section12ComplementIn M (section10Msigma M) (K ⊔ U) :=
    section15_sigma_complement_of_kappa_um_sigma_complement
      (G := G) (M := M) (K := K) (U := U) hM hK hKcomp hUHall hreg
  have hUnormKU : section10NormalIn U (K ⊔ U) :=
    ⟨le_sup_right,
      Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := K) (N := U) hreg.1⟩
  exact ⟨hK, hKcomp, hKUcomp, hUHall, hreg, hnormComp.2, hUnormKU⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_empty_kappa_hall_bot
    {M : Subgroup G}
    (hκempty : section14KappaPrimes M = ∅) :
    section12HallSubgroupIn (section14KappaPrimes M) (⊥ : Subgroup G) M := by
  refine ⟨bot_le, ?_⟩
  have hbot_subgroupOf :
      ((⊥ : Subgroup G).subgroupOf M) = (⊥ : Subgroup M) := by
    ext x
    simp
  rw [hκempty, hbot_subgroupOf]
  refine isHallSubgroup_of (G := M) (π := (∅ : Set Nat.Primes))
    (H := (⊥ : Subgroup M)) ?_ ?_
  · intro p hp
    exact False.elim (p.property.not_dvd_one (by simpa using hp))
  · intro p hp _hpidx
    exact hp

public theorem CFSG.section15_exists_sigma_complement
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    ∃ U : Subgroup G, section12ComplementToMsigma M U := by
  classical
  have hbotπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ (⊥ : Subgroup G) := by
    intro p hp
    exact False.elim (p.property.not_dvd_one (by simpa using hp))
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := (⊥ : Subgroup G)) hM bot_le hbotπ with
    ⟨E, E₁₂, E₁, E₂, E₃, hE, _hbotE⟩
  exact ⟨E, hE.1⟩

public theorem CFSG.section15_KUData_of_empty_kappa_sigma_complement
    {M U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hκempty : section14KappaPrimes M = ∅)
    (hUcomp : section12ComplementToMsigma M U) :
    section15KUData M (⊥ : Subgroup G) U := by
  classical
  let S : Subgroup G := section10Msigma M
  have hKHall : section12HallSubgroupIn (section14KappaPrimes M) (⊥ : Subgroup G) M :=
    section15_empty_kappa_hall_bot (G := G) (M := M) hκempty
  have hKcomp : section12ComplementIn M (⊥ : Subgroup G) (U ⊔ S) := by
    refine ⟨bot_le, sup_le hUcomp.2.1 hUcomp.1, ?_, ?_⟩
    · have hprod : M = S ⊔ U := by
        simpa [S] using hUcomp.2.2.1
      simpa [S, sup_assoc, sup_comm, sup_left_comm] using hprod
    · rw [Subgroup.disjoint_def]
      intro x hxbot _hxUS
      simpa using hxbot
  have hKUcomp : section12ComplementIn M S ((⊥ : Subgroup G) ⊔ U) := by
    change section12ComplementIn M (section10Msigma M) U at hUcomp
    simpa [S] using hUcomp
  have hUHall : section12HallSubgroupIn
      ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M := by
    refine ⟨hUcomp.2.1, ?_⟩
    have hHallσ :
        IsHallSubgroup (section10SigmaPrimes M)ᶜ (U.subgroupOf M) :=
      section12_msigma_complement_isHall_sigma_compl hM hUcomp
    simpa [hκempty] using hHallσ
  have hreg : section14ActsRegularlyOn (⊥ : Subgroup G) U :=
    section15_bot_actsRegularlyOn (G := G) U
  have hUMnormal : section10NormalIn (U ⊔ S) M := by
    have hUM : U ⊔ S = M := by
      have hprod : M = S ⊔ U := by
        simpa [S] using hUcomp.2.2.1
      simpa [S, sup_comm] using hprod.symm
    rw [hUM]
    refine ⟨le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hUnormKU : section10NormalIn U ((⊥ : Subgroup G) ⊔ U) := by
    simpa using (show section10NormalIn U U from by
      refine ⟨le_rfl, ?_⟩
      rw [Subgroup.subgroupOf_self]
      infer_instance)
  exact ⟨hKHall, hKcomp, hKUcomp, hUHall, hreg, hUMnormal, hUnormKU⟩

/-- Section 15 fixed-complement existence used after Lemma 15.1. -/
public theorem CFSG.section15_exists_KUData_for_maximal
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    ∃ K U : Subgroup G, section15KUData M K U := by
  classical
  by_cases hκ : (section14KappaPrimes M).Nonempty
  · rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with ⟨K, hK⟩
    have hMP : M ∈ section14MFamilyP G := ⟨hM, hκ⟩
    rcases proposition_14_2_a (G := G) (M := M) (K := K) hMP hK with ⟨U, hU⟩
    exact ⟨K, U, section15_KUData_of_proposition14_2AData hM hK hU⟩
  · have hκempty : section14KappaPrimes M = ∅ := by
      ext p
      constructor
      · intro hp
        exact False.elim (hκ ⟨p, hp⟩)
      · intro hp
        simp at hp
    rcases section15_exists_sigma_complement (G := G) (M := M) hM with ⟨U, hUcomp⟩
    exact ⟨⊥, U,
      section15_KUData_of_empty_kappa_sigma_complement
        (G := G) (M := M) (U := U) hM hκempty hUcomp⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isHallSubgroup_inf_subgroupOf_right
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hK_norm_H : K ≤ Subgroup.normalizer (H : Set G))
    (hH : IsHallSubgroup π H) :
    IsHallSubgroup π ((H ⊓ K).subgroupOf K) := by
  classical
  let A : Subgroup G := H ⊓ K
  refine isHallSubgroup_of (G := K) (π := π) (H := A.subgroupOf K) ?_ ?_
  · intro q hq_dvd
    have hcard_eq : Nat.card (A.subgroupOf K) = Nat.card A := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) inf_le_right).toEquiv
    have hq_dvd_H : q.val ∣ Nat.card H := by
      have hq_dvd_A : q.val ∣ Nat.card A := by
        simpa [hcard_eq] using hq_dvd
      exact hq_dvd_A.trans (Subgroup.card_dvd_of_le (show A ≤ H from by
        simp [A]))
    exact hH.p_in_pi_of_p_dvd_card q hq_dvd_H
  · intro q hqπ hq_dvd_idx
    have hidx_eq : (A.subgroupOf K).index = A.relIndex K := by
      rw [← Subgroup.relIndex_top_right (H := A.subgroupOf K)]
      simpa [A] using
        (Subgroup.relIndex_subgroupOf (H := A) (K := K) (L := K) (hKL := le_rfl))
    have hrel_eq : A.relIndex K = H.relIndex (H ⊔ K) := by
      calc
        A.relIndex K = H.relIndex K := by
          simpa [A, inf_comm] using (Subgroup.inf_relIndex_left (H := K) (K := H))
        _ = H.relIndex (H ⊔ K) := by
          let HK : Subgroup G := K ⊔ H
          have hHloc_norm : (H.subgroupOf HK).Normal := by
            simpa [HK] using
              (Subgroup.normal_subgroupOf_sup_of_le_normalizer
                (H := K) (N := H) hK_norm_H)
          have htop :
              H.subgroupOf HK ⊔ K.subgroupOf HK = (⊤ : Subgroup HK) := by
            calc
              H.subgroupOf HK ⊔ K.subgroupOf HK = (H ⊔ K).subgroupOf HK := by
                symm
                simpa [HK] using
                  (Subgroup.subgroupOf_sup (A := H) (A' := K) (B := HK)
                    (by exact le_sup_right) (by exact le_sup_left))
              _ = ⊤ := by
                apply (Subgroup.subgroupOf_eq_top).2
                simp [HK, sup_comm]
          calc
            H.relIndex K =
                (H.subgroupOf HK).relIndex (K.subgroupOf HK) := by
              exact (Subgroup.relIndex_subgroupOf
                (H := H) (K := K) (L := HK) (by exact le_sup_left)).symm
            _ =
                (H.subgroupOf HK).relIndex
                  (H.subgroupOf HK ⊔ K.subgroupOf HK) := by
              rw [sup_comm]
              exact (Subgroup.relIndex_sup_right
                (H := K.subgroupOf HK) (K := H.subgroupOf HK)).symm
            _ = (H.subgroupOf HK).relIndex (⊤ : Subgroup HK) := by
              rw [htop]
            _ = H.relIndex (H ⊔ K) := by
              have htopHK : (H ⊔ K).subgroupOf HK = (⊤ : Subgroup HK) := by
                apply (Subgroup.subgroupOf_eq_top).2
                simp [HK, sup_comm]
              rw [← htopHK]
              simpa [HK, sup_comm] using
                (Subgroup.relIndex_subgroupOf
                  (H := H) (K := H ⊔ K) (L := HK) (by
                    simp [HK, sup_comm]))
    have hrel_dvd_idx : H.relIndex (H ⊔ K) ∣ H.index :=
      Subgroup.relIndex_dvd_index_of_le (H := H) (K := H ⊔ K) le_sup_left
    have hq_dvd_Hidx : q.val ∣ H.index := by
      have hq_dvd_rel : q.val ∣ A.relIndex K := by
        simpa [hidx_eq] using hq_dvd_idx
      have hq_dvd_Hrel : q.val ∣ H.relIndex (H ⊔ K) := by
        simpa [hrel_eq] using hq_dvd_rel
      exact hq_dvd_Hrel.trans hrel_dvd_idx
    exact (hH.p_in_pi_of_p_dvd_index q hq_dvd_Hidx) hqπ

omit [IsMinCE G] in
private theorem CFSG.section15_exists_sylow_overgroup_for_hall_subgroup
    {H T S : Subgroup G} {q : Nat.Primes}
    (hHallHS : section15HallSubgroupOf H S)
    (hTleH : T ≤ H)
    (hTleS : T ≤ S)
    (hTne : T ≠ ⊥)
    (hTp : IsPGroup q.val T)
    (hTHall : section15HallSubgroupOf T H) :
    ∃ P : Sylow q.val S, section10AmbientSylowSubgroup S P = T := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases hHallHS with ⟨hHS, hHHallS⟩
  rcases hTHall with ⟨_hTH, hTHallH⟩
  let TsubS : Subgroup S := T.subgroupOf S
  let HsubS : Subgroup S := H.subgroupOf S
  have hTsubS_p : IsPGroup q.val TsubS :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := T) (K := S) hTleS).symm
  have hTprimeSet : subgroupPrimeSet T = ({q} : Set Nat.Primes) := by
    have hq_eq : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := Subtype.ext rfl
    simpa [hq_eq] using
      (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
        (G := G) (p := q.val) (H := T) hTp hTne)
  have hqT : q ∈ subgroupPrimeSet T := by
    simp [hTprimeSet]
  have hqH : q ∈ subgroupPrimeSet H := by
    have hq_dvd_T : q.val ∣ Nat.card T := by
      simpa [subgroupPrimeSet] using hqT
    exact hq_dvd_T.trans (Subgroup.card_dvd_of_le hTleH)
  have hTsubH_not_idx : ¬ q.val ∣ (T.subgroupOf H).index := by
    intro hqidx
    exact (hTHallH.p_in_pi_of_p_dvd_index q hqidx) hqT
  have hHsubS_not_idx : ¬ q.val ∣ HsubS.index := by
    intro hqidx
    exact (hHHallS.p_in_pi_of_p_dvd_index q (by simpa [HsubS] using hqidx)) hqH
  have hTsubS_card : Nat.card TsubS = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := T) (K := S) hTleS).toEquiv
  have hHsubS_card : Nat.card HsubS = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := H) (K := S) hHS).toEquiv
  have hTsubH_card : Nat.card (T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := T) (K := H) hTleH).toEquiv
  have hTsubS_index :
      TsubS.index = (T.subgroupOf H).index * HsubS.index := by
    have hcard :
        TsubS.index * Nat.card T =
          ((T.subgroupOf H).index * HsubS.index) * Nat.card T := by
      calc
        TsubS.index * Nat.card T =
            TsubS.index * Nat.card TsubS := by rw [hTsubS_card]
        _ = Nat.card S := Subgroup.index_mul_card (H := TsubS)
        _ = HsubS.index * Nat.card HsubS := by
          exact (Subgroup.index_mul_card (H := HsubS)).symm
        _ = HsubS.index * Nat.card H := by rw [hHsubS_card]
        _ = HsubS.index * ((T.subgroupOf H).index * Nat.card (T.subgroupOf H)) := by
          rw [Subgroup.index_mul_card (H := T.subgroupOf H)]
        _ = HsubS.index * ((T.subgroupOf H).index * Nat.card T) := by
          rw [hTsubH_card]
        _ = ((T.subgroupOf H).index * HsubS.index) * Nat.card T := by
          ac_rfl
    exact Nat.mul_right_cancel (Nat.card_pos (α := T)) hcard
  have hTsubS_not_idx : ¬ q.val ∣ TsubS.index := by
    intro hqidx
    have hqprod :
        q.val ∣ (T.subgroupOf H).index * HsubS.index := by
      simpa [hTsubS_index] using hqidx
    rcases q.property.dvd_or_dvd hqprod with hqTidx | hqHidx
    · exact hTsubH_not_idx hqTidx
    · exact hHsubS_not_idx hqHidx
  let P : Sylow q.val S := hTsubS_p.toSylow hTsubS_not_idx
  refine ⟨P, ?_⟩
  calc
    section10AmbientSylowSubgroup S P = TsubS.map S.subtype := by
      simp [P, section10AmbientSylowSubgroup]
    _ = T := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        simpa [TsubS, Subgroup.mem_subgroupOf] using hy
      · intro hx
        exact Subgroup.mem_map.mpr ⟨⟨x, hTleS hx⟩, by simpa [TsubS], rfl⟩


private theorem CFSG.section15_corollary15_3_centralizer_kappa_compl
    {M H K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hKU : section15KUData M K U)
    (hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (section10Msigma M)) :
    IsPiSubgroup (G := G) (section14KappaPrimes M)ᶜ
      (subgroupCentralizerIn M H) := by
  classical
  rcases hHall with ⟨hHleσ, hHHallσ⟩
  intro p hpC
  rw [Set.mem_compl_iff]
  intro hpκ
  let C : Subgroup G := subgroupCentralizerIn M H
  obtain ⟨x, hxC, hxne, hXprimeC₀⟩ :=
    section15_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := C) (q := p) (by simpa [C] using hpC)
  let X : Subgroup G := Subgroup.zpowers x
  have hXprimeC : X ∈ section10PrimeOrderSubgroupsIn p C := by
    simpa [X] using hXprimeC₀
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hXprimeC) with
    ⟨hXleC, hXcard⟩
  have hXleM : X ≤ M := fun y hy => (hXleC hy).1
  have hMP : M ∈ section14MFamilyP G := ⟨hM, ⟨p, hpκ⟩⟩
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  letI : MulDistribMulAction Unit M := {
    smul := fun _ y => y
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let Xsub : Subgroup M := X.subgroupOf M
  have hXsubπ :
      IsPiSubgroup (G := M) (section14KappaPrimes M) Xsub := by
    intro q hqXsub
    have hqdiv : q.val ∣ p.val := by
      have hcard : Nat.card Xsub = Nat.card X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXleM).toEquiv
      simpa [Xsub, hcard, hXcard] using hqXsub
    have hqeq : q = p :=
      Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hqdiv)
    simpa [hqeq] using hpκ
  have hXsubInv : IsInvariant Unit M Xsub := by
    refine ⟨?_⟩
    intro _ y
    simp [Xsub]
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨Ksub, hKsubHall, _hKsubInv, hXsubK⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcop (section14KappaPrimes M)
      Xsub hXsubπ hXsubInv
  let K₀ : Subgroup G := Ksub.map M.subtype
  have hK₀ : section12HallSubgroupIn (section14KappaPrimes M) K₀ M :=
    section15_hallSubgroupIn_map_subtype hKsubHall
  have hXleK₀ : X ≤ K₀ := by
    intro y hyX
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hXleM hyX⟩,
        hXsubK (show (⟨y, hXleM hyX⟩ : M) ∈ Xsub from hyX), rfl⟩
  have hXprimeK₀ : X ∈ section12PrimeOrderSubgroups K₀ := by
    exact section15_primeOrderSubgroups_of_primeOrderSubgroupsIn
      (show X ∈ section10PrimeOrderSubgroupsIn p K₀ from ⟨hXleK₀, hXcard⟩)
  rcases proposition_14_2_a (G := G) (M := M) (K := K₀) hMP hK₀ with
    ⟨U₀, h14a⟩
  have hCentX :
      subgroupCentralizerIn (section10Msigma M) X = section14KStar M K₀ :=
    section15_centralizer_eq_kstar_of_prime_manner
      (M := M) (K := K₀) (X := X) h14a.1 hXprimeK₀
  have hHleKstar : H ≤ section14KStar M K₀ := by
    intro y hyH
    have hyCentX : y ∈ subgroupCentralizerIn (section10Msigma M) X := by
      refine ⟨hHleσ hyH, ?_⟩
      change y ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hzX
      rcases Subgroup.mem_zpowers_iff.mp (by simpa [X] using hzX) with ⟨n, rfl⟩
      have hyx_eq : y * x = x * y :=
        Subgroup.mem_centralizer_iff.mp hxC.2 y hyH
      have hyx : Commute y x := hyx_eq
      exact (hyx.zpow_right n).eq.symm
    simpa [hCentX] using hyCentX
  have hH_card_ne_one : Nat.card H ≠ 1 := by
    intro hcard
    exact hHne ((Subgroup.card_eq_one (H := H)).1 hcard)
  obtain ⟨q0, hq0prime, hq0dvdH⟩ := Nat.exists_prime_and_dvd hH_card_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hqH : q.val ∣ Nat.card H := by
    simpa [q] using hq0dvdH
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let P : Sylow q.val H := Classical.choice (Sylow.nonempty (p := q.val) (G := H))
  let T : Subgroup G := section10AmbientSylowSubgroup H P
  have hTleH : T ≤ H := by
    intro y hy
    have hymap : y ∈ (P : Subgroup H).map H.subtype := by
      simpa [T, section10AmbientSylowSubgroup] using hy
    rcases Subgroup.mem_map.mp hymap with ⟨z, _hz, rfl⟩
    exact z.property
  have hPne : (P : Subgroup H) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := H) (p := q.val) P (by simpa [q] using hqH)
  have hTne : T ≠ ⊥ := by
    intro hTbot
    have hmapbot : (P : Subgroup H).map H.subtype = ⊥ := by
      simpa [T, section10AmbientSylowSubgroup] using hTbot
    exact hPne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := (P : Subgroup H)) (f := H.subtype) H.subtype_injective).1 hmapbot)
  have hTp : IsPGroup q.val T := by
    change IsPGroup q.val ((P : Subgroup H).map H.subtype)
    exact IsPGroup.map (p := q.val) (H := (P : Subgroup H)) P.isPGroup' H.subtype
  have hTsub_eq : T.subgroupOf H = (P : Subgroup H) := by
    simpa [T, section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := H) (P : Subgroup H))
  have hTprimeSet : subgroupPrimeSet T = ({q} : Set Nat.Primes) := by
    simpa using
      (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
        (G := G) (p := q.val) (H := T) hTp hTne)
  have hPprimeSet : subgroupPrimeSet (P : Subgroup H) = ({q} : Set Nat.Primes) := by
    simpa using
      (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
        (G := H) (p := q.val) (H := (P : Subgroup H)) P.isPGroup' hPne)
  have hTHall : section15HallSubgroupOf T H := by
    refine ⟨hTleH, ?_⟩
    rw [hTsub_eq, hTprimeSet]
    refine isHallSubgroup_of (G := H) ({q} : Set Nat.Primes) (P : Subgroup H) ?_ ?_
    · intro r hrP
      have hrPset : r ∈ subgroupPrimeSet (P : Subgroup H) := by
        simpa [subgroupPrimeSet] using hrP
      simpa [hPprimeSet] using hrPset
    · intro r hrq hridx
      have hr_eq : r = q := by simpa using hrq
      subst r
      exact P.not_dvd_index hridx
  have hTleσ : T ≤ section10Msigma M := hTleH.trans hHleσ
  obtain ⟨Pσ, hPσ⟩ :=
    section15_exists_sylow_overgroup_for_hall_subgroup
      (G := G) (H := H) (T := T) (S := section10Msigma M) (q := q)
      ⟨hHleσ, hHHallσ⟩ hTleH hTleσ hTne hTp hTHall
  have hqKstar : q ∈ subgroupPrimeSet (section14KStar M K₀) := by
    exact hqH.trans (Subgroup.card_dvd_of_le hHleKstar)
  have hnot_sylow_le :
      ¬ section10AmbientSylowSubgroup (section10Msigma M) Pσ ≤ section14KStar M K₀ :=
    (proposition_14_2_e (G := G) (M := M) (K := K₀) hMP hK₀ q hqKstar Pσ).2
  exact hnot_sylow_le (by
    simpa [hPσ] using hTleH.trans hHleKstar)

/-- Corollary 15.3(a), source step before the `X=1` split: the centralizer of
a Hall subgroup of `M_σ` splits over `C_{M_σ}(H)` with a Hall
`(κ(M) ∪ σ(M))'` factor inside `C_M(H)`. -/
private theorem CFSG.section15_corollary15_3_centralizer_factor
    {M H K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (section10Msigma M)) :
    ∃ X : Subgroup G,
      X ≤ subgroupCentralizerIn M H ∧
        IsHallSubgroup (section10SigmaPrimes M)ᶜ
          (X.subgroupOf (subgroupCentralizerIn M H)) ∧
            IsPiSubgroup (G := G) ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) X ∧
              ((subgroupCentralizerIn M H : Subgroup G) : Set G) =
                (subgroupCentralizerIn (section10Msigma M) H : Set G) * (X : Set G) := by
  classical
  let C : Subgroup G := subgroupCentralizerIn M H
  let Cσ : Subgroup G := subgroupCentralizerIn (section10Msigma M) H
  have hCκ' :
      IsPiSubgroup (G := G) (section14KappaPrimes M)ᶜ C :=
    section15_corollary15_3_centralizer_kappa_compl
      (G := G) (M := M) (H := H) (K := K) (U := U) hM hKU hHne hHall
  have hCne_top : C ≠ ⊤ := by
    intro hCtop
    have hC_le_M : C ≤ M := fun _ hx => hx.1
    exact hM.1 (top_le_iff.mp (by
      simpa [hCtop] using hC_le_M))
  have hCsolv : IsSolvable C :=
    IsMinCE.proper_subgroups_solvable C (lt_top_iff_ne_top.mpr hCne_top)
  letI : MulDistribMulAction Unit C := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  rcases exists_isHallSubgroup_isInvariant
      (G := C) (A := Unit) hCsolv (by simp) (section10SigmaPrimes M)ᶜ with
    ⟨Xloc, hXlocHall, _hXlocInv⟩
  let X : Subgroup G := Xloc.map C.subtype
  have hXleC : X ≤ C := by
    simpa [X] using Subgroup.map_subtype_le (H := C) Xloc
  have hXHallC :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ (X.subgroupOf C) := by
    simpa [X, subgroupOf_map_subtype_eq] using hXlocHall
  have hCσleC : Cσ ≤ C := by
    intro x hx
    exact ⟨section15_msigma_le hx.1, hx.2⟩
  let Cσloc : Subgroup C := Cσ.subgroupOf C
  have hCσ_eq_inf : Cσ = section10Msigma M ⊓ C := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, ⟨section15_msigma_le hx.1, hx.2⟩⟩
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
  have hC_norm_sigma : C ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
    intro x hx
    exact section15_msigma_le_normalizer (M := M) hx.1
  have hCσHall : IsHallSubgroup (section10SigmaPrimes M) Cσloc := by
    have hInfHall :
        IsHallSubgroup (section10SigmaPrimes M)
          (((section10Msigma M) ⊓ C).subgroupOf C) :=
      section15_isHallSubgroup_inf_subgroupOf_right
        (G := G) (π := section10SigmaPrimes M)
        (H := section10Msigma M) (K := C) hC_norm_sigma
        (theorem_10_2_b (G := G) hM).1
    simpa [Cσloc, hCσ_eq_inf] using hInfHall
  have hC_norm_Cσ : C ≤ Subgroup.normalizer (Cσ : Set G) := by
    have hC_norm_H : C ≤ Subgroup.normalizer (H : Set G) := by
      intro x hx
      exact centralizer_le_normalizer H hx.2
    simpa [Cσ] using
      section15_le_normalizer_subgroupCentralizerIn
        (G := G) (N := C) (E := section10Msigma M) (A := H)
        hC_norm_sigma hC_norm_H
  haveI : Cσloc.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCσleC).2 hC_norm_Cσ
  have hcomp : Cσloc.IsComplement' Xloc :=
    section11_isComplement_of_isHall_compl hCσHall hXlocHall
  have hlocal_prod :
      (Set.univ : Set C) = (Cσloc : Set C) * (Xloc : Set C) := by
    have hXloc_norm_Cσloc : Xloc ≤ Subgroup.normalizer (Cσloc : Set C) := by
      simp [Subgroup.normalizer_eq_top]
    have hmul :
        ((Cσloc ⊔ Xloc : Subgroup C) : Set C) =
          (Cσloc : Set C) * (Xloc : Set C) :=
      Subgroup.coe_mul_of_right_le_normalizer_left
        (N := Cσloc) (H := Xloc) hXloc_norm_Cσloc
    simpa [hcomp.sup_eq_top] using hmul
  have hfactor :
      ((C : Subgroup G) : Set G) = (Cσ : Set G) * (X : Set G) := by
    ext z
    constructor
    · intro hzC
      let zC : C := ⟨z, hzC⟩
      have hzloc : zC ∈ (Cσloc : Set C) * (Xloc : Set C) := by
        rw [← hlocal_prod]
        simp
      rcases hzloc with ⟨a, ha, b, hb, hab⟩
      refine ⟨(a : G), ?_, (b : G), ?_, ?_⟩
      · simpa [Cσloc, Subgroup.mem_subgroupOf] using ha
      · exact Subgroup.mem_map_of_mem C.subtype hb
      · exact congrArg Subtype.val hab
    · rintro ⟨a, ha, b, hb, hab⟩
      have haC : a ∈ C := hCσleC ha
      have hbC : b ∈ C := hXleC hb
      rw [← hab]
      exact C.mul_mem haC hbC
  have hXσ' : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ X :=
    section15_isPiSubgroup_map
      (fun p hp => hXlocHall.p_in_pi_of_p_dvd_card p hp) C.subtype
  have hXκ' : IsPiSubgroup (G := G) (section14KappaPrimes M)ᶜ X :=
    IsPiSubgroup.of_le hXleC hCκ'
  have hXπ :
      IsPiSubgroup (G := G)
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) X := by
    intro p hpX
    have hpκ' := hXκ' p hpX
    have hpσ' := hXσ' p hpX
    rw [Set.mem_compl_iff, Set.mem_union]
    intro hpκσ
    rcases hpκσ with hpκ | hpσ
    · exact hpκ' hpκ
    · exact hpσ' hpσ
  exact ⟨X, hXleC, hXHallC, hXπ, by simpa [C, Cσ, X] using hfactor⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_conjBy_le_of_subgroupOf_conjBy_le
    {H K M : Subgroup G} {g : G}
    (hgM : g ∈ M) (hHM : H ≤ M)
    (hsub :
      (H.subgroupOf M).map (MulAut.conj (⟨g, hgM⟩ : M)).toMonoidHom ≤
        K.subgroupOf M) :
    H.conjBy g ≤ K := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hyH, hyx⟩
  have hxM : x ∈ M := by
    have hyM : y ∈ M := hHM hyH
    have hconjM : g * y * g⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hgM hyM) (M.inv_mem hgM)
    have hx_eq : x = g * y * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx.symm
    simpa [hx_eq] using hconjM
  let xM : M := ⟨x, hxM⟩
  let yM : M := ⟨y, hHM hyH⟩
  have hyM_sub : yM ∈ H.subgroupOf M := hyH
  have hxM_conj :
      xM ∈ (H.subgroupOf M).map
        (MulAut.conj (⟨g, hgM⟩ : M)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨yM, hyM_sub, ?_⟩
    apply Subtype.ext
    simpa [xM, yM, MulAut.conj_apply] using hyx
  exact (hsub hxM_conj : x ∈ K)

private theorem CFSG.section15_exists_conjBy_le_hall_of_isPiSubgroup
    {M U X : Subgroup G} {π : Set Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hUHall : section12HallSubgroupIn π U M)
    (hXM : X ≤ M)
    (hXπ : IsPiSubgroup (G := G) π X) :
    ∃ a : M, X.conjBy (a : G) ≤ U := by
  classical
  rcases hUHall with ⟨hUM, hUHallM⟩
  let Xsub : Subgroup M := X.subgroupOf M
  have hXsubπ : IsPiSubgroup (G := M) π Xsub := by
    intro q hqXsub
    have hcard : Nat.card Xsub = Nat.card X :=
      section12_card_subgroupOf_eq hXM
    exact hXπ q (by simpa [Xsub, hcard] using hqXsub)
  letI : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hXsubInv : IsInvariant Unit M Xsub := by
    refine ⟨?_⟩
    intro _ x
    simp [Xsub]
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨L, hLHall, _hLInv, hXsubL⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcop π Xsub hXsubπ hXsubInv
  obtain ⟨a, ha⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := M) hsolvM hLHall hUHallM
  refine ⟨a, ?_⟩
  have hXsub_conj_le :
      Xsub.map (MulAut.conj a).toMonoidHom ≤ U.subgroupOf M := by
    have hXsub_conj_le_L :
        Xsub.map (MulAut.conj a).toMonoidHom ≤
          L.map (MulAut.conj a).toMonoidHom :=
      Subgroup.map_mono hXsubL
    simpa [ha] using hXsub_conj_le_L
  exact section15_conjBy_le_of_subgroupOf_conjBy_le
    (G := G) (H := X) (K := U) (M := M) (g := (a : G))
    a.property hXM hXsub_conj_le

/-- Corollary 15.3(a), nontrivial branch of the source proof: the Hall factor
`X` can be conjugated into the fixed `U`, and its conjugate has a nontrivial
`M_σ`-centralizer. -/
private theorem CFSG.section15_corollary15_3_nontrivial_factor_conjugate_to_U
    {M H K U X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (section10Msigma M))
    (hXleC : X ≤ subgroupCentralizerIn M H)
    (hXπ :
      IsPiSubgroup (G := G) ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) X)
    (hXne : X ≠ ⊥) :
    ∃ X₀ : Subgroup G,
      X₀ ≤ U ∧ X₀ ≠ ⊥ ∧
        subgroupCentralizerIn (section10Msigma M) X₀ ≠ ⊥ ∧
          section14ConjugateSubgroups X X₀ := by
  classical
  have hXM : X ≤ M := hXleC.trans inf_le_left
  have hUHall :
      section12HallSubgroupIn
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M :=
    section15_kappa_compl_context_U_hall hKU
  obtain ⟨a, hXaU⟩ :=
    section15_exists_conjBy_le_hall_of_isPiSubgroup
      (G := G) (M := M) (U := U) (X := X)
      hM hUHall hXM hXπ
  let X₀ : Subgroup G := X.conjBy (a : G)
  have hHleMs : H ≤ section10Msigma M := hHall.1
  have hHleCX : H ≤ subgroupCentralizerIn (section10Msigma M) X := by
    intro y hyH
    refine ⟨hHleMs hyH, ?_⟩
    change y ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxX
    have hxC := hXleC hxX
    exact (Subgroup.mem_centralizer_iff.mp hxC.2 y hyH).symm
  have hCXne : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
    intro hCXbot
    exact hHne (le_bot_iff.mp (by
      intro y hyH
      have hyCX : y ∈ subgroupCentralizerIn (section10Msigma M) X :=
        hHleCX hyH
      simpa [hCXbot] using hyCX))
  have ha_norm_msigma : (a : G) ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section15_msigma_le_normalizer (M := M) a.property
  have hX₀cent : subgroupCentralizerIn (section10Msigma M) X₀ ≠ ⊥ := by
    simpa [X₀] using
      section11_subgroupCentralizerIn_conjBy_self_ne_bot_of_mem_normalizer
        (G := G) (R := section10Msigma M) (X := X) (g := (a : G))
        ha_norm_msigma hCXne
  have hX₀ne : X₀ ≠ ⊥ := by
    simpa [X₀] using section11_conjBy_ne_bot (G := G) (H := X) (g := (a : G)) hXne
  have hconj : section14ConjugateSubgroups X X₀ := by
    refine ⟨(a : G)⁻¹, ?_⟩
    ext x
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨(a : G) * x * (a : G)⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      · simp [mul_assoc]
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyX₀, hyx⟩
      rcases Subgroup.mem_map.mp hyX₀ with ⟨z, hzX, hzy⟩
      have hx_eq : x = z := by
        have hy_eq : y = (a : G) * z * (a : G)⁻¹ := by
          simpa [MulAut.conj_apply] using hzy.symm
        have hx_eq' : x = (a : G)⁻¹ * y * ((a : G)⁻¹)⁻¹ := by
          simpa [MulAut.conj_apply] using hyx.symm
        rw [hx_eq', hy_eq]
        group
      simpa [hx_eq] using hzX
  exact ⟨X₀, hXaU, hX₀ne, hX₀cent, hconj⟩

/-- Corollary 15.3(a), source step from Lemma 15.1(c): a factor conjugate to
a subgroup of the fixed `U` is cyclic and has prime support in `τ₂(M)`. -/
private theorem CFSG.section15_corollary15_3_factor_cyclic_tau2
    {M H K U X X₀ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (_hHne : H ≠ ⊥)
    (_hHall : section15HallSubgroupOf H (section10Msigma M))
    (hX₀U : X₀ ≤ U)
    (hX₀ne : X₀ ≠ ⊥)
    (hX₀cent : subgroupCentralizerIn (section10Msigma M) X₀ ≠ ⊥)
    (hconj : section14ConjugateSubgroups X X₀) :
    IsCyclic X ∧ IsPiSubgroup (G := G) (section12Tau2Primes M) X := by
  rcases hconj with ⟨g, rfl⟩
  have h151c := lemma_15_1_c
    (G := G) (M := M) (K := K) (U := U) (X := X₀)
    hM hKU hX₀U hX₀ne hX₀cent
  let eMap : X₀ ≃* X₀.map (MulAut.conj g).toMonoidHom :=
    Subgroup.equivMapOfInjective
      (f := (MulAut.conj g).toMonoidHom) X₀
      (EquivLike.injective (MulAut.conj g))
  have hmap : X₀.map (MulAut.conj g).toMonoidHom = X₀.conjBy g := by
    rfl
  let e : X₀ ≃* X₀.conjBy g := eMap.trans (MulEquiv.subgroupCongr hmap)
  refine ⟨?_, ?_⟩
  · exact e.isCyclic.1 h151c.2.1
  · intro p hp
    have hcard : Nat.card (X₀.conjBy g) = Nat.card X₀ :=
      (Nat.card_congr e.toEquiv).symm
    exact h151c.2.2 p (by simpa [hcard] using hp)


/-- Corollary 15.3(a), with the Hall complement information retained for the
centralizer factor constructed in the proof. -/
public theorem CFSG.section15_corollary15_3_a_hall_factor
    {M H : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (section10Msigma M)) :
    ∃ X : Subgroup G,
      X ≤ subgroupCentralizerIn M H ∧ IsCyclic X ∧
        IsPiSubgroup (G := G) (section12Tau2Primes M) X ∧
          IsHallSubgroup (section10SigmaPrimes M)ᶜ
            (X.subgroupOf (subgroupCentralizerIn M H)) ∧
            ((subgroupCentralizerIn M H : Subgroup G) : Set G) =
              (subgroupCentralizerIn (section10Msigma M) H : Set G) * (X : Set G) := by
  rcases section15_exists_KUData_for_maximal hM with ⟨K, U, hKU⟩
  rcases section15_corollary15_3_centralizer_factor
      hM hKU hHne hHall with
    ⟨X, hXleC, hXHallC, hXπ, hfactor⟩
  by_cases hXbot : X = ⊥
  · subst X
    have hbotτ2 : IsPiSubgroup (G := G) (section12Tau2Primes M) (⊥ : Subgroup G) := by
      intro p hp
      exact False.elim (p.property.not_dvd_one (by simpa using hp))
    exact ⟨⊥, bot_le, isCyclic_of_subsingleton (α := (⊥ : Subgroup G)),
      hbotτ2, hXHallC, hfactor⟩
  · rcases section15_corollary15_3_nontrivial_factor_conjugate_to_U
        hM hKU hHne hHall hXleC hXπ hXbot with
      ⟨X₀, hX₀U, hX₀ne, hX₀cent, hconj⟩
    have hcyc_tau2 :
        IsCyclic X ∧ IsPiSubgroup (G := G) (section12Tau2Primes M) X :=
      section15_corollary15_3_factor_cyclic_tau2
        hM hKU hHne hHall hX₀U hX₀ne hX₀cent hconj
    exact ⟨X, hXleC, hcyc_tau2.1, hcyc_tau2.2, hXHallC, hfactor⟩

public theorem CFSG.section15_isHall_compl_of_isHall_complement
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {K D : Subgroup R}
    (hKHall : IsHallSubgroup π K)
    (hcomp : K.IsComplement' D) :
    IsHallSubgroup πᶜ D := by
  classical
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := D) ?_ ?_
  · intro q hqD hqπ
    have hqKidx : q.val ∣ K.index := by
      simpa [hcomp.symm.index_eq_card] using hqD
    exact (hKHall.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqDidx
    have hqK : q.val ∣ Nat.card K := by
      simpa [hcomp.index_eq_card] using hqDidx
    exact hqπc (hKHall.p_in_pi_of_p_dvd_card q hqK)

-- Corollary 15.3(b), Theorem 14.4 adjustment: if two elements of `H` are
-- conjugate in `G`, then after multiplying by a centralizer element the
-- conjugating element can be taken in `M`.
omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_mem_normalizer_of_conjBy_eq
    {H : Subgroup G} {g : G} (hg : H.conjBy g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g :=
      Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [hg] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      simpa [hg] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by
          rw [show g * x * g⁻¹ = g * y * g⁻¹ by
            simpa [MulAut.conj_apply] using hyx.symm]
        _ = y := by group
    simpa [hxy] using hy

private theorem CFSG.section15_corollary15_3_conjugacy_into_M
    {M H : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (section10Msigma M))
    {x y : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hxy : section15ConjugateInSubgroup (⊤ : Subgroup G) x y) :
    section15ConjugateInSubgroup M x y := by
  classical
  rcases hxy with ⟨g, _hg, hgy⟩
  by_cases hx1 : x = 1
  · subst x
    refine ⟨1, M.one_mem, ?_⟩
    simpa using hgy
  · have hHleMs : H ≤ section10Msigma M := hHall.1
    have hxMs : x ∈ section10Msigma M := hHleMs hxH
    have hyMs : y ∈ section10Msigma M := hHleMs hyH
    have hMx : M ∈ section14MsigmaElement x := by
      refine ⟨hM, ?_⟩
      intro z hz
      have hz_eq : z = x := by simpa using hz
      simpa [hz_eq] using hxMs
    have hMy : M ∈ section14MsigmaElement y := by
      refine ⟨hM, ?_⟩
      intro z hz
      have hz_eq : z = y := by simpa using hz
      simpa [hz_eq] using hyMs
    have hMginv_x : M.conjBy g⁻¹ ∈ section14MsigmaElement x := by
      have htmp :=
        section14_msigmaElement_conjBy
          (G := G) (M := M) (x := y) (a := g⁻¹) hMy
      have hback : g⁻¹ * y * (g⁻¹)⁻¹ = x := by
        rw [hgy]
        group
      rw [← hback]
      simpa using htmp
    have hσ : (section14MsigmaElement x).Nonempty := ⟨M, hMx⟩
    have h144 := theorem_14_4 (G := G) (x := x) hx1 hσ
    have hRleCx : section14R x ≤ Subgroup.centralizer ({x} : Set G) :=
      Classical.choose h144.1
    have hsharp : section14SharpTransitiveOn (section14R x) (section14MsigmaElement x) :=
      h144.2.1
    rcases hsharp M hMx (M.conjBy g⁻¹) hMginv_x with ⟨c, hcM, _hcuniq⟩
    have hfix : M.conjBy (g * (c : G)) = M := by
      calc
        M.conjBy (g * (c : G)) = (M.conjBy (c : G)).conjBy g := by
          simpa using (section11_conjBy_conjBy (G := G) M (c : G) g).symm
        _ = (M.conjBy g⁻¹).conjBy g := by rw [← hcM]
        _ = M := section11_conjBy_inv' (G := G) M g
    have hgc_norm : g * (c : G) ∈ Subgroup.normalizer (M : Set G) :=
      section15_mem_normalizer_of_conjBy_eq (G := G) (H := M) hfix
    have hgcM : g * (c : G) ∈ M := by
      have hnorm_eq :
          Subgroup.normalizer (M : Set G) = M :=
        section14_maximal_normalizer_eq_self_of_msigma_member
          (G := G) hM hxMs hx1
      simpa [hnorm_eq] using hgc_norm
    refine ⟨g * (c : G), hgcM, ?_⟩
    have hccomm : Commute (c : G) x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hRleCx c.property)
    have hcx : (c : G) * x * (c : G)⁻¹ = x := by
      calc
        (c : G) * x * (c : G)⁻¹ = x * (c : G) * (c : G)⁻¹ := by
          rw [hccomm.eq]
        _ = x := by simp [mul_assoc]
    calc
      y = g * x * g⁻¹ := hgy
      _ = g * ((c : G) * x * (c : G)⁻¹) * g⁻¹ := by rw [hcx]
      _ = (g * (c : G)) * x * (g * (c : G))⁻¹ := by group

omit [Finite G] [IsMinCE G] in
/-- Corollary 15.3(b), normal case: if `H ⊲ M`, conjugacy inside `M`
already uses an element of `N_M(H)`. -/
private theorem CFSG.section15_corollary15_3_conjugacy_normal_case
    {M H : Subgroup G}
    (hHnormal : section10NormalIn H M)
    {x y : G} (_hxH : x ∈ H) (_hyH : y ∈ H)
    (hxyM : section15ConjugateInSubgroup M x y) :
    section15ConjugateInSubgroup (subgroupNormalizerIn M (H : Set G)) x y := by
  rcases hHnormal with ⟨hHM, hHnormM⟩
  rcases hxyM with ⟨m, hmM, hmy⟩
  have hm_norm : m ∈ Subgroup.normalizer (H : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hHnormM) hmM
  exact ⟨m, mem_subgroupNormalizerIn.mpr ⟨hm_norm, hmM⟩, hmy⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_isHallSubgroup_map_of_surjective
    {R R' : Type*} [Group R] [Finite R] [Group R'] [Finite R']
    {π : Set Nat.Primes} {H : Subgroup R} (hHall : IsHallSubgroup π H)
    (f : R →* R') (hf : Function.Surjective f) :
    IsHallSubgroup π (H.map f) := by
  refine isHallSubgroup_of (G := R') (π := π) (H := H.map f) ?_ ?_
  · intro q hq_dvd
    exact hHall.p_in_pi_of_p_dvd_card q
      (hq_dvd.trans (Subgroup.card_map_dvd (H := H) f))
  · intro q hq_mem hq_dvd_idx
    have hidx_dvd : (H.map f).index ∣ H.index := Subgroup.index_map_dvd (H := H) hf
    exact (hHall.p_in_pi_of_p_dvd_index q (hq_dvd_idx.trans hidx_dvd)) hq_mem

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_map_subgroupOf_map_conj_eq
    {K0 K : Subgroup G} (hK : K ≤ K0) (n : K0) :
    ((K.subgroupOf K0).map (MulAut.conj (n : K0)).toMonoidHom).map K0.subtype
      = K.map (MulAut.conj ((n : K0) : G)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(z : G), hz, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    have hyK0 : y ∈ K0 := hK hy
    have hny_mem : (n : G) * y ∈ K0 := K0.mul_mem n.property hyK0
    have hxyK0 : (n : G) * y * (n : G)⁻¹ ∈ K0 :=
      K0.mul_mem hny_mem (K0.inv_mem n.property)
    refine Subgroup.mem_map.mpr ⟨⟨(n : G) * y * (n : G)⁻¹, hxyK0⟩, ?_, rfl⟩
    let z : K.subgroupOf K0 := ⟨⟨y, hK hy⟩, hy⟩
    refine Subgroup.mem_map.mpr ⟨z, z.property, ?_⟩
    ext
    simp [z, MulAut.conj_apply, mul_assoc]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_conjNormal_subgroupOf_map_subtype
    {N H : Subgroup G} [N.Normal] (hHN : H ≤ N) (g : G) :
    ((H.subgroupOf N).map (MulAut.conjNormal (H := N) g).toMonoidHom).map N.subtype =
      H.conjBy g := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    refine Subgroup.mem_map.mpr ⟨((z : N) : G), ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hz
    · simp [MulAut.conjNormal_apply, MulAut.conj_apply, mul_assoc]
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyH, rfl⟩
    have hyN : y ∈ N := hHN hyH
    have hconjN : g * y * g⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem (inferInstance : N.Normal) y hyN g
    refine Subgroup.mem_map.mpr ⟨⟨g * y * g⁻¹, hconjN⟩, ?_, rfl⟩
    let z : H.subgroupOf N := ⟨⟨y, hyN⟩, by simpa [Subgroup.mem_subgroupOf] using hyH⟩
    refine Subgroup.mem_map.mpr ⟨z, z.property, ?_⟩
    ext
    simp [z, MulAut.conjNormal_apply, mul_assoc]

omit [IsMinCE G] in
private theorem CFSG.section15_hall_frattini_sup_normalizer_eq_top
    {N H : Subgroup G} [N.Normal] {π : Set Nat.Primes}
    (hsolvN : IsSolvable N)
    (hHN : H ≤ N)
    (hHall : IsHallSubgroup π (H.subgroupOf N)) :
    N ⊔ Subgroup.normalizer (H : Set G) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro g _hg
  let φ : MulAut N := MulAut.conjNormal (H := N) g
  have hHallφ : IsHallSubgroup π ((H.subgroupOf N).map φ.toMonoidHom) :=
    hHall.map_mulAut φ
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := N) hsolvN hHall hHallφ with
    ⟨n, hn⟩
  have hconj_eq : H.conjBy g = H.conjBy (n : G) := by
    calc
      H.conjBy g =
          ((H.subgroupOf N).map φ.toMonoidHom).map N.subtype := by
            simpa [φ] using
              (section15_conjNormal_subgroupOf_map_subtype
                (G := G) (N := N) (H := H) hHN g).symm
      _ = ((H.subgroupOf N).map (MulAut.conj n).toMonoidHom).map N.subtype := by
            rw [hn]
       _ = H.conjBy (n : G) := by
             simpa [Subgroup.conjBy] using
              (section15_map_subgroupOf_map_conj_eq
                (G := G) (K0 := N) (K := H) hHN n)
  have hnorm : (n : G)⁻¹ * g ∈ Subgroup.normalizer (H : Set G) := by
    apply section15_mem_normalizer_of_conjBy_eq (G := G) (H := H)
    calc
      H.conjBy ((n : G)⁻¹ * g) = (H.conjBy g).conjBy (n : G)⁻¹ := by
        simpa using
          (section11_conjBy_conjBy (G := G) H g (n : G)⁻¹).symm
      _ = (H.conjBy (n : G)).conjBy (n : G)⁻¹ := by
        rw [hconj_eq]
      _ = H := section11_conjBy_inv (G := G) H (n : G)
  exact
    (Subgroup.mem_sup_of_normal_left
      (s := N) (t := Subgroup.normalizer (H : Set G)) (x := g)).2
      ⟨(n : G), n.property, (n : G)⁻¹ * g, hnorm, by group⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isPiSubgroup_of_isPGroup_of_mem
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes} {p : Nat.Primes}
    {P : Subgroup R} (hPp : IsPGroup p.val P) (hpπ : p ∈ π) :
    IsPiSubgroup (G := R) π P := by
  intro q hq
  haveI : Fact p.val.Prime := ⟨p.2⟩
  rcases hPp.exists_card_eq with ⟨n, hn⟩
  have hq_dvd_p : q.val ∣ p.val := q.2.dvd_of_dvd_pow (by simpa [hn] using hq)
  have hqp : q = p := Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hq_dvd_p)
  simpa [hqp] using hpπ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_piCore_isHallSubgroup_of_nilpotent
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    (hnil : Group.IsNilpotent R) :
    IsHallSubgroup π (piCore π R) := by
  classical
  refine isHallSubgroup_of (G := R) π (piCore π R) ?_ ?_
  · exact piCore_isPiSubgroup π
  · intro p hpπ hp_dvd_idx
    haveI : Fact p.val.Prime := ⟨p.2⟩
    let P : Sylow p.val R := Classical.choice (Sylow.nonempty (p := p.val) (G := R))
    have hPnorm : (P : Subgroup R).Normal :=
      Group.IsNilpotent.sylow_normal hnil p.val P
    have hPπ : IsPiSubgroup (G := R) π (P : Subgroup R) :=
      section15_isPiSubgroup_of_isPGroup_of_mem P.isPGroup' hpπ
    haveI : (P : Subgroup R).Normal := hPnorm
    have hP_le_core : (P : Subgroup R) ≤ piCore π R :=
      le_piCore_of_normal_isPiSubgroup (G := R) π (P : Subgroup R) hPπ
    have hidx_dvd : (piCore π R).index ∣ (P : Subgroup R).index :=
      Subgroup.index_dvd_of_le hP_le_core
    exact P.not_dvd_index (hp_dvd_idx.trans hidx_dvd)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_hall_subgroup_normal_of_nilpotent
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes} {H : Subgroup R}
    (hnil : Group.IsNilpotent R)
    (hHall : IsHallSubgroup π H) :
    H.Normal := by
  classical
  have hCoreHall : IsHallSubgroup π (piCore π R) :=
    section15_piCore_isHallSubgroup_of_nilpotent hnil
  haveI : (piCore π R).Normal := by infer_instance
  have hEq : H = piCore π R := hCoreHall.eq_of_normal hHall
  rw [hEq]
  infer_instance

omit [IsMinCE G] in
private theorem CFSG.section15_normalIn_of_MF_eq_msigma_hall
    {M MF H : Subgroup G}
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M)
    (hHall : section15HallSubgroupOf H (section10Msigma M)) :
    section10NormalIn H M := by
  classical
  rcases hHall with ⟨hHleσ, hHhallσ⟩
  have hσnil : Group.IsNilpotent (section10Msigma M) := by
    subst MF
    exact hMF.1.2.2.1
  have hHcharσ : (H.subgroupOf (section10Msigma M)).Characteristic := by
    have hCoreHall :
        IsHallSubgroup (subgroupPrimeSet H)
          (piCore (subgroupPrimeSet H) (section10Msigma M)) :=
      section15_piCore_isHallSubgroup_of_nilpotent hσnil
    haveI : (piCore (subgroupPrimeSet H) (section10Msigma M)).Normal := by
      infer_instance
    have hEqCore :
        H.subgroupOf (section10Msigma M) =
          piCore (subgroupPrimeSet H) (section10Msigma M) :=
      hCoreHall.eq_of_normal hHhallσ
    rw [hEqCore]
    exact piCore_characteristic (G := section10Msigma M) (subgroupPrimeSet H)
  have hHleM : H ≤ M := hHleσ.trans section15_msigma_le
  refine ⟨hHleM, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hHleM]
  intro m hmM
  have hmap_subtype :
      (H.subgroupOf (section10Msigma M)).map (section10Msigma M).subtype = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hy
    · intro hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hHleσ hx⟩, by simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩
  letI : (H.subgroupOf (section10Msigma M)).Characteristic := hHcharσ
  have hmσ : m ∈ Subgroup.normalizer ((section10Msigma M : Subgroup G) : Set G) :=
    section15_msigma_le_normalizer (M := M) hmM
  have hmH :
      m ∈ Subgroup.normalizer
        (((H.subgroupOf (section10Msigma M)).map (section10Msigma M).subtype) : Set G) :=
    (section8_normalizer_map_subtype_le_of_characteristic
      (G := G) (H := section10Msigma M) (K := H.subgroupOf (section10Msigma M))) hmσ
  simpa [hmap_subtype] using hmH

omit [IsMinCE G] in
public theorem CFSG.section15_hallSubgroupOf_of_le
    {H R S : Subgroup G}
    (hHall : section15HallSubgroupOf H S)
    (hHR : H ≤ R)
    (hRS : R ≤ S) :
    section15HallSubgroupOf H R := by
  classical
  rcases hHall with ⟨hHS, hHallHS⟩
  refine ⟨hHR, ?_⟩
  let RsubS : Subgroup S := R.subgroupOf S
  let HsubS : Subgroup S := H.subgroupOf S
  have hHsubS_le_RsubS : HsubS ≤ RsubS := by
    intro x hx
    have hxH : (x : G) ∈ H := by
      simpa [HsubS, Subgroup.mem_subgroupOf] using hx
    simpa [RsubS, Subgroup.mem_subgroupOf] using hHR hxH
  have hHallLocal :
      IsHallSubgroup (subgroupPrimeSet H) (HsubS.subgroupOf RsubS) :=
    hHallHS.subgroupOf hHsubS_le_RsubS
  let e : RsubS ≃* R := Subgroup.subgroupOfEquivOfLe (H := R) (K := S) hRS
  have hmap :
      (HsubS.subgroupOf RsubS).map e.toMonoidHom = H.subgroupOf R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyH : ((y : RsubS) : S) ∈ HsubS := by
        simpa [Subgroup.mem_subgroupOf] using hy
      have hyHG : (((y : RsubS) : S) : G) ∈ H := by
        simpa [HsubS, Subgroup.mem_subgroupOf] using hyH
      change ((e y : R) : G) ∈ H
      convert hyHG using 1
      rfl
    · intro hx
      have hxH : (x : G) ∈ H := by
        simpa [Subgroup.mem_subgroupOf] using hx
      let xS : S := ⟨(x : G), hHS hxH⟩
      let xRsubS : RsubS := ⟨xS, by
        change (x : G) ∈ R
        exact hHR hxH⟩
      have hxLocal : xRsubS ∈ HsubS.subgroupOf RsubS := by
        simpa [xRsubS, xS, HsubS, Subgroup.mem_subgroupOf] using hxH
      refine Subgroup.mem_map.mpr ⟨xRsubS, hxLocal, ?_⟩
      ext
      rfl
  rw [← hmap]
  exact section15_isHallSubgroup_map_of_surjective hHallLocal e.toMonoidHom e.surjective

omit [IsMinCE G] in
private theorem CFSG.section15_hallSubgroupOf_subgroupOf_overgroup
    {H R M : Subgroup G}
    (hHall : section15HallSubgroupOf H R)
    (hRM : R ≤ M) :
    IsHallSubgroup (subgroupPrimeSet H)
      ((H.subgroupOf M).subgroupOf (R.subgroupOf M)) := by
  classical
  rcases hHall with ⟨hHR, hHallHR⟩
  let e : R ≃* R.subgroupOf M :=
    (Subgroup.subgroupOfEquivOfLe (H := R) (K := M) hRM).symm
  have hmap :
      (H.subgroupOf R).map e.toMonoidHom =
        (H.subgroupOf M).subgroupOf (R.subgroupOf M) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyH : (y : G) ∈ H := by
        simpa [Subgroup.mem_subgroupOf] using hy
      simpa [Subgroup.mem_subgroupOf, e] using hyH
    · intro hx
      have hxH : ((x : R.subgroupOf M) : G) ∈ H := by
        simpa [Subgroup.mem_subgroupOf] using hx
      let y : R := ⟨((x : R.subgroupOf M) : G), by
        exact (x : R.subgroupOf M).property⟩
      have hy : y ∈ H.subgroupOf R := by
        simpa [y, Subgroup.mem_subgroupOf] using hxH
      refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
      ext
      simp [y, e]
  rw [← hmap]
  exact section15_isHallSubgroup_map_of_surjective hHallHR e.toMonoidHom e.surjective

omit [IsMinCE G] in
private theorem CFSG.section15_sylowSubgroupIn_subgroupOf_characteristic
    {M S Q : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQS : Q ≤ S)
    (hSM : S ≤ M) :
    (Q.subgroupOf S).Characteristic := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases hQ with ⟨P, hPamb⟩
  let Qloc : Subgroup S := Q.subgroupOf S
  have hQM : Q ≤ M := hQS.trans hSM
  have hQsubM_eq : Q.subgroupOf M = (P : Subgroup M) := by
    rw [← hPamb]
    simpa [section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := M) (P : Subgroup M))
  have hQp : IsPGroup q.val Q := by
    rw [← hPamb]
    change IsPGroup q.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := q.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  have hQloc_p : IsPGroup q.val Qloc :=
    hQp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Q) (K := S) hQS).symm
  have hQloc_index_dvd :
      Qloc.index ∣ (P : Subgroup M).index := by
    have hrel :
        Q.relIndex S * S.relIndex M = Q.relIndex M :=
      Subgroup.relIndex_mul_relIndex (H := Q) (K := S) (L := M) hQS hSM
    have hQrel_dvd :
        Q.relIndex S ∣ Q.relIndex M := ⟨S.relIndex M, hrel.symm⟩
    have hQrelM_eq : Q.relIndex M = (P : Subgroup M).index := by
      change (Q.subgroupOf M).index = (P : Subgroup M).index
      rw [hQsubM_eq]
    change (Q.subgroupOf S).index ∣ (P : Subgroup M).index
    rwa [← hQrelM_eq]
  have hQloc_not_dvd : ¬ q.val ∣ Qloc.index := by
    intro hdiv
    exact P.not_dvd_index (hdiv.trans hQloc_index_dvd)
  let PS : Sylow q.val S := hQloc_p.toSylow hQloc_not_dvd
  have hPS_eq : (PS : Subgroup S) = Qloc := by
    simp [PS]
  have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
  have hS_norm_Q : S ≤ Subgroup.normalizer (Q : Set G) := hSM.trans hM_norm_Q
  have hQloc_normal : Qloc.Normal := by
    simpa [Qloc] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQS).2 hS_norm_Q
  have hPS_normal : (PS : Subgroup S).Normal := by
    simpa [hPS_eq] using hQloc_normal
  have hPS_char : (PS : Subgroup S).Characteristic :=
    Sylow.characteristic_of_normal PS hPS_normal
  simpa [Qloc, hPS_eq] using hPS_char

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_quotient_nilpotent_of_normal_complement
    {S Q D : Subgroup G}
    [_hQnormalS : (Q.subgroupOf S).Normal]
    (hcomp : section12ComplementIn S Q D)
    (hQnorm : section10NormalIn Q S)
    (hDnil : Group.IsNilpotent D) :
    Group.IsNilpotent (S ⧸ Q.subgroupOf S) := by
  classical
  let Qloc : Subgroup S := Q.subgroupOf S
  let Dloc : Subgroup S := D.subgroupOf S
  haveI : Qloc.Normal := by
    simpa [Qloc] using hQnorm.2
  have hcomp_symm : section12ComplementIn S D Q := by
    rcases hcomp with ⟨hQS, hDS, hsup, hdisj⟩
    exact ⟨hDS, hQS, by simpa [sup_comm] using hsup, hdisj.symm⟩
  have hcomp' : Dloc.IsComplement' Qloc := by
    simpa [Qloc, Dloc] using
      section15_normal_complementIn_isComplement'
        (M := S) (K := D) (N := Q) hcomp_symm hQnorm
  have hDloc_nil : Group.IsNilpotent Dloc := by
    let e : Dloc ≃* D :=
      Subgroup.subgroupOfEquivOfLe (H := D) (K := S) hcomp.2.1
    exact Group.nilpotent_of_mulEquiv (G := D) (G' := Dloc) (_h := hDnil) e.symm
  let e : S ⧸ Qloc ≃* Dloc := hcomp'.QuotientMulEquiv
  exact Group.nilpotent_of_mulEquiv (G := Dloc) (G' := S ⧸ Qloc)
    (_h := hDloc_nil) e.symm

omit [IsMinCE G] in
private theorem CFSG.section15_sup_hall_normalIn_of_quotient_piCore
    {M S Q H : Subgroup G}
    [hQcharS : (Q.subgroupOf S).Characteristic]
    (hSM : S ≤ M)
    (hMnormS : M ≤ Subgroup.normalizer (S : Set G))
    (hQleS : Q ≤ S)
    (hQnormalM : section10NormalIn Q M)
    (hHall : section15HallSubgroupOf H S)
    (hquotNil : Group.IsNilpotent (S ⧸ Q.subgroupOf S)) :
    section10NormalIn (Q ⊔ H) M := by
  classical
  rcases hHall with ⟨hHS, hHallHS⟩
  have hQleM : Q ≤ M := hQleS.trans hSM
  have hHleM : H ≤ M := hHS.trans hSM
  have hQHleM : Q ⊔ H ≤ M := sup_le hQleM hHleM
  refine ⟨hQHleM, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQHleM]
  let Qloc : Subgroup S := Q.subgroupOf S
  let Hloc : Subgroup S := H.subgroupOf S
  have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormalM.1).1 hQnormalM.2
  have hS_norm_Q : S ≤ Subgroup.normalizer (Q : Set G) :=
    hSM.trans hM_norm_Q
  have hQnormalS : Qloc.Normal := by
    simpa [Qloc] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQleS).2 hS_norm_Q
  letI : Qloc.Normal := hQnormalS
  let πq : S →* S ⧸ Qloc := QuotientGroup.mk' Qloc
  let Hbar : Subgroup (S ⧸ Qloc) := Hloc.map πq
  have hHbarHall :
      IsHallSubgroup (subgroupPrimeSet H) Hbar := by
    simpa [Hbar, Hloc, πq] using
      (section15_isHallSubgroup_map_of_surjective hHallHS πq
        (QuotientGroup.mk'_surjective Qloc))
  have hCoreHall :
      IsHallSubgroup (subgroupPrimeSet H)
        (piCore (subgroupPrimeSet H) (S ⧸ Qloc)) :=
    section15_piCore_isHallSubgroup_of_nilpotent hquotNil
  have hHbar_eq_core : Hbar = piCore (subgroupPrimeSet H) (S ⧸ Qloc) :=
    hCoreHall.eq_of_normal hHbarHall
  have hHbar_char : Hbar.Characteristic := by
    rw [hHbar_eq_core]
    exact piCore_characteristic (G := S ⧸ Qloc) (subgroupPrimeSet H)
  have hcomap_char :
      (Hbar.comap πq).Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk
      (H := Qloc) (K := Hbar) hHbar_char
  have hcomap_eq : Hbar.comap πq = Qloc ⊔ Hloc := by
    simp [Hbar, πq]
  let L : Subgroup S := Qloc ⊔ Hloc
  have hLchar : L.Characteristic := by
    simpa [L, hcomap_eq] using hcomap_char
  have hQmap : Qloc.map S.subtype = Q := by
    simpa [Qloc] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := Q) (K := S) hQleS)
  have hHmap : Hloc.map S.subtype = H := by
    simpa [Hloc] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := H) (K := S) hHS)
  have hLmap_eq : L.map S.subtype = Q ⊔ H := by
    calc
      L.map S.subtype =
          Qloc.map S.subtype ⊔ Hloc.map S.subtype := by
        simpa [L] using (Subgroup.map_sup Qloc Hloc S.subtype)
      _ = Q ⊔ H := by
        rw [hQmap, hHmap]
  letI : L.Characteristic := hLchar
  have hnorm_lift :
      Subgroup.normalizer (S : Set G) ≤
        Subgroup.normalizer (L.map S.subtype : Set G) :=
    section8_normalizer_map_subtype_le_of_characteristic
      (H := S) (K := L)
  intro m hm
  have hmL : m ∈ Subgroup.normalizer (L.map S.subtype : Set G) :=
    hnorm_lift (hMnormS hm)
  simpa [hLmap_eq] using hmL

private theorem CFSG.section15_Q_sup_H_normalIn_of_theorem15_2_context
    {M MF K Q D H : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hMFne : MF ≠ section10Msigma M)
    (_hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hHall : section15HallSubgroupOf H (section10Msigma M)) :
    section10NormalIn (Q ⊔ H) M := by
  -- Source line: `sub_normal_Hall hallH` after identifying the image of
  -- `QH/Q` with the `π`-core of the nilpotent quotient `M_σ/Q`.
  classical
  let S : Subgroup G := section10Msigma M
  have hMFleS : MF ≤ S := by
    simpa [S] using section15_MF_le_msigma hM hMF
  have hQleS : Q ≤ S := hQMF.trans hMFleS
  have hSM : S ≤ M := by
    simpa [S] using (section15_msigma_le (M := M))
  have hQnormS : section10NormalIn Q S := by
    refine ⟨hQleS, ?_⟩
    have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
    have hS_norm_Q : S ≤ Subgroup.normalizer (Q : Set G) := by
      simpa [S] using section15_msigma_le.trans hM_norm_Q
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQleS).2 hS_norm_Q
  have hQcharS : (Q.subgroupOf S).Characteristic :=
    section15_sylowSubgroupIn_subgroupOf_characteristic
      (M := M) (S := S) (Q := Q) (q := q) hQ hQnormal hQleS hSM
  letI : (Q.subgroupOf S).Characteristic := hQcharS
  have hquotNil : Group.IsNilpotent (S ⧸ Q.subgroupOf S) := by
    simpa [S] using
      section15_quotient_nilpotent_of_normal_complement
        (S := section10Msigma M) (Q := Q) (D := D)
        hD.2.1 (by simpa [S] using hQnormS) hD.2.2.1
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    simpa [S] using (section15_msigma_le_normalizer (M := M))
  exact
    section15_sup_hall_normalIn_of_quotient_piCore
      (M := M) (S := S) (Q := Q) (H := H)
      hSM hMnormS hQleS hQnormal
      (by simpa [S] using hHall) hquotNil

private theorem CFSG.section15_Q_disjoint_H_of_nonnormal
    {M MF Q H : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hHall : section15HallSubgroupOf H (section10Msigma M))
    (hHnotNormal : ¬ section10NormalIn H M)
    (hQHnormal : section10NormalIn (Q ⊔ H) M) :
    Disjoint Q H := by
  classical
  by_contra hnot
  have hQHinf_ne_bot : Q ⊓ H ≠ ⊥ := by
    intro hbot
    exact hnot (disjoint_iff_inf_le.mpr (by simp [hbot]))
  rcases hQ with ⟨P, hPamb⟩
  have hQp : IsPGroup q.val Q := by
    rw [← hPamb]
    change IsPGroup q.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := q.val) (H := (P : Subgroup M))
      P.isPGroup' M.subtype
  have hQσ : Q ≤ section10Msigma M :=
    hQMF.trans (section15_MF_le_msigma hM hMF)
  have hQsubσ_p : IsPGroup q.val (Q.subgroupOf (section10Msigma M)) :=
    hQp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Q) (K := section10Msigma M) hQσ).symm
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hQnormalσ : (Q.subgroupOf (section10Msigma M)).Normal := by
    have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
    have hσ_norm_Q :
        section10Msigma M ≤ Subgroup.normalizer (Q : Set G) :=
      section15_msigma_le.trans hM_norm_Q
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQσ).2 hσ_norm_Q
  have hqH : q ∈ subgroupPrimeSet H := by
    have hcard_ne_one : Nat.card (Q ⊓ H : Subgroup G) ≠ 1 := by
      intro hcard
      exact hQHinf_ne_bot ((Subgroup.card_eq_one (H := Q ⊓ H)).1 hcard)
    obtain ⟨r, hrPrime, hrDvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
    let r' : Nat.Primes := ⟨r, hrPrime⟩
    have hrQ : r' ∈ ({q} : Set Nat.Primes) := by
      have hQsingle : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
        section8_isPiSubgroup_singleton_of_isPGroup hQp
      exact hQsingle r' (hrDvd.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hrq : r' = q := by
      simpa using hrQ
    have hq_dvd_H : q.val ∣ Nat.card H := by
      have hr_dvd_H : r ∣ Nat.card H :=
        hrDvd.trans (Subgroup.card_dvd_of_le (show Q ⊓ H ≤ H from inf_le_right))
      have hr_val : r = q.val := congrArg Subtype.val hrq
      simpa [hr_val] using hr_dvd_H
    simpa [subgroupPrimeSet] using hq_dvd_H
  have hQleH : Q ≤ H := by
    have hqH' :
        (⟨q.val, Fact.out⟩ : Nat.Primes) ∈ subgroupPrimeSet H := by
      rw [show (⟨q.val, Fact.out⟩ : Nat.Primes) = q by exact Subtype.ext rfl]
      exact hqH
    have hQsub_le_Hsub :
        Q.subgroupOf (section10Msigma M) ≤ H.subgroupOf (section10Msigma M) :=
      section12_normal_pSubgroup_le_of_isHallSubgroup_of_prime_mem
        (R := section10Msigma M)
        (π := subgroupPrimeSet H)
        (H := H.subgroupOf (section10Msigma M))
        (N := Q.subgroupOf (section10Msigma M))
        (p := q.val) hQsubσ_p hHall.2 hqH'
    intro x hxQ
    have hxσ : x ∈ section10Msigma M := hQσ hxQ
    have hxQsub :
        (⟨x, hxσ⟩ : section10Msigma M) ∈
          Q.subgroupOf (section10Msigma M) := by
      simpa [Subgroup.mem_subgroupOf] using hxQ
    have hxHsub := hQsub_le_Hsub hxQsub
    simpa [Subgroup.mem_subgroupOf] using hxHsub
  have hQH_eq_H : Q ⊔ H = H := sup_eq_right.mpr hQleH
  exact hHnotNormal (by simpa [hQH_eq_H] using hQHnormal)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_ambient_mem_normalizer_of_subgroupOf_mem_normalizer
    {M H : Subgroup G} (hHM : H ≤ M) {m : M}
    (hm : m ∈ Subgroup.normalizer ((H.subgroupOf M) : Set M)) :
    (m : G) ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hxH
    let xM : M := ⟨x, hHM hxH⟩
    have hxHloc : xM ∈ H.subgroupOf M := by
      simpa [xM, Subgroup.mem_subgroupOf] using hxH
    have hloc :
        m * xM * m⁻¹ ∈ H.subgroupOf M :=
      (Subgroup.mem_normalizer_iff.mp hm xM).1 hxHloc
    simpa [xM, Subgroup.mem_subgroupOf, mul_assoc] using hloc
  · intro hxConj
    let y : G := (m : G) * x * (m : G)⁻¹
    let yM : M := ⟨y, hHM hxConj⟩
    have hyHloc : yM ∈ H.subgroupOf M := by
      simpa [yM, y, Subgroup.mem_subgroupOf] using hxConj
    have hloc :
        m⁻¹ * yM * (m⁻¹)⁻¹ ∈ H.subgroupOf M := by
      have hminv : m⁻¹ ∈ Subgroup.normalizer ((H.subgroupOf M) : Set M) :=
        (Subgroup.normalizer ((H.subgroupOf M) : Set M)).inv_mem hm
      exact (Subgroup.mem_normalizer_iff.mp hminv yM).1 hyHloc
    simpa [yM, y, Subgroup.mem_subgroupOf, mul_assoc] using hloc

omit [IsMinCE G] in
private theorem CFSG.section15_conjugacy_from_Q_frattini
    {M Q H : Subgroup G}
    (hsolvM : IsSolvable M)
    (hQM : Q ≤ M)
    (hHM : H ≤ M)
    (hQnormalM : (Q.subgroupOf M).Normal)
    (hQHnormalM : section10NormalIn (Q ⊔ H) M)
    (hQHdisj : Disjoint Q H)
    (hHallHN :
      IsHallSubgroup (subgroupPrimeSet H)
        ((H.subgroupOf M).subgroupOf ((Q ⊔ H).subgroupOf M)))
    {x y : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hxyM : section15ConjugateInSubgroup M x y) :
    section15ConjugateInSubgroup (subgroupNormalizerIn M (H : Set G)) x y := by
  classical
  rcases hxyM with ⟨b, hbM, hby⟩
  let Qm : Subgroup M := Q.subgroupOf M
  let Hm : Subgroup M := H.subgroupOf M
  let N : Subgroup M := (Q ⊔ H).subgroupOf M
  have hNnormal : N.Normal := by
    simpa [N] using hQHnormalM.2
  haveI : N.Normal := hNnormal
  have hHleN : Hm ≤ N := by
    intro z hzH
    change ((z : M) : G) ∈ Q ⊔ H
    exact Subgroup.mem_sup_right (by
      simpa [Hm, Subgroup.mem_subgroupOf] using hzH)
  have hsolvN : Group.IsSolvable N := by
    let : Group.IsSolvable M := hsolvM
    infer_instance
  have hFrattini :
      N ⊔ Subgroup.normalizer (Hm : Set M) = ⊤ :=
    section15_hall_frattini_sup_normalizer_eq_top
      (G := M) (N := N) (H := Hm)
      hsolvN hHleN (by simpa [Hm, N] using hHallHN)
  let bM : M := ⟨b, hbM⟩
  have hbFrattini : bM ∈ N ⊔ Subgroup.normalizer (Hm : Set M) := by
    simp [hFrattini]
  obtain ⟨z, hzN, n, hnNorm, hzn⟩ :=
    (Subgroup.mem_sup_of_normal_left
      (s := N) (t := Subgroup.normalizer (Hm : Set M)) (x := bM)).1 hbFrattini
  have hQHloc : Qm ⊔ Hm = N := by
    calc
      Qm ⊔ Hm = (Q ⊔ H).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := Q) (A' := H) (B := M) hQM hHM
      _ = N := rfl
  have hzQH : z ∈ Qm ⊔ Hm := by
    simpa [hQHloc] using hzN
  haveI : Qm.Normal := hQnormalM
  obtain ⟨q, hqQ, h, hhH, hqh⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Qm) (t := Hm) (x := z)).1 hzQH
  have hhNorm : h ∈ Subgroup.normalizer (Hm : Set M) := Subgroup.le_normalizer hhH
  have hn'Norm : h * n ∈ Subgroup.normalizer (Hm : Set M) :=
    (Subgroup.normalizer (Hm : Set M)).mul_mem hhNorm hnNorm
  let n' : M := h * n
  have hn'Norm' : n' ∈ Subgroup.normalizer (Hm : Set M) := by
    simpa [n'] using hn'Norm
  have hn'_ambient_norm : (n' : G) ∈ Subgroup.normalizer (H : Set G) :=
    section15_ambient_mem_normalizer_of_subgroupOf_mem_normalizer hHM hn'Norm'
  have hn'_M : (n' : G) ∈ M := n'.property
  refine ⟨(n' : G), mem_subgroupNormalizerIn.mpr ⟨hn'_ambient_norm, hn'_M⟩, ?_⟩
  have hb_eq : b = (q : G) * (n' : G) := by
    have hbM_eq : bM = q * n' := by
      calc
        bM = z * n := hzn.symm
        _ = (q * h) * n := by rw [hqh]
        _ = q * n' := by simp [n', mul_assoc]
    exact congrArg Subtype.val hbM_eq
  let xM : M := ⟨x, hHM hxH⟩
  have hxHloc : xM ∈ Hm := by
    simpa [xM, Hm, Subgroup.mem_subgroupOf] using hxH
  have hnconj_loc : n' * xM * n'⁻¹ ∈ Hm :=
    (Subgroup.mem_normalizer_iff.mp hn'Norm' xM).1 hxHloc
  have hnconjH : (n' : G) * x * (n' : G)⁻¹ ∈ H := by
    simpa [xM, n', Hm, Subgroup.mem_subgroupOf, mul_assoc] using hnconj_loc
  let u : G := (n' : G) * x * (n' : G)⁻¹
  have huH : u ∈ H := by simpa [u] using hnconjH
  have hy_eq_qu : y = (q : G) * u * (q : G)⁻¹ := by
    rw [hby, hb_eq]
    simp [u, mul_assoc]
  have hquH : (q : G) * u * (q : G)⁻¹ ∈ H := by
    simpa [← hy_eq_qu] using hyH
  have hqQ_ambient : (q : G) ∈ Q := by
    simpa [Qm, Subgroup.mem_subgroupOf] using hqQ
  have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).1 hQnormalM
  have huM : u ∈ M := hHM huH
  have huNormQ : u ∈ Subgroup.normalizer (Q : Set G) := hM_norm_Q huM
  have hcommQ : (q : G) * u * (q : G)⁻¹ * u⁻¹ ∈ Q := by
    have hqinvQ : (q : G)⁻¹ ∈ Q := Q.inv_mem hqQ_ambient
    have hu_q_inv : u * (q : G)⁻¹ * u⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp huNormQ ((q : G)⁻¹)).1 hqinvQ
    simpa [mul_assoc] using Q.mul_mem hqQ_ambient hu_q_inv
  have hcommH : (q : G) * u * (q : G)⁻¹ * u⁻¹ ∈ H :=
    H.mul_mem hquH (H.inv_mem huH)
  have hcomm_one : (q : G) * u * (q : G)⁻¹ * u⁻¹ = 1 := by
    have hbot := Subgroup.disjoint_def.mp hQHdisj hcommQ hcommH
    simpa using hbot
  have hqu_eq_u : (q : G) * u * (q : G)⁻¹ = u := by
    have hmul := congrArg (fun t : G => t * u) hcomm_one
    simpa [mul_assoc] using hmul
  calc
    y = (q : G) * u * (q : G)⁻¹ := hy_eq_qu
    _ = u := hqu_eq_u
    _ = (n' : G) * x * (n' : G)⁻¹ := rfl

/-- Corollary 15.3(b), nonnormal case: Theorem 15.2 gives a normal Sylow
`Q`; the Frattini argument for `QH ⊲ M` removes the `Q` component of the
conjugating element. -/
private theorem CFSG.section15_corollary15_3_conjugacy_nonnormal_case
    {M MF H : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (section10Msigma M))
    (hHnotNormal : ¬ section10NormalIn H M)
    {x y : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hxy : section15ConjugateInSubgroup (⊤ : Subgroup G) x y) :
    section15ConjugateInSubgroup (subgroupNormalizerIn M (H : Set G)) x y := by
  classical
  have hxyM : section15ConjugateInSubgroup M x y :=
    section15_corollary15_3_conjugacy_into_M hM hHne hHall hxH hyH hxy
  have hMFne : MF ≠ section10Msigma M := by
    intro hEq
    exact hHnotNormal
      (section15_normalIn_of_MF_eq_msigma_hall hMF hEq hHall)
  rcases section15_exists_kappa_hallSubgroupIn (G := G) (M := M) hM with
    ⟨K, hK⟩
  rcases theorem_15_2_c (M := M) (MF := MF) (K := K)
      hM hMF hK hMFne with
    ⟨q, hq, Q, hQ, hQnormal, hQMF⟩
  rcases theorem_15_2_d (M := M) (MF := MF) (K := K) (Q := Q)
      (q := q) hM hMF hK hMFne hq hQ hQnormal hQMF with
    ⟨D, hD⟩
  let R : Subgroup G := Q ⊔ H
  have hQσ : Q ≤ section10Msigma M :=
    hQMF.trans (section15_MF_le_msigma hM hMF)
  have hHσ : H ≤ section10Msigma M := hHall.1
  have hRσ : R ≤ section10Msigma M := by
    simpa [R] using sup_le hQσ hHσ
  have hRM : R ≤ M := hRσ.trans section15_msigma_le
  have hHM : H ≤ M := hHσ.trans section15_msigma_le
  have hQHnormal : section10NormalIn R M := by
    simpa [R] using
      section15_Q_sup_H_normalIn_of_theorem15_2_context
        (M := M) (MF := MF) (K := K) (Q := Q) (D := D)
        (H := H) (q := q)
        hM hMF hK hMFne hq hQ hQnormal hQMF hD hHall
  have hQHdisj : Disjoint Q H :=
    section15_Q_disjoint_H_of_nonnormal
      (M := M) (MF := MF) (Q := Q) (H := H) (q := q)
      hM hMF hQ hQnormal hQMF hHall hHnotNormal
      (by simpa [R] using hQHnormal)
  have hHallHR : section15HallSubgroupOf H R :=
    section15_hallSubgroupOf_of_le
      (H := H) (R := R) (S := section10Msigma M)
      hHall (by simp [R]) hRσ
  have hHallHN :
      IsHallSubgroup (subgroupPrimeSet H)
        ((H.subgroupOf M).subgroupOf (R.subgroupOf M)) :=
    section15_hallSubgroupOf_subgroupOf_overgroup
      (H := H) (R := R) (M := M) hHallHR hRM
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  exact
    section15_conjugacy_from_Q_frattini
      (M := M) (Q := Q) (H := H)
      hsolvM hQnormal.1 hHM hQnormal.2
      (by simpa [R] using hQHnormal) hQHdisj
      (by simpa [R] using hHallHN)
      hxH hyH hxyM

/-- Corollary 15.3(b): elements of a nonidentity Hall subgroup of `M_σ`
that are conjugate in `G` are conjugate in `N_M(H)`. -/
public theorem CFSG.corollary_15_3_b
    {M MF H : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (section10Msigma M)) :
    ∀ x y : G, x ∈ H → y ∈ H →
      section15ConjugateInSubgroup (⊤ : Subgroup G) x y →
        section15ConjugateInSubgroup (subgroupNormalizerIn M (H : Set G)) x y := by
  intro x y hxH hyH hxy
  by_cases hHnormal : section10NormalIn H M
  · have hxyM : section15ConjugateInSubgroup M x y :=
      section15_corollary15_3_conjugacy_into_M hM hHne hHall hxH hyH hxy
    exact section15_corollary15_3_conjugacy_normal_case
      hHnormal hxH hyH hxyM
  · exact section15_corollary15_3_conjugacy_nonnormal_case
      hM hMF hHne hHall hHnormal hxH hyH hxy

end Section15
