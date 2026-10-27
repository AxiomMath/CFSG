module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.corollary_15_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 15 6 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Corollary 15.6: for `M ∈ 𝓜_P`, `K*` is a nonidentity cyclic
subgroup of both `M_F` and `M''`, and `M_F` is not cyclic. -/
private theorem CFSG.section15_corollary15_6_Kstar_nontrivial_cyclic
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14KStar M K ≠ ⊥ ∧ IsCyclic (section14KStar M K) := by
  have hKstar_ne : section14KStar M K ≠ ⊥ :=
    (proposition_14_2_c (G := G) (M := M) (K := K) hM hK).1
  have hKstar_cyclic : IsCyclic (section14KStar M K) := by
    have hZcyclic : IsCyclic (section14Z M K) :=
      (theorem_14_7_d (G := G) (M := M) (K := K) hM hK).2.1
    letI : IsCyclic (section14Z M K) := hZcyclic
    exact Subgroup.isCyclic_of_le (show section14KStar M K ≤ section14Z M K by
      change section14KStar M K ≤ K ⊔ section14KStar M K
      exact le_sup_right)
  exact ⟨hKstar_ne, hKstar_cyclic⟩

/-- Corollary 15.6 source step from Theorem 14.7(h) and Lemma 6.3:
`K*` lies in the second derived subgroup. -/
private theorem CFSG.section15_corollary15_6_Kstar_le_secondDerived
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14KStar M K ≤ section15SecondDerivedSubgroup M := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Hloc : Subgroup M := D.subgroupOf M
  let Kloc : Subgroup M := K.subgroupOf M
  have hDnormM : section10NormalIn D M := by
    simpa [D] using (section15_ambientDerived_normalIn (M := M))
  have hcompAmb : section12ComplementIn M K D := by
    simpa [D] using theorem_14_7_h (G := G) (M := M) (K := K) hM hK
  have hcompKloc : Kloc.IsComplement' Hloc := by
    simpa [D, Hloc, Kloc] using
      section15_normal_complementIn_isComplement'
        (M := M) (K := K) (N := D) hcompAmb hDnormM
  have hCompl : IsCompl Hloc Kloc := by
    refine IsCompl.of_eq ?_ ?_
    · simpa [inf_comm] using hcompKloc.disjoint.eq_bot
    · simpa [sup_comm] using hcompKloc.sup_eq_top
  have hKlocHall : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hHcop : Nat.Coprime (Nat.card Hloc) Hloc.index := by
    simpa [Hloc, Kloc, hcompKloc.index_eq_card, hcompKloc.symm.index_eq_card]
      using hKlocHall.card_coprime_index.symm
  have hHlocHall : IsHallSubgroup (subgroupPrimeSet Hloc) Hloc := by
    refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet Hloc) (H := Hloc) ?_ ?_
    · intro p hp
      simpa [subgroupPrimeSet] using hp
    · intro p hpH hpidx
      exact (Nat.not_coprime_of_dvd_of_dvd p.property.one_lt
        (by simpa [subgroupPrimeSet] using hpH) hpidx) hHcop
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1.1)
  let : Group.IsSolvable M := hsolvM
  haveI : Hloc.Normal := by
    simpa [D, Hloc] using hDnormM.2
  have hHleDerived : Hloc ≤ derivedSubgroup M := by
    intro x hx
    have hx' : x ∈ (ambientDerivedSubgroup M).subgroupOf M := by
      simpa [D, Hloc] using hx
    simpa [section15_ambientDerived_subgroupOf_eq] using hx'
  have hcentral_le : subgroupCentralizerIn Hloc Kloc ≤ ⁅Hloc, Hloc⁆ :=
    lemma_6_3_a_2 (G := M) (H := Hloc) (K := Kloc)
      ⟨subgroupPrimeSet Hloc, hHlocHall⟩ hCompl hHleDerived
  have hHloc_map : Hloc.map M.subtype = D := by
    simpa [D, Hloc] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := D) (K := M)
        (section15_ambientDerived_le (M := M)))
  have hcomm_map :
      (⁅Hloc, Hloc⁆).map M.subtype = section15SecondDerivedSubgroup M := by
    calc
      (⁅Hloc, Hloc⁆).map M.subtype =
          ⁅Hloc.map M.subtype, Hloc.map M.subtype⁆ := by
        simpa using
          (Subgroup.map_commutator (H₁ := Hloc) (H₂ := Hloc) M.subtype)
      _ = ⁅D, D⁆ := by
        rw [hHloc_map]
      _ = section15SecondDerivedSubgroup M := by
        simpa [section15SecondDerivedSubgroup, D] using
          (section12_ambientDerivedSubgroup_eq_commutator
            (G := G) (H := ambientDerivedSubgroup M)).symm
  intro x hx
  change x ∈ subgroupCentralizerIn (section10Msigma M) K at hx
  have hxS : x ∈ section10Msigma M := hx.1
  have hxCentK : x ∈ Subgroup.centralizer (K : Set G) := hx.2
  have hxD : x ∈ D := by
    simpa [D] using (section15_msigma_le_ambientDerived hM.1 hxS)
  have hxM : x ∈ M := by
    exact hDnormM.1 hxD
  let xM : M := ⟨x, hxM⟩
  have hxHloc : xM ∈ Hloc := by
    simpa [xM, Hloc, D, Subgroup.mem_subgroupOf] using hxD
  have hxCentLoc : xM ∈ Subgroup.centralizer (Kloc : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hyKloc
    apply Subtype.ext
    have hyK : (y : G) ∈ K := by
      simpa [Kloc, Subgroup.mem_subgroupOf] using hyKloc
    have hcomm : (y : G) * x = x * (y : G) :=
      (Subgroup.mem_centralizer_iff.mp hxCentK) (y : G) hyK
    simpa [xM] using hcomm
  have hxCentral : xM ∈ subgroupCentralizerIn Hloc Kloc := ⟨hxHloc, hxCentLoc⟩
  have hxComm : xM ∈ ⁅Hloc, Hloc⁆ := hcentral_le hxCentral
  have hxMap : x ∈ (⁅Hloc, Hloc⁆).map M.subtype :=
    Subgroup.mem_map.mpr ⟨xM, hxComm, rfl⟩
  simpa [hcomm_map] using hxMap

/-- Corollary 15.6 source step from Theorem 15.2(b,c): `K*` lies in `M_F`. -/
private theorem CFSG.section15_corollary15_6_Kstar_le_MF
    {M MF K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14KStar M K ≤ MF := by
  by_cases hEq : MF = section10Msigma M
  · rw [hEq]
    exact inf_le_left
  · rcases section15_kstar_prime_and_normal_sylow
      hM.1 hMF hK hEq with
      ⟨_q, _hq, _Q, _hQ, _hQnormal, hKstarQ, hQMF⟩
    exact hKstarQ.trans hQMF

omit [IsMinCE G] in
private theorem CFSG.section15_K_ne_bot_of_MFamilyP
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    K ≠ ⊥ := by
  classical
  rcases hM.2 with ⟨p, hpκ⟩
  intro hKbot
  have hpM : p ∈ subgroupPrimeSet M :=
    (section15_kappa_subset_primeSet_diff_sigma (G := G) (M := M) hpκ).1
  have hpidx : p.val ∣ (K.subgroupOf M).index := by
    simpa [hKbot, subgroupPrimeSet, Subgroup.index_bot] using hpM
  exact (hK.2.p_in_pi_of_p_dvd_index p hpidx) hpκ

public theorem CFSG.section15_ambientDerived_hallSubgroup_of_MFamilyP
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    IsHallSubgroup (subgroupPrimeSet (ambientDerivedSubgroup M))
      ((ambientDerivedSubgroup M).subgroupOf M) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Hloc : Subgroup M := D.subgroupOf M
  let Kloc : Subgroup M := K.subgroupOf M
  have hDnormM : section10NormalIn D M := by
    simpa [D] using (section15_ambientDerived_normalIn (M := M))
  have hcompAmb : section12ComplementIn M K D := by
    simpa [D] using theorem_14_7_h (G := G) (M := M) (K := K) hM hK
  have hcompKloc : Kloc.IsComplement' Hloc := by
    simpa [D, Hloc, Kloc] using
      section15_normal_complementIn_isComplement'
        (M := M) (K := K) (N := D) hcompAmb hDnormM
  have hKlocHall : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hHcop : Nat.Coprime (Nat.card Hloc) Hloc.index := by
    simpa [Hloc, Kloc, hcompKloc.index_eq_card, hcompKloc.symm.index_eq_card]
      using hKlocHall.card_coprime_index.symm
  have hHlocHall : IsHallSubgroup (subgroupPrimeSet Hloc) Hloc := by
    refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet Hloc) (H := Hloc) ?_ ?_
    · intro p hp
      simpa [subgroupPrimeSet] using hp
    · intro p hpH hpidx
      exact (Nat.not_coprime_of_dvd_of_dvd p.property.one_lt
        (by simpa [subgroupPrimeSet] using hpH) hpidx) hHcop
  have hprime_eq : subgroupPrimeSet Hloc = subgroupPrimeSet D := by
    exact section8_subgroupPrimeSet_subgroupOf_eq
      (G := G) (H := D) (K := M)
      (by simpa [D] using (section15_ambientDerived_le (M := M)))
  simpa [D, Hloc] using (by simpa [hprime_eq] using hHlocHall)

/-- Corollary 15.6 final contradiction: if `M_F` were cyclic, Corollary 15.5
would force `F(M)` cyclic and hence `M''=1`, contradicting nontrivial `K*`. -/
private theorem CFSG.section15_corollary15_6_MF_not_cyclic
    {M MF K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKstar_ne : section14KStar M K ≠ ⊥)
    (hKstar_le_second : section14KStar M K ≤ section15SecondDerivedSubgroup M) :
    ¬ IsCyclic MF := by
  classical
  intro hMFcyc
  let D : Subgroup G := ambientDerivedSubgroup M
  let F : Subgroup G := section8FittingSubgroup M
  let C : Subgroup G := subgroupCentralizerIn M MF
  rcases hMF.1 with ⟨hMFM, hMFnormM, _hMFnil, _hMFHall⟩
  have hDcentMF : D ≤ Subgroup.centralizer (MF : Set G) := by
    simpa [D] using
      section15_ambientDerived_le_centralizer_of_cyclic_normal
        (M := M) (Z := MF) hMFM hMFnormM hMFcyc
  have hDleC : D ≤ C := by
    intro x hxD
    exact ⟨section15_ambientDerived_le (M := M) hxD, hDcentMF hxD⟩
  have hF_eq : F = C ⊔ MF := by
    simpa [F, C] using (corollary_15_5_b (M := M) (MF := MF) hM.1 hMF).2.1
  have hCleF : C ≤ F := by
    intro x hxC
    rw [hF_eq]
    exact Subgroup.mem_sup_left hxC
  have hDleF : D ≤ F := hDleC.trans hCleF
  have hKne : K ≠ ⊥ := section15_K_ne_bot_of_MFamilyP hM hK
  have hFleD : F ≤ D := by
    simpa [D, F] using
      corollary_15_5_d (M := M) (MF := MF) (K := K) hM.1 hMF hK hKne
  have hD_eq_F : D = F := le_antisymm hDleF hFleD
  have hDnil : Group.IsNilpotent D := by
    rw [hD_eq_F]
    exact section8FittingSubgroup_isNilpotent M
  have hDhall : IsHallSubgroup (subgroupPrimeSet D) (D.subgroupOf M) := by
    simpa [D] using
      section15_ambientDerived_hallSubgroup_of_MFamilyP
        (M := M) (K := K) hM hK
  have hDnilHall : section15NilpotentNormalHallIn D M :=
    ⟨by simpa [D] using (section15_ambientDerived_le (M := M)),
      by simpa [D] using (section15_ambientDerived_normalIn (M := M)).2,
      hDnil, hDhall⟩
  have hDleMF : D ≤ MF := hMF.2 D hDnilHall
  have hDcyc : IsCyclic D := by
    letI : IsCyclic MF := hMFcyc
    exact Subgroup.isCyclic_of_le hDleMF
  have hDcomm : IsMulCommutative D := by
    letI : IsCyclic D := hDcyc
    infer_instance
  have hSecond_bot : section15SecondDerivedSubgroup M = ⊥ := by
    simpa [section15SecondDerivedSubgroup, D] using
      section15_ambientDerived_eq_bot_of_isMulCommutative (M := D) hDcomm
  have hKstar_bot : section14KStar M K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    simpa [hSecond_bot] using hKstar_le_second hx
  exact hKstar_ne hKstar_bot

/-- Corollary 15.6: for `M ∈ 𝓜_P`, `K*` is a nonidentity cyclic
subgroup of both `M_F` and `M''`, and `M_F` is not cyclic. -/
public theorem CFSG.corollary_15_6
    {M MF K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14KStar M K ≠ ⊥ ∧ IsCyclic (section14KStar M K) ∧
      section14KStar M K ≤ MF ∧
        section14KStar M K ≤ section15SecondDerivedSubgroup M ∧
          ¬ IsCyclic MF := by
  have hbasic : section14KStar M K ≠ ⊥ ∧ IsCyclic (section14KStar M K) :=
    section15_corollary15_6_Kstar_nontrivial_cyclic hM hK
  have hleMF : section14KStar M K ≤ MF :=
    section15_corollary15_6_Kstar_le_MF hM hMF hK
  have hleSecond : section14KStar M K ≤ section15SecondDerivedSubgroup M :=
    section15_corollary15_6_Kstar_le_secondDerived hM hK
  have hnotCyclic : ¬ IsCyclic MF :=
    section15_corollary15_6_MF_not_cyclic
      hM hMF hK hbasic.1 hleSecond
  exact ⟨hbasic.1, hbasic.2, hleMF, hleSecond, hnotCyclic⟩

end Section15
