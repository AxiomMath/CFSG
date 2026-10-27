module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.RealVirtualParity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 12: Theorem (12.7)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.7) -/


/-- Peterfalvi `(12.7)` Theorem.

Every maximal subgroup `M` of `G` of Type I is a Frobenius group
with kernel `M_F`. -/
public theorem theorem_12_7
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF : Subgroup G)
    (hmax : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hTypeI : Section8.typeIDefinitionData M MF) :
    Section7.frobeniusWithKernel M MF := by
  by_contra hnot
  rcases exists_badPrimeForHypothesis12_of_typeIDefinitionData_not_frobenius
      M MF hmax hMF hTypeI hnot with
    ⟨p, hbad⟩
  have hbadExists : ∃ q : ℕ, badPrimeForHypothesis12 G q := ⟨p, hbad⟩
  have hMs :
      ∀ q : ℕ, ∀ M MF : Subgroup G,
        badPrimeForHypothesis12 G q →
          M ∈ section9MaximalSubgroups G →
            section16MFSubgroup M MF →
              Section8.typeIDefinitionData M MF →
                quotientHasNoncyclicSylow q MF M →
                  Section8.msChoiceSource M MF MF := by
    intro _q _M _MF _hbadq _hM _hMF hTypeI _hquot
    exact Section8.msChoiceSource_of_typeIDefinitionData hTypeI
  rcases exists_hypothesis_12_8_data_of_badPrimeForHypothesis12_exists
      (G := G) hbadExists hMs with
    ⟨M0, K0, K0', P0, q, h128⟩
  exact theorem_12_16 M0 K0 K0' P0 q h128

/-- Invoke PF `(12.7)` for one representative in the PF `(12.17)`
all-Type-I route. -/
public theorem theorem_12_17_representative_frobeniusWithKernel
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF : Subgroup G → Subgroup G}
    (hRepSystem : theorem_12_17_representative_system_data Ms MF)
    (M : Subgroup G)
    (hM : M ∈ Ms) :
    Section7.frobeniusWithKernel M (MF M) := by
  classical
  have hReps16 : section16MaximalConjugacyRepresentatives (G := G) Ms := by
    simpa [Section8.representativeSystemData] using hRepSystem.1
  exact theorem_12_7 M (MF M) (hReps16.1 M hM)
    (hRepSystem.2 M hM).1 (hRepSystem.2 M hM).2.2

/-- In the PF `(12.17)` representative system, `N_G((L_i)_F) = L_i`.

This is the source step saying that, since `G` is simple and `L_i` is
maximal, the nontrivial normal subgroup `(L_i)_F` has normalizer exactly
`L_i`. -/
public theorem theorem_12_17_representative_normalizer_mf_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinCE G)
    {Ms : List (Subgroup G)}
    {MF : Subgroup G → Subgroup G}
    (hRepSystem : theorem_12_17_representative_system_data Ms MF)
    (M : Subgroup G)
    (hM : M ∈ Ms) :
    Subgroup.normalizer ((MF M : Subgroup G) : Set G) = M := by
  classical
  letI : IsMinCE G := hmin
  have hReps16 : section16MaximalConjugacyRepresentatives (G := G) Ms := by
    simpa [Section8.representativeSystemData] using hRepSystem.1
  have hMmax9 : M ∈ section9MaximalSubgroups G := hReps16.1 M hM
  have hMmax8 : M ∈ section8MaximalSubgroups G :=
    section8_maximal_of_section9_maximal (G := G) hMmax9
  have hMFdata : section16MFSubgroup M (MF M) := (hRepSystem.2 M hM).1
  rcases hMFdata.1 with ⟨hMFM, hMFnorm, _hNil, _hHall⟩
  rcases (hRepSystem.2 M hM).2.2 with ⟨_, _, _, hF, _hTypeICases⟩
  have hMF_ne_bot : MF M ≠ ⊥ := ne_of_gt hF.2.2.2.1
  exact
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      (G := G) hMmax8 hMFM hMF_ne_bot hMFnorm

/-- In a maximal subgroup, the Frobenius kernel `M_F` is a
`σ(M)`-subgroup.  This is the PF `(12.17)` part of Theorem E(2) needed to
turn the disjoint union of the `σ(L_i)` into coprimeness of the kernels
`H_i = (L_i)_F`. -/
public theorem theorem_12_17_mf_isPiSubgroup_sigma_of_maximal
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M) MF := by
  classical
  rcases theorem_16_A (G := G) hM hMF with ⟨K, U, hA⟩
  dsimp [section16TheoremAConclusions] at hA
  rcases hA with
    ⟨hA1, _hKcyc, _hKHall, _hKnorm, _hCompKM, _hUMsigmaNormal,
      _hProduct, _hUnormal, _hCentralizersU, _hKstarNe, _hCentralizersK,
      _hMFpos, hMFleSigma, _hSigmaLeDerived, _hDerivedProper, _hQuotNil,
      _hSecondLeFitting, _hFittingEq, _hFittingLeDerived,
      _hProperBranch⟩
  have hSigmaHall :
      section12HallSubgroupIn (section10SigmaPrimes M) (section10Msigma M) M :=
    hA1.2.1
  intro p hpMF
  have hpSigmaSubgroup : p ∈ subgroupPrimeSet (section10Msigma M) :=
    section8_subgroupPrimeSet_mono hMFleSigma hpMF
  have hpSigmaCard : p.val ∣ Nat.card (section10Msigma M) := by
    simpa [subgroupPrimeSet] using hpSigmaSubgroup
  have hpSigmaSubgroupOf :
      p.val ∣ Nat.card ((section10Msigma M).subgroupOf M) := by
    rw [section12_card_subgroupOf_eq hSigmaHall.1]
    exact hpSigmaCard
  exact hSigmaHall.2.p_in_pi_of_p_dvd_card p hpSigmaSubgroupOf

/-- PF `(12.17)`, condition `(7.10.c)`: kernels attached to distinct
maximal-subgroup conjugacy representatives have coprime orders. -/
public theorem theorem_12_17_representative_kernel_card_coprime
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {Ms : List (Subgroup G)}
    {MF : Subgroup G → Subgroup G}
    (hRepSystem : theorem_12_17_representative_system_data Ms MF) :
    ∀ i j : Fin Ms.length, i ≠ j →
      Nat.Coprime (Nat.card (MF (Ms.get i))) (Nat.card (MF (Ms.get j))) := by
  classical
  have hReps16 : section16MaximalConjugacyRepresentatives (G := G) Ms := by
    simpa [Section8.representativeSystemData] using hRepSystem.1
  have hSigmaDisjoint :
      ∀ i j : Fin (Ms.map section10SigmaPrimes).length, i ≠ j →
        Disjoint ((Ms.map section10SigmaPrimes).get i)
          ((Ms.map section10SigmaPrimes).get j) :=
    (theorem_16_E_2 (G := G) Ms hReps16).2
  intro i j hij
  have hMi : Ms.get i ∈ section9MaximalSubgroups G :=
    hReps16.1 (Ms.get i) (List.get_mem Ms i)
  have hMj : Ms.get j ∈ section9MaximalSubgroups G :=
    hReps16.1 (Ms.get j) (List.get_mem Ms j)
  have hMFi : section16MFSubgroup (Ms.get i) (MF (Ms.get i)) :=
    (hRepSystem.2 (Ms.get i) (List.get_mem Ms i)).1
  have hMFj : section16MFSubgroup (Ms.get j) (MF (Ms.get j)) :=
    (hRepSystem.2 (Ms.get j) (List.get_mem Ms j)).1
  have hPi_i :
      IsPiSubgroup (G := G) (section10SigmaPrimes (Ms.get i)) (MF (Ms.get i)) :=
    theorem_12_17_mf_isPiSubgroup_sigma_of_maximal (G := G) hMi hMFi
  have hPi_j :
      IsPiSubgroup (G := G) (section10SigmaPrimes (Ms.get j)) (MF (Ms.get j)) :=
    theorem_12_17_mf_isPiSubgroup_sigma_of_maximal (G := G) hMj hMFj
  let i' : Fin (Ms.map section10SigmaPrimes).length :=
    ⟨i.1, by
      simp [List.length_map]⟩
  let j' : Fin (Ms.map section10SigmaPrimes).length :=
    ⟨j.1, by
      simp [List.length_map]⟩
  have hij' : i' ≠ j' := by
    intro h
    apply hij
    apply Fin.ext
    simpa [i', j'] using congrArg Fin.val h
  have hdis :
      Disjoint (section10SigmaPrimes (Ms.get i))
        (section10SigmaPrimes (Ms.get j)) := by
    simpa [i', j', List.length_map] using hSigmaDisjoint i' j' hij'
  exact section10_coprime_card_of_isPiSubgroup_disjoint_primes hPi_i hPi_j hdis

/-- PF `(12.17)`, easy Type-I branch: if the Type-I definition supplies the
literal `H#` TI condition, convert it to the Section 7/Section 2 package used
by PF `(7.10)`. -/
public theorem theorem_12_17_isTISubsetWithNormalizer_puncturedSubgroupSet_of_section16
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (L H : Subgroup G)
    (hmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hHne : H.subgroupOf L ≠ ⊥)
    (hTI : section16TISubset (section16NonidentityElements (H : Set G))) :
    Section2.IsTISubsetWithNormalizer
      (Section7.puncturedSubgroupSet H) L := by
  classical
  have hHL : H ≤ L := section16MFSubgroup_le hMF
  have hHmap : (H.subgroupOf L).map L.subtype = H := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyH, hyx⟩
      simpa [← hyx] using (Subgroup.mem_subgroupOf.1 hyH)
    · intro hx
      exact ⟨⟨x, hHL hx⟩, hx, rfl⟩
  have hAeq :
      Section6.subgroupImagePuncturedSet L (H.subgroupOf L) =
        Section7.puncturedSubgroupSet H := by
    rw [Section6.theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured, hHmap]
    ext x
    rfl
  have hImg :
      Section2.IsTISubsetWithNormalizer
        (Section6.subgroupImagePuncturedSet L (H.subgroupOf L)) L :=
    theorem_12_6_isTISubsetWithNormalizer_subgroupImagePuncturedSet
      L H hmax hHL (section16MFSubgroup_subgroupOf_normal hMF) hHne hTI
  simpa [hAeq] using hImg

private theorem theorem_12_17_subgroupOf_ne_bot_of_gt_bot
    {G : Type u} [Group G] {L H : Subgroup G}
    (hHL : H ≤ L) (hHgt : (⊥ : Subgroup G) < H) :
    H.subgroupOf L ≠ ⊥ := by
  intro hbot
  have hHleBot : H ≤ (⊥ : Subgroup G) := by
    intro x hxH
    have hxSub : (⟨x, hHL hxH⟩ : L) ∈ H.subgroupOf L := hxH
    have hxBot : (⟨x, hHL hxH⟩ : L) ∈ (⊥ : Subgroup L) := by
      simpa [hbot] using hxSub
    have hxoneL : (⟨x, hHL hxH⟩ : L) = 1 := Subgroup.mem_bot.mp hxBot
    have hxoneG : x = 1 := congrArg Subtype.val hxoneL
    simp [hxoneG]
  exact hHgt.ne' (le_antisymm hHleBot bot_le)

private theorem theorem_12_17_puncturedSubgroupSet_nonempty_of_ne_bot
    {G : Type u} [Group G] {H : Subgroup G}
    (hHne : H ≠ (⊥ : Subgroup G)) :
    (Section7.puncturedSubgroupSet H).Nonempty := by
  by_contra hEmpty
  apply hHne
  rw [Subgroup.eq_bot_iff_forall]
  intro x hxH
  by_contra hxne
  exact hEmpty ⟨x, hxH, hxne⟩

private theorem theorem_12_17_setNormalizer_puncturedSubgroupSet_eq
    {G : Type u} [Group G] {L H : Subgroup G}
    (hNorm : Subgroup.normalizer ((H : Set G)) = L) :
    Section2.setNormalizer (Section7.puncturedSubgroupSet H) = L := by
  ext g
  constructor
  · intro hg
    have hgNormH : g ∈ Subgroup.normalizer ((H : Set G)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hxH
        by_cases hx1 : x = 1
        · simp [hx1]
        · exact ((hg x).2 ⟨hxH, hx1⟩).1
      · intro hxH
        by_cases hx1 : x = 1
        · simp [hx1]
        · have hxConjNe : Section2.conjBy g x ≠ 1 := by
            intro hconj
            apply hx1
            have h := congrArg (fun y : G => g⁻¹ * y * g) hconj
            simpa [Section2.conjBy, mul_assoc] using h
          exact ((hg x).1 ⟨hxH, hxConjNe⟩).1
    simpa [hNorm] using hgNormH
  · intro hgL
    have hgNormH : g ∈ Subgroup.normalizer ((H : Set G)) := by
      simpa [hNorm] using hgL
    rw [Subgroup.mem_normalizer_iff] at hgNormH
    intro x
    constructor
    · intro hx
      refine ⟨(hgNormH x).2 hx.1, ?_⟩
      intro hxone
      exact hx.2 (by simp [hxone, Section2.conjBy])
    · intro hx
      refine ⟨(hgNormH x).1 hx.1, ?_⟩
      intro hconj
      apply hx.2
      have h := congrArg (fun y : G => g⁻¹ * y * g) hconj
      simpa [Section2.conjBy, mul_assoc] using h

/-- If the textbook support step has shown `C_G(x) ≤ L` for every
`x ∈ H#`, then PF `(2.3)` upgrades the punctured kernel to the
`IsTISubsetWithNormalizer` package needed in PF `(7.10)`. -/
public theorem theorem_12_17_isTISubsetWithNormalizer_puncturedSubgroupSet_of_centralizer_le
    {G : Type u} [Group G] [Finite G]
    (L H : Subgroup G)
    (hHL : H ≤ L)
    (hHne : H ≠ (⊥ : Subgroup G))
    (hNorm : Subgroup.normalizer ((H : Set G)) = L)
    (hFusion :
      ∀ ⦃a b : G⦄,
        a ∈ Section7.puncturedSubgroupSet H →
        b ∈ Section7.puncturedSubgroupSet H →
        Section2.conjugateIn a b →
          Section2.conjugateInSubgroup L a b)
    (hCent :
      ∀ ⦃a : G⦄,
        a ∈ Section7.puncturedSubgroupSet H →
          Section2.elementCentralizer a ≤ L) :
    Section2.IsTISubsetWithNormalizer
      (Section7.puncturedSubgroupSet H) L := by
  classical
  let A : Set G := Section7.puncturedSubgroupSet H
  have hAne : A.Nonempty :=
    theorem_12_17_puncturedSubgroupSet_nonempty_of_ne_bot (H := H) hHne
  have hNormA : Section2.setNormalizer A = L :=
    theorem_12_17_setNormalizer_puncturedSubgroupSet_eq (L := L) (H := H) hNorm
  have hHyp : Section2.Hypothesis2 A L (fun _ : G => (⊥ : Subgroup G)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      exact ha.2
    · intro a ha
      exact hHL ha.1
    · rw [hNormA]
    · intro a b ha hb hconj
      exact hFusion ha hb hconj
    · intro a ha
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        have hx1 : x = 1 := by simpa using hx
        subst x
        simp [Section2.elementCentralizer]
      · intro x hx
        exact hx.2
      · intro x hx y hy
        have hy1 : y = 1 := by simpa using hy
        subst y
        simp [Section2.conjBy]
      · simp [Section2.centralizerIn]
      · intro c hc
        refine ⟨1, by simp, c, ?_, by simp⟩
        exact ⟨hCent ha hc, hc⟩
    · intro a b ha hb
      simp
  exact (Section2.proposition_2_3 A L hAne).mpr hHyp


public theorem theorem_12_17_frobenius_kernel_centralizer_contradiction
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G} {x y : G}
    (hfrob : Section7.frobeniusWithKernel L H)
    (hxL : x ∈ L)
    (hxnotH : x ∉ H)
    (hyH : y ∈ H)
    (hyne : y ≠ 1)
    (hycent : y ∈ Section2.elementCentralizer x) :
    False := by
  have hfrob6 : Section6.frobeniusWithKernel L H := by
    simpa [Section6.frobeniusWithKernel, Section7.frobeniusWithKernel] using hfrob
  have hcentBot : Section2.centralizerIn H x = ⊥ :=
    Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
      hfrob6 x hxL hxnotH
  have hyCentIn : y ∈ Section2.centralizerIn H x := ⟨hyH, hycent⟩
  have hyBot : y ∈ (⊥ : Subgroup G) := by
    simpa [hcentBot] using hyCentIn
  exact hyne (Subgroup.mem_bot.mp hyBot)

/-- A minimal counterexample has at least two maximal-subgroup conjugacy
representatives in the PF `(12.17)` all-Type-I contradiction route. -/
public theorem theorem_12_17_representative_system_card_ge_two_source_leaf
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinCE G)
    {Ms : List (Subgroup G)}
    {MF : Subgroup G → Subgroup G}
    (hRepSystem : theorem_12_17_representative_system_data Ms MF) :
    2 ≤ Fintype.card (Fin Ms.length) := by
  classical
  letI : IsMinCE G := hmin
  have hReps16 : section16MaximalConjugacyRepresentatives (G := G) Ms := by
    simpa [Section8.representativeSystemData] using hRepSystem.1
  rw [Fintype.card_fin]
  by_contra hcard
  have hbot_ne_top : (⊥ : Subgroup G) ≠ ⊤ := by
    intro hbot
    apply IsMinCE.not_solvable (G := G)
    apply isSolvable_of_comm
    intro x y
    have hx : x = 1 := Subgroup.mem_bot.mp (by simp [hbot])
    have hy : y = 1 := Subgroup.mem_bot.mp (by simp [hbot])
    simp [hx, hy]
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) hbot_ne_top with ⟨N, hNmax, _hbotN⟩
  rcases hReps16.2.2 N hNmax with ⟨L, ⟨hLMs, _hNconjL⟩, _hunique⟩
  have hlen_pos : 0 < Ms.length := List.length_pos_of_mem hLMs
  have hlen_one : Ms.length = 1 := by omega
  rcases List.length_eq_one_iff.mp hlen_one with ⟨L0, hMs⟩
  subst Ms
  have hL_eq : L = L0 := by simpa using hLMs
  subst L
  have hL0mem : L0 ∈ [L0] := by simp
  have hL0max : L0 ∈ section9MaximalSubgroups G :=
    hReps16.1 L0 hL0mem
  have hL0MF : section16MFSubgroup L0 (MF L0) :=
    (hRepSystem.2 L0 hL0mem).1
  have hL0TypeI : Section8.typeIDefinitionData L0 (MF L0) :=
    (hRepSystem.2 L0 hL0mem).2.2
  have hBGTypeI : section16TypeI L0 (MF L0) :=
    (hRepSystem.2 L0 hL0mem).2.1
  rcases hL0TypeI with ⟨U, U1, U0, hTypeF, _hTypeICases⟩
  rcases hTypeF with
    ⟨_hsolv, _hodd, _hMF, _hMFpos, hMFlt, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hCent, _hU0le, _hExp, _hFrob⟩
  have hMF_eq_sigma : MF L0 = section10Msigma L0 :=
    (section16_typeI_KUData_of_complement
      (G := G) hL0max hL0MF hBGTypeI hcomp).2
  have hPrimeSubset : subgroupPrimeSet L0 ⊆ section10SigmaPrimes L0 := by
    intro p hpL0
    have hpTop : p ∈ subgroupPrimeSet (⊤ : Subgroup G) :=
      section8_subgroupPrimeSet_mono (le_top : L0 ≤ (⊤ : Subgroup G)) hpL0
    rcases ((theorem_16_E_2 (G := G) [L0] hReps16).1 p).mp hpTop with
      ⟨i, hi⟩
    simpa using hi
  have hSigmaTop : section10MsigmaSubgroup L0 = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hqprime hqidx
    let p : Nat.Primes := ⟨q, hqprime⟩
    have hpidx : p.val ∣ (section10MsigmaSubgroup L0).index := by
      simpa [p] using hqidx
    have hp_not_sigma : p ∉ section10SigmaPrimes L0 :=
      ((theorem_10_2_b (G := G) hL0max).2).p_in_pi_of_p_dvd_index p hpidx
    have hpL0 : p ∈ subgroupPrimeSet L0 := by
      have hmul :
          (section10MsigmaSubgroup L0).index *
              Nat.card (section10MsigmaSubgroup L0) = Nat.card L0 :=
        Subgroup.index_mul_card (H := section10MsigmaSubgroup L0)
      have hp_mul :
          p.val ∣ (section10MsigmaSubgroup L0).index *
            Nat.card (section10MsigmaSubgroup L0) :=
        dvd_mul_of_dvd_left hpidx _
      rw [hmul] at hp_mul
      simpa [subgroupPrimeSet] using hp_mul
    exact hp_not_sigma (hPrimeSubset hpL0)
  have hSigma_eq_L0 : section10Msigma L0 = L0 := by
    rw [section10Msigma, hSigmaTop]
    simpa [MonoidHom.range_eq_map] using
      (L0.range_subtype : L0.subtype.range = L0)
  rw [hMF_eq_sigma, hSigma_eq_L0] at hMFlt
  exact (lt_irrefl L0) hMFlt

/-- Source leaf for PF `(12.17)`: in the non-TI Type-I alternatives, every
nonidentity element of the Frobenius kernel has ambient centralizer contained
in its maximal subgroup representative. -/
public theorem theorem_12_17_centralizer_le_of_all_typeI_source_leaf
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinCE G)
    (hall : ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      ∃ MF : Subgroup G,
        section16MFSubgroup M MF ∧ section16TypeI M MF ∧
          Section8.typeIDefinitionData M MF)
    (L H : Subgroup G)
    (hmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hBGTypeI : section16TypeI L H)
    (hTypeI : Section8.typeIDefinitionData L H)
    (_hfrob : Section7.frobeniusWithKernel L H)
    (_hNorm : Subgroup.normalizer ((H : Subgroup G) : Set G) = L) :
    ∀ ⦃a : G⦄,
      a ∈ Section7.puncturedSubgroupSet H →
        Section2.elementCentralizer a ≤ L := by
  classical
  letI : IsMinCE G := hmin
  intro a ha
  by_contra hcent_not_le
  have ha_ne_one : a ≠ 1 := ha.2
  have hcentralizer_ne_top :
      Subgroup.centralizer ({a} : Set G) ≠ ⊤ :=
    section8_centralizer_singleton_ne_top_of_ne_one ha_ne_one
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      hcentralizer_ne_top with ⟨M, hMcont⟩
  have hTypeI' := hTypeI
  rcases hTypeI' with ⟨U, _U1, _U0, hTypeF, _hCases⟩
  rcases hTypeF with
    ⟨_hsolv, _hodd, _hMF, _hMFne, _hMFM, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrobU0⟩
  rcases section16_typeI_KUData_of_complement
      (G := G) hmax hMF hBGTypeI hcomp with ⟨hKU, hH_eq_sigma⟩
  have haUnion : a ∈ Section8.section8CentralizerUnion L H := by
    refine ⟨a, ⟨ha.1, ha_ne_one⟩, ⟨?_, ha_ne_one⟩⟩
    exact ⟨section16MFSubgroup_le hMF ha.1,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have haASet : a ∈ section16ASet L U :=
    Section8.theorem_8_13_source_centralizerUnion_subset_ASet_of_complement
      (G := G) (M := L) (D := L) (H := H) (U := U)
      (A := Section8.section8CentralizerUnion L H) le_rfl hMF hH_eq_sigma
      hcomp rfl haUnion
  have haD : a ∈ section16TheoremIIDSet L (section16ASet L U) :=
    ⟨haASet, ha_ne_one, by
      simpa [Section2.elementCentralizer] using hcent_not_le⟩
  have hII := theorem_16_II (G := G) hmax hMF hKU (Or.inl rfl)
  rcases theorem_16_II_canonical_D_data
      (G := G) hmax hMF hKU (Or.inl rfl) haD with
    ⟨NK, NU, hNcont, hNMF, hNKU, haN, hNType, _hNcomp, _hNTypeII⟩
  rcases hII.2.1 a haD with ⟨N, hNunique⟩
  have hM_eq_N : M = section14N a := by
    have hM_eq : M = N := by
      have : M ∈ ({N} : Set (Subgroup G)) := by
        simpa [← hNunique] using hMcont
      simpa using this
    have hN_eq : section14N a = N := by
      have : section14N a ∈ ({N} : Set (Subgroup G)) := by
        simpa [← hNunique] using hNcont
      simpa using this
    exact hM_eq.trans hN_eq.symm
  subst M
  rcases hall (section14N a) hNcont.1 with
    ⟨MF, hNMF', hNBGTypeI, hNSourceTypeI⟩
  have hMF_eq_sigma : MF = section10Msigma (section14N a) :=
    section16MFSubgroup_unique hNMF' hNMF
  have hNSourceTypeI' :
      Section8.typeIDefinitionData (section14N a)
        (section10Msigma (section14N a)) := by
    simpa [hMF_eq_sigma] using hNSourceTypeI
  have hNBGTypeI' :
      section16TypeI (section14N a) (section10Msigma (section14N a)) := by
    simpa [hMF_eq_sigma] using hNBGTypeI
  rcases hNType with hNTypeI | hNTypeII
  · have haSource :=
      Section8.theorem_8_13_source_typeI_mem_A_diff_A1_of_ASet
        (G := G) haN
    rcases haSource with ⟨haCentralizerUnion, ha_not_a1⟩
    have ha_not_sigma : a ∉ section10Msigma (section14N a) := by
      intro haSigma
      exact ha_not_a1 ⟨haSigma, ha_ne_one⟩
    rw [Section8.section8CentralizerUnion] at haCentralizerUnion
    rcases haCentralizerUnion with
      ⟨y, ⟨hySigma, hy_ne_one⟩, ⟨haCentY, _ha_ne_one'⟩⟩
    have hyCentA : y ∈ Section2.elementCentralizer a := by
      rw [Section2.elementCentralizer,
        Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp haCentY.2).symm
    have haNmem : a ∈ section14N a := by
      exact hNcont.2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    exact theorem_12_17_frobenius_kernel_centralizer_contradiction
      (theorem_12_7 (section14N a) (section10Msigma (section14N a))
        hNcont.1 hNMF hNSourceTypeI')
      haNmem ha_not_sigma hySigma hy_ne_one hyCentA
  · have hCases := proposition_16_1 (G := G) hNcont.1 hNMF hNKU
    have hCaseF : section16CaseF NK NU := hCases.1.mp hNBGTypeI'
    have hCaseP2 : section16CaseP2 NK NU := hCases.2.1.mp hNTypeII
    exact False.elim (hCaseP2.1 hCaseF.1)

/-- Source leaf for PF `(12.17)`: every nonidentity element lies in a conjugate
of one of the punctured Frobenius kernels in the all-Type-I contradiction
route. -/
public theorem theorem_12_17_conjugate_kernel_cover_nonidentity_source_leaf
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinCE G)
    (hall : ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      ∃ MF : Subgroup G,
        section16MFSubgroup M MF ∧ section16TypeI M MF ∧
          Section8.typeIDefinitionData M MF)
    {Ms : List (Subgroup G)}
    {MF : Subgroup G → Subgroup G}
    (hRepSystem : theorem_12_17_representative_system_data Ms MF)
    (hTI : ∀ i : Fin Ms.length,
      Section2.IsTISubsetWithNormalizer
        (Section7.puncturedSubgroupSet (MF (Ms.get i))) (Ms.get i)) :
    ∀ ⦃g : G⦄,
      g ≠ 1 →
        g ∈ ⋃ i : Fin Ms.length,
          Section2.conjugateSet
            (Section7.puncturedSubgroupSet (MF (Ms.get i))) := by
  classical
  letI : IsMinCE G := hmin
  have hReps : section16MaximalConjugacyRepresentatives (G := G) Ms := by
    simpa [Section8.representativeSystemData] using hRepSystem.1
  have hNoP : ∀ P : Subgroup G, ¬ section16MaximalTypeP P := by
    intro P hP
    have hPmax : P ∈ section9MaximalSubgroups G := by
      rcases (by
        simpa [section16MaximalTypeP, section14MFamilyP] using hP) with
        ⟨hPmax, _hKappa⟩
      exact hPmax
    rcases hall P hPmax with ⟨PF, hPF, hPTypeI, _hPSourceTypeI⟩
    exact (section16_not_typeI_of_maximalTypeP (G := G) hP hPF) hPTypeI
  have hCover :
      section16NonidentityElements (Set.univ : Set G) =
        section16TildeGForRepresentatives Ms (fun _ x => section14R x) :=
    theorem_16_E_3_noP_nonidentity_eq_tildeG (G := G) Ms hReps hNoP
  intro g hg
  have hgNonidentity :
      g ∈ section16NonidentityElements (Set.univ : Set G) :=
    ⟨Set.mem_univ g, hg⟩
  have hgTilde :
      g ∈ section16TildeGForRepresentatives Ms (fun _ x => section14R x) := by
    rw [← hCover]
    exact hgNonidentity
  rcases hgTilde with
    ⟨M, hMmem, x, ⟨a, haSigma, hane, r, hr, hxa⟩, z, _hz, hgz⟩
  rcases List.mem_iff_get.mp hMmem with ⟨i, hiM⟩
  subst M
  have hMmem' : Ms.get i ∈ Ms := List.get_mem Ms i
  rcases hRepSystem.2 (Ms.get i) hMmem' with
    ⟨hMF, hBGTypeI, hSourceTypeI⟩
  rcases hSourceTypeI with ⟨U, _U1, _U0, hTypeF, _hCases⟩
  rcases hTypeF with
    ⟨_hsolv, _hodd, _hMF, _hMFne, _hMFM, _hUne, hcomp, _hU1le,
      _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrob⟩
  have hSigmaEq : MF (Ms.get i) = section10Msigma (Ms.get i) :=
    (section16_typeI_KUData_of_complement
      (G := G) (hReps.1 (Ms.get i) hMmem') hMF hBGTypeI hcomp).2
  have haSharp : a ∈ Section7.puncturedSubgroupSet (MF (Ms.get i)) := by
    refine ⟨?_, hane⟩
    rw [hSigmaEq]
    exact haSigma
  have hHyp2 :
      Section2.Hypothesis2
        (Section7.puncturedSubgroupSet (MF (Ms.get i))) (Ms.get i)
        (fun _ : G => (⊥ : Subgroup G)) :=
    (Section2.proposition_2_3
      (Section7.puncturedSubgroupSet (MF (Ms.get i))) (Ms.get i)
      (hTI i).1).mp (hTI i)
  have haCent : Section2.elementCentralizer a ≤ Ms.get i := by
    intro c hc
    have hprod := hHyp2.centralizer_eq_product haSharp
    rcases hprod.mul_surjective c hc with ⟨b, hb, k, hk, hck⟩
    have hb1 : b = 1 := by simpa using hb
    subst b
    have hck' : c = k := by simpa using hck
    have hkM : (k : G) ∈ Ms.get i := hk.1
    simpa [hck'] using hkM
  have haRbot : section14R a = (⊥ : Subgroup G) :=
    section16_section14R_eq_bot_of_centralizer_le_public
      (G := G) (hReps.1 (Ms.get i) hMmem') haSigma hane (by
        simpa [Section2.elementCentralizer] using haCent)
  have hr1 : r = 1 := by
    change r ∈ section14R a at hr
    rw [haRbot] at hr
    exact Subgroup.mem_bot.mp hr
  subst r
  have hx_eq : x = a := by simpa using hxa
  subst x
  rw [Set.mem_iUnion]
  refine ⟨i, a, haSharp, ?_⟩
  exact ⟨z, by simpa [Section2.conjBy] using hgz.symm⟩

/-- Elements in a conjugate of a punctured subgroup are nonidentity. -/
public theorem theorem_12_17_conjugate_kernel_cover_only_nonidentity
    {G : Type u} [Group G]
    {I : Type v} [Fintype I]
    (H : I → Subgroup G) :
    ∀ ⦃g : G⦄,
      g ∈ ⋃ i : I, Section2.conjugateSet (Section7.puncturedSubgroupSet (H i)) →
        g ≠ 1 := by
  intro g hg hg1
  rw [Set.mem_iUnion] at hg
  rcases hg with ⟨i, hg⟩
  rcases hg with ⟨s, hs, hconj⟩
  rcases hconj with ⟨y, hy⟩
  have hconj1 : Section2.conjBy y s = 1 := by
    simpa [hg1] using hy
  have hs1 : s = 1 := by
    simpa [Section2.conjBy, mul_assoc] using
      congrArg (fun z : G => y⁻¹ * z * y) hconj1
  exact hs.2 hs1

/-- Source wrapper for PF `(12.17)`: the conjugates of the punctured Frobenius
kernels cover all nonidentity elements in the all-Type-I contradiction route. -/
public theorem theorem_12_17_conjugate_kernel_cover_source_leaf
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinCE G)
    (hall : ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      ∃ MF : Subgroup G,
        section16MFSubgroup M MF ∧ section16TypeI M MF ∧
          Section8.typeIDefinitionData M MF)
    {Ms : List (Subgroup G)}
    {MF : Subgroup G → Subgroup G}
    (hRepSystem : theorem_12_17_representative_system_data Ms MF)
    (hTI : ∀ i : Fin Ms.length,
      Section2.IsTISubsetWithNormalizer
        (Section7.puncturedSubgroupSet (MF (Ms.get i))) (Ms.get i)) :
    ({1} : Set G) =
      (Set.univ \ ⋃ i : Fin Ms.length,
        Section2.conjugateSet
          (Section7.puncturedSubgroupSet (MF (Ms.get i)))) := by
  ext g
  constructor
  · intro hg
    refine ⟨Set.mem_univ g, ?_⟩
    intro hmem
    have hg1 : g = 1 := by simpa using hg
    exact theorem_12_17_conjugate_kernel_cover_only_nonidentity
      (fun i : Fin Ms.length => MF (Ms.get i)) hmem hg1
  · intro hg
    by_cases hg1 : g = 1
    · simp [hg1]
    · exact False.elim (hg.2
        (theorem_12_17_conjugate_kernel_cover_nonidentity_source_leaf
          hmin hall hRepSystem hTI hg1))

set_option maxHeartbeats 1000000 in
/-- Source leaf for PF `(12.17)`: the lower-bound data needed to invoke
PF `(7.11)` from the all-Type-I family. -/
public theorem theorem_12_17_lowerBoundData_source_leaf
    {G : Type u} [Group G] [Finite G]
    {I : Type v} [Fintype I]
    (L H : I → Subgroup G)
    (hmin : IsMinCE G)
    (hCardI : 2 ≤ Fintype.card I)
    (hMax : ∀ i : I, L i ∈ section9MaximalSubgroups G)
    (hMF : ∀ i : I, section16MFSubgroup (L i) (H i))
    (hTypeI : ∀ i : I, Section8.typeIDefinitionData (L i) (H i))
    (hFrob : ∀ i : I, Section7.frobeniusWithKernel (L i) (H i))
    (hTI : ∀ i : I,
      Section2.IsTISubsetWithNormalizer
        (Section7.puncturedSubgroupSet (H i)) (L i))
    (hCoprime : ∀ i j : I, i ≠ j → Nat.Coprime (Nat.card (H i)) (Nat.card (H j)))
    (hG0 : ({1} : Set G) =
      (Set.univ \ ⋃ i : I, Section2.conjugateSet (Section7.puncturedSubgroupSet (H i)))) :
    Section7.theorem_7_10_lowerBoundData L H ({1} : Set G) := by
  classical
  letI : IsMinCE G := hmin
  let A : I → Set G := fun i => Section7.puncturedSubgroupSet (H i)
  have hAeq (i : I) : typeIASet (L i) (H i) = A i := by
    simpa [A, Section7.puncturedSubgroupSet,
      section16NonidentityElements] using
      typeIASet_eq_nonidentity_kernel_of_frobenius (L i) (H i) (hFrob i)
  choose S hS using fun i : I => exists_puncturedInducedFamily ((H i).subgroupOf (L i))
  let R : I → G → Subgroup G := fun _ _ => ⊥
  have h22 (i : I) :
      Section2.Hypothesis2 (typeIASet (L i) (H i)) (L i) (R i) := by
    have htriv : Section2.Hypothesis2 (A i) (L i) (fun _ : G => ⊥) :=
      (Section2.proposition_2_3 (A i) (L i) (hTI i).1).mp (hTI i)
    simpa [R, hAeq i] using htriv
  let τ : (i : I) →
      Section1.ClassFunction (L i) →ₗ[ℂ] Section1.ClassFunction G :=
    fun i => dadeTransformLinear (R i) (h22 i).subset_L
  have hDade (i : I) :
      dadeIsometryRelativeToTypeIASet (L i) (H i) (R i) (τ i) := by
    simpa [τ] using
      dadeIsometryRelativeToTypeIASet_of_hypothesis2
        (L i) (H i) (R i) (h22 i)
  have h12 (i : I) : hypothesis_12_1_data (L i) (H i) (S i) (R i) (τ i) :=
    ⟨hMax i, hMF i, hTypeI i, hS i, hDade i⟩
  have h126 (i : I) :
      (∀ χ : Section1.ClassFunction (L i), χ ∈ S i →
        Section1.IsIrreducibleCharacterOnGroup χ) ∧
      Section6.coherentFamily (S i) (τ i) :=
    theorem_12_6 (L i) (H i) (S i) (R i) (τ i) (h12 i) (hFrob i)
  choose ν hν using fun i : I =>
    Section6.theorem_6_8_coherentExtension_of_coherentFamily (h126 i).2
  have hζexists (i : I) :
      ∃ ζ : Section1.ClassFunction (L i),
        ζ ∈ S i ∧ Section1.IsIrreducibleCharacterOnGroup ζ ∧
          Section1.degree ζ = ((H i).relIndex (L i) : ℂ) := by
    rcases (hMF i).1 with ⟨hHL, _hHnormal, hHnil, _hHall⟩
    letI : Group.IsNilpotent (H i) := hHnil
    haveI : IsSolvable (H i) := IsNilpotent.to_isSolvable
    let e : (H i).subgroupOf (L i) ≃* H i :=
      Subgroup.subgroupOfEquivOfLe hHL
    have hKsolv : IsSolvable ((H i).subgroupOf (L i)) :=
      solvable_of_solvable_injective (f := e.toMonoidHom) e.injective
    rcases hTypeI i with ⟨_U, _U1, _U0, hF, _hcases⟩
    have hHne : H i ≠ ⊥ := hF.2.2.2.1.ne'
    have hsub_ne : (H i).subgroupOf (L i) ≠ ⊥ := by
      intro hbot
      apply hHne
      exact (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hHL
    have hSbot :
        Section6.inducedKernelFamily ((H i).subgroupOf (L i))
          (⊥ : Subgroup (L i)) (S i) :=
      theorem_12_6_inducedKernelFamily_bot_of_hypothesis12
        (L i) (H i) (S i) (R i) (τ i) (h12 i)
    rcases Section6.inducedKernelFamily_exists_degree_relIndex_of_lt
        hKsolv (inferInstance : (⊥ : Subgroup (L i)).Normal)
        (bot_lt_iff_ne_bot.mpr hsub_ne) hSbot with
      ⟨ζ, hζS, hζdeg⟩
    refine ⟨ζ, hζS, (h126 i).1 ζ hζS, ?_⟩
    have hrel :
        ((H i).subgroupOf (L i)).relIndex (⊤ : Subgroup (L i)) =
          (H i).relIndex (L i) := by
      simpa using
        (Subgroup.relIndex_subgroupOf
          (H := H i) (K := L i) (L := L i) le_rfl)
    simpa [hrel] using hζdeg
  choose ζ hζ using hζexists
  let T : (i : I) → Finset (Section1.ClassFunction (L i)) :=
    fun i => insert (Section7.principalInducedCharacter (L i) (H i)) (S i)
  have hT (i : I) :
      Section7.inducedFamilyNotation ((H i).subgroupOf (L i)) (T i) := by
    intro χ
    constructor
    · intro hχ
      rw [Finset.mem_insert] at hχ
      rcases hχ with hχ | hχ
      · refine ⟨Section1.principalCharacter ((H i).subgroupOf (L i)),
          Section3.principalCharacter_isIrreducibleCharacterOnGroup, ?_⟩
        simpa [T, Section7.principalInducedCharacter] using hχ
      · rcases (hS i χ).mp hχ with ⟨θ, hθirr, _hθne, rfl⟩
        exact ⟨θ, hθirr, rfl⟩
    · rintro ⟨θ, hθirr, rfl⟩
      rw [Finset.mem_insert]
      by_cases hθ : θ = Section1.principalCharacter ((H i).subgroupOf (L i))
      · left
        simp [Section7.principalInducedCharacter, hθ]
      · right
        exact (hS i _).mpr ⟨θ, hθirr, hθ, rfl⟩
  have h76 (i : I) :
      Section7.hypothesis_7_6_statement
        (typeIASet (L i) (H i)) (L i) (H i) (R i) (T i) := by
    rcases hFrob i with ⟨hHL, hHnormal, _C, _hcomp, _hHne, _hCne, _hcent⟩
    exact ⟨hHL, hHnormal, h22 i, hAeq i, hT i⟩
  have hAgree (i : I) :
      Section7.agreesWithDadeTransform
        (typeIASet (L i) (H i)) (L i) (R i) (τ i) := by
    rcases hDade i with ⟨_h22, hAL, hτ⟩
    exact ⟨hAL, hτ⟩
  have h78 (i : I) :
      Section7.theorem_7_8_hypothesis
        (L i) (H i) (T i) (S i) (τ i) (ν i) (ζ i) := by
    refine ⟨Section12.section16MFSubgroup_le (hMF i), ?_, hS i,
      (h126 i).2, hν i, (hζ i).1, (hζ i).2.1, (hζ i).2.2⟩
    intro χ
    constructor
    · intro hχ
      refine ⟨by simp [T, hχ], ?_⟩
      intro hχp
      have hzero := Section7.theorem_7_8_punctured_member_principal_orthogonal
        (hS i) hχ
      rw [hχp] at hzero
      have hone := Section7.theorem_7_8_principalInduced_principal_scalar
        (G := G) (L := L i) (H := H i)
      exact one_ne_zero (hone.symm.trans hzero)
    · rintro ⟨hχT, hχne⟩
      rw [Finset.mem_insert] at hχT
      exact hχT.resolve_left hχne
  have hIne : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hIuniv : (Finset.univ : Finset I).Nonempty := Finset.univ_nonempty
  rcases Finset.exists_min_image (Finset.univ : Finset I)
      (fun i => Nat.card (H i)) hIuniv with
    ⟨i1, _hi1, hi1min⟩
  have hh (i : I) : 0 < Nat.card (H i) := Nat.card_pos
  have he (i : I) : 0 < (H i).relIndex (L i) := by
    haveI : ((H i).subgroupOf (L i)).FiniteIndex := inferInstance
    exact Nat.pos_of_ne_zero (by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := (H i).subgroupOf (L i))))
  have he1 (i : I) : 1 < (H i).relIndex (L i) := by
    rcases hFrob i with ⟨_hHL, hHnormal, C, hcomp, _hHne, hCne, _hcent⟩
    haveI : ((H i).subgroupOf (L i)).Normal := hHnormal
    have hindex : (H i).relIndex (L i) = Nat.card C := by
      rw [Subgroup.relIndex, hcomp.symm.index_eq_card]
    rw [hindex]
    exact (Subgroup.one_lt_card_iff_ne_bot C).2 hCne
  have h2e (i : I) :
      2 * (H i).relIndex (L i) ≤ Nat.card (H i) - 1 :=
    Section7.theorem_7_11_two_mul_relIndex_le_card_sub_one
      hmin.odd_order (hFrob i)
  have hehalf (i : I) :
      (H i).relIndex (L i) ≤ (Nat.card (H i) - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    simpa [Nat.mul_comm] using h2e i
  have hh1 (i : I) : 1 < Nat.card (H i) := by
    have := h2e i
    have := he1 i
    omega
  have hoddH (i : I) : Odd (Nat.card (H i)) :=
    odd_of_card_dvd hmin.odd_order (Subgroup.card_subgroup_dvd_card (H i))
  have hi1gap (i : I) (hne : i ≠ i1) :
      Nat.card (H i1) + 2 ≤ Nat.card (H i) := by
    have hle : Nat.card (H i1) ≤ Nat.card (H i) :=
      hi1min i (Finset.mem_univ i)
    have hcardne : Nat.card (H i1) ≠ Nat.card (H i) := by
      intro heq
      have hcop := hCoprime i1 i (Ne.symm hne)
      rw [heq] at hcop
      have hone : Nat.card (H i) = 1 := by
        simpa [Nat.Coprime] using hcop
      have hgt := hh1 i
      omega
    rcases hoddH i1 with ⟨m, hm⟩
    rcases hoddH i with ⟨n, hn⟩
    omega
  have h78a (i : I) :
      ∃ a : ℤ, ∃ r : Section1.ClassFunction G,
        Section7.theorem_7_8_decompositionData
          (L i) (H i) (S i) (τ i) (ν i) (ζ i)
          ((H i).relIndex (L i)) a r :=
    Section7.theorem_7_8_a
      (typeIASet (L i) (H i)) (L i) (H i) (R i) (T i) (S i)
        (τ i) (ν i) (ζ i) (h76 i) (hAgree i) (h78 i)
  choose a r hdecomp using h78a
  have h78b (i : I) :
      1 - ((H i).relIndex (L i) : ℝ) / (Nat.card (H i) : ℝ) ≤
          Section5.cfNormSq
            (Section7.dadeProjectionOn (typeIASet (L i) (H i))
              (L i) (R i) (ν i (ζ i))) ∧
        Section5.cfNormSq (r i) ≤ ((H i).relIndex (L i) : ℝ) - 1 := by
    rcases Section7.theorem_7_8_b
      (typeIASet (L i) (H i)) (L i) (H i) (R i) (T i) (S i)
        (τ i) (ν i) (ζ i) (h76 i) (hAgree i) (h78 i)
        (fun ai ri hd =>
          Section7.theorem_7_8_b_projectionData_source_bridge
            (h76 i) (hAgree i) (h78 i) hd)
        (hehalf i) with ⟨hp, hr⟩
    exact ⟨hp, hr (a i) (r i) (hdecomp i)⟩
  have h12a (i : I) :
      ∃ SX : S i → Finset (Section1.ClassFunction (L i)),
        constituentFamilyData (L i) (H i) (S i) SX (R i) (τ i) :=
    theorem_12_2_a (L i) (H i) (S i) (R i) (τ i) (h12 i)
  choose SX hSX using h12a
  have h12b (i : I) :
      ∃ R1 : Section1.ClassFunction (L i) →
          Finset (Section1.ClassFunction G),
      ∃ Rfun : S i → Finset (Section1.ClassFunction G),
        (∀ χ : S i,
          rFamilyData (χ : Section1.ClassFunction (L i)) (SX i χ) (τ i)
            R1 (Rfun χ)) ∧
        hypothesis52WithRData (S i) (τ i) Rfun :=
    theorem_12_2_b (L i) (H i) (S i) (SX i) (R i) (τ i)
      (h12 i) (hSX i)
  choose R1 Rfun hRdata h52 using h12b
  have hγsigned (i : I) :
      Section3.IsSignedIrreducibleCharacter (ν i (ζ i)) :=
    Section6.theorem_6_8_coherentExtension_mem_signedIrreducible
      (hν i) (hζ i).1 (hζ i).2.1
  have hγvirt (i : I) :
      Theory.Character.IsVirtualCharacter (ν i (ζ i)) :=
    Section3.isVirtualCharacter_of_signedIrreducible_pf35 (hγsigned i)
  have hβvirt (i : I) :
      Theory.Character.IsVirtualCharacter
        (Section7.theorem_7_8_beta (L i) (H i) (τ i) (ζ i)) :=
    Section7.theorem_7_8_beta_virtual (h76 i) (hAgree i) (h78 i)
  have hsignedSumNorm :
      ∀ (Q E : Finset (Section1.ClassFunction G)),
        Section5.signedOrthonormalFinset Q → E ⊆ Q →
          Section1.scalarProduct G (E.sum fun ψ => ψ) (E.sum fun ψ => ψ) =
            (E.card : ℂ) := by
    intro Q E hQ hEQ
    induction E using Finset.induction_on with
    | empty => simp [Section1.scalarProduct]
    | @insert ψ E hψ ih =>
        have hEsub : E ⊆ Q := by
          intro φ hφ
          exact hEQ (Finset.mem_insert_of_mem hφ)
        have hψQ : ψ ∈ Q := hEQ (Finset.mem_insert_self ψ E)
        have hψself : Section1.scalarProduct G ψ ψ = 1 :=
          scalarProduct_self_of_isSignedIrreducibleCharacter (hQ.1 ψ hψQ)
        have hsumE : E.sum (fun φ => φ) =
            (fun g : G => ∑ φ : E, (φ : Section1.ClassFunction G) g) := by
          ext g
          simpa using
            (Finset.sum_attach E fun φ : Section1.ClassFunction G => φ g).symm
        have hψE : Section1.scalarProduct G ψ (E.sum fun φ => φ) = 0 := by
          rw [hsumE, Section1.scalarProduct_fintype_sum_right]
          refine Finset.sum_eq_zero ?_
          intro φ _hφ
          exact hQ.2 hψQ (hEsub φ.property) (by
            intro heq
            exact hψ (by
              simp [heq]))
        have hEψ : Section1.scalarProduct G (E.sum fun φ => φ) ψ = 0 := by
          have hstar := congrArg star hψE
          simpa [Section1.scalarProduct_star_swap] using hstar
        rw [Finset.sum_insert hψ, Section1.scalarProduct_add_left,
          Section5.scalarProduct_add_right, Section5.scalarProduct_add_right,
          hψself, hψE, hEψ, ih hEsub, Finset.card_insert_of_notMem hψ,
          Nat.cast_add, Nat.cast_one]
        ring
  have hsubsetMem :
      ∀ (Q : Finset (Section1.ClassFunction G))
        (φ : Section1.ClassFunction G),
        Section5.signedOrthonormalFinset Q →
        Section5.isSubsetSumOf Q φ →
        Section1.scalarProduct G φ φ = 1 → φ ∈ Q := by
    intro Q φ hQ hsubset hφnorm
    rcases hsubset with ⟨E, hEQ, hφ⟩
    have hcardC : (E.card : ℂ) = 1 := by
      rw [← hsignedSumNorm Q E hQ hEQ]
      simpa [hφ] using hφnorm
    have hcard : E.card = 1 := by exact_mod_cast hcardC
    rcases Finset.card_eq_one.mp hcard with ⟨ψ, rfl⟩
    have hφψ : φ = ψ := by simpa using hφ
    rw [hφψ]
    exact hEQ (by simp)
  have hγconj (i : I) :
      Section1.conjugateCharacter (ν i (ζ i)) =
        ν i (Section1.conjugateCharacter (ζ i)) := by
    letI : Fintype (L i) := Fintype.ofFinite (L i)
    let X : S i := ⟨ζ i, (hζ i).1⟩
    rcases h52 i with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
    have hζbar : Section1.conjugateCharacter (ζ i) ∈ S i := by
      simpa [X] using (h52a X).1
    have hζne : ζ i ≠ Section1.conjugateCharacter (ζ i) := by
      simpa [X] using (h52a X).2
    have hpairSub :
        ({(X : Section1.ClassFunction (L i)),
            Section1.conjugateCharacter (X : Section1.ClassFunction (L i))} :
          Finset (Section1.ClassFunction (L i))) ⊆ S i := by
      intro ψ hψ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hψ
      rcases hψ with rfl | rfl
      · exact X.2
      · exact (h52a X).1
    have hIsoPair :
        Section5.isCFLinearIsometryOnSpan
          ({(X : Section1.ClassFunction (L i)),
              Section1.conjugateCharacter (X : Section1.ClassFunction (L i))} :
            Finset (Section1.ClassFunction (L i))) (ν i) :=
      Section5.isCFLinearIsometryOnSpan_mono hpairSub (hν i).1
    have hVirtPair :
        Section5.mapsIntegerSpanToVirtualCharacters
          ({(X : Section1.ClassFunction (L i)),
              Section1.conjugateCharacter (X : Section1.ClassFunction (L i))} :
            Finset (Section1.ClassFunction (L i))) (ν i) :=
      Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSub (hν i).2.1
    have hdiffOn : Section5.integerSpanOn (S i) Section5.puncturedSet
        (ζ i - Section1.conjugateCharacter (ζ i)) := by
      have hspan := Section5.integerSpan_sub
        (Section5.integerSpan_of_mem (S i) (hζ i).1)
        (Section5.integerSpan_of_mem (S i) hζbar)
      have hdeg : Section1.degree
          (ζ i - Section1.conjugateCharacter (ζ i)) = 0 := by
        change Section1.degree (ζ i) -
          Section1.degree (Section1.conjugateCharacter (ζ i)) = 0
        rw [Section5.degree_conjugateCharacter_eq_of_isCharacter
          (hsetup.2 X)]
        exact sub_self _
      exact ⟨hspan,
        (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩
    have hagree :
        ν i (ζ i - Section1.conjugateCharacter (ζ i)) =
          τ i (ζ i - Section1.conjugateCharacter (ζ i)) :=
      (hν i).2.2 _ hdiffOn
    have hsubset : Section5.isSubsetSumOf (Rfun i X) (ν i (ζ i)) := by
      have hsubX := Section5.theorem_5_5 (S i) (τ i) (Rfun i)
        hsetup h52a h52b h52c h52d h52e X (ν i)
        hIsoPair hVirtPair hagree
      simpa [X] using hsubX
    have hγmem : ν i (ζ i) ∈ Rfun i X :=
      hsubsetMem (Rfun i X) (ν i (ζ i)) (h52d X).1 hsubset
        (scalarProduct_self_of_isSignedIrreducibleCharacter (hγsigned i))
    have hdiffNormSource :
        Section1.scalarProduct (L i)
            (ζ i - Section1.conjugateCharacter (ζ i))
            (ζ i - Section1.conjugateCharacter (ζ i)) = 2 := by
      have hself : Section1.scalarProduct (L i) (ζ i) (ζ i) = 1 :=
        scalarProduct_self_of_isIrreducibleCharacterOnGroup (hζ i).2.1
      have hbarself : Section1.scalarProduct (L i)
          (Section1.conjugateCharacter (ζ i))
          (Section1.conjugateCharacter (ζ i)) = 1 :=
        scalarProduct_self_of_isIrreducibleCharacterOnGroup
          (Section1.isIrreducibleCharacterOnGroup_conjugateCharacter
            (hζ i).2.1)
      have hcross : Section1.scalarProduct (L i) (ζ i)
          (Section1.conjugateCharacter (ζ i)) = 0 :=
        h52c (hζ i).1 hζbar hζne
      have hcross' : Section1.scalarProduct (L i)
          (Section1.conjugateCharacter (ζ i)) (ζ i) = 0 :=
        h52c hζbar (hζ i).1 hζne.symm
      rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
        Section5.scalarProduct_sub_right, hself, hcross, hcross', hbarself]
      norm_num
    have hdiffNormTarget :
        Section1.scalarProduct G
            (τ i (ζ i - Section1.conjugateCharacter (ζ i)))
            (τ i (ζ i - Section1.conjugateCharacter (ζ i))) = 2 := by
      rw [h52b.1 _ _ hdiffOn hdiffOn, hdiffNormSource]
    have hRcard : (Rfun i X).card = 2 := by
      have hsumNorm := hsignedSumNorm (Rfun i X) (Rfun i X)
        (h52d X).1 (by intro ψ hψ; exact hψ)
      have hsumEq :
          τ i (ζ i - Section1.conjugateCharacter (ζ i)) =
            (Rfun i X).sum fun ψ => ψ := by
        simpa [X] using (h52d X).2
      have hcardC : ((Rfun i X).card : ℂ) = 2 := by
        rw [← hsumNorm, ← hsumEq]
        exact hdiffNormTarget
      exact_mod_cast hcardC
    have hskew : Section1.conjugateCharacter
        (τ i (ζ i - Section1.conjugateCharacter (ζ i))) =
          -(τ i (ζ i - Section1.conjugateCharacter (ζ i))) :=
      conjugateCharacter_tau_sub_conjugate_of_hypothesis12
        (L i) (H i) (S i) (SX i) (R i) (τ i)
          (h12 i) (hSX i) (hζ i).1
    have htarget :
        τ i (ζ i - Section1.conjugateCharacter (ζ i)) =
          ν i (ζ i) - Section1.conjugateCharacter (ν i (ζ i)) :=
      signedOrthonormalPair_sum_eq_sub_conjugate_of_skew
        (h52d X).1 hRcard (h52d X).2 hskew hγmem
    have hcancel :
        ν i (ζ i) - ν i (Section1.conjugateCharacter (ζ i)) =
          ν i (ζ i) - Section1.conjugateCharacter (ν i (ζ i)) := by
      rw [← (ν i).map_sub, hagree, htarget]
    ext g
    have hg := congrFun hcancel g
    exact (sub_right_inj.mp hg).symm
  have hcentralizer (i : I) {x : G}
      (hx : x ∈ typeIASet (L i) (H i)) :
      Subgroup.centralizer ({x} : Set G) ≤ L i := by
    change Section2.elementCentralizer x ≤ L i
    intro c hc
    have hprod := (h22 i).centralizer_eq_product hx
    rcases hprod.mul_surjective c hc with ⟨b, hb, k, hk, hck⟩
    have hb1 : b = 1 := by simpa [R] using hb
    subst b
    have hck' : c = k := by simpa using hck
    have hkL : (k : G) ∈ L i := hk.1
    simpa [hck'] using hkL
  let D : I → Set G := fun i =>
    Section8.section8DSet (L i) (typeIASet (L i) (H i))
  let tildeA : I → Set G := fun i =>
    {y | ∃ x : G, x ∈ typeIASet (L i) (H i) ∧
      y ∈ section16ConjugatesOfSetBySet
        (section16LeftCosetSet x (R i x)) Set.univ}
  have hnot (i : I) :
      Section8.notation_8_14_source_data (L i)
        (typeIASet (L i) (H i)) (typeIASet (L i) (H i))
        (Section8.a1Set (H i)) (D i) (tildeA i) (tildeA i) (tildeA i)
        (R i) := by
    refine ⟨?_, le_rfl, rfl, ?_, ?_, ?_, rfl, rfl, ?_⟩
    · intro x hx
      simpa [hAeq i, A, Section8.a1Set,
        Section7.puncturedSubgroupSet, section16NonidentityElements] using hx
    · intro x _hx
      rfl
    · intro x hx
      have hx' :
          x ∈ typeIASet (L i) (H i) ∧
            ¬ Subgroup.centralizer ({x} : Set G) ≤ L i := by
        simpa [D, Section8.section8DSet] using hx
      exact False.elim (hx'.2 (hcentralizer i hx'.1))
    · intro x hx
      have hx' :
          x ∈ typeIASet (L i) (H i) ∧
            ¬ Subgroup.centralizer ({x} : Set G) ≤ L i := by
        simpa [D, Section8.section8DSet] using hx
      exact False.elim (hx'.2 (hcentralizer i hx'.1))
    · simp [tildeA, hAeq i, A, Section8.a1Set,
        Section7.puncturedSubgroupSet, section16NonidentityElements]
  have htildeDisjoint (i j : I) (hne : i ≠ j) :
      Disjoint (tildeA i) (tildeA j) := by
    rw [Set.disjoint_left]
    intro g hgi hgj
    rcases hgi with ⟨x, hxA, z, ⟨r, hr, hzr⟩, y, _hy, hgy⟩
    rcases hgj with ⟨x', hxA', z', ⟨r', hr', hzr'⟩, y', _hy', hgy'⟩
    have hr1 : r = 1 := Subgroup.mem_bot.mp hr
    have hr1' : r' = 1 := Subgroup.mem_bot.mp hr'
    have horderx : orderOf x = orderOf g := by
      apply SemiconjBy.orderOf_eq y
      rw [hgy, hzr, hr1]
      simp [SemiconjBy, mul_assoc]
    have horderx' : orderOf x' = orderOf g := by
      apply SemiconjBy.orderOf_eq y'
      rw [hgy', hzr', hr1']
      simp [SemiconjBy, mul_assoc]
    have hxpunctured : x ∈ Section7.puncturedSubgroupSet (H i) := by
      simpa [hAeq i] using hxA
    have hxpunctured' : x' ∈ Section7.puncturedSubgroupSet (H j) := by
      simpa [hAeq j] using hxA'
    have hord1 : orderOf g = 1 :=
      Nat.eq_one_of_dvd_coprimes (hCoprime i j hne)
        (horderx ▸ Subgroup.orderOf_dvd_natCard (H i) hxpunctured.1)
        (horderx' ▸ Subgroup.orderOf_dvd_natCard (H j) hxpunctured'.1)
    exact hxpunctured.2
      (orderOf_eq_one_iff.mp (horderx.trans hord1))
  have hselfmem (i : I) (χ : Section1.ClassFunction (L i)) (hχ : χ ∈ S i) :
      χ ∈ SX i ⟨χ, hχ⟩ := by
    by_contra hχnot
    have hzero := constituentSetData_scalarProduct_left_eq_zero_of_not_mem
      ((hSX i).1 ⟨χ, hχ⟩) ((h126 i).1 χ hχ) hχnot
    have hone := scalarProduct_self_of_isIrreducibleCharacterOnGroup
      ((h126 i).1 χ hχ)
    exact one_ne_zero (hone.symm.trans hzero)
  have hRorth (i j : I) (hne : i ≠ j)
      (χi : Section1.ClassFunction (L i)) (hχi : χi ∈ S i)
      (χj : Section1.ClassFunction (L j)) (hχj : χj ∈ S j) :
      Section5.orthogonalFinsets
        (Rfun i ⟨χi, hχi⟩) (Rfun j ⟨χj, hχj⟩) := by
    rcases h52 j with ⟨_hsetup, _h52a, _h52b, _h52c, h52d, _h52e⟩
    have hRi := hRdata i ⟨χi, hχi⟩
    have hdiffi : rFamilyDiffData (SX i ⟨χi, hχi⟩) (τ i)
        (Rfun i ⟨χi, hχi⟩) :=
      rFamilyDiffData_of_hypothesis12_rFamilyData (h12 i) (hSX i) hRi
    have hψvirt : Theory.Character.IsVirtualCharacter
        (τ j (χj - Section1.conjugateCharacter χj)) :=
      isVirtualCharacter_tau_sub_conjugate_of_hypothesis12
        (L j) (H j) (S j) (SX j) (R j) (τ j) (h12 j) (hSX j) hχj
    have hψskew : Section1.conjugateCharacter
        (τ j (χj - Section1.conjugateCharacter χj)) =
          -τ j (χj - Section1.conjugateCharacter χj) :=
      conjugateCharacter_tau_sub_conjugate_of_hypothesis12
        (L j) (H j) (S j) (SX j) (R j) (τ j) (h12 j) (hSX j) hχj
    refine orthogonalFinsets_of_rFamilyData_left_tau_sub_conjugate_right
      hRi (h52d ⟨χj, hχj⟩).1 (h52d ⟨χj, hχj⟩).2 ?_
    intro α hα
    have hαsigned : Section3.IsSignedIrreducibleCharacter α :=
      isSignedIrreducibleCharacter_of_mem_rFamilyData hRi hα
    have hdiffzero : Section1.scalarProduct G
        (α - Section1.conjugateCharacter α)
        (τ j (χj - Section1.conjugateCharacter χj)) = 0 := by
      rcases hdiffi α hα with ⟨φ, hφ, hφeq⟩
      rw [← hφeq]
      exact scalarProduct_eq_zero_of_supportedOn_disjoint
        (supportedOn_tau_sub_conjugate_of_constituentFamily_mem_tilde
          (h12 i) (hSX i) (hnot i) hφ)
        (supportedOn_tau_sub_conjugate_of_constituentFamily_mem_tilde
          (h12 j) (hSX j) (hnot j) (hselfmem j χj hχj))
        (htildeDisjoint i j hne)
    exact scalarProduct_eq_zero_of_sub_conjugate_left_eq_zero
      hαsigned hψvirt hψskew hdiffzero
  have hνSubset (i : I) (χ : Section1.ClassFunction (L i)) (hχ : χ ∈ S i) :
      Section5.isSubsetSumOf (Rfun i ⟨χ, hχ⟩) (ν i χ) := by
    letI : Fintype (L i) := Fintype.ofFinite (L i)
    rcases h52 i with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
    let X : S i := ⟨χ, hχ⟩
    have hχbar : Section1.conjugateCharacter χ ∈ S i := by
      simpa [X] using (h52a X).1
    have hpairSub :
        ({(X : Section1.ClassFunction (L i)),
            Section1.conjugateCharacter (X : Section1.ClassFunction (L i))} :
          Finset (Section1.ClassFunction (L i))) ⊆ S i := by
      intro ψ hψ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hψ
      rcases hψ with rfl | rfl
      · exact hχ
      · exact hχbar
    have hIsoPair :
        Section5.isCFLinearIsometryOnSpan
          ({(X : Section1.ClassFunction (L i)),
              Section1.conjugateCharacter (X : Section1.ClassFunction (L i))} :
            Finset (Section1.ClassFunction (L i))) (ν i) :=
      Section5.isCFLinearIsometryOnSpan_mono hpairSub (hν i).1
    have hVirtPair :
        Section5.mapsIntegerSpanToVirtualCharacters
          ({(X : Section1.ClassFunction (L i)),
              Section1.conjugateCharacter (X : Section1.ClassFunction (L i))} :
            Finset (Section1.ClassFunction (L i))) (ν i) :=
      Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSub (hν i).2.1
    have hdiffOn : Section5.integerSpanOn (S i) Section5.puncturedSet
        (χ - Section1.conjugateCharacter χ) := by
      have hspan := Section5.integerSpan_sub
        (Section5.integerSpan_of_mem (S i) hχ)
        (Section5.integerSpan_of_mem (S i) hχbar)
      have hdeg : Section1.degree
          (χ - Section1.conjugateCharacter χ) = 0 := by
        change Section1.degree χ -
          Section1.degree (Section1.conjugateCharacter χ) = 0
        rw [Section5.degree_conjugateCharacter_eq_of_isCharacter
          (hsetup.2 X)]
        exact sub_self _
      exact ⟨hspan,
        (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩
    have hagree :
        ν i (χ - Section1.conjugateCharacter χ) =
          τ i (χ - Section1.conjugateCharacter χ) :=
      (hν i).2.2 _ hdiffOn
    have hsubsetX := Section5.theorem_5_5 (S i) (τ i) (Rfun i)
      hsetup h52a h52b h52c h52d h52e X (ν i)
      hIsoPair hVirtPair hagree
    simpa [X] using hsubsetX
  have hsubsetOrth :
      ∀ {Q Ω : Finset (Section1.ClassFunction G)}
        {φ ψ : Section1.ClassFunction G},
        Section5.isSubsetSumOf Q φ →
        Section5.isSubsetSumOf Ω ψ →
        Section5.orthogonalFinsets Q Ω →
          Section1.scalarProduct G φ ψ = 0 := by
    intro Q Ω φ ψ hφ hψ horth
    rcases hφ with ⟨E, hEQ, rfl⟩
    rcases hψ with ⟨F, hFΩ, rfl⟩
    have hsumE : E.sum (fun χ => χ) =
        (fun g : G => ∑ χ : E, (χ : Section1.ClassFunction G) g) := by
      ext g
      simpa using
        (Finset.sum_attach E fun χ : Section1.ClassFunction G => χ g).symm
    have hsumF : F.sum (fun χ => χ) =
        (fun g : G => ∑ χ : F, (χ : Section1.ClassFunction G) g) := by
      ext g
      simpa using
        (Finset.sum_attach F fun χ : Section1.ClassFunction G => χ g).symm
    rw [hsumE, Section1.scalarProduct_fintype_sum_left]
    refine Finset.sum_eq_zero ?_
    intro χ _hχ
    rw [hsumF, Section1.scalarProduct_fintype_sum_right]
    refine Finset.sum_eq_zero ?_
    intro ψ _hψ
    exact horth (hEQ χ.property) (hFΩ ψ.property)
  have hγorth (i j : I) (hne : i ≠ j) :
      Section1.scalarProduct G (ν i (ζ i)) (ν j (ζ j)) = 0 :=
    hsubsetOrth (hνSubset i (ζ i) (hζ i).1)
      (hνSubset j (ζ j) (hζ j).1)
      (hRorth i j hne (ζ i) (hζ i).1 (ζ j) (hζ j).1)
  let β : I → Section1.ClassFunction G := fun i =>
    Section7.theorem_7_8_beta (L i) (H i) (τ i) (ζ i)
  let γ : I → Section1.ClassFunction G := fun i => ν i (ζ i)
  have hβon_of (i : I) (χ : Section1.ClassFunction (L i))
      (hχ : χ ∈ S i)
      (hχdeg : Section1.degree χ = ((H i).relIndex (L i) : ℂ)) :
      Section2.CFOn (L i) (typeIASet (L i) (H i))
        (Section7.theorem_7_8_betaInput (L i) (H i) χ) := by
    letI : ((H i).subgroupOf (L i)).Normal :=
      section16MFSubgroup_subgroupOf_normal (hMF i)
    rcases (hS i χ).mp hχ with ⟨θ, _hθirr, _hθne, hχeq⟩
    have hprincipalClass :
        Section1.IsClassFunction
          (Section7.principalInducedCharacter (L i) (H i)) := by
      unfold Section7.principalInducedCharacter
      exact Section1.inducedCF_isClassFunction ((H i).subgroupOf (L i))
        (Section1.principalCharacter ((H i).subgroupOf (L i)))
    have hχclass : Section1.IsClassFunction χ := by
      rw [hχeq]
      exact Section1.inducedCF_isClassFunction ((H i).subgroupOf (L i)) θ
    constructor
    · intro x g
      simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
        hprincipalClass x g, hχclass x g]
    · intro l hlA
      have hprincipal_degree :
          Section1.degree
              (Section7.principalInducedCharacter (L i) (H i)) =
            ((H i).relIndex (L i) : ℂ) := by
        unfold Section7.principalInducedCharacter
        rw [Section1.degree_inducedClassFunction]
        simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
      have hprincipal_one :
          Section7.principalInducedCharacter (L i) (H i) (1 : L i) =
            ((H i).relIndex (L i) : ℂ) := by
        simpa [Section1.degree_apply] using hprincipal_degree
      have hχ_one : χ 1 = ((H i).relIndex (L i) : ℂ) := by
        simpa [Section1.degree_apply] using hχdeg
      have hβ_one :
          Section7.theorem_7_8_betaInput (L i) (H i) χ (1 : L i) = 0 := by
        simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
          hprincipal_one, hχ_one]
      by_cases hl_one : l = 1
      · simpa [hl_one] using hβ_one
      · have hl_ne_oneG : (l : G) ≠ 1 := by
          intro hG
          apply hl_one
          ext
          exact hG
        have hlnotH : (l : G) ∉ H i := by
          intro hlH
          apply hlA
          rw [hAeq i]
          exact ⟨hlH, hl_ne_oneG⟩
        have hlnotHsub : l ∉ (H i).subgroupOf (L i) := by
          intro hlHsub
          exact hlnotH hlHsub
        have hprincipal_zero :
            Section7.principalInducedCharacter (L i) (H i) l = 0 := by
          unfold Section7.principalInducedCharacter
          exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
            ((H i).subgroupOf (L i))
            (Section1.principalCharacter ((H i).subgroupOf (L i))) hlnotHsub
        have hχ_zero : χ l = 0 := by
          rw [hχeq]
          exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
            ((H i).subgroupOf (L i)) θ hlnotHsub
        simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
          hprincipal_zero, hχ_zero]
  have hβon (i : I) :
      Section2.CFOn (L i) (typeIASet (L i) (H i))
        (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i)) :=
    hβon_of i (ζ i) (hζ i).1 (hζ i).2.2
  have hβsupp (i : I) : Section1.supportedOn (β i) (tildeA i) := by
    rcases hDade i with ⟨_h22, hAL, hτeq⟩
    have hτβ :
        τ i (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i)) =
          Section2.dadeTransform (R i) hAL
            (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i)) :=
      hτeq _ (hβon i)
    rw [show β i =
      τ i (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i)) by rfl,
      hτβ]
    have hsupp := supportedOn_dadeTransform_dadeSupport (R := R i) hAL
      (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i))
    rw [dadeSupport_eq_tildeA_of_notation_8_14_source_data
      (L i) (typeIASet (L i) (H i)) (typeIASet (L i) (H i))
      (Section8.a1Set (H i)) (D i) (tildeA i) (tildeA i) (tildeA i)
      (R i) (hnot i)] at hsupp
    exact hsupp
  have hβorth (i j : I) (hne : i ≠ j) :
      Section1.scalarProduct G (β i) (β j) = 0 :=
    scalarProduct_eq_zero_of_supportedOn_disjoint
      (hβsupp i) (hβsupp j) (htildeDisjoint i j hne)
  have hζbarMem (i : I) :
      Section1.conjugateCharacter (ζ i) ∈ S i :=
    puncturedInducedFamily_conjugate_mem (L i) (H i) (S i)
      (section16MFSubgroup_subgroupOf_normal (hMF i))
      (hS i) (ζ i) (hζ i).1
  have hβconj (i : I) :
      Section1.conjugateCharacter (β i) =
        τ i (Section7.theorem_7_8_betaInput (L i) (H i)
          (Section1.conjugateCharacter (ζ i))) := by
    letI : ((H i).subgroupOf (L i)).Normal :=
      section16MFSubgroup_subgroupOf_normal (hMF i)
    have hζchar : Section1.IsCharacter (ζ i) :=
      isCharacter_of_isIrreducibleCharacterOnGroup (hζ i).2.1
    have hζbarDeg :
        Section1.degree (Section1.conjugateCharacter (ζ i)) =
          ((H i).relIndex (L i) : ℂ) := by
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hζchar,
        (hζ i).2.2]
    have hprincipalConj :
        Section1.conjugateCharacter
            (Section7.principalInducedCharacter (L i) (H i)) =
          Section7.principalInducedCharacter (L i) (H i) := by
      unfold Section7.principalInducedCharacter
      rw [Section1.conjugateCharacter_inducedCF,
        Section1.conjugateCharacter_principalCharacter]
    have hinputConj :
        Section1.conjugateCharacter
            (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i)) =
          Section7.theorem_7_8_betaInput (L i) (H i)
            (Section1.conjugateCharacter (ζ i)) := by
      calc
        Section1.conjugateCharacter
            (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i)) =
            Section1.conjugateCharacter
                (Section7.principalInducedCharacter (L i) (H i)) -
              Section1.conjugateCharacter (ζ i) := by
                ext x
                simp [Section7.theorem_7_8_betaInput,
                  Section1.conjugateCharacter, Pi.sub_apply]
        _ = Section7.principalInducedCharacter (L i) (H i) -
              Section1.conjugateCharacter (ζ i) := by rw [hprincipalConj]
        _ = Section7.theorem_7_8_betaInput (L i) (H i)
              (Section1.conjugateCharacter (ζ i)) := rfl
    rcases hDade i with ⟨_h22, hAL, hτeq⟩
    have hτβ :
        τ i (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i)) =
          Section2.dadeTransform (R i) hAL
            (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i)) :=
      hτeq _ (hβon i)
    have hτβbar :
        τ i (Section7.theorem_7_8_betaInput (L i) (H i)
            (Section1.conjugateCharacter (ζ i))) =
          Section2.dadeTransform (R i) hAL
            (Section7.theorem_7_8_betaInput (L i) (H i)
              (Section1.conjugateCharacter (ζ i))) :=
      hτeq _ (hβon_of i (Section1.conjugateCharacter (ζ i))
        (hζbarMem i) hζbarDeg)
    calc
      Section1.conjugateCharacter (β i) =
          Section1.conjugateCharacter
            (τ i (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i))) := rfl
      _ = Section1.conjugateCharacter
          (Section2.dadeTransform (R i) hAL
            (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i))) := by rw [hτβ]
      _ = Section2.dadeTransform (R i) hAL
          (Section1.conjugateCharacter
            (Section7.theorem_7_8_betaInput (L i) (H i) (ζ i))) :=
        conjugateCharacter_dadeTransform (R i) hAL _
      _ = Section2.dadeTransform (R i) hAL
          (Section7.theorem_7_8_betaInput (L i) (H i)
            (Section1.conjugateCharacter (ζ i))) := by rw [hinputConj]
      _ = τ i (Section7.theorem_7_8_betaInput (L i) (H i)
            (Section1.conjugateCharacter (ζ i))) := hτβbar.symm
  have hcoherentDiff (i : I) :
      ν i (ζ i - Section1.conjugateCharacter (ζ i)) =
        τ i (ζ i - Section1.conjugateCharacter (ζ i)) := by
    have hspan := Section5.integerSpan_sub
      (Section5.integerSpan_of_mem (S i) (hζ i).1)
      (Section5.integerSpan_of_mem (S i) (hζbarMem i))
    have hdeg : Section1.degree
        (ζ i - Section1.conjugateCharacter (ζ i)) = 0 := by
      change Section1.degree (ζ i) -
        Section1.degree (Section1.conjugateCharacter (ζ i)) = 0
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter
        (isCharacter_of_isIrreducibleCharacterOnGroup (hζ i).2.1)]
      exact sub_self _
    exact (hν i).2.2 _ ⟨hspan,
      (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2 hdeg⟩
  have hβγreal (i : I) :
      β i + γ i = Section1.conjugateCharacter (β i + γ i) := by
    have hdiff :
        ν i (ζ i) - ν i (Section1.conjugateCharacter (ζ i)) =
          τ i (ζ i) - τ i (Section1.conjugateCharacter (ζ i)) := by
      simpa using hcoherentDiff i
    have hrearrange :
        ν i (ζ i) - τ i (ζ i) =
          ν i (Section1.conjugateCharacter (ζ i)) -
            τ i (Section1.conjugateCharacter (ζ i)) := by
      apply sub_eq_sub_iff_add_eq_add.mpr
      exact (sub_eq_sub_iff_add_eq_add.mp hdiff).trans (add_comm _ _)
    calc
      β i + γ i =
          τ i (Section7.principalInducedCharacter (L i) (H i) - ζ i) +
            ν i (ζ i) := rfl
      _ = τ i (Section7.principalInducedCharacter (L i) (H i)) -
            τ i (ζ i) + ν i (ζ i) := by rw [map_sub]
      _ = τ i (Section7.principalInducedCharacter (L i) (H i)) +
            (ν i (ζ i) - τ i (ζ i)) := by abel
      _ = τ i (Section7.principalInducedCharacter (L i) (H i)) +
            (ν i (Section1.conjugateCharacter (ζ i)) -
              τ i (Section1.conjugateCharacter (ζ i))) := by rw [hrearrange]
      _ = τ i (Section7.principalInducedCharacter (L i) (H i)) -
            τ i (Section1.conjugateCharacter (ζ i)) +
              ν i (Section1.conjugateCharacter (ζ i)) := by abel
      _ = τ i (Section7.theorem_7_8_betaInput (L i) (H i)
              (Section1.conjugateCharacter (ζ i))) +
            ν i (Section1.conjugateCharacter (ζ i)) := by
              rw [← map_sub]
              rfl
      _ = Section1.conjugateCharacter (β i) +
            Section1.conjugateCharacter (γ i) := by
              rw [hβconj i, hγconj i]
      _ = Section1.conjugateCharacter (β i + γ i) := by
        ext g
        simp [Section1.conjugateCharacter, Pi.add_apply]
  let Δ : I → Section1.ClassFunction G := fun i =>
    β i + γ i - Section1.principalCharacter G
  have hΔvirt (i : I) : Theory.Character.IsVirtualCharacter (Δ i) := by
    exact Section3.isVirtualCharacter_sub
      (Section3.isVirtualCharacter_add (by simpa [β] using hβvirt i)
        (by simpa [γ] using hγvirt i))
      Section3.isVirtualCharacter_principalCharacter
  have hΔreal (i : I) : Δ i = Section1.conjugateCharacter (Δ i) := by
    dsimp [Δ]
    calc
      β i + γ i - Section1.principalCharacter G =
          Section1.conjugateCharacter (β i + γ i) -
            Section1.conjugateCharacter (Section1.principalCharacter G) := by
              rw [← hβγreal i,
                Section1.conjugateCharacter_principalCharacter]
      _ = Section1.conjugateCharacter
          (β i + γ i - Section1.principalCharacter G) := by
        ext g
        simp [Section1.conjugateCharacter, Pi.sub_apply]
  have hγprincipal (i : I) :
      Section1.scalarProduct G (γ i) (Section1.principalCharacter G) = 0 := by
    have hleft := (hdecomp i).1 (ζ i) (hζ i).1
    have hswap := Section1.scalarProduct_star_swap (G := G)
      (Section1.principalCharacter G) (γ i)
    have hstarzero :
        star (Section1.scalarProduct G (γ i)
          (Section1.principalCharacter G)) = 0 := by
      simpa [γ, hleft] using hswap
    simpa using congrArg star hstarzero
  have hweightedPrincipal (i : I) :
      Section1.scalarProduct G
        (Section7.theorem_7_8_weightedSum (S i) (ν i)
          ((H i).relIndex (L i)))
        (Section1.principalCharacter G) = 0 := by
    have hsum :
        Section7.theorem_7_8_weightedSum (S i) (ν i)
            ((H i).relIndex (L i)) =
          fun g => ∑ ψ : S i,
            ((((ψ : Section1.ClassFunction (L i)) 1) /
              ((((H i).relIndex (L i) : ℕ) : ℂ) *
                (Section5.cfNormSq
                  (ψ : Section1.ClassFunction (L i)) : ℂ))) •
              ν i (ψ : Section1.ClassFunction (L i))) g := by
      ext g
      simp only [Section7.theorem_7_8_weightedSum, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      exact (Finset.sum_attach (S i)
        (fun ψ : Section1.ClassFunction (L i) =>
          ψ 1 / ((((H i).relIndex (L i) : ℕ) : ℂ) *
            (Section5.cfNormSq ψ : ℂ)) * ν i ψ g)).symm
    rw [hsum, Section1.scalarProduct_fintype_sum_left]
    refine Finset.sum_eq_zero ?_
    intro ψ _hψ
    have hleft := (hdecomp i).1
      (ψ : Section1.ClassFunction (L i)) ψ.2
    have hswap := Section1.scalarProduct_star_swap (G := G)
      (Section1.principalCharacter G)
      (ν i (ψ : Section1.ClassFunction (L i)))
    have hright :
        Section1.scalarProduct G (ν i (ψ : Section1.ClassFunction (L i)))
          (Section1.principalCharacter G) = 0 := by
      have hstarzero :
          star (Section1.scalarProduct G
            (ν i (ψ : Section1.ClassFunction (L i)))
            (Section1.principalCharacter G)) = 0 := by
        simpa [hleft] using hswap
      simpa using congrArg star hstarzero
    rw [Section1.scalarProduct_smul_left, hright]
    simp
  have hβprincipal (i : I) :
      Section1.scalarProduct G (β i) (Section1.principalCharacter G) = 1 := by
    have hβeq :
        β i = Section1.principalCharacter G - γ i +
            ((a i : ℂ) • Section7.theorem_7_8_weightedSum
              (S i) (ν i) ((H i).relIndex (L i))) + r i := by
      simpa [β, γ] using (hdecomp i).2.2.2
    have hpGself :
        Section1.scalarProduct G (Section1.principalCharacter G)
          (Section1.principalCharacter G) = 1 := by
      simp [Section1.scalarProduct, Section1.principalCharacter]
    rw [hβeq, Section1.scalarProduct_add_left,
      Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
      Section1.scalarProduct_smul_left, hpGself, hγprincipal i,
      hweightedPrincipal i, (hdecomp i).2.2.1]
    ring
  have hβγprincipal (i : I) :
      Section1.scalarProduct G (β i + γ i)
        (Section1.principalCharacter G) = 1 := by
    rw [Section1.scalarProduct_add_left, hβprincipal i, hγprincipal i]
    ring
  have hprincipalβγ (i : I) :
      Section1.scalarProduct G (Section1.principalCharacter G)
        (β i + γ i) = 1 := by
    have hswap := Section1.scalarProduct_star_swap (G := G)
      (Section1.principalCharacter G) (β i + γ i)
    have hrev :
        (1 : ℂ) = Section1.scalarProduct G (Section1.principalCharacter G)
          (β i + γ i) := by
      simpa [hβγprincipal i] using hswap
    exact hrev.symm
  have hΔprincipal (i : I) :
      Section1.scalarProduct G (Δ i) (Section1.principalCharacter G) = 0 := by
    dsimp [Δ]
    have hpGself :
        Section1.scalarProduct G (Section1.principalCharacter G)
          (Section1.principalCharacter G) = 1 := by
      simp [Section1.scalarProduct, Section1.principalCharacter]
    rw [Section5.scalarProduct_sub_left, hβγprincipal i, hpGself]
    ring
  have hβγflip (i j : I) :
      Section1.scalarProduct G (β i) (γ j) =
        Section1.scalarProduct G (γ j) (β i) := by
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int
        (by simpa [β] using hβvirt i) (by simpa [γ] using hγvirt j) with
      ⟨z, hz⟩
    calc
      Section1.scalarProduct G (β i) (γ j) = (z : ℂ) := hz
      _ = star (z : ℂ) := by simp
      _ = star (Section1.scalarProduct G (β i) (γ j)) := by rw [hz]
      _ = Section1.scalarProduct G (γ j) (β i) :=
        Section1.scalarProduct_star_swap (G := G) (γ j) (β i)
  have hoddPair (i j : I) (hne : i ≠ j) :
      ∃ z : ℤ,
        Section1.scalarProduct G (γ i) (β j + γ j) +
            Section1.scalarProduct G (γ j) (β i + γ i) =
          (1 : ℂ) + 2 * (z : ℂ) := by
    have heven :
        ∃ m : ℤ,
          Section1.scalarProduct G
              (β i + γ i - Section1.principalCharacter G)
              (β j + γ j - Section1.principalCharacter G) =
            ((2 * m : ℤ) : ℂ) := by
      simpa [Δ] using
        Section5.real_virtual_principal_orthogonal_scalarProduct_even
          hmin.odd_order (hΔvirt i) (hΔreal i) (hΔprincipal i)
          (hΔvirt j) (hΔreal j)
    rcases heven with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    let pG : Section1.ClassFunction G := Section1.principalCharacter G
    have hpGself : Section1.scalarProduct G pG pG = 1 := by
      simp [pG, Section1.scalarProduct]
    have hcorrExpand :
        Section1.scalarProduct G (β i + γ i - pG) (β j + γ j - pG) =
          Section1.scalarProduct G (β i + γ i) (β j + γ j) - 1 := by
      rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
        Section5.scalarProduct_sub_right]
      simp [pG, hβγprincipal i, hprincipalβγ j, hpGself]
    have htotal :
        Section1.scalarProduct G (β i + γ i) (β j + γ j) =
          (1 : ℂ) + 2 * (m : ℂ) := by
      have hm' :
          Section1.scalarProduct G (β i + γ i) (β j + γ j) - 1 =
            ((2 * m : ℤ) : ℂ) := by
        simpa [pG, hcorrExpand] using hm
      calc
        Section1.scalarProduct G (β i + γ i) (β j + γ j) =
            (Section1.scalarProduct G (β i + γ i) (β j + γ j) - 1) + 1 := by
              ring
        _ = ((2 * m : ℤ) : ℂ) + 1 := by rw [hm']
        _ = (1 : ℂ) + 2 * (m : ℂ) := by
          rw [Int.cast_mul]
          norm_num
          ring
    have hγij : Section1.scalarProduct G (γ i) (γ j) = 0 := by
      simpa [γ] using hγorth i j hne
    have hγji : Section1.scalarProduct G (γ j) (γ i) = 0 := by
      simpa [γ] using hγorth j i hne.symm
    have hleftExpand :
        Section1.scalarProduct G (γ i) (β j + γ j) +
            Section1.scalarProduct G (γ j) (β i + γ i) =
          Section1.scalarProduct G (γ i) (β j) +
            Section1.scalarProduct G (γ j) (β i) := by
      rw [Section5.scalarProduct_add_right, Section5.scalarProduct_add_right,
        hγij, hγji]
      ring
    have hrightExpand :
        Section1.scalarProduct G (β i + γ i) (β j + γ j) =
          Section1.scalarProduct G (γ j) (β i) +
            Section1.scalarProduct G (γ i) (β j) := by
      rw [Section1.scalarProduct_add_left, Section5.scalarProduct_add_right,
        Section5.scalarProduct_add_right, hβorth i j hne, hγij,
        hβγflip i j]
      ring
    calc
      Section1.scalarProduct G (γ i) (β j + γ j) +
          Section1.scalarProduct G (γ j) (β i + γ i) =
          Section1.scalarProduct G (β i + γ i) (β j + γ j) := by
            rw [hleftExpand, hrightExpand]
            ring
      _ = (1 : ℂ) + 2 * (m : ℂ) := htotal
  have h79nonzero (i j : I) (hne : i ≠ j) :
      Section1.scalarProduct G (β i) (γ j) ≠ 0 ∨
        Section1.scalarProduct G (β j) (γ i) ≠ 0 := by
    let A₂ : Fin 2 → Set G := λ
      | 0 => typeIASet (L i) (H i)
      | 1 => typeIASet (L j) (H j)
    let L₂ : Fin 2 → Subgroup G := λ
      | 0 => L i
      | 1 => L j
    let H₂ : Fin 2 → Subgroup G := λ
      | 0 => H i
      | 1 => H j
    let K₂ : Fin 2 → G → Subgroup G := λ
      | 0 => R i
      | 1 => R j
    let S₂ : (k : Fin 2) → Finset (Section1.ClassFunction (L₂ k)) := λ
      | 0 => S i
      | 1 => S j
    let τ₂ : (k : Fin 2) →
        Section1.ClassFunction (L₂ k) →ₗ[ℂ] Section1.ClassFunction G := λ
      | 0 => τ i
      | 1 => τ j
    let ν₂ : (k : Fin 2) →
        Section1.ClassFunction (L₂ k) →ₗ[ℂ] Section1.ClassFunction G := λ
      | 0 => ν i
      | 1 => ν j
    let ζ₂ : (k : Fin 2) → Section1.ClassFunction (L₂ k) := λ
      | 0 => ζ i
      | 1 => ζ j
    let β₂ : Fin 2 → Section1.ClassFunction G := λ
      | 0 => β i
      | 1 => β j
    let γ₂ : Fin 2 → Section1.ClassFunction G := λ
      | 0 => γ i
      | 1 => γ j
    have hfamily : Section7.familyHypothesis A₂ L₂ K₂ := by
      refine ⟨?_, ?_⟩
      · intro k
        fin_cases k
        · simpa [A₂, L₂, K₂, Section2.hypothesis_2_2_statement] using h22 i
        · simpa [A₂, L₂, K₂, Section2.hypothesis_2_2_statement] using h22 j
      · intro k l hkl
        fin_cases k <;> fin_cases l
        · exact (hkl rfl).elim
        · change Disjoint
            (Section7.dadeProjectionSupport (typeIASet (L i) (H i)) (R i))
            (Section7.dadeProjectionSupport (typeIASet (L j) (H j)) (R j))
          simpa [Section7.dadeProjectionSupport,
            dadeSupport_eq_tildeA_of_notation_8_14_source_data
              (L i) (typeIASet (L i) (H i)) (typeIASet (L i) (H i))
              (Section8.a1Set (H i)) (D i) (tildeA i) (tildeA i) (tildeA i)
              (R i) (hnot i),
            dadeSupport_eq_tildeA_of_notation_8_14_source_data
              (L j) (typeIASet (L j) (H j)) (typeIASet (L j) (H j))
              (Section8.a1Set (H j)) (D j) (tildeA j) (tildeA j) (tildeA j)
              (R j) (hnot j)] using htildeDisjoint i j hne
        · change Disjoint
            (Section7.dadeProjectionSupport (typeIASet (L j) (H j)) (R j))
            (Section7.dadeProjectionSupport (typeIASet (L i) (H i)) (R i))
          simpa [Section7.dadeProjectionSupport,
            dadeSupport_eq_tildeA_of_notation_8_14_source_data
              (L j) (typeIASet (L j) (H j)) (typeIASet (L j) (H j))
              (Section8.a1Set (H j)) (D j) (tildeA j) (tildeA j) (tildeA j)
              (R j) (hnot j),
            dadeSupport_eq_tildeA_of_notation_8_14_source_data
              (L i) (typeIASet (L i) (H i)) (typeIASet (L i) (H i))
              (Section8.a1Set (H i)) (D i) (tildeA i) (tildeA i) (tildeA i)
              (R i) (hnot i)] using (htildeDisjoint i j hne).symm
        · exact (hkl rfl).elim
    have hsource :
        Section7.theorem_7_9_source_hypothesis
          A₂ L₂ H₂ K₂ S₂ τ₂ ν₂ ζ₂ β₂ γ₂ := by
      refine ⟨hfamily, ?_, hmin.odd_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k
        fin_cases k
        · simpa [A₂, L₂, K₂, τ₂] using hAgree i
        · simpa [A₂, L₂, K₂, τ₂] using hAgree j
      · intro k
        fin_cases k
        · simpa [H₂, L₂] using section16MFSubgroup_le (hMF i)
        · simpa [H₂, L₂] using section16MFSubgroup_le (hMF j)
      · intro k
        fin_cases k
        · simpa [H₂, L₂] using section16MFSubgroup_subgroupOf_normal (hMF i)
        · simpa [H₂, L₂] using section16MFSubgroup_subgroupOf_normal (hMF j)
      · intro k
        fin_cases k
        · simpa [A₂, H₂] using hAeq i
        · simpa [A₂, H₂] using hAeq j
      · intro k
        fin_cases k
        · simpa [S₂, H₂, L₂] using hS i
        · simpa [S₂, H₂, L₂] using hS j
      · intro k
        fin_cases k
        · simpa [L₂, S₂, τ₂] using (h126 i).2
        · simpa [L₂, S₂, τ₂] using (h126 j).2
      · intro k
        fin_cases k
        · dsimp [S₂, τ₂, ν₂]
          rcases hν i with ⟨h1, h2, h3⟩
          exact ⟨h1, h2, h3⟩
        · dsimp [S₂, τ₂, ν₂]
          rcases hν j with ⟨h1, h2, h3⟩
          exact ⟨h1, h2, h3⟩
      · intro k
        fin_cases k
        · simpa [S₂, ζ₂, H₂, L₂] using hζ i
        · simpa [S₂, ζ₂, H₂, L₂] using hζ j
      · intro k
        fin_cases k <;> rfl
      · intro k
        fin_cases k <;> rfl
    have hparity : Section7.theorem_7_9_parityData β₂ γ₂ := by
      have hγ01 : Section1.scalarProduct G (γ₂ 0) (γ₂ 1) = 0 := by
        simpa [γ₂, γ] using hγorth i j hne
      have hγ10 : Section1.scalarProduct G (γ₂ 1) (γ₂ 0) = 0 := by
        simpa [γ₂, γ] using hγorth j i hne.symm
      have hodd :
          ∃ z : ℤ,
            Section1.scalarProduct G (γ₂ 0) (β₂ 1 + γ₂ 1) +
                Section1.scalarProduct G (γ₂ 1) (β₂ 0 + γ₂ 0) =
              (1 : ℂ) + 2 * (z : ℂ) := by
        simpa [β₂, γ₂] using hoddPair i j hne
      exact Section7.theorem_7_9_parityData_of_delta_odd hγ01 hγ10 hodd
    have h79 := Section7.theorem_7_9
      A₂ L₂ H₂ K₂ S₂ τ₂ ν₂ ζ₂ β₂ γ₂ hsource hparity
    simpa [β₂, γ₂] using h79
  rcases hγsigned i1 with ⟨ε, hε, χ, hχirr, hγi1⟩
  have hγi1eq : γ i1 = ε • χ := by simpa [γ] using hγi1
  have hχclass : Section1.IsClassFunction χ :=
    Section1.isCharacter_isClassFunction χ
      (isCharacter_of_isIrreducibleCharacterOnGroup hχirr)
  have hνχorth (k : I) (hne : k ≠ i1)
      (φ : Section1.ClassFunction (L k)) (hφ : φ ∈ S k) :
      Section1.scalarProduct G (ν k φ) χ = 0 := by
    have hγzero :
        Section1.scalarProduct G (ν k φ) (γ i1) = 0 :=
      hsubsetOrth (hνSubset k φ hφ)
        (hνSubset i1 (ζ i1) (hζ i1).1)
        (hRorth k i1 hne φ hφ (ζ i1) (hζ i1).1)
    rcases hε with hε | hε
    · rw [hε] at hγi1eq
      simpa [hγi1eq] using hγzero
    · rw [hε] at hγi1eq
      have hneg := congrArg Neg.neg hγzero
      simpa [hγi1eq, Section1.scalarProduct] using hneg
  have hprojectionFormula (k : I) (hne : k ≠ i1) :
      (Section5.cfNormSq
          (Section7.dadeProjectionOn (typeIASet (L k) (H k))
            (L k) (R k) χ) : ℂ) =
        (((typeIASet (L k) (H k)).ncard : ℂ) / (Nat.card (L k) : ℂ)) *
          (Section1.scalarProduct G (β k) χ) ^ 2 := by
    have h78k := h78 k
    rcases h78k with
      ⟨_hHL, hST, _hpunctured, _hcoherent, _hext,
        hζS, _hζirr, hζdeg⟩
    have hζT : ζ k ∈ T k := (hST (ζ k)).1 hζS |>.1
    have hζnePrincipal :
        ζ k ≠ Section7.principalInducedCharacter (L k) (H k) :=
      (hST (ζ k)).1 hζS |>.2
    have hprincipalT :
        Section7.principalInducedCharacter (L k) (H k) ∈ T k := by
      simp [T]
    let Q : Finset (Section1.ClassFunction (L k)) := (T k).erase (ζ k)
    let n : ℕ := Fintype.card
      {ψ : Section1.ClassFunction (L k) // ψ ∈ Q}
    let restEquiv : Fin n ≃
        {ψ : Section1.ClassFunction (L k) // ψ ∈ Q} :=
      (Fintype.equivFin _).symm
    let η : Fin (n + 1) → Section1.ClassFunction (L k) :=
      Fin.cases (ζ k) (fun q : Fin n => (restEquiv q).1)
    let d : Fin n → ℂ := fun q =>
      Section1.degree (η (Fin.succ q)) / Section1.degree (η 0)
    have heC : (((H k).relIndex (L k) : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (he k).ne'
    have hη0deg :
        Section1.degree (η 0) = ((H k).relIndex (L k) : ℂ) := by
      simpa [η] using hζdeg
    have hη0deg_ne : Section1.degree (η 0) ≠ 0 := by
      rw [hη0deg]
      exact heC
    have henum : Section7.inducedFamilyEnumeration (T k) η d := by
      refine ⟨?_, ?_, ?_⟩
      · intro ψ
        constructor
        · intro hψT
          by_cases hψζ : ψ = ζ k
          · exact ⟨0, by simp [η, hψζ]⟩
          · have hψQ : ψ ∈ Q := by simp [Q, hψζ, hψT]
            let x : {ψ : Section1.ClassFunction (L k) // ψ ∈ Q} := ⟨ψ, hψQ⟩
            refine ⟨Fin.succ (restEquiv.symm x), ?_⟩
            simp [η, x]
        · rintro ⟨q, rfl⟩
          cases q using Fin.cases with
          | zero => simpa [η] using hζT
          | succ q =>
              have hqQ : (restEquiv q).1 ∈ Q := (restEquiv q).2
              exact (Finset.mem_erase.mp hqQ).2
      · intro q r hqr
        cases q using Fin.cases with
        | zero =>
            cases r using Fin.cases with
            | zero => rfl
            | succ r =>
                exfalso
                have hrQ : (restEquiv r).1 ∈ Q := (restEquiv r).2
                have hrne : (restEquiv r).1 ≠ ζ k :=
                  (Finset.mem_erase.mp hrQ).1
                exact hrne (by simpa [η] using hqr.symm)
        | succ q =>
            cases r using Fin.cases with
            | zero =>
                exfalso
                have hqQ : (restEquiv q).1 ∈ Q := (restEquiv q).2
                have hqne : (restEquiv q).1 ≠ ζ k :=
                  (Finset.mem_erase.mp hqQ).1
                exact hqne (by simpa [η] using hqr)
            | succ r =>
                apply congrArg Fin.succ
                apply restEquiv.injective
                apply Subtype.ext
                simpa [η] using hqr
      · intro q
        dsimp [d]
        field_simp [hη0deg_ne]
    have hprincipalQ :
        Section7.principalInducedCharacter (L k) (H k) ∈ Q := by
      simp [Q, hζnePrincipal.symm, hprincipalT]
    let iβ : Fin n := restEquiv.symm
      ⟨Section7.principalInducedCharacter (L k) (H k), hprincipalQ⟩
    letI : Nonempty (Fin n) := ⟨iβ⟩
    have hiβ :
        η (Fin.succ iβ) =
          Section7.principalInducedCharacter (L k) (H k) := by
      simp [η, iβ]
    have hprincipalDegree :
        Section1.degree (Section7.principalInducedCharacter (L k) (H k)) =
          ((H k).relIndex (L k) : ℂ) := by
      unfold Section7.principalInducedCharacter
      rw [Section1.degree_inducedClassFunction]
      simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
    have hdβ : d iβ = 1 := by
      simp [d, hiβ, hprincipalDegree, hη0deg, heC]
    have hbasis :
        Section7.projectionBasisPackage (typeIASet (L k) (H k))
          (L k) (H k) η d :=
      Section7.theorem_7_8_b_projectionBasisPackage_source_bridge
        (h76 k) henum
    have htailS (q : Fin n) (hq : q ≠ iβ) : η (Fin.succ q) ∈ S k := by
      apply (hST (η (Fin.succ q))).2
      constructor
      · exact (henum.1 (η (Fin.succ q))).2 ⟨Fin.succ q, rfl⟩
      · intro hprincipal
        apply hq
        apply Fin.succ_injective
        apply henum.2.1
        rw [hprincipal, hiβ]
    let c : Fin n → ℂ := fun q =>
      if q = iβ then Section1.scalarProduct G (β k) χ else 0
    have hcoeff :
        Section7.projectionCoefficientPackage η d (τ k) χ c := by
      intro q
      by_cases hq : q = iβ
      · subst q
        have hcomboβ :
            τ k (η (Fin.succ iβ) - d iβ • η 0) = β k := by
          rw [hiβ, hdβ]
          simp only [one_smul]
          change τ k
              (Section7.principalInducedCharacter (L k) (H k) - ζ k) = β k
          rfl
        simp [c, hcomboβ]
      · have hqS : η (Fin.succ q) ∈ S k := htailS q hq
        rcases Section7.theorem_7_8_degree_zero_combo_mem_integerSpanOn
            (h78 k) hqS with
          ⟨m, _hm_ne, hdegm, hcombo⟩
        have hdq : d q = (m : ℂ) := by
          dsimp [d]
          rw [hdegm, hη0deg]
          field_simp [heC]
        have hcomboEq :
            η (Fin.succ q) - d q • η 0 =
              η (Fin.succ q) - (m : ℂ) • ζ k := by
          rw [hdq]
          rfl
        have hντ :
            ν k (η (Fin.succ q) - (m : ℂ) • ζ k) =
              τ k (η (Fin.succ q) - (m : ℂ) • ζ k) :=
          (hν k).2.2 _ hcombo
        have hzero :
            Section1.scalarProduct G
              (τ k (η (Fin.succ q) - d q • η 0)) χ = 0 := by
          rw [hcomboEq, ← hντ, map_sub, map_smul,
            Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left,
            hνχorth k hne (η (Fin.succ q)) hqS,
            hνχorth k hne (ζ k) (hζ k).1]
          ring
        have hzero' :
            Section1.scalarProduct G
              (τ k (η (Fin.succ q)) - d q • τ k (η 0)) χ = 0 := by
          simpa using hzero
        simp [c, hq, hzero']
    have h77 := Section7.theorem_7_7
      (typeIASet (L k) (H k)) (L k) (H k) (R k) (T k)
      η d (τ k) χ c (h76 k) (hAgree k) henum hbasis hχclass hcoeff
    let D : Fin n → Fin n → ℂ := fun q r =>
      (Section5.cfNormSq (η (Fin.succ q)) : ℂ) *
        (Section5.cfNormSq (η (Fin.succ r)) : ℂ)
    let B : Fin n → Fin n → ℂ := fun q r =>
      Section1.scalarProduct (L k) (η (Fin.succ q)) (η (Fin.succ r)) -
        η (Fin.succ q) 1 * η (Fin.succ r) 1 /
          (((H k).relIndex (L k) : ℂ) * (Nat.card (H k) : ℂ))
    have hsumOne :
        (∑ q : Fin n, ∑ r : Fin n,
          (star (c q) * c r) / D q r * B q r) =
          (star (c iβ) * c iβ) / D iβ iβ * B iβ iβ := by
      calc
        (∑ q : Fin n, ∑ r : Fin n,
            (star (c q) * c r) / D q r * B q r) =
            ∑ r : Fin n,
              (star (c iβ) * c r) / D iβ r * B iβ r := by
          rw [Finset.sum_eq_single iβ]
          · intro q _hq hq
            simp [c, hq]
          · intro hiβ
            exact False.elim (hiβ (by simp))
        _ = (star (c iβ) * c iβ) / D iβ iβ * B iβ iβ := by
          rw [Finset.sum_eq_single iβ]
          · intro q _hq hq
            simp [c, hq]
          · intro hiβ
            exact False.elim (hiβ (by simp))
    have hprincipalChar :
        Section1.IsCharacter
          (Section7.principalInducedCharacter (L k) (H k)) := by
      have hprincipalH :
          Section1.IsCharacter
            (Section1.principalCharacter ((H k).subgroupOf (L k))) :=
        isCharacter_of_isIrreducibleCharacterOnGroup
          Section3.principalCharacter_isIrreducibleCharacterOnGroup
      unfold Section7.principalInducedCharacter
      exact Section1.isCharacter_inducedCF_of_isCharacter
        ((H k).subgroupOf (L k))
        (Section1.principalCharacter ((H k).subgroupOf (L k))) hprincipalH
    have hprincipalNorm :
        (Section5.cfNormSq
          (Section7.principalInducedCharacter (L k) (H k)) : ℂ) =
          ((H k).relIndex (L k) : ℂ) := by
      have hsc := Section5.scalarProduct_self_eq_cfNormSq_of_character
        hprincipalChar
      rw [← hsc]
      exact Section7.theorem_7_8_principalInduced_self_scalar
        (section16MFSubgroup_subgroupOf_normal (hMF k))
    have hprincipalSelf :
        Section1.scalarProduct (L k)
          (Section7.principalInducedCharacter (L k) (H k))
          (Section7.principalInducedCharacter (L k) (H k)) =
            ((H k).relIndex (L k) : ℂ) :=
      Section7.theorem_7_8_principalInduced_self_scalar
        (section16MFSubgroup_subgroupOf_normal (hMF k))
    have hprincipalOne :
        Section7.principalInducedCharacter (L k) (H k) (1 : L k) =
          ((H k).relIndex (L k) : ℂ) := by
      simpa [Section1.degree_apply] using hprincipalDegree
    have hAcard :
        (typeIASet (L k) (H k)).ncard = Nat.card (H k) - 1 := by
      rw [hAeq k]
      change (Section7.puncturedSubgroupSet (H k)).ncard = _
      have hset :
          Section7.puncturedSubgroupSet (H k) =
            ((H k : Set G) \ {1}) := by
        ext g
        simp [Section7.puncturedSubgroupSet]
      rw [hset, Set.ncard_sdiff_singleton_of_mem (H k).one_mem]
      exact congrArg (fun m : ℕ => m - 1)
        (Nat.card_coe_set_eq (H k : Set G)).symm
    have hcardHsub :
        Nat.card ((H k).subgroupOf (L k)) = Nat.card (H k) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (section16MFSubgroup_le (hMF k))).toEquiv
    have hcardLNat :
        (H k).relIndex (L k) * Nat.card (H k) = Nat.card (L k) := by
      rw [Subgroup.relIndex, ← hcardHsub]
      exact Subgroup.index_mul_card (H := (H k).subgroupOf (L k))
    have hcardLC :
        (Nat.card (L k) : ℂ) =
          ((H k).relIndex (L k) : ℂ) * (Nat.card (H k) : ℂ) := by
      exact_mod_cast hcardLNat.symm
    have hhC : (Nat.card (H k) : ℂ) ≠ 0 := by
      exact_mod_cast (hh k).ne'
    have hcardSubC :
        ((Nat.card (H k) - 1 : ℕ) : ℂ) = (Nat.card (H k) : ℂ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (hh k).ne')]
      norm_num
    have hcoeffReal :
        star (Section1.scalarProduct G (β k) χ) =
          Section1.scalarProduct G (β k) χ := by
      rcases Section3.scalarProduct_isVirtualCharacter_eq_int
          (by simpa [β] using hβvirt k)
          (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hχirr) with
        ⟨z, hz⟩
      rw [hz]
      simp
    calc
      (Section5.cfNormSq
          (Section7.dadeProjectionOn (typeIASet (L k) (H k))
            (L k) (R k) χ) : ℂ) =
          ∑ q : Fin n, ∑ r : Fin n,
            (star (c q) * c r) / D q r * B q r := by
              simpa [D, B] using h77.2
      _ = (star (c iβ) * c iβ) / D iβ iβ * B iβ iβ := hsumOne
      _ = (((typeIASet (L k) (H k)).ncard : ℂ) /
              (Nat.card (L k) : ℂ)) *
            (Section1.scalarProduct G (β k) χ) ^ 2 := by
        rw [hAcard, hcardLC, hcardSubC]
        simp [c, D, B, hiβ, hprincipalNorm, hprincipalSelf,
          hprincipalOne, hcoeffReal]
        field_simp [heC, hhC]
  have hAcardAll (k : I) :
      (typeIASet (L k) (H k)).ncard = Nat.card (H k) - 1 := by
    rw [hAeq k]
    change (Section7.puncturedSubgroupSet (H k)).ncard = _
    have hset :
        Section7.puncturedSubgroupSet (H k) = ((H k : Set G) \ {1}) := by
      ext g
      simp [Section7.puncturedSubgroupSet]
    rw [hset, Set.ncard_sdiff_singleton_of_mem (H k).one_mem]
    exact congrArg (fun m : ℕ => m - 1)
      (Nat.card_coe_set_eq (H k : Set G)).symm
  have hcardLAll (k : I) :
      (Nat.card (L k) : ℝ) =
        ((H k).relIndex (L k) : ℝ) * (Nat.card (H k) : ℝ) := by
    have hcardHsub :
        Nat.card ((H k).subgroupOf (L k)) = Nat.card (H k) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (section16MFSubgroup_le (hMF k))).toEquiv
    have hcardLNat :
        (H k).relIndex (L k) * Nat.card (H k) = Nat.card (L k) := by
      rw [Subgroup.relIndex, ← hcardHsub]
      exact Subgroup.index_mul_card (H := (H k).subgroupOf (L k))
    exact_mod_cast hcardLNat.symm
  have hsupportFactor (k : I) :
      ((typeIASet (L k) (H k)).ncard : ℝ) / (Nat.card (L k) : ℝ) =
        ((Nat.card (H k) : ℝ) - 1) /
          (((H k).relIndex (L k) : ℝ) * (Nat.card (H k) : ℝ)) := by
    rw [hAcardAll k, hcardLAll k,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (hh k).ne')]
    norm_num
  have hprojectionLower (k : I) (hne : k ≠ i1)
      (hcoeffGamma : Section1.scalarProduct G (β k) (γ i1) ≠ 0) :
      ((Nat.card (H k) : ℝ) - 1) /
          (((H k).relIndex (L k) : ℝ) * (Nat.card (H k) : ℝ)) ≤
        Section7.weightedProjectionEnergy
          (typeIASet (L k) (H k)) (L k) (R k) χ := by
    have hcoeffChi : Section1.scalarProduct G (β k) χ ≠ 0 := by
      intro hzero
      apply hcoeffGamma
      rw [hγi1eq, Section1.scalarProduct_smul_right, hzero]
      simp
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int
        (by simpa [β] using hβvirt k)
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hχirr) with
      ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      intro hz0
      apply hcoeffChi
      rw [hz, hz0]
      simp
    have hzsq : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
      rcases lt_or_gt_of_ne hz0 with hzneg | hzpos
      · have hzle : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
        nlinarith
      · have hzge : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
        nlinarith
    have hformulaC := hprojectionFormula k hne
    rw [hz] at hformulaC
    have hformulaR :
        Section5.cfNormSq
            (Section7.dadeProjectionOn (typeIASet (L k) (H k))
              (L k) (R k) χ) =
          ((typeIASet (L k) (H k)).ncard : ℝ) /
              (Nat.card (L k) : ℝ) * (z : ℝ) ^ 2 := by
      have hre := congrArg Complex.re hformulaC
      norm_num at hre
      have hzpow : Complex.re ((z : ℂ) ^ 2) = (z : ℝ) ^ 2 := by
        norm_num [pow_two]
      rw [hzpow] at hre
      simpa using hre
    have hfactorNonneg :
        0 ≤ ((typeIASet (L k) (H k)).ncard : ℝ) /
          (Nat.card (L k) : ℝ) := by positivity
    rw [Section7.weightedProjectionEnergy, hformulaR, ← hsupportFactor k]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hzsq hfactorNonneg
  have hdadeProjectionOn_smul
      (X : Set G) (M : Subgroup G) (K : G → Subgroup G)
      (ψ : Section1.ClassFunction G) (z : ℂ) :
      Section7.dadeProjectionOn X M K (z • ψ) =
        z • Section7.dadeProjectionOn X M K ψ := by
    ext x
    by_cases hx : (x : G) ∈ X
    · simp [Section7.dadeProjectionOn, Section7.dadeProjection,
        Section2.dadeAveragingFunction, hx, ← Finset.mul_sum]
      ring
    · simp [Section7.dadeProjectionOn, hx]
  have hweightSign
      (X : Set G) (M : Subgroup G) (K : G → Subgroup G)
      (ψ : Section1.ClassFunction G) {z : ℂ} (hz : Section1.IsSign z) :
      Section7.weightedProjectionEnergy X M K (z • ψ) =
        Section7.weightedProjectionEnergy X M K ψ := by
    unfold Section7.weightedProjectionEnergy Section5.cfNormSq
      Section1.scalarProduct
    rw [hdadeProjectionOn_smul]
    rcases hz with rfl | rfl <;> simp
  have hweightI1 :
      1 - ((H i1).relIndex (L i1) : ℝ) / (Nat.card (H i1) : ℝ) ≤
        Section7.weightedProjectionEnergy
          (typeIASet (L i1) (H i1)) (L i1) (R i1) χ := by
    have hlower := (h78b i1).1
    change 1 - ((H i1).relIndex (L i1) : ℝ) /
        (Nat.card (H i1) : ℝ) ≤
      Section7.weightedProjectionEnergy
        (typeIASet (L i1) (H i1)) (L i1) (R i1) (γ i1) at hlower
    rw [hγi1eq, hweightSign _ _ _ χ hε] at hlower
    exact hlower
  have hconjugateInSymm {x y : G} (hxy : Section2.conjugateIn x y) :
      Section2.conjugateIn y x := by
    rcases hxy with ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    have hg' := congrArg (fun t : G => g⁻¹ * t * g) hg
    simpa [Section2.conjBy, mul_assoc] using hg'.symm
  have hsupportConjugate (k : I) :
      Section7.dadeProjectionSupport (typeIASet (L k) (H k)) (R k) =
        Section2.conjugateSet (Section7.puncturedSubgroupSet (H k)) := by
    rw [hAeq k]
    change Section2.dadeSupport (A k) (fun _ : G => ⊥) =
      Section2.conjugateSet (A k)
    ext g
    constructor
    · rintro ⟨x, hx, y, hy, hconj⟩
      have hy1 : y = 1 := by simpa using hy
      subst y
      refine ⟨x, hx, ?_⟩
      exact hconjugateInSymm (by simpa using hconj)
    · rintro ⟨x, hx, hconj⟩
      exact ⟨x, hx, 1, by simp, by simpa using hconjugateInSymm hconj⟩
  have hfamily : Section7.familyHypothesis
      (fun k : I => typeIASet (L k) (H k)) L R := by
    refine ⟨h22, ?_⟩
    intro k l hkl
    simpa [Section7.dadeProjectionSupport,
      dadeSupport_eq_tildeA_of_notation_8_14_source_data
        (L k) (typeIASet (L k) (H k)) (typeIASet (L k) (H k))
        (Section8.a1Set (H k)) (D k) (tildeA k) (tildeA k) (tildeA k)
        (R k) (hnot k),
      dadeSupport_eq_tildeA_of_notation_8_14_source_data
        (L l) (typeIASet (L l) (H l)) (typeIASet (L l) (H l))
        (Section8.a1Set (H l)) (D l) (tildeA l) (tildeA l) (tildeA l)
        (R l) (hnot l)] using htildeDisjoint k l hkl
  have h74 : Section7.hypothesis_7_4_statement
      (fun k : I => typeIASet (L k) (H k)) L R ({1} : Set G) := by
    refine ⟨hfamily, ?_⟩
    have hu :
        (⋃ k : I,
            Section7.dadeProjectionSupport (typeIASet (L k) (H k)) (R k)) =
          ⋃ k : I,
            Section2.conjugateSet (Section7.puncturedSubgroupSet (H k)) := by
      ext g
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨k, hg⟩
        exact ⟨k, by rwa [hsupportConjugate k] at hg⟩
      · rintro ⟨k, hg⟩
        exact ⟨k, by rwa [hsupportConjugate k]⟩
    calc
      ({1} : Set G) = Set.univ \ ⋃ k : I,
          Section2.conjugateSet (Section7.puncturedSubgroupSet (H k)) := hG0
      _ = Set.univ \ ⋃ k : I,
          Section7.dadeProjectionSupport (typeIASet (L k) (H k)) (R k) := by
        exact congrArg (fun X : Set G => Set.univ \ X) hu.symm
  have h75 := Section7.theorem_7_5
    (fun k : I => typeIASet (L k) (H k)) L R ({1} : Set G)
      h74 χ hχirr
  have hsupportEnergySingleton
      (ψ : Section1.ClassFunction G) :
      Section7.supportEnergy ({1} : Set G) ψ = Complex.normSq (ψ 1) := by
    unfold Section7.supportEnergy
    rw [Finset.sum_eq_single (1 : G)]
    · simp
    · intro g _hg hg
      simp [hg]
    · simp
  have hprincipalEnergy :
      Section7.normalizedSupportEnergy ({1} : Set G)
          (Section1.principalCharacter G) =
        (Nat.card G : ℝ)⁻¹ := by
    rw [Section7.normalizedSupportEnergy, hsupportEnergySingleton]
    simp [Section1.principalCharacter]
  have hχone : 1 ≤ Complex.normSq (χ 1) := by
    rcases hχirr with ⟨n, ρ, hρ, hχeq⟩
    haveI : Representation.IsIrreducible ρ := hρ
    haveI : Nontrivial (Fin n → ℂ) :=
      Theory.Character.irreducible_nontrivial (ρ := ρ)
    have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) :=
      (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
    have hn : 0 < n := by simpa using hdim_pos
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hχeq]
    simp only [Representation.char_one]
    norm_num [Complex.normSq]
    nlinarith
  have hχEnergy :
      (Nat.card G : ℝ)⁻¹ ≤
        Section7.normalizedSupportEnergy ({1} : Set G) χ := by
    rw [Section7.normalizedSupportEnergy, hsupportEnergySingleton]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hχone (by positivity : 0 ≤ (Nat.card G : ℝ)⁻¹)
  let q : I → ℝ := fun i =>
    ((Nat.card (H i) : ℝ) - 1) /
      (((H i).relIndex (L i) : ℝ) * (Nat.card (H i) : ℝ))
  let coeff : I → ℂ := fun i => Section1.scalarProduct G (β i) (γ i1)
  let rest : Finset I := Finset.univ.erase i1
  let calB : Finset I := rest.filter fun i => coeff i = 0
  let calC : Finset I := rest.filter fun i => coeff i ≠ 0
  let sumB : ℝ := ∑ i ∈ calB, q i
  have hweightSumUpper :
      (∑ i : I,
          Section7.weightedProjectionEnergy
            (typeIASet (L i) (H i)) (L i) (R i) χ) ≤
        ∑ i : I, q i := by
    have h75' := h75
    rw [hprincipalEnergy] at h75'
    simp_rw [hsupportFactor] at h75'
    dsimp [q]
    linarith
  have hweightLowerC :
      (∑ i ∈ calC, q i) ≤
        ∑ i ∈ calC,
          Section7.weightedProjectionEnergy
            (typeIASet (L i) (H i)) (L i) (R i) χ := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hne : i ≠ i1 := (Finset.mem_erase.mp hi'.1).1
    exact hprojectionLower i hne hi'.2
  have hweightBnonneg :
      0 ≤ ∑ i ∈ calB,
        Section7.weightedProjectionEnergy
          (typeIASet (L i) (H i)) (L i) (R i) χ := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact Section5.cfNormSq_nonneg _
  have hweightPartition :
      (∑ i ∈ calB,
          Section7.weightedProjectionEnergy
            (typeIASet (L i) (H i)) (L i) (R i) χ) +
        (∑ i ∈ calC,
          Section7.weightedProjectionEnergy
            (typeIASet (L i) (H i)) (L i) (R i) χ) =
        ∑ i ∈ rest,
          Section7.weightedProjectionEnergy
            (typeIASet (L i) (H i)) (L i) (R i) χ := by
    simpa [calB, calC] using
      (Finset.sum_filter_add_sum_filter_not rest (fun i => coeff i = 0)
        (fun i => Section7.weightedProjectionEnergy
          (typeIASet (L i) (H i)) (L i) (R i) χ))
  have hweightErase :
      (∑ i ∈ rest,
          Section7.weightedProjectionEnergy
            (typeIASet (L i) (H i)) (L i) (R i) χ) +
        Section7.weightedProjectionEnergy
            (typeIASet (L i1) (H i1)) (L i1) (R i1) χ =
        ∑ i : I,
          Section7.weightedProjectionEnergy
            (typeIASet (L i) (H i)) (L i) (R i) χ := by
    simp [rest]
  have hweightSumLower :
      1 - ((H i1).relIndex (L i1) : ℝ) / (Nat.card (H i1) : ℝ) +
          ∑ i ∈ calC, q i ≤
        ∑ i : I,
          Section7.weightedProjectionEnergy
            (typeIASet (L i) (H i)) (L i) (R i) χ := by
    linarith
  have hqPartition :
      (∑ i ∈ calB, q i) + (∑ i ∈ calC, q i) = ∑ i ∈ rest, q i := by
    simp [calB, calC]
    exact (Finset.sum_filter_add_sum_filter_not rest (fun i => coeff i = 0) q)
  have hqErase :
      (∑ i ∈ rest, q i) + q i1 = ∑ i : I, q i := by
    simp [rest]
  have hbase :
      1 - ((H i1).relIndex (L i1) : ℝ) / (Nat.card (H i1) : ℝ) -
          q i1 - sumB ≤ 0 := by
    dsimp [sumB]
    linarith
  have hνorth (i j : I) (hne : i ≠ j)
      (φ : Section1.ClassFunction (L i)) (hφ : φ ∈ S i)
      (ψ : Section1.ClassFunction (L j)) (hψ : ψ ∈ S j) :
      Section1.scalarProduct G (ν i φ) (ν j ψ) = 0 :=
    hsubsetOrth (hνSubset i φ hφ) (hνSubset j ψ hψ)
      (hRorth i j hne φ hφ ψ hψ)
  let W : I → Section1.ClassFunction G := fun i =>
    Section7.theorem_7_8_weightedSum (S i) (ν i)
      ((H i).relIndex (L i))
  have hWsum (i : I) :
      W i = fun g => ∑ φ : S i,
        (((φ : Section1.ClassFunction (L i)) 1 /
          (((H i).relIndex (L i) : ℂ) *
            (Section5.cfNormSq
              (φ : Section1.ClassFunction (L i)) : ℂ))) •
          ν i (φ : Section1.ClassFunction (L i))) g := by
    ext g
    simp only [W, Section7.theorem_7_8_weightedSum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_attach (S i)
      (fun φ : Section1.ClassFunction (L i) =>
        φ 1 / (((H i).relIndex (L i) : ℂ) *
          (Section5.cfNormSq φ : ℂ)) * ν i φ g)).symm
  have hWnorm (i : I) :
      Section5.cfNormSq (W i) =
        ((Nat.card (H i) : ℝ) - 1) /
          ((H i).relIndex (L i) : ℝ) := by
    have hdegree := Section7.theorem_7_8_b_degree_sum_identity
      (h76 i) (h78 i)
    simpa [W] using
      Section7.theorem_7_8_b_weightedSum_norm_of_degree_sum
        (h76 i) (h78 i) hdegree
  have hWνcross (i j : I) (hne : i ≠ j)
      (ψ : Section1.ClassFunction (L j)) (hψ : ψ ∈ S j) :
      Section1.scalarProduct G (W i) (ν j ψ) = 0 := by
    rw [hWsum i, Section1.scalarProduct_fintype_sum_left]
    refine Finset.sum_eq_zero ?_
    intro φ _hφ
    rw [Section1.scalarProduct_smul_left,
      hνorth i j hne (φ : Section1.ClassFunction (L i)) φ.2 ψ hψ]
    simp
  have hspanCF (i : I) (α : Section1.ClassFunction (L i))
      (hα : Section5.integerSpanOn (S i) Section5.puncturedSet α) :
      Section2.CFOn (L i) (typeIASet (L i) (H i)) α := by
    letI : ((H i).subgroupOf (L i)).Normal :=
      section16MFSubgroup_subgroupOf_normal (hMF i)
    refine CFOn_typeIASet_of_integerSpanOn_punctured_of_generators
      (L i) (H i) (S i) ?_ ?_ α hα
    · intro φ hφ
      exact isClassFunction_of_isIrreducibleCharacterOnGroup φ
        ((h126 i).1 φ hφ)
    · intro φ hφ l hlA hl1
      have hlnotH : (l : G) ∉ H i := by
        intro hlH
        apply hlA
        rw [hAeq i]
        exact ⟨hlH, hl1⟩
      have hlnotHsub : l ∉ (H i).subgroupOf (L i) := by
        intro hlHsub
        exact hlnotH hlHsub
      rcases (hS i φ).mp hφ with ⟨θ, _hθirr, _hθne, rfl⟩
      exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
        ((H i).subgroupOf (L i)) θ hlnotHsub
  have hτspanSupp (i : I) (α : Section1.ClassFunction (L i))
      (hα : Section5.integerSpanOn (S i) Section5.puncturedSet α) :
      Section1.supportedOn (τ i α) (tildeA i) := by
    rcases hDade i with ⟨_h22, htrans⟩
    rcases htrans with ⟨hAL, hτeq⟩
    rw [hτeq α (hspanCF i α hα)]
    have hsupp := supportedOn_dadeTransform_dadeSupport (R := R i) hAL α
    rw [dadeSupport_eq_tildeA_of_notation_8_14_source_data
      (L i) (typeIASet (L i) (H i)) (typeIASet (L i) (H i))
      (Section8.a1Set (H i)) (D i) (tildeA i) (tildeA i) (tildeA i)
      (R i) (hnot i)] at hsupp
    exact hsupp
  have hβτorth (i : I) (hne : i ≠ i1)
      (α : Section1.ClassFunction (L i))
      (hα : Section5.integerSpanOn (S i) Section5.puncturedSet α) :
      Section1.scalarProduct G (β i1) (τ i α) = 0 :=
    scalarProduct_eq_zero_of_supportedOn_disjoint
      (hβsupp i1) (hτspanSupp i α hα)
      (htildeDisjoint i1 i hne.symm)
  have hβνratio (i : I) (hne : i ≠ i1)
      (φ : Section1.ClassFunction (L i)) (hφ : φ ∈ S i) :
      Section1.scalarProduct G (β i1) (ν i φ) =
        (φ 1 / ((H i).relIndex (L i) : ℂ)) *
          Section1.scalarProduct G (β i1) (γ i) := by
    rcases Section7.theorem_7_8_degree_zero_combo_mem_integerSpanOn
        (h78 i) hφ with ⟨m, _hm, hdeg, hcombo⟩
    have hagree :
        ν i (φ - (m : ℂ) • ζ i) = τ i (φ - (m : ℂ) • ζ i) :=
      (hν i).2.2 _ hcombo
    have hzero := hβτorth i hne (φ - (m : ℂ) • ζ i) hcombo
    rw [← hagree, map_sub, map_smul, Section5.scalarProduct_sub_right,
      Section1.scalarProduct_smul_right] at hzero
    have heC : ((H i).relIndex (L i) : ℂ) ≠ 0 := by
      exact_mod_cast (he i).ne'
    have hratio :
        φ 1 / ((H i).relIndex (L i) : ℂ) = (m : ℂ) := by
      have hφone :
          φ 1 = ((H i).relIndex (L i) : ℂ) * (m : ℂ) := by
        simpa [Section1.degree_apply] using hdeg
      rw [hφone]
      field_simp [heC]
    rw [hratio]
    simpa [γ] using (sub_eq_zero.mp hzero)
  let dcoeff : I → ℂ := fun i => Section1.scalarProduct G (β i1) (γ i)
  have hdcoeffNonzero (i : I) (hi : i ∈ calB) : dcoeff i ≠ 0 := by
    have hi' := Finset.mem_filter.mp hi
    have hne : i ≠ i1 := (Finset.mem_erase.mp hi'.1).1
    rcases h79nonzero i i1 hne with hbad | hgood
    · exact False.elim (hbad hi'.2)
    · exact hgood
  have hrνratio (i : I) (hne : i ≠ i1)
      (φ : Section1.ClassFunction (L i)) (hφ : φ ∈ S i) :
      Section1.scalarProduct G (r i1) (ν i φ) =
        (φ 1 / ((H i).relIndex (L i) : ℂ)) * dcoeff i := by
    have hβeq :
        β i1 = Section1.principalCharacter G - γ i1 +
            ((a i1 : ℂ) • W i1) + r i1 := by
      simpa [β, γ, W] using (hdecomp i1).2.2.2
    have hp :
        Section1.scalarProduct G (Section1.principalCharacter G) (ν i φ) = 0 :=
      (hdecomp i).1 φ hφ
    have hγ : Section1.scalarProduct G (γ i1) (ν i φ) = 0 := by
      simpa [γ] using hνorth i1 i hne.symm (ζ i1) (hζ i1).1 φ hφ
    have hW : Section1.scalarProduct G (W i1) (ν i φ) = 0 :=
      hWνcross i1 i hne.symm φ hφ
    have hpair := congrArg
      (fun f : Section1.ClassFunction G => Section1.scalarProduct G f (ν i φ)) hβeq
    change Section1.scalarProduct G (β i1) (ν i φ) =
      Section1.scalarProduct G
        (Section1.principalCharacter G - γ i1 +
          (a i1 : ℂ) • W i1 + r i1) (ν i φ) at hpair
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left,
      Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left,
      hp, hγ, hW] at hpair
    simp only [sub_zero, mul_zero, zero_add] at hpair
    calc
      Section1.scalarProduct G (r i1) (ν i φ) =
          Section1.scalarProduct G (β i1) (ν i φ) := hpair.symm
      _ = (φ 1 / ((H i).relIndex (L i) : ℂ)) *
          Section1.scalarProduct G (β i1) (γ i) := hβνratio i hne φ hφ
      _ = (φ 1 / ((H i).relIndex (L i) : ℂ)) * dcoeff i := rfl
  let X : Section1.ClassFunction G :=
    ∑ i ∈ calB, dcoeff i • W i
  have hXsum :
      X = fun g => ∑ i : calB, (dcoeff (i : I) • W (i : I)) g := by
    ext g
    simp only [X, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_attach calB
      (fun i : I => dcoeff i * W i g)).symm
  have hXν (i : I) (hi : i ∈ calB)
      (φ : Section1.ClassFunction (L i)) (hφ : φ ∈ S i) :
      Section1.scalarProduct G X (ν i φ) =
        dcoeff i * (φ 1 / ((H i).relIndex (L i) : ℂ)) := by
    rw [hXsum, Section1.scalarProduct_fintype_sum_left]
    rw [Finset.sum_eq_single (⟨i, hi⟩ : calB)]
    · rw [Section1.scalarProduct_smul_left]
      have hWi := Section7.theorem_7_8_weightedSum_scalarProduct_of_mem
        (h76 i) (h78 i) hφ
      simpa [W] using congrArg (fun z : ℂ => dcoeff i * z) hWi
    · intro j _hj hji
      have hji' : (j : I) ≠ i := by
        intro hji'
        apply hji
        apply Subtype.ext
        exact hji'
      rw [Section1.scalarProduct_smul_left,
        hWνcross (j : I) i hji' φ hφ]
      simp
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  have hGammaImage (i : I) (hi : i ∈ calB)
      (φ : Section1.ClassFunction (L i)) (hφ : φ ∈ S i) :
      Section1.scalarProduct G (r i1 - X) (ν i φ) = 0 := by
    have hi' := Finset.mem_filter.mp hi
    have hne : i ≠ i1 := (Finset.mem_erase.mp hi'.1).1
    rw [Section5.scalarProduct_sub_left, hrνratio i hne φ hφ,
      hXν i hi φ hφ]
    ring
  have hGammaW (i : I) (hi : i ∈ calB) :
      Section1.scalarProduct G (r i1 - X) (W i) = 0 := by
    rw [hWsum i, Section1.scalarProduct_fintype_sum_right]
    refine Finset.sum_eq_zero ?_
    intro φ _hφ
    rw [Section1.scalarProduct_smul_right,
      hGammaImage i hi (φ : Section1.ClassFunction (L i)) φ.2]
    simp
  have hGammaX : Section1.scalarProduct G (r i1 - X) X = 0 := by
    calc
      Section1.scalarProduct G (r i1 - X) X =
          Section1.scalarProduct G (r i1 - X)
            (fun g => ∑ i : calB, (dcoeff (i : I) • W (i : I)) g) := by
              rw [hXsum]
      _ = ∑ i : calB,
          Section1.scalarProduct G (r i1 - X)
            (dcoeff (i : I) • W (i : I)) := by
              rw [Section1.scalarProduct_fintype_sum_right]
      _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _hi
        rw [Section1.scalarProduct_smul_right, hGammaW (i : I) i.2]
        simp
  have hXGamma : Section1.scalarProduct G X (r i1 - X) = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := G) X (r i1 - X)
    rw [hGammaX] at hswap
    simpa using hswap.symm
  have hWorth (i j : I) (hne : i ≠ j) :
      Section1.scalarProduct G (W i) (W j) = 0 := by
    rw [hWsum j, Section1.scalarProduct_fintype_sum_right]
    refine Finset.sum_eq_zero ?_
    intro ψ _hψ
    rw [Section1.scalarProduct_smul_right,
      hWνcross i j hne (ψ : Section1.ClassFunction (L j)) ψ.2]
    simp
  have htermSumOrth (i : I) (U : Finset I) (hi : i ∉ U) :
      Section1.scalarProduct G (dcoeff i • W i)
          (∑ j ∈ U, dcoeff j • W j) = 0 ∧
        Section1.scalarProduct G (∑ j ∈ U, dcoeff j • W j)
          (dcoeff i • W i) = 0 := by
    induction U using Finset.induction_on with
    | empty => simp [Section1.scalarProduct]
    | @insert j U hj ih =>
        have hij : i ≠ j := by
          intro hij
          subst j
          exact hi (Finset.mem_insert_self i U)
        have hiU : i ∉ U := by
          intro hiU
          exact hi (Finset.mem_insert_of_mem hiU)
        rcases ih hiU with ⟨hleft, hright⟩
        constructor
        · rw [Finset.sum_insert hj, Section5.scalarProduct_add_right,
            Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
            hWorth i j hij, hleft]
          simp
        · rw [Finset.sum_insert hj, Section1.scalarProduct_add_left,
            Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
            hWorth j i hij.symm, hright]
          simp
  have hnormSum (U : Finset I) :
      Section5.cfNormSq (∑ i ∈ U, dcoeff i • W i) =
        ∑ i ∈ U, Complex.normSq (dcoeff i) *
          (((Nat.card (H i) : ℝ) - 1) /
            ((H i).relIndex (L i) : ℝ)) := by
    induction U using Finset.induction_on with
    | empty => simp [Section5.cfNormSq, Section1.scalarProduct]
    | @insert i U hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          Section5.cfNormSq_add_eq_add_of_orthogonal
            (htermSumOrth i U hi).1 (htermSumOrth i U hi).2,
          Section5.cfNormSq_smul, hWnorm i, ih]
  have hXnorm :
      Section5.cfNormSq X =
        ∑ i ∈ calB, Complex.normSq (dcoeff i) *
          (((Nat.card (H i) : ℝ) - 1) /
            ((H i).relIndex (L i) : ℝ)) := by
    simpa [X] using hnormSum calB
  have hXleR : Section5.cfNormSq X ≤ Section5.cfNormSq (r i1) := by
    have hrEq : r i1 = (r i1 - X) + X := by abel
    have hnormEq :
        Section5.cfNormSq (r i1) =
          Section5.cfNormSq (r i1 - X) + Section5.cfNormSq X := by
      calc
        Section5.cfNormSq (r i1) =
            Section5.cfNormSq ((r i1 - X) + X) := congrArg Section5.cfNormSq hrEq
        _ = Section5.cfNormSq (r i1 - X) + Section5.cfNormSq X :=
          Section5.cfNormSq_add_eq_add_of_orthogonal hGammaX hXGamma
    nlinarith [Section5.cfNormSq_nonneg (r i1 - X)]
  have hdcoeffNorm (i : I) (hi : i ∈ calB) :
      1 ≤ Complex.normSq (dcoeff i) := by
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int
        (by simpa [β] using hβvirt i1)
        (by simpa [γ] using hγvirt i) with ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      intro hz0
      apply hdcoeffNonzero i hi
      change Section1.scalarProduct G (β i1) (γ i) = 0
      rw [hz, hz0]
      simp
    have hzsq : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
      rcases lt_or_gt_of_ne hz0 with hzneg | hzpos
      · have hzle : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
        nlinarith
      · have hzge : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
        nlinarith
    change 1 ≤ Complex.normSq (Section1.scalarProduct G (β i1) (γ i))
    rw [hz]
    norm_num [Complex.normSq, pow_two]
    simpa [pow_two] using hzsq
  have hfactorSumLeX :
      (∑ i ∈ calB,
          ((Nat.card (H i) : ℝ) - 1) /
            ((H i).relIndex (L i) : ℝ)) ≤
        Section5.cfNormSq X := by
    rw [hXnorm]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hfactorNonneg :
        0 ≤ ((Nat.card (H i) : ℝ) - 1) /
          ((H i).relIndex (L i) : ℝ) := by
      have hhR : (1 : ℝ) ≤ Nat.card (H i) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hh i).ne')
      have heR : (0 : ℝ) < (H i).relIndex (L i) := by
        exact_mod_cast he i
      exact div_nonneg (by linarith) heR.le
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hdcoeffNorm i hi) hfactorNonneg
  have hfactorSumBound :
      (∑ i ∈ calB,
          ((Nat.card (H i) : ℝ) - 1) /
            ((H i).relIndex (L i) : ℝ)) ≤
        ((H i1).relIndex (L i1) : ℝ) - 1 := by
    linarith [hXleR, (h78b i1).2]
  have hqNonneg (i : I) : 0 ≤ q i := by
    have hhR : (1 : ℝ) ≤ Nat.card (H i) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hh i).ne')
    have heR : (0 : ℝ) < (H i).relIndex (L i) := by
      exact_mod_cast he i
    have hcardR : (0 : ℝ) < Nat.card (H i) := by
      exact_mod_cast hh i
    dsimp [q]
    exact div_nonneg (by linarith) (mul_nonneg heR.le hcardR.le)
  have hqScale (i : I) :
      (Nat.card (H i) : ℝ) * q i =
        ((Nat.card (H i) : ℝ) - 1) /
          ((H i).relIndex (L i) : ℝ) := by
    have hhR : (Nat.card (H i) : ℝ) ≠ 0 := by
      exact_mod_cast (hh i).ne'
    have heR : ((H i).relIndex (L i) : ℝ) ≠ 0 := by
      exact_mod_cast (he i).ne'
    dsimp [q]
    field_simp [hhR, heR]
  have hscaledSum :
      ((Nat.card (H i1) : ℝ) + 2) * sumB ≤
        ((H i1).relIndex (L i1) : ℝ) - 1 := by
    calc
      ((Nat.card (H i1) : ℝ) + 2) * sumB =
          ∑ i ∈ calB, ((Nat.card (H i1) : ℝ) + 2) * q i := by
            dsimp [sumB]
            rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ calB,
          ((Nat.card (H i) : ℝ) - 1) /
            ((H i).relIndex (L i) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi' := Finset.mem_filter.mp hi
        have hne : i ≠ i1 := (Finset.mem_erase.mp hi'.1).1
        have hgapR :
            (Nat.card (H i1) : ℝ) + 2 ≤ Nat.card (H i) := by
          exact_mod_cast hi1gap i hne
        calc
          ((Nat.card (H i1) : ℝ) + 2) * q i ≤
              (Nat.card (H i) : ℝ) * q i :=
            mul_le_mul_of_nonneg_right hgapR (hqNonneg i)
          _ = ((Nat.card (H i) : ℝ) - 1) /
              ((H i).relIndex (L i) : ℝ) := hqScale i
      _ ≤ ((H i1).relIndex (L i1) : ℝ) - 1 := hfactorSumBound
  have hsumB :
      sumB ≤
        (((H i1).relIndex (L i1) : ℝ) - 1) /
          ((Nat.card (H i1) : ℝ) + 2) := by
    have hden : (0 : ℝ) < (Nat.card (H i1) : ℝ) + 2 := by positivity
    apply (le_div_iff₀ hden).2
    simpa [mul_comm] using hscaledSum
  refine ⟨i1, hh i1, he i1, ?_⟩
  simp only [Set.ncard_singleton, Nat.cast_one, sub_self, zero_div]
  have hbase' := hbase
  dsimp [q] at hbase'
  nlinarith

/-- Source-data proof placeholder for the all-Type-I contradiction used in
PF `(12.17)`. -/
public theorem theorem_12_17_all_typeI_contradiction
    {G : Type u} [Group G] [Finite G]
    : theorem_12_17_all_typeI_contradiction_source_data G := by
  classical
  intro hmin hall
  rcases theorem_12_17_exists_representative_system_data
      (G := G) hmin hall with
    ⟨Ms, MF, hRepSystem⟩
  have hReps : Section8.representativeSystemData Ms := hRepSystem.1
  have hReps16 : section16MaximalConjugacyRepresentatives (G := G) Ms := by
    simpa [Section8.representativeSystemData] using hReps
  have hTypeI :
      ∀ M : Subgroup G, M ∈ Ms →
        section16MFSubgroup M (MF M) ∧
          section16TypeI M (MF M) ∧
            Section8.typeIDefinitionData M (MF M) := hRepSystem.2
  have hFrob_of_127 :
      ∀ M : Subgroup G, M ∈ Ms →
          Section7.frobeniusWithKernel M (MF M) := by
    intro M hM
    exact
      theorem_12_17_representative_frobeniusWithKernel
        (G := G) (Ms := Ms) (MF := MF) hRepSystem M hM
  have hNormMF :
      ∀ M : Subgroup G, M ∈ Ms →
        Subgroup.normalizer ((MF M : Subgroup G) : Set G) = M := by
    intro M hM
    exact
      theorem_12_17_representative_normalizer_mf_eq
        (G := G) hmin (Ms := Ms) (MF := MF) hRepSystem M hM
  let I : Type _ := Fin Ms.length
  let L : I → Subgroup G := fun i => Ms.get i
  let H : I → Subgroup G := fun i => MF (Ms.get i)
  have hOdd : Odd (Nat.card G) := hmin.odd_order
  have hCardI : 2 ≤ Fintype.card I := by
    simpa [I] using
      theorem_12_17_representative_system_card_ge_two_source_leaf
        (G := G) hmin (Ms := Ms) (MF := MF) hRepSystem
  have hFrob : ∀ i : I, Section7.frobeniusWithKernel (L i) (H i) := by
    intro i
    have hM : Ms.get i ∈ Ms := List.get_mem _ _
    exact hFrob_of_127 (Ms.get i) hM
  have hTI : ∀ i : I, Section2.IsTISubsetWithNormalizer
      (Section7.puncturedSubgroupSet (H i)) (L i) := by
    intro i
    have hM : Ms.get i ∈ Ms := List.get_mem _ _
    rcases hTypeI (Ms.get i) hM with ⟨hMF, hBGTypeI, hTypeI_data⟩
    rcases hTypeI_data with ⟨U, U1, U0, hF, hCases⟩
    rcases hCases with hTI16 | hCases
    · haveI : IsMinCE G := hmin
      rcases hF with
        ⟨_hsolv, _hodd, hMF_from_typeF, hHgt, _hHlt, _hUne, _hcomp,
          _hU1le, _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrob⟩
      have hHne : (H i).subgroupOf (L i) ≠ ⊥ :=
        theorem_12_17_subgroupOf_ne_bot_of_gt_bot
          (section16MFSubgroup_le hMF_from_typeF) hHgt
      exact
        theorem_12_17_isTISubsetWithNormalizer_puncturedSubgroupSet_of_section16
          (L i) (H i) (hReps16.1 (Ms.get i) hM) hMF_from_typeF hHne hTI16
    ·
      -- prove every `x ∈ H_i#` has `C_G(x) ≤ L_i` by contradiction with
      -- `(12.7)`, then invoke PF `(2.3)` and the Section 8 support facts.
      haveI : IsMinCE G := hmin
      have hTypeI_LH : Section8.typeIDefinitionData (L i) (H i) :=
        ⟨U, U1, U0, hF, Or.inr hCases⟩
      rcases hF with
        ⟨_hsolv, _hodd, hMF_from_typeF, hHgt, _hHlt, _hUne, hcomp,
          _hU1le, _hU1comm, _hU1norm, _hcent, _hU0le, _hexp, _hfrob⟩
      have hHL : H i ≤ L i := section16MFSubgroup_le hMF_from_typeF
      have hHne : H i ≠ (⊥ : Subgroup G) := ne_of_gt hHgt
      have hNorm : Subgroup.normalizer (((H i) : Subgroup G) : Set G) = L i := by
        simpa [L, H] using hNormMF (Ms.get i) hM
      have hFusion :
          ∀ ⦃a b : G⦄,
            a ∈ Section7.puncturedSubgroupSet (H i) →
            b ∈ Section7.puncturedSubgroupSet (H i) →
            Section2.conjugateIn a b →
              Section2.conjugateInSubgroup (L i) a b := by
        rcases section16_typeI_KUData_of_complement
            (G := G) (hReps16.1 (Ms.get i) hM) hMF hBGTypeI hcomp with
          ⟨hKU, hH_eq_sigma⟩
        have hII := theorem_16_II (G := G)
          (hReps16.1 (Ms.get i) hM) hMF hKU (Or.inl rfl)
        have hKernelASet :
            Section7.puncturedSubgroupSet (H i) ⊆ section16ASet (L i) U := by
          intro x hx
          have hxUnion : x ∈ Section8.section8CentralizerUnion (L i) (H i) := by
            refine ⟨x, ⟨hx.1, hx.2⟩, ⟨?_, hx.2⟩⟩
            exact ⟨section16MFSubgroup_le hMF hx.1,
              Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
          exact
            Section8.theorem_8_13_source_centralizerUnion_subset_ASet_of_complement
              (G := G) (M := L i) (D := L i) (H := H i) (U := U)
              (A := Section8.section8CentralizerUnion (L i) (H i))
              le_rfl hMF hH_eq_sigma hcomp rfl hxUnion
        intro a b ha hb hconj
        have hconj16 :
            section16ConjugateInSubgroup (⊤ : Subgroup G) a b := by
          rcases hconj with ⟨g, hg⟩
          exact ⟨g, by simp, by simpa [Section2.conjBy] using hg.symm⟩
        rcases hII.2.2.1 a b (hKernelASet ha) (hKernelASet hb) hconj16 with
          ⟨g, hgL, hgb⟩
        exact ⟨⟨g, hgL⟩, by simpa [Section2.conjBy] using hgb.symm⟩
      have hCent :
          ∀ ⦃a : G⦄,
            a ∈ Section7.puncturedSubgroupSet (H i) →
              Section2.elementCentralizer a ≤ L i := by
        exact theorem_12_17_centralizer_le_of_all_typeI_source_leaf
          hmin hall (L i) (H i) (hReps16.1 (Ms.get i) hM) hMF hBGTypeI
          hTypeI_LH (hFrob i) hNorm
      exact
        theorem_12_17_isTISubsetWithNormalizer_puncturedSubgroupSet_of_centralizer_le
          (L i) (H i) hHL hHne hNorm hFusion hCent
  have hCoprime : ∀ i j : I, i ≠ j → Nat.Coprime (Nat.card (H i)) (Nat.card (H j)) := by
    intro i j hne
    exact
      theorem_12_17_representative_kernel_card_coprime
        (G := G) (Ms := Ms) (MF := MF) hRepSystem i j hne
  have hG0 : ({1} : Set G) = (Set.univ \ ⋃ i : I,     Section2.conjugateSet (Section7.puncturedSubgroupSet (H i))) := by
    simpa [I, L, H] using
      theorem_12_17_conjugate_kernel_cover_source_leaf
        (G := G) hmin hall hRepSystem (by simpa [I, L, H] using hTI)
  have hLB : Section7.theorem_7_10_lowerBoundData L H ({1} : Set G) := by
    exact theorem_12_17_lowerBoundData_source_leaf
      (G := G) (I := I) L H hmin hCardI
        (fun i => hReps16.1 (Ms.get i) (List.get_mem Ms i))
        (fun i => (hTypeI (L i) (List.get_mem Ms i)).1)
        (fun i => (hTypeI (L i) (List.get_mem Ms i)).2.2)
        hFrob hTI hCoprime hG0
  exact (Section7.theorem_7_11 (G := G) L H)
    ⟨hOdd, hCardI, hFrob, hTI, hCoprime, hG0⟩ hLB

end CFSG.Section12
