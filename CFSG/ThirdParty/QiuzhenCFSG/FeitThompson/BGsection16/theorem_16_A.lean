module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 16 a from BG Section 16 -/

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Theorem A(1): uniqueness of `M_sigma` as a normal Hall `sigma(M)`-subgroup of `M`
and the fact that it is also a Hall `sigma(M)`-subgroup of `G`. -/
@[expose] public def CFSG.section16TheoremA1 (M : Subgroup G) : Prop :=
  section10NormalIn (section10Msigma M) M ∧
    section12HallSubgroupIn (section10SigmaPrimes M) (section10Msigma M) M ∧
      (∀ S : Subgroup G,
        section10NormalIn S M →
          section12HallSubgroupIn (section10SigmaPrimes M) S M →
            S = section10Msigma M) ∧
        IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M)

/-- Theorem A: the eight structural assertions for a maximal subgroup `M`. -/
@[expose] public def CFSG.section16TheoremAConclusions
    (M MF K U : Subgroup G) : Prop :=
  section16TheoremA1 M ∧
    IsCyclic K ∧ section12HallSubgroupIn (section16KappaPrimes M) K M ∧
    K ≤ Subgroup.normalizer (U : Set G) ∧
    section12ComplementIn M (section16KMsigma M K) U ∧
    section10NormalIn (U ⊔ section10Msigma M) M ∧
    M = K ⊔ U ⊔ section10Msigma M ∧
    section10NormalIn U (U ⊔ K) ∧
    (∀ k : G, k ∈ K → k ≠ 1 → elementCentralizerIn U k = ⊥) ∧
    section16Kstar M K ≠ ⊥ ∧
    (K ≠ ⊥ →
      ∀ k : G, k ∈ K → k ≠ 1 →
        elementCentralizerIn M k = section16ZSubgroup K (section16Kstar M K) ∧
          section12InternalDirectProduct K (section16Kstar M K) (elementCentralizerIn M k)) ∧
    ⊥ < MF ∧ MF ≤ section10Msigma M ∧
    section10Msigma M ≤ ambientDerivedSubgroup M ∧ ambientDerivedSubgroup M < M ∧
    section10QuotientNilpotent (ambientDerivedSubgroup M) MF ∧
    section16SecondDerivedSubgroup M ≤ section8FittingSubgroup M ∧
    section8FittingSubgroup M = subgroupCentralizerIn M MF ⊔ MF ∧
    (K ≠ ⊥ → section8FittingSubgroup M ≤ ambientDerivedSubgroup M) ∧
    (MF ≠ section10Msigma M →
      U = ⊥ ∧ section16TISubset (section8FittingSubgroup M : Set G) ∧
        section16HasPrimeOrder K)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_msigma_le (M : Subgroup G) :
    section10Msigma M ≤ M := by
  rw [section10_msigma_eq_piCoreIn]
  exact piCoreIn_le (section10SigmaPrimes M) M

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_msigma_subgroupOf_eq {M : Subgroup G} :
    (section10Msigma M).subgroupOf M = section10MsigmaSubgroup M := by
  change (piCoreIn (section10SigmaPrimes M) M).subgroupOf M =
    piCore (section10SigmaPrimes M) M
  exact piCore_map_subtype_subgroupOf (G := G) (section10SigmaPrimes M) M

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_subgroupCentralizerIn_bot (H : Subgroup G) :
    subgroupCentralizerIn H (⊥ : Subgroup G) = H := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    change x ∈ Subgroup.centralizer (((⊥ : Subgroup G) : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy_one : y = 1 := by simpa using hy
    subst hy_one
    simp

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_mf_to_section15
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF) :
    section15MFSubgroup M MF := by
  simpa [section16MFSubgroup, section15MFSubgroup,
    section16NilpotentNormalHallIn, section15NilpotentNormalHallIn] using hMF

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_KUData_of_section15
    {M K U : Subgroup G}
    (hKU : section15KUData M K U) :
    section16KUData M K U := by
  simpa [section16KUData] using hKU

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_kudata_to_section15
    {M K U : Subgroup G}
    (hKU : section16KUData M K U) :
    section15KUData M K U := by
  simpa [section16KUData] using hKU

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_U_normal_in_UK_of_section15
    {M K U : Subgroup G}
    (hKU : section15KUData M K U) :
    section10NormalIn U (U ⊔ K) := by
  rw [sup_comm]
  exact hKU.2.2.2.2.2.2

omit [IsMinCE G] in
public theorem CFSG.section16_MFamilyP_of_nontrivial_hall_kappa
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKne : K ≠ ⊥) :
    M ∈ section14MFamilyP G := by
  classical
  rcases hK with ⟨hKM, hKHall⟩
  have hK_card_ne_one : Nat.card K ≠ 1 := by
    intro hcard
    exact hKne ((Subgroup.card_eq_one (H := K)).1 hcard)
  obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hK_card_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hcard_sub : Nat.card (K.subgroupOf M) = Nat.card K := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hKM).toEquiv
  have hq_sub : q.val ∣ Nat.card (K.subgroupOf M) := by
    simpa [q, hcard_sub] using hq0dvd
  exact ⟨hM, ⟨q, hKHall.p_in_pi_of_p_dvd_card q hq_sub⟩⟩


omit [IsMinCE G] in
public theorem CFSG.section16_K_ne_bot_of_MFamilyP
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    K ≠ ⊥ := by
  classical
  intro hbot
  rcases hM.2 with ⟨p, hpκ⟩
  rcases hK with ⟨hKM, hHallK⟩
  have hpM : p ∈ subgroupPrimeSet M := by
    rcases hpκ.2 with ⟨P, hPprime, _hCP⟩
    rcases hPprime with ⟨hPM, hPcard⟩
    have hpP : p.val ∣ Nat.card P := by rw [hPcard]
    exact hpP.trans (Subgroup.card_dvd_of_le hPM)
  have hHallBot :
      IsHallSubgroup (section14KappaPrimes M) ((⊥ : Subgroup G).subgroupOf M) := by
    simpa [hbot] using hHallK
  have hpindex : p.val ∣ ((⊥ : Subgroup G).subgroupOf M).index := by
    simpa [subgroupPrimeSet, Subgroup.bot_subgroupOf, Subgroup.index_bot] using hpM
  exact (hHallBot.p_in_pi_of_p_dvd_index p hpindex) hpκ

private theorem CFSG.section16_theoremA1_of_maximal
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    section16TheoremA1 M := by
  classical
  have hσM : section10Msigma M ≤ M := section16_msigma_le (G := G) M
  have hσNormal : section10NormalIn (section10Msigma M) M :=
    section10_normalIn_of_le_normalizer hσM
      (section10_le_normalizer_msigma (G := G) (M := M))
  have hσHallIn :
      section12HallSubgroupIn (section10SigmaPrimes M) (section10Msigma M) M := by
    refine ⟨hσM, ?_⟩
    simpa [section16_msigma_subgroupOf_eq (G := G) (M := M)] using
      (theorem_10_2_b (G := G) hM).2
  refine ⟨hσNormal, hσHallIn, ?_, (theorem_10_2_b (G := G) hM).1⟩
  intro S hSNormal hSHall
  rcases hSNormal with ⟨hSM, hSNormalM⟩
  rcases hSHall with ⟨_hSM', hSHallM⟩
  have hlocal :
      (section10Msigma M).subgroupOf M = S.subgroupOf M := by
    letI : (S.subgroupOf M).Normal := hSNormalM
    exact hSHallM.eq_of_normal hσHallIn.2
  apply le_antisymm
  · intro x hxS
    have hxM : x ∈ M := hSM hxS
    have hxLocal : (⟨x, hxM⟩ : M) ∈ S.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxS
    have hxSigmaLocal :
        (⟨x, hxM⟩ : M) ∈ (section10Msigma M).subgroupOf M := by
      simpa [hlocal] using hxLocal
    simpa [Subgroup.mem_subgroupOf] using hxSigmaLocal
  · intro x hxSigma
    have hxM : x ∈ M := hσM hxSigma
    have hxLocal :
        (⟨x, hxM⟩ : M) ∈ (section10Msigma M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxSigma
    have hxSLocal : (⟨x, hxM⟩ : M) ∈ S.subgroupOf M := by
      simpa [hlocal] using hxLocal
    simpa [Subgroup.mem_subgroupOf] using hxSLocal

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_section14TI_to_section16TISubset
    {H : Subgroup G}
    (hTI : section14TISubgroup H) :
    section16TISubset (H : Set G) := by
  classical
  intro g
  by_cases hg : g ∈ Subgroup.normalizer (H : Set G)
  · left
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyH, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).1 hyH
    · intro hx
      have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normalizer (H : Set G)).inv_mem hg
      have hyH : g⁻¹ * x * g ∈ H := by
        simpa using (Subgroup.mem_normalizer_iff.mp hginv x).1 hx
      exact ⟨g⁻¹ * x * g, hyH, by simp [mul_assoc]⟩
  · right
    have hginv : g⁻¹ ∉ Subgroup.normalizer (H : Set G) := by
      intro hginv
      exact hg (by simpa using
        (Subgroup.normalizer (H : Set G)).inv_mem hginv)
    intro x hx
    have hx14 : x ∈ (H : Set G) ∩ section14SetConjBy (H : Set G) g⁻¹ := by
      constructor
      · exact hx.1
      · rcases hx.2 with ⟨y, hyH, hxy⟩
        exact ⟨y, hyH, by simpa [section14SetConjBy] using hxy⟩
    exact hTI.2.2.2 g⁻¹ hginv hx14

private theorem CFSG.section16_fitting_section14TI_of_proper
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hMFne : MF ≠ section10Msigma M) :
    section14TISubgroup (section8FittingSubgroup M) := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  have hchain := theorem_15_2_chain (G := G) (M := M) (MF := MF) hM hMF
  have h155b := corollary_15_5_b (G := G) (M := M) (MF := MF) hM hMF
  have hMFleF : MF ≤ F := by
    change MF ≤ section8FittingSubgroup M
    rw [h155b.2.1]
    exact le_sup_right
  have hFne : F ≠ ⊥ := by
    intro hFbot
    have hMFbot : MF = ⊥ := le_bot_iff.mp (by
      simpa [F, hFbot] using hMFleF)
    exact (ne_of_gt hchain.1) hMFbot
  have hFproper : F ≠ ⊤ := by
    intro hFtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [F, hFtop] using (section8FittingSubgroup_le M)
    exact hM.1 (top_le_iff.mp htop_le_M)
  refine ⟨hFne, hFproper, ?_⟩
  by_contra hnotTISet
  have hnotTISubgroup : ¬ section14TISubgroup F := by
    intro hTI
    exact hnotTISet hTI.2.2
  have hnonempty : (F : Set G).Nonempty := ⟨1, F.one_mem⟩
  have hnotForall :
      ¬ ∀ g : G, g ∉ Subgroup.normalizer (F : Set G) →
        (F : Set G) ∩ section14SetConjBy (F : Set G) g ⊆ ({1} : Set G) := by
    intro hall
    exact hnotTISet ⟨hnonempty, hall⟩
  push Not at hnotForall
  rcases hnotForall with ⟨a, haNotNorm, haNotSubset⟩
  rcases Set.not_subset.mp haNotSubset with ⟨x, hx, hxnotone⟩
  have hxne : x ≠ 1 := by
    intro hxone
    exact hxnotone (by simp [hxone])
  let g : G := a⁻¹
  let X : Subgroup G := F ⊓ F.conjBy g
  have hxConj : x ∈ F.conjBy g := by
    rcases hx.2 with ⟨y, hyF, hxy⟩
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨y, hyF, ?_⟩
    simpa [g, section14SetConjBy] using hxy.symm
  have hxX : x ∈ X := ⟨hx.1, hxConj⟩
  have hXne : X ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨x, hxX⟩, ?_⟩
    intro hxsub
    exact hxne (by simpa [X] using congrArg Subtype.val hxsub)
  have hgM : g ∉ M := by
    intro hgM
    have hMnormF : M ≤ Subgroup.normalizer (F : Set G) := by
      simpa [F] using section10_le_normalizer_fitting (G := G) M
    have hginvNorm : a⁻¹ ∈ Subgroup.normalizer (F : Set G) := hMnormF hgM
    exact haNotNorm (by simpa using
      (Subgroup.normalizer (F : Set G)).inv_mem hginvNorm)
  have hbotπ :
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ (⊥ : Subgroup G) := by
    intro q hq
    exact False.elim (q.property.not_dvd_one (by simpa using hq))
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := ⊥) hM bot_le hbotπ with
    ⟨E, E₁₂, E₁, E₂, E₃, hE, _hbotE⟩
  have h157 := theorem_15_7_a
    (G := G) (M := M) (MF := MF) (X := X) (E := E)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g)
    hM hMF hnotTISubgroup hgM (by rfl) hXne hE
  exact hMFne h157.2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_complement_eq_bot_of_left_eq
    {M A U : Subgroup G}
    (hcomp : section12ComplementIn M A U)
    (hM : M = A) :
    U = ⊥ := by
  rcases hcomp with ⟨_hAM, hUM, _hprod, hdisj⟩
  apply le_antisymm
  · intro u hu
    have huM : u ∈ M := hUM hu
    have huA : u ∈ A := by simpa [hM] using huM
    have huInf : u ∈ A ⊓ U := ⟨huA, hu⟩
    simpa [hdisj.eq_bot] using huInf
  · exact bot_le

private theorem CFSG.section16_MFamilyP1_hall_kappa_sup_msigma_eq
    {M K : Subgroup G}
    (hP1 : M ∈ section14MFamilyP1 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    M = K ⊔ section10Msigma M := by
  classical
  rcases hK with ⟨hKM, hHallK⟩
  have hKHall :
      section12HallSubgroupIn (section10SigmaPrimes M)ᶜ K M := by
    refine ⟨hKM, ?_⟩
    refine isHallSubgroup_of (G := M) (section10SigmaPrimes M)ᶜ
      (K.subgroupOf M) ?_ ?_
    · intro p hpKsub
      have hpκ : p ∈ section14KappaPrimes M :=
        hHallK.p_in_pi_of_p_dvd_card p hpKsub
      have hpκ' : p ∈ subgroupPrimeSet M \ section10SigmaPrimes M := by
        simpa [hP1.2] using hpκ
      exact hpκ'.2
    · intro p hpσc hpidx
      have hpM : p ∈ subgroupPrimeSet M := by
        rw [subgroupPrimeSet]
        exact hpidx.trans (Subgroup.index_dvd_card (H := K.subgroupOf M))
      have hpκ : p ∈ section14KappaPrimes M := by
        rw [hP1.2]
        exact ⟨hpM, hpσc⟩
      exact (hHallK.p_in_pi_of_p_dvd_index p hpidx) hpκ
  have hσHall :
      IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b (G := G) hP1.1.1).2
  have hcomp :
      (section10MsigmaSubgroup M).IsComplement' (K.subgroupOf M) :=
    section11_isComplement_of_isHall_compl hσHall hKHall.2
  have htop_map : (⊤ : Subgroup M).map M.subtype = M := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
  calc
    M = (⊤ : Subgroup M).map M.subtype := htop_map.symm
    _ = (section10MsigmaSubgroup M ⊔ K.subgroupOf M).map M.subtype := by
      rw [hcomp.sup_eq_top]
    _ = section10Msigma M ⊔ K := by
      rw [Subgroup.map_sup]
      have hσmap :
          (section10MsigmaSubgroup M).map M.subtype = section10Msigma M := by
        simp [section10Msigma]
      have hKmap : (K.subgroupOf M).map M.subtype = K := by
        simpa using
          (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := K) (K := M) hKM)
      rw [hσmap, hKmap]
    _ = K ⊔ section10Msigma M := by rw [sup_comm]

public theorem CFSG.section16_complement_k_msigma_of_KUData
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section12ComplementIn M (K ⊔ section10Msigma M) U := by
  classical
  let S : Subgroup G := section10Msigma M
  rcases hKU with ⟨hKHall, hKcomp, hScomp, hUHall, _hReg, _hUMnorm, _hUnorm⟩
  have hKSleM : K ⊔ S ≤ M := sup_le hKHall.1 hScomp.1
  refine ⟨hKSleM, hUHall.1, ?_, ?_⟩
  · have hprod : M = S ⊔ (K ⊔ U) := hScomp.2.2.1
    simpa [S, sup_assoc, sup_comm, sup_left_comm] using hprod
  · rw [Subgroup.disjoint_def]
    intro x hxKS hxU
    have hxM : x ∈ M := hUHall.1 hxU
    let SK : Subgroup G := S ⊔ K
    have hSNormSK : (S.subgroupOf SK).Normal := by
      have hM_norm_S : M ≤ Subgroup.normalizer (S : Set G) := by
        simpa [S] using section10_le_normalizer_msigma (G := G) (M := M)
      have hSK_norm_S : SK ≤ Subgroup.normalizer (S : Set G) := by
        exact sup_le (hScomp.1.trans hM_norm_S) (hKHall.1.trans hM_norm_S)
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := S) (K := SK) le_sup_left).2 hSK_norm_S
    let xSK : SK := ⟨x, by simpa [SK, S, sup_comm] using hxKS⟩
    have hxTop : xSK ∈ S.subgroupOf SK ⊔ K.subgroupOf SK := by
      have htop :
          S.subgroupOf SK ⊔ K.subgroupOf SK = ⊤ := by
        calc
          S.subgroupOf SK ⊔ K.subgroupOf SK =
              (S ⊔ K).subgroupOf SK := by
                symm
                exact Subgroup.subgroupOf_sup
                  (A := S) (A' := K) (B := SK) le_sup_left le_sup_right
          _ = ⊤ := by
                apply Subgroup.subgroupOf_eq_top.mpr
                intro y hySK
                simpa [SK] using hySK
      rw [htop]
      exact trivial
    letI : (S.subgroupOf SK).Normal := hSNormSK
    rcases (Subgroup.mem_sup_of_normal_left
        (s := S.subgroupOf SK) (t := K.subgroupOf SK) (x := xSK)).1 hxTop with
      ⟨sSK, hsS, kSK, hkK, hsk⟩
    let s : G := sSK
    let k : G := kSK
    have hsS' : s ∈ S := by
      simpa [s, Subgroup.mem_subgroupOf] using hsS
    have hkK' : k ∈ K := by
      simpa [k, Subgroup.mem_subgroupOf] using hkK
    have hskG : s * k = x := by
      simpa [s, k, xSK] using congrArg (fun y : SK => (y : G)) hsk
    have hkSU : k ∈ S ⊔ U := by
      have hk_eq : k = s⁻¹ * x := by
        rw [← hskG]
        simp
      rw [hk_eq]
      exact (S ⊔ U).mul_mem (Subgroup.mem_sup_left (S.inv_mem hsS'))
        (Subgroup.mem_sup_right hxU)
    have hkBot : k ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hKcomp.2.2.2 hkK'
        (by simpa [S, sup_comm] using hkSU)
    have hkone : k = 1 := by simpa using hkBot
    have hxS : x ∈ S := by
      have hx_eq_s : x = s := by
        simpa [hkone] using hskG.symm
      simpa [hx_eq_s] using hsS'
    have hxSsub : (⟨x, hxM⟩ : M) ∈ S.subgroupOf M := by
      simpa [S, Subgroup.mem_subgroupOf] using hxS
    have hxUsub : (⟨x, hxM⟩ : M) ∈ U.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hxU
    have hSHall :
        IsHallSubgroup (section10SigmaPrimes M) (S.subgroupOf M) := by
      simpa [S, section16_msigma_subgroupOf_eq (G := G) (M := M)] using
        (theorem_10_2_b (G := G) hM).2
    have hπdisj :
        Disjoint (section10SigmaPrimes M)
          ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
      rw [Set.disjoint_left]
      intro p hpσ hpcompl
      exact hpcompl (Or.inr hpσ)
    have hSUdisj : Disjoint (S.subgroupOf M) (U.subgroupOf M) :=
      section10_disjoint_of_hall_disjoint_primes hSHall hUHall.2 hπdisj
    have hxbotSub : (⟨x, hxM⟩ : M) ∈ (⊥ : Subgroup M) :=
      Subgroup.disjoint_def.mp hSUdisj hxSsub hxUsub
    have hxone : x = 1 := by
      have hxoneSub : (⟨x, hxM⟩ : M) = 1 := by
        simpa using hxbotSub
      simpa using congrArg Subtype.val hxoneSub
    simp [hxone]

private theorem CFSG.section16_U_eq_bot_of_MFamilyP1
    {M K U : Subgroup G}
    (hKU : section15KUData M K U)
    (hP1 : M ∈ section14MFamilyP1 G) :
    U = ⊥ := by
  classical
  have hM : M = K ⊔ section10Msigma M :=
    section16_MFamilyP1_hall_kappa_sup_msigma_eq (G := G) hP1 hKU.1
  exact section16_complement_eq_bot_of_left_eq (G := G)
    (section16_complement_k_msigma_of_KUData (G := G) hP1.1.1 hKU) hM

public theorem CFSG.section16_MFamilyP2_of_nontrivial_U
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥)
    (hUne : U ≠ ⊥) :
    M ∈ section14MFamilyP2 G := by
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU.1 hKne
  refine ⟨hMP, ?_⟩
  intro hκeq
  exact hUne (section16_U_eq_bot_of_MFamilyP1 (G := G) hKU ⟨hMP, hκeq⟩)

public theorem CFSG.section16_proper_branch_of_section15
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U) :
    MF ≠ section10Msigma M →
      U = ⊥ ∧ section16TISubset (section8FittingSubgroup M : Set G) ∧
        section16HasPrimeOrder K := by
  intro hMFne
  have hKHall : section12HallSubgroupIn (section14KappaPrimes M) K M := hKU.1
  have hP1 := theorem_15_2_a (G := G) (M := M) (MF := MF) (K := K)
    hM hMF hKHall hMFne
  have hUbot : U = ⊥ :=
    section16_U_eq_bot_of_MFamilyP1 (G := G) hKU hP1.1
  rcases theorem_15_2_b (G := G) (M := M) (MF := MF) (K := K)
      hM hMF hKHall hMFne with
    ⟨p, _q, hpK, _hqKstar, _hqmem⟩
  have hPrimeK : section16HasPrimeOrder K := ⟨p, hpK.symm⟩
  have hTI14 : section14TISubgroup (section8FittingSubgroup M) :=
    section16_fitting_section14TI_of_proper (G := G) hM hMF hMFne
  exact ⟨hUbot, section16_section14TI_to_section16TISubset (G := G) hTI14,
    hPrimeK⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_hasPrimeOrder_of_prime_card
    {K : Subgroup G}
    (hprime : Nat.Prime (Nat.card K)) :
    section16HasPrimeOrder K :=
  ⟨⟨Nat.card K, hprime⟩, rfl⟩

public theorem CFSG.section16_MF_eq_msigma_of_U_ne_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U)
    (hUne : U ≠ ⊥) :
    MF = section10Msigma M := by
  by_contra hMFne
  exact hUne ((section16_proper_branch_of_section15 (G := G) hM hMF hKU hMFne).1)

public theorem CFSG.section16_msigma_le_fitting_of_MF_eq_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hEq : MF = section10Msigma M) :
    section10Msigma M ≤ section8FittingSubgroup M := by
  have h155b := corollary_15_5_b (G := G) (M := M) (MF := MF) hM hMF
  rw [h155b.2.1, ← hEq]
  exact le_sup_right

private theorem CFSG.section16_fitting_section14TI_of_nontrivial_U
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥)
    (hUne : U ≠ ⊥) :
    section14TISubgroup (section8FittingSubgroup M) := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  have hchain := theorem_15_2_chain (G := G) (M := M) (MF := MF) hM hMF
  have h155b := corollary_15_5_b (G := G) (M := M) (MF := MF) hM hMF
  have hMFleF : MF ≤ F := by
    change MF ≤ section8FittingSubgroup M
    rw [h155b.2.1]
    exact le_sup_right
  have hFne : F ≠ ⊥ := by
    intro hFbot
    have hMFbot : MF = ⊥ := le_bot_iff.mp (by
      simpa [F, hFbot] using hMFleF)
    exact (ne_of_gt hchain.1) hMFbot
  have hFproper : F ≠ ⊤ := by
    intro hFtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [F, hFtop] using (section8FittingSubgroup_le M)
    exact hM.1 (top_le_iff.mp htop_le_M)
  refine ⟨hFne, hFproper, ?_⟩
  by_contra hnotTISet
  have hnotTISubgroup : ¬ section14TISubgroup F := by
    intro hTI
    exact hnotTISet hTI.2.2
  have hnonempty : (F : Set G).Nonempty := ⟨1, F.one_mem⟩
  have hnotForall :
      ¬ ∀ g : G, g ∉ Subgroup.normalizer (F : Set G) →
        (F : Set G) ∩ section14SetConjBy (F : Set G) g ⊆ ({1} : Set G) := by
    intro hall
    exact hnotTISet ⟨hnonempty, hall⟩
  push Not at hnotForall
  rcases hnotForall with ⟨a, haNotNorm, haNotSubset⟩
  rcases Set.not_subset.mp haNotSubset with ⟨x, hx, hxnotone⟩
  have hxne : x ≠ 1 := by
    intro hxone
    exact hxnotone (by simp [hxone])
  let g : G := a⁻¹
  let X : Subgroup G := F ⊓ F.conjBy g
  have hxConj : x ∈ F.conjBy g := by
    rcases hx.2 with ⟨y, hyF, hxy⟩
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨y, hyF, ?_⟩
    simpa [g, section14SetConjBy] using hxy.symm
  have hxX : x ∈ X := ⟨hx.1, hxConj⟩
  have hXne : X ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨x, hxX⟩, ?_⟩
    intro hxsub
    exact hxne (by simpa [X] using congrArg Subtype.val hxsub)
  have hgM : g ∉ M := by
    intro hgM
    have hMnormF : M ≤ Subgroup.normalizer (F : Set G) := by
      simpa [F] using section10_le_normalizer_fitting (G := G) M
    have hginvNorm : a⁻¹ ∈ Subgroup.normalizer (F : Set G) := hMnormF hgM
    exact haNotNorm (by simpa using
      (Subgroup.normalizer (F : Set G)).inv_mem hginvNorm)
  have hbotπ :
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ (⊥ : Subgroup G) := by
    intro q hq
    exact False.elim (q.property.not_dvd_one (by simpa using hq))
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := ⊥) hM bot_le hbotπ with
    ⟨E, E₁₂, E₁, E₂, E₃, hE, _hbotE⟩
  have h157 := theorem_15_7_a
    (G := G) (M := M) (MF := MF) (X := X) (E := E)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g)
    hM hMF hnotTISubgroup hgM (by rfl) hXne hE
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU.1 hKne
  have hnotF : M ∉ section14MFamilyF G := by
    intro hF
    rcases hMP.2 with ⟨p, hp⟩
    simp [hF.2] at hp
  rcases h157.1 with hF | hP1
  · exact hnotF hF
  · exact hUne (section16_U_eq_bot_of_MFamilyP1 (G := G) hKU hP1)

private theorem CFSG.section16_msigma_le_fitting_of_U_ne_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U)
    (hUne : U ≠ ⊥) :
    section10Msigma M ≤ section8FittingSubgroup M := by
  have hEq : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_U_ne_bot (G := G) hM hMF hKU hUne
  exact section16_msigma_le_fitting_of_MF_eq_msigma (G := G) hM hMF hEq

public theorem CFSG.section16_fitting_TI_prime_order_of_U_ne_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    U ≠ ⊥ →
      section16HasPrimeOrder K ∧
        section16TISubset (section8FittingSubgroup M : Set G) ∧
          section10Msigma M ≤ section8FittingSubgroup M := by
  intro hUne
  have hP2 : M ∈ section14MFamilyP2 G :=
    section16_MFamilyP2_of_nontrivial_U (G := G) hM hKU hKne hUne
  have h142g := proposition_14_2_g (G := G) (M := M) (K := K) hP2 hKU.1
  have hTI14 : section14TISubgroup (section8FittingSubgroup M) :=
    section16_fitting_section14TI_of_nontrivial_U (G := G) hM hMF hKU hKne hUne
  exact ⟨section16_hasPrimeOrder_of_prime_card (G := G) h142g.2.1,
    section16_section14TI_to_section16TISubset (G := G) hTI14,
    section16_msigma_le_fitting_of_U_ne_bot (G := G) hM hMF hKU hUne⟩

public theorem CFSG.section16_ambientDerived_hallSubgroup_of_caseP
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    section16HallSubgroupOf (ambientDerivedSubgroup M) M := by
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU.1 hKne
  exact ⟨section10_ambientDerivedSubgroup_le_base,
    section15_ambientDerived_hallSubgroup_of_MFamilyP (G := G) hMP hKU.1⟩

public theorem CFSG.section16_complementIn_ambientDerived_of_caseP2
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥)
    (hUne : U ≠ ⊥) :
    section12ComplementIn (ambientDerivedSubgroup M) MF U := by
  have hD_eq : ambientDerivedSubgroup M = U ⊔ section10Msigma M :=
    (lemma_15_1_b (G := G) (M := M) (K := K) (U := U) hM hKU hKne).1
  have hMF_eq : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_U_ne_bot (G := G) hM hMF hKU hUne
  have hcompSigma : section12ComplementIn M (section10Msigma M) (K ⊔ U) :=
    hKU.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hMF_eq, hD_eq]
    exact le_sup_right
  · rw [hD_eq]
    exact le_sup_left
  · rw [hMF_eq, hD_eq, sup_comm]
  · rw [hMF_eq]
    exact hcompSigma.2.2.2.mono_right le_sup_right

public theorem CFSG.section16_typeIIToIVExtra_of_caseP2
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥)
    (hUne : U ≠ ⊥) :
    section16TypeIIToIVExtra M K := by
  have hExtra :=
    section16_fitting_TI_prime_order_of_U_ne_bot (G := G) hM hMF hKU hKne hUne
  exact ⟨hExtra.1, hExtra.2.1⟩

public theorem CFSG.section16_theoremAConclusions_of_section15
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U) :
    section16TheoremAConclusions M MF K U := by
  classical
  have hKU' : section15KUData M K U := hKU
  rcases hKU with ⟨hKHall, _hCompK, _hCompMsigma, _hUHall, hReg, _hUMsigmaNormal,
    _hUNormal⟩
  have h151a := lemma_15_1_a (G := G) (M := M) (K := K) (U := U) hM
    hKU'
  rcases h151a with ⟨hUMsigmaNormal, hProduct, hKcyclic, hMsigmaDerived,
    _hQuotAbel⟩
  have hKHall16 :
      section12HallSubgroupIn (section16KappaPrimes M) K M := by
    simpa [section16KappaPrimes] using hKHall
  have hCompKM16 : section12ComplementIn M (section16KMsigma M K) U := by
    simpa [section16KMsigma] using
      section16_complement_k_msigma_of_KUData (G := G) hM hKU'
  have hUnormalUK : section10NormalIn U (U ⊔ K) :=
    section16_U_normal_in_UK_of_section15 (G := G) hKU'
  have hKstarNe : section16Kstar M K ≠ ⊥ := by
    by_cases hKbot : K = ⊥
    · have hMsigma_ne : section10Msigma M ≠ ⊥ := theorem_10_2_e (G := G) hM
      simpa [section16Kstar, hKbot, section16_subgroupCentralizerIn_bot] using hMsigma_ne
    · have hMP : M ∈ section14MFamilyP G :=
        section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKHall hKbot
      simpa [section16Kstar, section14KStar] using
        (proposition_14_2_c (G := G) (M := M) (K := K) hMP hKHall).1
  have hCentralizers :
      K ≠ ⊥ →
        ∀ k : G, k ∈ K → k ≠ 1 →
          elementCentralizerIn M k = section16ZSubgroup K (section16Kstar M K) ∧
            section12InternalDirectProduct K (section16Kstar M K)
              (elementCentralizerIn M k) := by
    intro hKne k hkK hkne
    have hMP : M ∈ section14MFamilyP G :=
      section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKHall hKne
    have hKstar_ne : section14KStar M K ≠ ⊥ :=
      (proposition_14_2_c (G := G) (M := M) (K := K) hMP hKHall).1
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hKstar_ne with ⟨y, hyne⟩
    let yG : G := y
    have hyKstar : yG ∈ section14KStar M K := y.property
    have hyneG : yG ≠ 1 := by
      intro hy
      exact hyne (Subtype.ext hy)
    have h147 := theorem_14_7_d (G := G) (M := M) (K := K) hMP hKHall
    have hkdata := h147.2.2 k yG hkK hkne hyKstar hyneG
    have hcent :
        elementCentralizerIn M k = section16ZSubgroup K (section16Kstar M K) := by
      simpa [section16ZSubgroup, section16Kstar, section14Z, section14KStar]
        using hkdata.2.1
    refine ⟨hcent, ?_⟩
    rw [hcent]
    simpa [section16ZSubgroup, section16Kstar, section14ZInternalDirectProduct,
      section14Z, section14KStar] using h147.1
  have hchain := theorem_15_2_chain (G := G) (M := M) (MF := MF) hM hMF
  have h155b := corollary_15_5_b (G := G) (M := M) (MF := MF) hM hMF
  have h155c := corollary_15_5_c (G := G) (M := M) (MF := MF) hM hMF
  have hFittingLeDerived :
      K ≠ ⊥ → section8FittingSubgroup M ≤ ambientDerivedSubgroup M := by
    intro hKne
    exact corollary_15_5_d (G := G) (M := M) (MF := MF) (K := K)
      hM hMF hKHall hKne
  exact ⟨section16_theoremA1_of_maximal (G := G) hM,
    hKcyclic, hKHall16, hReg.1, hCompKM16, hUMsigmaNormal, hProduct,
    hUnormalUK, hReg.2, hKstarNe, hCentralizers, hchain.1,
    hchain.2.1, hchain.2.2.1, hchain.2.2.2, h155c.2,
    by simpa [section16SecondDerivedSubgroup, section15SecondDerivedSubgroup] using h155b.1,
    h155b.2.1, hFittingLeDerived,
    section16_proper_branch_of_section15 (G := G) hM hMF hKU'⟩

/-- Theorem A of Section 16. -/
public theorem CFSG.theorem_16_A
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF) :
    ∃ K U : Subgroup G, section16TheoremAConclusions M MF K U := by
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU⟩
  exact ⟨K, U,
    section16_theoremAConclusions_of_section15 (G := G) hM
      (section16_mf_to_section15 (G := G) hMF) hKU⟩

end MainResults
