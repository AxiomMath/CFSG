module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.lemma_14_6

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 14 7 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section14_7_not_conjugate_and_z_le
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G))) :
    ¬ section14ConjugateSubgroups Mi M ∧ section14Z M K ≤ Mi := by
  rcases hXi with ⟨hXiK, p, hXicard⟩
  have hXiPrime : Xi ∈ section10PrimeOrderSubgroupsIn p K := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXiK, hXicard⟩
  have hpσMi : p ∈ section10SigmaPrimes Mi :=
    section14_b2_prime_mem_sigma_of_primeOrder
      (G := G) (M := M) (K := K) (X := Xi) (Mstar := Mi) (p := p)
      hM hK hXiPrime hMi
  have hpκ : p ∈ section14KappaPrimes M := by
    have hpXi : p.val ∣ Nat.card Xi := by
      rw [hXicard]
    have hXiM : Xi ≤ M := hXiK.trans hK.1
    have hXisub_le_Ksub : Xi.subgroupOf M ≤ K.subgroupOf M := by
      intro x hx
      exact hXiK (by simpa [Subgroup.mem_subgroupOf] using hx)
    have hcardXisub : Nat.card (Xi.subgroupOf M) = Nat.card Xi :=
      section12_card_subgroupOf_eq hXiM
    have hpXisub : p.val ∣ Nat.card (Xi.subgroupOf M) := by
      simpa [hcardXisub] using hpXi
    exact hK.2.p_in_pi_of_p_dvd_card p
      (hpXisub.trans (Subgroup.card_dvd_of_le hXisub_le_Ksub))
  have hnotconj : ¬ section14ConjugateSubgroups Mi M := by
    intro hconj
    rcases hconj with ⟨a, hMa⟩
    have hpσM : p ∈ section10SigmaPrimes M := by
      simpa [hMa, section14_sigmaPrimes_conjBy (G := G) M a] using hpσMi
    exact section14_kappa_subset_not_sigma (M := M) hpκ hpσM
  have hNXZ :=
    proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK Xi ⟨hXiK, ⟨p, hXicard⟩⟩
  have hNXeqZ : subgroupNormalizerIn M (Xi : Set G) = section14Z M K :=
    hNXZ.1.trans hNXZ.2.1
  have hZle_subNX : section14Z M K ≤ subgroupNormalizerIn M (Xi : Set G) := by
    rw [← hNXeqZ]
  have hZleMi : section14Z M K ≤ Mi :=
    hZle_subNX.trans <|
      (subgroupNormalizerIn_le_normalizer M (Xi : Set G)).trans hMi.2
  exact ⟨hnotconj, hZleMi⟩

private theorem CFSG.section14_7_kstar_isPi_sigma_compl
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G))) :
    IsPiSubgroup (G := G) (section10SigmaPrimes Mi)ᶜ (section14KStar M K) := by
  have hstep :=
    section14_7_not_conjugate_and_z_le
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hnotconj : ¬ section14ConjugateSubgroups Mi M := hstep.1
  have hMi_not : section12NotConjugate Mi M := by
    intro a hMa
    exact hnotconj ⟨a⁻¹, by
      simpa [section11_conjBy_inv] using congrArg (fun H => H.conjBy a⁻¹) hMa⟩
  have hσdis : Disjoint (section10SigmaPrimes M) (section10SigmaPrimes Mi) :=
    theorem_13_9 (G := G) hM.1 hMi.1 hMi_not
  intro q hqKstar
  have hqσM : q ∈ section10SigmaPrimes M := by
    obtain ⟨Xstar, hXstar⟩ :=
      section14_exists_primeOrderSubgroupIn_of_dvd_card
        (G := G) (A := section14KStar M K) (p := q) hqKstar
    exact
      section14_c_sigma_of_primeOrder_le_kstar
        (G := G) (M := M) (K := K) (X := Xstar) (p := q) hM hXstar
  rw [Set.mem_compl_iff]
  rw [Set.disjoint_left] at hσdis
  exact fun hqσMi => hσdis hqσM hqσMi

private theorem CFSG.section14_7_kstar_isPi_kappa
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G))) :
    IsPiSubgroup (G := G) (section14KappaPrimes Mi) (section14KStar M K) := by
  have hstep :=
    section14_7_not_conjugate_and_z_le
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hnotconj : ¬ section14ConjugateSubgroups Mi M := hstep.1
  have hZleMi : section14Z M K ≤ Mi := hstep.2
  have hKstarLeMi : section14KStar M K ≤ Mi := le_sup_right.trans hZleMi
  have hXiMsigma : Xi ≤ section10Msigma Mi :=
    proposition_14_2_b2 (G := G) (M := M) (K := K) hM hK Xi hXi Mi hMi
  have hXiNe : Xi ≠ ⊥ := section14_b1_primeOrder_ne_bot (G := G) hXi
  haveI : Nontrivial ↥Xi := (Subgroup.nontrivial_iff_ne_bot (H := Xi)).2 hXiNe
  obtain ⟨x, hxXi, hxne⟩ := Subgroup.exists_ne_one_of_nontrivial Xi
  have hxMi : Mi ∈ section14MsigmaElement x := by
    refine ⟨hMi.1, ?_⟩
    intro y hy
    have hyx : y = x := by simpa using hy
    simpa [hyx] using hXiMsigma hxXi
  intro q hqKstar
  obtain ⟨Xstar, hXstar⟩ :=
    section14_exists_primeOrderSubgroupIn_of_dvd_card
      (G := G) (A := section14KStar M K) (p := q) hqKstar
  have hXstarPrime :
      Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K) :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXstar
  have hXstarNe : Xstar ≠ ⊥ := section14_b1_primeOrder_ne_bot (G := G) hXstarPrime
  haveI : Nontrivial ↥Xstar := (Subgroup.nontrivial_iff_ne_bot (H := Xstar)).2 hXstarNe
  obtain ⟨xstar, hxstarXstar, hxstarne⟩ := Subgroup.exists_ne_one_of_nontrivial Xstar
  have hxstarKstar : xstar ∈ section14KStar M K := hXstar.1 hxstarXstar
  have hXstar_le_zpow : Xstar ≤ Subgroup.zpowers xstar := by
    intro y hyXstar
    haveI : Fact q.val.Prime := ⟨q.2⟩
    have hySub :
        (⟨y, hyXstar⟩ : Xstar) ∈
          Subgroup.zpowers (⟨xstar, hxstarXstar⟩ : Xstar) :=
      mem_zpowers_of_prime_card
        (G := Xstar) (p := q.val) (by simpa using hXstar.2)
        (g := (⟨xstar, hxstarXstar⟩ : Xstar))
        (g' := (⟨y, hyXstar⟩ : Xstar))
        (by simpa using hxstarne)
    rcases Subgroup.mem_zpowers_iff.mp hySub with ⟨n, hn⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
  have hxstarMi : xstar ∈ Mi := hKstarLeMi hxstarKstar
  have hxstarCent : xstar ∈ elementCentralizerIn Mi x := by
    refine ⟨hxstarMi, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr <|
      (Subgroup.mem_centralizer_iff.mp hxstarKstar.2 x (hXi.1 hxXi)).symm
  have hxstarSigma' : section14IsPiElement (section10SigmaPrimes Mi)ᶜ xstar := by
    intro r hrSupp
    have hrKstar : r ∈ subgroupPrimeSet (section14KStar M K) :=
      section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hxstarKstar) hrSupp
    exact
      section14_7_kstar_isPi_sigma_compl
        (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
        r hrKstar
  have hcor :=
    corollary_14_3 (G := G) (M := Mi) (x := x) (x' := xstar) hMi.1
      (hXiMsigma hxXi) hxne hxstarne hxstarCent hxstarSigma'
  rcases hcor with hκ | hτ2
  · have hqSupp : q ∈ section14ElementPrimeSupport xstar := by
      have hqzpow : q ∈ subgroupPrimeSet (Subgroup.zpowers xstar) := by
        rw [subgroupPrimeSet]
        exact
          (show q.val ∣ Nat.card Xstar by rw [hXstar.2]).trans
            (Subgroup.card_dvd_of_le hXstar_le_zpow)
      simpa [section14ElementPrimeSupport] using hqzpow
    exact hκ.1 hqSupp
  · rcases hτ2 with ⟨_hτ2supp, _hlen, huniqCxstar⟩
    have huniqCXstar :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (Xstar : Set G)) = {M} :=
      (proposition_14_2_c (G := G) (M := M) (K := K) hM hK).2
        Xstar hXstarPrime
    have hCXstar_le_M : Subgroup.centralizer (Xstar : Set G) ≤ M := by
      have hMmem :
          M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (Xstar : Set G)) := by
        rw [huniqCXstar]
        simp
      exact hMmem.2
    have hCxstar_le_CXstar :
        Subgroup.centralizer ({xstar} : Set G) ≤ Subgroup.centralizer (Xstar : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro y hyXstar
      have hyzpow : y ∈ Subgroup.zpowers xstar := hXstar_le_zpow hyXstar
      rcases Subgroup.mem_zpowers_iff.mp hyzpow with ⟨n, rfl⟩
      have hxstarg : Commute g xstar :=
        Subgroup.mem_centralizer_singleton_iff.mp hg
      exact (hxstarg.zpow_right n).eq.symm
    have hMmemCxstar :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({xstar} : Set G)) :=
      ⟨hM.1, hCxstar_le_CXstar.trans hCXstar_le_M⟩
    have hMeqMi : M = Mi := by
      have hMmem : M ∈ ({Mi} : Set (Subgroup G)) := by
        simpa [huniqCxstar] using hMmemCxstar
      simpa using hMmem
    exact False.elim <| hnotconj ⟨1, by
      simpa [hMeqMi] using (section8_conjBy_one (G := G) M).symm⟩

private theorem CFSG.section14_7_exists_hall_kappa_containing_kstar
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G))) :
    ∃ Ki : Subgroup G,
      section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki := by
  have hstep :=
    section14_7_not_conjugate_and_z_le
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hKstarLeMi : section14KStar M K ≤ Mi := le_sup_right.trans hstep.2
  have hKstarPi :
      IsPiSubgroup (G := G) (section14KappaPrimes Mi) (section14KStar M K) :=
    section14_7_kstar_isPi_kappa
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  letI : MulDistribMulAction Unit Mi := {
    smul := fun _ y => y
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hKstarSubPi :
      IsPiSubgroup (G := Mi) (section14KappaPrimes Mi)
        ((section14KStar M K).subgroupOf Mi) := by
    intro p hp
    have hcard :
        Nat.card ((section14KStar M K).subgroupOf Mi) = Nat.card (section14KStar M K) :=
      section12_card_subgroupOf_eq hKstarLeMi
    exact hKstarPi p (by simpa [hcard] using hp)
  have hKstarSubInv : IsInvariant Unit Mi ((section14KStar M K).subgroupOf Mi) := by
    refine ⟨?_⟩
    intro _ y
    simp
  have hsolvMi : IsSolvable Mi :=
    IsMinCE.proper_subgroups_solvable Mi (lt_top_iff_ne_top.mpr hMi.1.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card Mi) := by simp
  obtain ⟨Kisub, hKisubHall, _hKisubInv, hKstarSubKi⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := Mi) (A := Unit) hsolvMi hcop (section14KappaPrimes Mi)
      ((section14KStar M K).subgroupOf Mi) hKstarSubPi hKstarSubInv
  let Ki : Subgroup G := Kisub.map Mi.subtype
  have hKi : section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi :=
    section14_hallSubgroupIn_map_subtype hKisubHall
  have hKstarKi : section14KStar M K ≤ Ki := by
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hKstarLeMi hy⟩, hKstarSubKi (show (⟨y, hKstarLeMi hy⟩ : Mi) ∈
        (section14KStar M K).subgroupOf Mi from hy), rfl⟩
  exact ⟨Ki, hKi, hKstarKi⟩

public theorem CFSG.section14_7_exists_initial_overgroup_data
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∃ Xi Mi Ki : Subgroup G,
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K ≤ Mi := by
  classical
  obtain ⟨p, Xi, hXiPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
  have hXi : Xi ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXiPrime
  have hNX_not_le_M : ¬ Subgroup.normalizer (Xi : Set G) ≤ M := by
    intro hNXM
    have hMcontNX : M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) :=
      ⟨hM.1, hNXM⟩
    have hpσM :
        p ∈ section10SigmaPrimes M :=
      section14_b2_prime_mem_sigma_of_primeOrder
        (G := G) (M := M) (K := K) (X := Xi) (Mstar := M) (p := p)
        hM hK hXiPrime hMcontNX
    have hpκ : p ∈ section14KappaPrimes M := by
      have hpXi : p.val ∣ Nat.card Xi := by
        rw [hXiPrime.2]
      have hXiM : Xi ≤ M := hXiPrime.1.trans hK.1
      have hXisub_le_Ksub : Xi.subgroupOf M ≤ K.subgroupOf M := by
        intro x hx
        exact hXiPrime.1 (by simpa [Subgroup.mem_subgroupOf] using hx)
      have hcardXisub : Nat.card (Xi.subgroupOf M) = Nat.card Xi :=
        section12_card_subgroupOf_eq hXiM
      have hpXisub : p.val ∣ Nat.card (Xi.subgroupOf M) := by
        simpa [hcardXisub] using hpXi
      exact hK.2.p_in_pi_of_p_dvd_card p
        (hpXisub.trans (Subgroup.card_dvd_of_le hXisub_le_Ksub))
    exact section14_kappa_subset_not_sigma (M := M) hpκ hpσM
  have hNXne_top : Subgroup.normalizer (Xi : Set G) ≠ ⊤ := by
    have hXine : Xi ≠ ⊥ := section12_primeOrder_ne_bot hXiPrime
    have hXine_top : Xi ≠ ⊤ := by
      intro hXitop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [hXitop] using hXi.1.trans hK.1
      exact hM.1.1 (top_le_iff.mp htop_le_M)
    intro hNtop
    have hXinormal : Xi.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases hXinormal.eq_bot_or_eq_top with hXibot | hXitop
    · exact hXine hXibot
    · exact hXine_top hXitop
  obtain ⟨Mi, hMi⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (Xi : Set G)) hNXne_top
  obtain ⟨Ki, hKi, hKstarKi⟩ :=
    section14_7_exists_hall_kappa_containing_kstar
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hstep :=
    section14_7_not_conjugate_and_z_le
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  exact ⟨Xi, Mi, Ki, hXi, hMi, hKi, hKstarKi, hstep.1, hstep.2⟩

private theorem CFSG.section14_7_overgroup_in_pFamily
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G))) :
    Mi ∈ section14MFamilyP G := by
  obtain ⟨q, Xstar, hXstar⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := section14KStar M K)
      (section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK)
  have hqκ : q ∈ section14KappaPrimes Mi :=
    section14_7_kstar_isPi_kappa
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
      q (by
        simpa [subgroupPrimeSet] using
          (show q.val ∣ Nat.card Xstar by rw [hXstar.2]).trans
            (Subgroup.card_dvd_of_le hXstar.1))
  exact ⟨hMi.1, ⟨q, hqκ⟩⟩

private theorem CFSG.section14_7_z_le_of_kstar_prime
    {M K Xi Mi Ki Xstar : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hKi : section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi)
    (hKstarKi : section14KStar M K ≤ Ki)
    (hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    section14Z M K ≤ section14Z Mi Ki := by
  have hMiP :
      Mi ∈ section14MFamilyP G :=
    section14_7_overgroup_in_pFamily
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi)
      hM hK hXi hMi
  have hZleMi :
      section14Z M K ≤ Mi :=
    (section14_7_not_conjugate_and_z_le
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi).2
  have hXstarKi :
      Xstar ∈ section12PrimeOrderSubgroups Ki := by
    exact ⟨hXstar.1.trans hKstarKi, hXstar.2⟩
  have hNXeqZ :
      subgroupNormalizerIn Mi (Xstar : Set G) = section14Z Mi Ki := by
    have hNXZ :=
      proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi Xstar hXstarKi
    exact hNXZ.1.trans hNXZ.2.1
  have hKi_le_NX : Ki ≤ subgroupNormalizerIn Mi (Xstar : Set G) := by
    intro y hyKi
    rw [hNXeqZ]
    exact Subgroup.mem_sup_left hyKi
  have hZleNX : section14Z M K ≤ subgroupNormalizerIn Mi (Xstar : Set G) := by
    apply sup_le
    · intro x hxK
      refine mem_subgroupNormalizerIn.mpr ?_
      refine ⟨?_, hZleMi (Subgroup.mem_sup_left hxK)⟩
      have hxCent : x ∈ Subgroup.centralizer (Xstar : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hyXstar
        exact
          (Subgroup.mem_centralizer_iff.mp ((hXstar.1 hyXstar).2) x hxK).symm
      exact (centralizer_le_normalizer Xstar) hxCent
    · intro y hyKstar
      exact hKi_le_NX (hKstarKi hyKstar)
  exact hZleNX.trans (by rw [hNXeqZ])

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_7_normalizer_le_normalizer_centralizer
    (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hxn : n⁻¹ * x * n ∈ X := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hn) x).1 hx
    have hcomm : (n⁻¹ * x * n) * c = c * (n⁻¹ * x * n) := hc _ hxn
    have hcomm' := congrArg (fun y : G => n * y * n⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hxn : n * x * n⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hn x).1 hx
    have hcomm :
        (n * x * n⁻¹) * (n * c * n⁻¹) =
          (n * c * n⁻¹) * (n * x * n⁻¹) :=
      hc _ hxn
    have hcomm' := congrArg (fun y : G => n⁻¹ * y * n) hcomm
    simpa [mul_assoc] using hcomm'

public theorem CFSG.section14_7_normalizer_le_of_unique_centralizer_primeOrder
    {M A X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hX : X ∈ section12PrimeOrderSubgroups A)
    (huniq : section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  classical
  have hCX_le_M : Subgroup.centralizer (X : Set G) ≤ M := by
    have hMmem :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      rw [huniq]
      simp
    exact hMmem.2
  have hNCX_ne_top :
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) ≠ ⊤ := by
    intro hNCXtop
    have hCXnormal :
        (Subgroup.centralizer (X : Set G)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNCXtop
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases hCXnormal.eq_bot_or_eq_top with hCXbot | hCXtop
    · have hXne : X ≠ ⊥ := section14_b1_primeOrder_ne_bot (G := G) hX
      haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot (H := X)).2 hXne
      obtain ⟨x, hxX, hxne⟩ := Subgroup.exists_ne_one_of_nontrivial X
      rcases hX with ⟨_hXA, p, hXcard⟩
      have hXle_zpow : X ≤ Subgroup.zpowers x := by
        intro y hyX
        haveI : Fact p.val.Prime := ⟨p.2⟩
        have hySub :
            (⟨y, hyX⟩ : X) ∈ Subgroup.zpowers (⟨x, hxX⟩ : X) :=
          mem_zpowers_of_prime_card
            (G := X) (p := p.val) (by simpa using hXcard)
            (g := (⟨x, hxX⟩ : X)) (g' := (⟨y, hyX⟩ : X))
            (by simpa using hxne)
        rcases Subgroup.mem_zpowers_iff.mp hySub with ⟨n, hn⟩
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
      letI : IsMulCommutative X :=
        section14_isMulCommutative_of_le
          (H := Subgroup.zpowers x) (K := X) (Subgroup.zpowers_isMulCommutative x)
          hXle_zpow
      have hXle_CX : X ≤ Subgroup.centralizer (X : Set G) :=
        Subgroup.le_centralizer X
      have hXbot : X = ⊥ := by
        apply le_bot_iff.mp
        simpa [hCXbot] using hXle_CX
      exact hXne hXbot
    · exact hM.1 (top_le_iff.mp (hCXtop ▸ hCX_le_M))
  have hNCX_le_M :
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) ≤ M := by
    obtain ⟨N, hN⟩ :=
      section9_exists_maximalSubgroupsContaining_of_ne_top
        (G := G) (H := Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G))
        hNCX_ne_top
    have hNcontCX :
        N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      exact ⟨hN.1, Subgroup.le_normalizer.trans hN.2⟩
    have hNeqM : N = M := by
      have hNmem : N ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq] using hNcontCX
      simpa using hNmem
    exact hNeqM ▸ hN.2
  exact
    (section14_7_normalizer_le_normalizer_centralizer (G := G) X).trans hNCX_le_M

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_7_subgroup_le_of_subgroupOf_quotient_map_eq_bot
    {N L C : Subgroup G} [hN : (N.subgroupOf L).Normal]
    (hCL : C ≤ L)
    (hmap : (C.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) = ⊥) :
    C ≤ N := by
  intro x hxC
  have hxsub : (⟨x, hCL hxC⟩ : L) ∈ C.subgroupOf L := by
    simpa [Subgroup.mem_subgroupOf] using hxC
  have hxmap :
      QuotientGroup.mk' (N.subgroupOf L) (⟨x, hCL hxC⟩ : L) ∈
        (C.subgroupOf L).map (QuotientGroup.mk' (N.subgroupOf L)) :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' (N.subgroupOf L)) hxsub
  have hxbot :
      QuotientGroup.mk' (N.subgroupOf L) (⟨x, hCL hxC⟩ : L) = 1 := by
    simpa [hmap] using hxmap
  have hxker : (⟨x, hCL hxC⟩ : L) ∈ (QuotientGroup.mk' (N.subgroupOf L)).ker := by
    simpa [MonoidHom.mem_ker] using hxbot
  have hxNsub : (⟨x, hCL hxC⟩ : L) ∈ N.subgroupOf L := by
    simpa [QuotientGroup.ker_mk'] using hxker
  simpa [Subgroup.mem_subgroupOf] using hxNsub

private theorem CFSG.section14_7_xi_le_kstar_of_xstar
    {M K Xi Mi Ki Xstar : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hKi : section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi)
    (hKstarKi : section14KStar M K ≤ Ki)
    (hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    Xi ≤ section14KStar Mi Ki := by
  classical
  rcases hXi with ⟨hXiK, p, hXicard⟩
  have hXi' : Xi ∈ section12PrimeOrderSubgroups K := ⟨hXiK, ⟨p, hXicard⟩⟩
  let Zi : Subgroup G := section14Z Mi Ki
  let Kistar : Subgroup G := section14KStar Mi Ki
  have hMiP :
      Mi ∈ section14MFamilyP G :=
    section14_7_overgroup_in_pFamily
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi' hMi
  have hXiPrime : Xi ∈ section10PrimeOrderSubgroupsIn p K := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXiK, hXicard⟩
  have hpσMi : p ∈ section10SigmaPrimes Mi :=
    section14_b2_prime_mem_sigma_of_primeOrder
      (G := G) (M := M) (K := K) (X := Xi) (Mstar := Mi) (p := p)
      hM hK hXiPrime hMi
  have hXstarKi :
      Xstar ∈ section12PrimeOrderSubgroups Ki := by
    exact ⟨hXstar.1.trans hKstarKi, hXstar.2⟩
  have hNXZ :=
    proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi Xstar hXstarKi
  have hZdp : section12InternalDirectProduct Ki Kistar Zi := by
    change section14ZInternalDirectProduct Mi Ki
    exact hNXZ.2.2
  have hZleZi : section14Z M K ≤ Zi :=
    section14_7_z_le_of_kstar_prime
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi' hMi hKi hKstarKi hXstar
  have hXiZ : Xi ≤ Zi := by
    intro x hxXi
    exact hZleZi (Subgroup.mem_sup_left (hXiK hxXi))
  have hKi_norm_Kistar : Ki ≤ Subgroup.normalizer (Kistar : Set G) := by
    intro x hx
    exact (centralizer_le_normalizer Kistar) (hZdp.2.2.2.2 hx)
  have hcompKistar :
      (Kistar.subgroupOf Zi).IsComplement' (Ki.subgroupOf Zi) := by
    change
      ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)).IsComplement'
        (Ki.subgroupOf (Ki ⊔ section14KStar Mi Ki))
    exact
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := section14KStar Mi Ki) (R := Ki) hKi_norm_Kistar
        (by simpa [disjoint_iff, Kistar, inf_comm] using hZdp.2.2.2.1)
  have hcompKi :
      (Ki.subgroupOf Zi).IsComplement' (Kistar.subgroupOf Zi) := hcompKistar.symm
  have hKistarNormal : (Kistar.subgroupOf Zi).Normal := by
    change ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)).Normal
    exact
      Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := Ki) (N := section14KStar Mi Ki) hKi_norm_Kistar
  letI : (Kistar.subgroupOf Zi).Normal := hKistarNormal
  let q : Zi →* Zi ⧸ (Kistar.subgroupOf Zi) :=
    QuotientGroup.mk' (Kistar.subgroupOf Zi)
  have hXiMap_dvd_card :
      Nat.card ((Xi.subgroupOf Zi).map q) ∣ Nat.card Xi := by
    have hcard_sub : Nat.card (Xi.subgroupOf Zi) = Nat.card Xi :=
      natCard_subgroupOf_eq Xi Zi hXiZ
    exact (Subgroup.card_map_dvd (H := Xi.subgroupOf Zi) q).trans (by simp [hcard_sub])
  have hQuot_card :
      Nat.card (Zi ⧸ (Kistar.subgroupOf Zi)) = Nat.card Ki := by
    calc
      Nat.card (Zi ⧸ (Kistar.subgroupOf Zi)) =
          Nat.card (Ki.subgroupOf Zi) := by
            exact Nat.card_congr hcompKi.QuotientMulEquiv.toEquiv
      _ = Nat.card Ki := natCard_subgroupOf_eq Ki Zi le_sup_left
  have hXiMap_dvd_quot :
      Nat.card ((Xi.subgroupOf Zi).map q) ∣ Nat.card (Zi ⧸ (Kistar.subgroupOf Zi)) :=
    (Subgroup.card_subgroup_dvd_card ((Xi.subgroupOf Zi).map q))
  have hp_not_Ki : ¬ p.val ∣ Nat.card Ki := by
    intro hpKi
    have hpKiSub : p.val ∣ Nat.card (Ki.subgroupOf Mi) := by
      simpa [natCard_subgroupOf_eq Ki Mi hKi.1] using hpKi
    have hpκMi : p ∈ section14KappaPrimes Mi :=
      hKi.2.p_in_pi_of_p_dvd_card p hpKiSub
    exact section14_kappa_subset_not_sigma (M := Mi) hpκMi hpσMi
  have hcop :
      Nat.Coprime (Nat.card Xi) (Nat.card (Zi ⧸ (Kistar.subgroupOf Zi))) := by
    rw [hXicard, hQuot_card]
    exact (p.2.coprime_iff_not_dvd).2 hp_not_Ki
  have hXiMap_card_one : Nat.card ((Xi.subgroupOf Zi).map q) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hXiMap_dvd_card hXiMap_dvd_quot
  have hXiMap_bot : (Xi.subgroupOf Zi).map q = ⊥ := by
    apply (Subgroup.eq_bot_iff_card (H := (Xi.subgroupOf Zi).map q)).2
    exact hXiMap_card_one
  exact
    section14_7_subgroup_le_of_subgroupOf_quotient_map_eq_bot
      (G := G) (N := Kistar) (L := Zi) (C := Xi) hXiZ (by simpa [q] using hXiMap_bot)

private theorem CFSG.section14_7_z_le_M_of_kstar_prime
    {M K Xi Mi Ki Xstar : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hKi : section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi)
    (hKstarKi : section14KStar M K ≤ Ki)
    (hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    section14Z Mi Ki ≤ M := by
  have hMiP :
      Mi ∈ section14MFamilyP G :=
    section14_7_overgroup_in_pFamily
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hNXstar_le_M :
      Subgroup.normalizer (Xstar : Set G) ≤ M :=
    section14_7_normalizer_le_of_unique_centralizer_primeOrder
      (G := G) (M := M) (A := section14KStar M K) (X := Xstar) hM.1 hXstar
      ((proposition_14_2_c (G := G) (M := M) (K := K) hM hK).2 Xstar hXstar)
  have hMcontNXstar :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xstar : Set G)) :=
    ⟨hM.1, hNXstar_le_M⟩
  have hXstarKi :
      Xstar ∈ section12PrimeOrderSubgroups Ki := by
    exact ⟨hXstar.1.trans hKstarKi, hXstar.2⟩
  exact
    (section14_7_not_conjugate_and_z_le
      (G := G) (M := Mi) (K := Ki) (Xi := Xstar) (Mi := M)
      hMiP hKi hXstarKi hMcontNXstar).2

private theorem CFSG.section14_7_ki_le_z_of_xstar
    {M K Xi Mi Ki Xstar : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hKi : section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi)
    (hKstarKi : section14KStar M K ≤ Ki)
    (hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    Ki ≤ section14Z M K := by
  have hXiLeKistar :
      Xi ≤ section14KStar Mi Ki :=
    section14_7_xi_le_kstar_of_xstar
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hZi_le_M : section14Z Mi Ki ≤ M :=
    section14_7_z_le_M_of_kstar_prime
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hMiP :
      Mi ∈ section14MFamilyP G :=
    section14_7_overgroup_in_pFamily
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hXstarKi :
      Xstar ∈ section12PrimeOrderSubgroups Ki := by
    exact ⟨hXstar.1.trans hKstarKi, hXstar.2⟩
  have hNXZ :=
    proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi Xstar hXstarKi
  have hZdp : section12InternalDirectProduct Ki (section14KStar Mi Ki) (section14Z Mi Ki) := by
    change section14ZInternalDirectProduct Mi Ki
    exact hNXZ.2.2
  have hKi_norm_Xi : Ki ≤ Subgroup.normalizer (Xi : Set G) := by
    intro y hy
    apply (centralizer_le_normalizer Xi)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxXi
    exact Subgroup.mem_centralizer_iff.mp (hZdp.2.2.2.2 hy) x (hXiLeKistar hxXi)
  have hKi_le_M : Ki ≤ M := le_sup_left.trans hZi_le_M
  have hKi_le_subNX : Ki ≤ subgroupNormalizerIn M (Xi : Set G) := by
    intro y hy
    exact mem_subgroupNormalizerIn.mpr ⟨hKi_norm_Xi hy, hKi_le_M hy⟩
  have hNXeqZ : subgroupNormalizerIn M (Xi : Set G) = section14Z M K := by
    have hNXZ' := proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK Xi hXi
    exact hNXZ'.1.trans hNXZ'.2.1
  exact hKi_le_subNX.trans (by rw [hNXeqZ])

private theorem CFSG.section14_7_kistar_isPi_kappa_of_xstar
    {M K Xi Mi Ki Xstar : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hKi : section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi)
    (hKstarKi : section14KStar M K ≤ Ki)
    (hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    IsPiSubgroup (G := G) (section14KappaPrimes M) (section14KStar Mi Ki) := by
  let Kistar : Subgroup G := section14KStar Mi Ki
  have hMiP :
      Mi ∈ section14MFamilyP G :=
    section14_7_overgroup_in_pFamily
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hnotconj : ¬ section14ConjugateSubgroups Mi M :=
    (section14_7_not_conjugate_and_z_le
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi).1
  have hZi_le_M : section14Z Mi Ki ≤ M :=
    section14_7_z_le_M_of_kstar_prime
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hKistarLeM : Kistar ≤ M := le_sup_right.trans hZi_le_M
  have hXstarKi :
      Xstar ∈ section12PrimeOrderSubgroups Ki := by
    exact ⟨hXstar.1.trans hKstarKi, hXstar.2⟩
  have hNXstar_le_M :
      Subgroup.normalizer (Xstar : Set G) ≤ M :=
    section14_7_normalizer_le_of_unique_centralizer_primeOrder
      (G := G) (M := M) (A := section14KStar M K) (X := Xstar) hM.1 hXstar
      ((proposition_14_2_c (G := G) (M := M) (K := K) hM hK).2 Xstar hXstar)
  have hMcontNXstar :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xstar : Set G)) :=
    ⟨hM.1, hNXstar_le_M⟩
  have hKistarSigma' :
      IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ Kistar := by
    simpa [Kistar] using
      section14_7_kstar_isPi_sigma_compl
        (G := G) (M := Mi) (K := Ki) (Xi := Xstar) (Mi := M)
        hMiP hKi hXstarKi hMcontNXstar
  have hXstarNe : Xstar ≠ ⊥ := section14_b1_primeOrder_ne_bot (G := G) hXstar
  haveI : Nontrivial ↥Xstar := (Subgroup.nontrivial_iff_ne_bot (H := Xstar)).2 hXstarNe
  obtain ⟨xstar, hxstarXstar, hxstarne⟩ := Subgroup.exists_ne_one_of_nontrivial Xstar
  have hxstarMsigma : xstar ∈ section10Msigma M := (hXstar.1 hxstarXstar).1
  have hxM : M ∈ section14MsigmaElement xstar := by
    refine ⟨hM.1, ?_⟩
    intro y hy
    have hyx : y = xstar := by simpa using hy
    simpa [hyx] using hxstarMsigma
  intro q hqKistar
  obtain ⟨Y, hY⟩ :=
    section14_exists_primeOrderSubgroupIn_of_dvd_card
      (G := G) (A := Kistar) (p := q) hqKistar
  have hYPrime :
      Y ∈ section12PrimeOrderSubgroups Kistar :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hY
  have hYNe : Y ≠ ⊥ := section14_b1_primeOrder_ne_bot (G := G) hYPrime
  haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot (H := Y)).2 hYNe
  obtain ⟨y, hyY, hyne⟩ := Subgroup.exists_ne_one_of_nontrivial Y
  have hyKistar : y ∈ Kistar := hY.1 hyY
  have hY_le_zpow : Y ≤ Subgroup.zpowers y := by
    intro z hzY
    haveI : Fact q.val.Prime := ⟨q.2⟩
    have hzSub :
        (⟨z, hzY⟩ : Y) ∈
          Subgroup.zpowers (⟨y, hyY⟩ : Y) :=
      mem_zpowers_of_prime_card
        (G := Y) (p := q.val) (by simpa using hY.2)
        (g := (⟨y, hyY⟩ : Y))
        (g' := (⟨z, hzY⟩ : Y))
        (by simpa using hyne)
    rcases Subgroup.mem_zpowers_iff.mp hzSub with ⟨n, hn⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
  have hyM : y ∈ M := hKistarLeM hyKistar
  have hyCent : y ∈ elementCentralizerIn M xstar := by
    refine ⟨hyM, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr <|
      (Subgroup.mem_centralizer_iff.mp hyKistar.2 xstar (hXstarKi.1 hxstarXstar)).symm
  have hySigma' : section14IsPiElement (section10SigmaPrimes M)ᶜ y := by
    intro r hrSupp
    have hrKistar : r ∈ subgroupPrimeSet Kistar :=
      section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hyKistar) hrSupp
    exact hKistarSigma' r hrKistar
  have hcor :=
    corollary_14_3 (G := G) (M := M) (x := xstar) (x' := y) hM.1
      hxstarMsigma hxstarne hyne hyCent hySigma'
  rcases hcor with hκ | hτ2
  · have hqSupp : q ∈ section14ElementPrimeSupport y := by
      have hqzpow : q ∈ subgroupPrimeSet (Subgroup.zpowers y) := by
        rw [subgroupPrimeSet]
        exact
          (show q.val ∣ Nat.card Y by rw [hY.2]).trans
            (Subgroup.card_dvd_of_le hY_le_zpow)
      simpa [section14ElementPrimeSupport] using hqzpow
    exact hκ.1 hqSupp
  · rcases hτ2 with ⟨_hτ2supp, _hlen, huniqCy⟩
    have huniqCY :
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer (Y : Set G)) = {Mi} := by
      simpa [Kistar] using
        (proposition_14_2_c (G := G) (M := Mi) (K := Ki) hMiP hKi).2 Y hYPrime
    have hCY_le_Mi : Subgroup.centralizer (Y : Set G) ≤ Mi := by
      have hMimem :
          Mi ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) := by
        rw [huniqCY]
        simp
      exact hMimem.2
    have hCy_le_CY :
        Subgroup.centralizer ({y} : Set G) ≤ Subgroup.centralizer (Y : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro z hzY
      have hzzpow : z ∈ Subgroup.zpowers y := hY_le_zpow hzY
      rcases Subgroup.mem_zpowers_iff.mp hzzpow with ⟨n, rfl⟩
      have hycommg : Commute g y :=
        Subgroup.mem_centralizer_singleton_iff.mp hg
      exact (hycommg.zpow_right n).eq.symm
    have hMimemCy :
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) :=
      ⟨hMi.1, hCy_le_CY.trans hCY_le_Mi⟩
    have hMieqM : Mi = M := by
      have hMimem : Mi ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniqCy] using hMimemCy
      simpa using hMimem
    exact False.elim <| hnotconj ⟨1, by
      simpa [hMieqM] using (section8_conjBy_one (G := G) M).symm⟩

private theorem CFSG.section14_7_kistar_le_k_of_xstar
    {M K Xi Mi Ki Xstar : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hKi : section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi)
    (hKstarKi : section14KStar M K ≤ Ki)
    (hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    section14KStar Mi Ki ≤ K := by
  let Kistar : Subgroup G := section14KStar Mi Ki
  have hKistarPi :
      IsPiSubgroup (G := G) (section14KappaPrimes M) Kistar :=
    section14_7_kistar_isPi_kappa_of_xstar
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hZi_le_M : section14Z Mi Ki ≤ M :=
    section14_7_z_le_M_of_kstar_prime
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hKistarLeM : Kistar ≤ M := le_sup_right.trans hZi_le_M
  have hXiLeKistar :
      Xi ≤ Kistar :=
    section14_7_xi_le_kstar_of_xstar
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hXiNe : Xi ≠ ⊥ := section14_b1_primeOrder_ne_bot (G := G) hXi
  have hKistarSubPi :
      IsPiSubgroup (G := M) (section14KappaPrimes M) (Kistar.subgroupOf M) := by
    intro p hp
    have hcard :
        Nat.card (Kistar.subgroupOf M) = Nat.card Kistar :=
      section12_card_subgroupOf_eq hKistarLeM
    exact hKistarPi p (by simpa [hcard] using hp)
  letI : MulDistribMulAction Unit M := {
    smul := fun _ y => y
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hKistarSubInv : IsInvariant Unit M (Kistar.subgroupOf M) := by
    refine ⟨?_⟩
    intro _ y
    simp [Kistar]
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨Hsub, hHsubHall, _hHsubInv, hKistarSubLeH⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcop (section14KappaPrimes M)
      (Kistar.subgroupOf M) hKistarSubPi hKistarSubInv
  let H : Subgroup G := Hsub.map M.subtype
  have hHLeM : H ≤ M := Subgroup.map_subtype_le Hsub
  have hKistarLeH : Kistar ≤ H := by
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hKistarLeM hy⟩, hKistarSubLeH
        (show (⟨y, hKistarLeM hy⟩ : M) ∈ Kistar.subgroupOf M from hy), rfl⟩
  obtain ⟨m, hm⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := M) hsolvM hK.2 hHsubHall
  have hmap_conj_inv :
      (((K.subgroupOf M).map (MulAut.conj m).toMonoidHom).map
        (MulAut.conj m⁻¹).toMonoidHom) = K.subgroupOf M := by
    rw [Subgroup.map_map]
    ext x
    simp [MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc]
  have hHsub_conj_inv_le :
      Hsub.map (MulAut.conj m⁻¹).toMonoidHom ≤ K.subgroupOf M := by
    rw [hm]
    exact hmap_conj_inv.le
  have hHsub_eq : H.subgroupOf M = Hsub := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hHLeM]
  have hHconjInv_le_K : H.conjBy (m : G)⁻¹ ≤ K := by
    have hmInvM : (m : G)⁻¹ ∈ M := M.inv_mem m.property
    have hsub :
        (H.subgroupOf M).map (MulAut.conj (⟨(m : G)⁻¹, hmInvM⟩ : M)).toMonoidHom ≤
          K.subgroupOf M := by
      change (H.subgroupOf M).map (MulAut.conj m⁻¹).toMonoidHom ≤ K.subgroupOf M
      simpa [hHsub_eq] using hHsub_conj_inv_le
    exact
      section14_conjBy_le_of_subgroupOf_conjBy_le
        (G := G) (H := H) (K := K) (M := M) (g := (m : G)⁻¹)
        hmInvM hHLeM hsub
  have hH_le_Kconj : H ≤ K.conjBy (m : G) := by
    intro x hxH
    have hxconj : (m : G)⁻¹ * x * (m : G) ∈ K := by
      exact hHconjInv_le_K <| Subgroup.mem_map.mpr ⟨x, hxH, by
        simp [mul_assoc]⟩
    exact Subgroup.mem_map.mpr ⟨(m : G)⁻¹ * x * (m : G), hxconj, by
      simp [MulAut.conj_apply, mul_assoc]⟩
  have hXiLeKm : Xi ≤ K.conjBy (m : G) :=
    hXiLeKistar.trans (hKistarLeH.trans hH_le_Kconj)
  have hmZ : (m : G) ∈ section14Z M K := by
    by_contra hmNotZ
    have hdisj :
        K ⊓ K.conjBy (m : G) = ⊥ :=
      (proposition_14_2_d (G := G) (M := M) (K := K) hM hK).2
        (m : G) m.property hmNotZ
    have hdisj' : Disjoint K (K.conjBy (m : G)) := by
      simpa [disjoint_iff] using hdisj
    have hXiBot : Xi ≤ ⊥ := by
      intro x hxXi
      exact Subgroup.disjoint_def.mp hdisj' (hXi.1 hxXi) (hXiLeKm hxXi)
    exact hXiNe (bot_unique hXiBot)
  have hNKZ : subgroupNormalizerIn M (K : Set G) = section14Z M K := by
    exact (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK Xi hXi).2.1
  have hmNK : (m : G) ∈ subgroupNormalizerIn M (K : Set G) := by
    simpa [hNKZ] using hmZ
  have hmNormK : (m : G) ∈ Subgroup.normalizer (K : Set G) :=
    (mem_subgroupNormalizerIn.mp hmNK).1
  have hKconj : K.conjBy (m : G) = K :=
    section11_conjBy_eq_of_mem_normalizer hmNormK
  exact hKistarLeH.trans (by simpa [hKconj] using hH_le_Kconj)

private theorem CFSG.section14_7_single_overgroup_data_of_xstar
    {M K Xi Mi Ki Xstar : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hKi : section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi)
    (hKstarKi : section14KStar M K ≤ Ki)
    (hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    Mi ∈ section14MFamilyP G ∧
      section14Z M K = section14Z Mi Ki ∧
      Xi ≤ section14KStar Mi Ki ∧
      Ki ≤ section14Z M K ∧
      section14KStar Mi Ki ≤ K := by
  let Kistar : Subgroup G := section14KStar Mi Ki
  have hMiP :
      Mi ∈ section14MFamilyP G :=
    section14_7_overgroup_in_pFamily
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hZleZi : section14Z M K ≤ section14Z Mi Ki :=
    section14_7_z_le_of_kstar_prime
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hXiLeKistar :
      Xi ≤ Kistar := by
    simpa [Kistar] using
      section14_7_xi_le_kstar_of_xstar
        (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
        (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hKiLeZ : Ki ≤ section14Z M K :=
    section14_7_ki_le_z_of_xstar
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hKistarLeK : Kistar ≤ K := by
    simpa [Kistar] using
      section14_7_kistar_le_k_of_xstar
        (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
        (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  have hZiLeZ : section14Z Mi Ki ≤ section14Z M K := by
    have hKistarLeZ : Kistar ≤ section14Z M K := hKistarLeK.trans le_sup_left
    simpa [section14Z, Kistar] using sup_le hKiLeZ hKistarLeZ
  refine ⟨hMiP, le_antisymm hZleZi hZiLeZ, ?_, hKiLeZ, hKistarLeK⟩
  simpa [Kistar] using hXiLeKistar

private theorem CFSG.section14_7_exists_single_overgroup_data
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G))) :
    ∃ Ki : Subgroup G,
      section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
  obtain ⟨Ki, hKi, hKstarKi⟩ :=
    section14_7_exists_hall_kappa_containing_kstar
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  have hMi_not_conj :
      ¬ section14ConjugateSubgroups Mi M :=
    (section14_7_not_conjugate_and_z_le
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi).1
  obtain ⟨q, Xstar, hXstarPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := section14KStar M K)
      (section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK)
  have hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K) :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXstarPrime
  obtain ⟨hMiP, hZeqZi, hXiLeKistar, hKiLeZ, hKistarLeK⟩ :=
    section14_7_single_overgroup_data_of_xstar
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hXi hMi hKi hKstarKi hXstar
  exact ⟨Ki, hKi, hKstarKi, hMiP, hMi_not_conj, hZeqZi, hXiLeKistar, hKiLeZ, hKistarLeK⟩

@[expose] public def CFSG.section14_7_overgroupFamily (K : Subgroup G) : Set (Subgroup G) :=
  {Mi | ∃ Xi : Subgroup G,
    Xi ∈ section12PrimeOrderSubgroups K ∧
      Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G))}


noncomputable local instance (K : Subgroup G) :
    Fintype {Mi // Mi ∈ section14_7_overgroupFamily K} :=
  Fintype.ofFinite _

private theorem CFSG.section14_7_overgroupFamily_nonempty
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    (section14_7_overgroupFamily K).Nonempty := by
  obtain ⟨Xi, Mi, _Ki, hXi, hMi, _hKi, _hKstarKi, _hMi_not_conj, _hZleMi⟩ :=
    section14_7_exists_initial_overgroup_data
      (G := G) (M := M) (K := K) hM hK
  exact ⟨Mi, ⟨Xi, hXi, hMi⟩⟩

public theorem CFSG.section14_7_exists_overgroupFamily_data
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    ∃ Xi Ki : Subgroup G,
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
  rcases hMiFam with ⟨Xi, hXi, hMi⟩
  obtain ⟨Ki, hKi, hKstarKi, hMiP, hMi_not_conj, hZeqZi, hXiLeKistar, hKiLeZ, hKistarLeK⟩ :=
    section14_7_exists_single_overgroup_data
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi
  exact
    ⟨Xi, Ki, hXi, hMi, hKi, hKstarKi, hMiP, hMi_not_conj, hZeqZi, hXiLeKistar, hKiLeZ,
      hKistarLeK⟩

private noncomputable def CFSG.section14_7_XiOfOvergroupFamily
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) : Subgroup G :=
  Classical.choose <|
    section14_7_exists_overgroupFamily_data
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam

@[expose] public noncomputable def CFSG.section14_7_KiOfOvergroupFamily
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) : Subgroup G :=
  Classical.choose <|
    Classical.choose_spec <|
      section14_7_exists_overgroupFamily_data
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam

private theorem CFSG.section14_7_XiKiOfOvergroupFamily_spec
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    let Xi := section14_7_XiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
    let Ki := section14_7_KiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
    Xi ∈ section12PrimeOrderSubgroups K ∧
      Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
      section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
      section14KStar M K ≤ Ki ∧
      Mi ∈ section14MFamilyP G ∧
      ¬ section14ConjugateSubgroups Mi M ∧
      section14Z M K = section14Z Mi Ki ∧
      Xi ≤ section14KStar Mi Ki ∧
      Ki ≤ section14Z M K ∧
      section14KStar Mi Ki ≤ K := by
  let Xi := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let hXiSpec :
      ∃ Ki : Subgroup G,
        Xi ∈ section12PrimeOrderSubgroups K ∧
          Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
          section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
          section14KStar M K ≤ Ki ∧
          Mi ∈ section14MFamilyP G ∧
          ¬ section14ConjugateSubgroups Mi M ∧
          section14Z M K = section14Z Mi Ki ∧
          Xi ≤ section14KStar Mi Ki ∧
          Ki ≤ section14Z M K ∧
          section14KStar Mi Ki ≤ K :=
    Classical.choose_spec <|
      section14_7_exists_overgroupFamily_data
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hKiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K :=
    Classical.choose_spec hXiSpec
  simpa [Xi, Ki] using hKiSpec

@[expose] public noncomputable def CFSG.section14_7_KstarOfOvergroupFamily
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) : Subgroup G :=
  section14KStar Mi <|
    section14_7_KiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam

private theorem CFSG.section14_7_kstar_inf_bot_of_distinct_overgroupFamily
    {M K Mi Mj : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hMjFam : Mj ∈ section14_7_overgroupFamily K)
    (hij : Mi ≠ Mj) :
    section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam ⊓
      section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam = ⊥ := by
  let Xi := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Xj := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  let Kj := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  let Kistar : Subgroup G := section14KStar Mi Ki
  let Kjstar : Subgroup G := section14KStar Mj Kj
  have hMiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
    simpa [Xi, Ki] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hMjSpec :
      Xj ∈ section12PrimeOrderSubgroups K ∧
        Mj ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xj : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mj) Kj Mj ∧
        section14KStar M K ≤ Kj ∧
        Mj ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mj M ∧
        section14Z M K = section14Z Mj Kj ∧
        Xj ≤ section14KStar Mj Kj ∧
        Kj ≤ section14Z M K ∧
        section14KStar Mj Kj ≤ K := by
    simpa [Xj, Kj] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  rcases hMiSpec with
    ⟨_hXi, _hMi, hKi, _hKstarKi, hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar, _hKiLeZ,
      _hKistarLeK⟩
  rcases hMjSpec with
    ⟨_hXj, _hMj, hKj, _hKstarKj, hMjP, _hMj_not_conj, _hZeqZj, _hXjLeKjstar, _hKjLeZ,
      _hKjstarLeK⟩
  by_contra hne
  obtain ⟨p, Y, hY⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot (G := G) (A := Kistar ⊓ Kjstar) hne
  have hYPrimeInf :
      Y ∈ section12PrimeOrderSubgroups (Kistar ⊓ Kjstar) :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hY
  have hYPrimeI :
      Y ∈ section12PrimeOrderSubgroups Kistar := by
    exact ⟨hYPrimeInf.1.trans inf_le_left, hYPrimeInf.2⟩
  have hYPrimeJ :
      Y ∈ section12PrimeOrderSubgroups Kjstar := by
    exact ⟨hYPrimeInf.1.trans inf_le_right, hYPrimeInf.2⟩
  have huniqI :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mi} := by
    simpa [Kistar] using
      (proposition_14_2_c (G := G) (M := Mi) (K := Ki) hMiP hKi).2 Y hYPrimeI
  have huniqJ :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mj} := by
    simpa [Kjstar] using
      (proposition_14_2_c (G := G) (M := Mj) (K := Kj) hMjP hKj).2 Y hYPrimeJ
  have hMjMem :
      Mj ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) := by
    rw [huniqJ]
    simp
  have hMjEqMi : Mj = Mi := by
    have hsingle : Mj ∈ ({Mi} : Set (Subgroup G)) := by
      simpa [huniqI] using hMjMem
    simpa using hsingle
  exact hij hMjEqMi.symm

private theorem CFSG.section14_7_base_kstar_inf_bot_of_overgroupFamily
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    section14KStar M K ⊓
      section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = ⊥ := by
  let Xi := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Kistar : Subgroup G := section14KStar Mi Ki
  have hMiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
    simpa [Xi, Ki] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  rcases hMiSpec with
    ⟨_hXi, _hMi, hKi, _hKstarKi, hMiP, hMi_not_conj, _hZeqZi, _hXiLeKistar, _hKiLeZ,
      _hKistarLeK⟩
  by_contra hne
  obtain ⟨p, Y, hY⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot (G := G) (A := section14KStar M K ⊓ Kistar) hne
  have hYPrimeInf :
      Y ∈ section12PrimeOrderSubgroups (section14KStar M K ⊓ Kistar) :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hY
  have hYPrimeBase :
      Y ∈ section12PrimeOrderSubgroups (section14KStar M K) := by
    exact ⟨hYPrimeInf.1.trans inf_le_left, hYPrimeInf.2⟩
  have hYPrimeI :
      Y ∈ section12PrimeOrderSubgroups Kistar := by
    exact ⟨hYPrimeInf.1.trans inf_le_right, hYPrimeInf.2⟩
  have huniqBase :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} :=
    (proposition_14_2_c (G := G) (M := M) (K := K) hM hK).2 Y hYPrimeBase
  have huniqI :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mi} := by
    simpa [Kistar] using
      (proposition_14_2_c (G := G) (M := Mi) (K := Ki) hMiP hKi).2 Y hYPrimeI
  have hMMem :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) := by
    rw [huniqBase]
    simp
  have hMeqMi : M = Mi := by
    have hsingle : M ∈ ({Mi} : Set (Subgroup G)) := by
      simpa [huniqI] using hMMem
    simpa using hsingle
  exact hMi_not_conj ⟨1, by simpa [hMeqMi] using (section8_conjBy_one (G := G) M).symm⟩


public theorem CFSG.section14_7_primeOrder_le_k_or_kstar_of_z
    {M K X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hX : X ∈ section12PrimeOrderSubgroups (section14Z M K)) :
    X ≤ K ∨ X ≤ section14KStar M K := by
  classical
  obtain ⟨q, Xi, hXiPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
  have hXi : Xi ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXiPrime
  have hZdp : section12InternalDirectProduct K (section14KStar M K) (section14Z M K) := by
    simpa [section14ZInternalDirectProduct] using
      (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK Xi hXi).2.2
  rcases hX with ⟨hXZ, p, hXcard⟩
  by_cases hpσ : p ∈ section10SigmaPrimes M
  · right
    let Z : Subgroup G := section14Z M K
    have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
      intro x hxK
      exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hxK)
    have hcompKstar :
        ((section14KStar M K).subgroupOf Z).IsComplement' (K.subgroupOf Z) := by
      change
        ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).IsComplement'
          (K.subgroupOf (K ⊔ section14KStar M K))
      exact
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := section14KStar M K) (R := K) hK_norm_Kstar
          (by simpa [disjoint_iff, inf_comm] using hZdp.2.2.2.1)
    have hcompK :
        (K.subgroupOf Z).IsComplement' ((section14KStar M K).subgroupOf Z) :=
      hcompKstar.symm
    have hKstarNormal : ((section14KStar M K).subgroupOf Z).Normal := by
      change ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).Normal
      exact
        Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := K) (N := section14KStar M K) hK_norm_Kstar
    letI : ((section14KStar M K).subgroupOf Z).Normal := hKstarNormal
    let φ : Z →* Z ⧸ ((section14KStar M K).subgroupOf Z) :=
      QuotientGroup.mk' ((section14KStar M K).subgroupOf Z)
    have hXMap_dvd_card : Nat.card ((X.subgroupOf Z).map φ) ∣ Nat.card X := by
      have hcard_sub : Nat.card (X.subgroupOf Z) = Nat.card X :=
        natCard_subgroupOf_eq X Z (by simpa [Z] using hXZ)
      exact (Subgroup.card_map_dvd (H := X.subgroupOf Z) φ).trans (by
        simp [hcard_sub])
    have hQuot_card :
        Nat.card (Z ⧸ ((section14KStar M K).subgroupOf Z)) = Nat.card K := by
      calc
        Nat.card (Z ⧸ ((section14KStar M K).subgroupOf Z)) =
            Nat.card (K.subgroupOf Z) := by
              exact Nat.card_congr hcompK.QuotientMulEquiv.toEquiv
        _ = Nat.card K := natCard_subgroupOf_eq K Z le_sup_left
    have hXMap_dvd_quot :
        Nat.card ((X.subgroupOf Z).map φ) ∣
          Nat.card (Z ⧸ ((section14KStar M K).subgroupOf Z)) :=
      Subgroup.card_subgroup_dvd_card ((X.subgroupOf Z).map φ)
    have hp_not_K : ¬ p.val ∣ Nat.card K := by
      intro hpKcard
      have hpKsub : p.val ∣ Nat.card (K.subgroupOf M) := by
        simpa [section12_card_subgroupOf_eq hK.1] using hpKcard
      have hpκ : p ∈ section14KappaPrimes M :=
        hK.2.p_in_pi_of_p_dvd_card p hpKsub
      exact section14_kappa_subset_not_sigma (M := M) hpκ hpσ
    have hcop :
        Nat.Coprime (Nat.card X)
          (Nat.card (Z ⧸ ((section14KStar M K).subgroupOf Z))) := by
      rw [hXcard, hQuot_card]
      exact (p.2.coprime_iff_not_dvd).2 hp_not_K
    have hXMap_card_one : Nat.card ((X.subgroupOf Z).map φ) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hXMap_dvd_card hXMap_dvd_quot
    have hXMap_bot : (X.subgroupOf Z).map φ = ⊥ := by
      exact (Subgroup.eq_bot_iff_card (H := (X.subgroupOf Z).map φ)).2 hXMap_card_one
    exact
      section14_7_subgroup_le_of_subgroupOf_quotient_map_eq_bot
        (G := G) (N := section14KStar M K) (L := Z) (C := X)
        (by simpa [Z] using hXZ) (by simpa [φ] using hXMap_bot)
  · left
    let Z : Subgroup G := section14KStar M K ⊔ K
    have hKstar_norm_K : section14KStar M K ≤ Subgroup.normalizer (K : Set G) := by
      intro y hy
      apply (centralizer_le_normalizer K)
      rw [Subgroup.mem_centralizer_iff]
      intro x hxK
      exact (Subgroup.mem_centralizer_iff.mp (hZdp.2.2.2.2 hxK) y hy).symm
    have hcompK :
        (K.subgroupOf Z).IsComplement' ((section14KStar M K).subgroupOf Z) := by
      simpa [Z] using
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := K) (R := section14KStar M K) hKstar_norm_K
          (by simpa [disjoint_iff] using hZdp.2.2.2.1)
    have hcompKstar :
        ((section14KStar M K).subgroupOf Z).IsComplement' (K.subgroupOf Z) :=
      hcompK.symm
    have hKNormal : (K.subgroupOf Z).Normal := by
      simpa [Z] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := section14KStar M K) (N := K) hKstar_norm_K)
    letI : (K.subgroupOf Z).Normal := hKNormal
    let φ : Z →* Z ⧸ (K.subgroupOf Z) := QuotientGroup.mk' (K.subgroupOf Z)
    have hXMap_dvd_card : Nat.card ((X.subgroupOf Z).map φ) ∣ Nat.card X := by
      have hcard_sub : Nat.card (X.subgroupOf Z) = Nat.card X :=
        natCard_subgroupOf_eq X Z (by simpa [Z, section14Z, sup_comm] using hXZ)
      exact (Subgroup.card_map_dvd (H := X.subgroupOf Z) φ).trans (by
        simp [hcard_sub])
    have hQuot_card :
        Nat.card (Z ⧸ (K.subgroupOf Z)) = Nat.card (section14KStar M K) := by
      calc
        Nat.card (Z ⧸ (K.subgroupOf Z)) =
            Nat.card ((section14KStar M K).subgroupOf Z) := by
              exact Nat.card_congr hcompKstar.QuotientMulEquiv.toEquiv
        _ = Nat.card (section14KStar M K) :=
          natCard_subgroupOf_eq (section14KStar M K) Z le_sup_left
    have hXMap_dvd_quot :
        Nat.card ((X.subgroupOf Z).map φ) ∣ Nat.card (Z ⧸ (K.subgroupOf Z)) :=
      Subgroup.card_subgroup_dvd_card ((X.subgroupOf Z).map φ)
    have hp_not_Kstar : ¬ p.val ∣ Nat.card (section14KStar M K) := by
      intro hpKstar
      have hpMsigma : p.val ∣ Nat.card (section10Msigma M) :=
        hpKstar.trans <| Subgroup.card_dvd_of_le (by intro x hx; exact hx.1)
      have hpMsigmaSub : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
        have hcardMsigma :
            Nat.card (section10MsigmaSubgroup M) = Nat.card (section10Msigma M) := by
          simpa [section14_msigma_subgroupOf_eq (M := M)] using
            (section12_card_subgroupOf_eq (section14_msigma_le M))
        rw [hcardMsigma]
        exact hpMsigma
      have hpσ' : p ∈ section10SigmaPrimes M :=
        ((theorem_10_2_b hM.1).2).p_in_pi_of_p_dvd_card p hpMsigmaSub
      exact hpσ hpσ'
    have hcop :
        Nat.Coprime (Nat.card X) (Nat.card (Z ⧸ (K.subgroupOf Z))) := by
      rw [hXcard, hQuot_card]
      exact (p.2.coprime_iff_not_dvd).2 hp_not_Kstar
    have hXMap_card_one : Nat.card ((X.subgroupOf Z).map φ) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hXMap_dvd_card hXMap_dvd_quot
    have hXMap_bot : (X.subgroupOf Z).map φ = ⊥ := by
      exact (Subgroup.eq_bot_iff_card (H := (X.subgroupOf Z).map φ)).2 hXMap_card_one
    exact
      section14_7_subgroup_le_of_subgroupOf_quotient_map_eq_bot
        (G := G) (N := K) (L := Z) (C := X)
        (by simpa [Z, section14Z, sup_comm] using hXZ) (by simpa [φ] using hXMap_bot)

private theorem CFSG.section14_7_exists_maximal_overgroup_of_primeOrderSubgroup
    {M K X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hX : X ∈ section12PrimeOrderSubgroups K) :
    ∃ Mi : Subgroup G,
      Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) := by
  rcases hX with ⟨hXK, p, hXcard⟩
  have hXPrime : X ∈ section10PrimeOrderSubgroupsIn p K := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXK, hXcard⟩
  have hNX_not_le_M :
      ¬ Subgroup.normalizer (X : Set G) ≤ M := by
    intro hNXM
    have hMcontNX :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
      ⟨hM.1, hNXM⟩
    have hpσM : p ∈ section10SigmaPrimes M :=
      section14_b2_prime_mem_sigma_of_primeOrder
        (G := G) (M := M) (K := K) (X := X) (Mstar := M) (p := p)
        hM hK hXPrime hMcontNX
    have hpκ : p ∈ section14KappaPrimes M := by
      have hpX : p.val ∣ Nat.card X := by
        rw [hXcard]
      have hXM : X ≤ M := hXK.trans hK.1
      have hXsub_le_Ksub : X.subgroupOf M ≤ K.subgroupOf M := by
        intro x hx
        exact hXK (by simpa [Subgroup.mem_subgroupOf] using hx)
      have hcardXsub : Nat.card (X.subgroupOf M) = Nat.card X :=
        section12_card_subgroupOf_eq hXM
      have hpXsub : p.val ∣ Nat.card (X.subgroupOf M) := by
        simpa [hcardXsub] using hpX
      exact hK.2.p_in_pi_of_p_dvd_card p
        (hpXsub.trans (Subgroup.card_dvd_of_le hXsub_le_Ksub))
    exact section14_kappa_subset_not_sigma (M := M) hpκ hpσM
  have hXne : X ≠ ⊥ := section12_primeOrder_ne_bot hXPrime
  have hXne_top : X ≠ ⊤ := by
    intro hXtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hXK.trans hK.1
    exact hM.1.1 (top_le_iff.mp htop_le_M)
  have hNXne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro hNtop
    have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    letI : IsSimpleGroup G := IsMinCE.simple
    rcases hXnormal.eq_bot_or_eq_top with hXbot | hXtop
    · exact hXne hXbot
    · exact hXne_top hXtop
  exact
    section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (X : Set G)) hNXne_top

private theorem CFSG.section14_7_exists_overgroupFamily_kstar_cover_of_k
    {M K X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hX : X ∈ section12PrimeOrderSubgroups K) :
    ∃ Mi : Subgroup G, ∃ hMiFam : Mi ∈ section14_7_overgroupFamily K,
      X ≤ section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam := by
  classical
  obtain ⟨q, Xstar, hXstarPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := section14KStar M K)
      (section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK)
  have hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K) :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXstarPrime
  obtain ⟨Mi, hMi⟩ :=
    section14_7_exists_maximal_overgroup_of_primeOrderSubgroup
      (G := G) (M := M) (K := K) (X := X) hM hK hX
  have hMiFam : Mi ∈ section14_7_overgroupFamily K := ⟨X, hX, hMi⟩
  let Ki : Subgroup G :=
    section14_7_KiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hMiSpec :
      section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki := by
    rcases
        (section14_7_XiKiOfOvergroupFamily_spec
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
      ⟨_hXi, _hMi', hKi, hKstarKi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
        _hKiLeZ, _hKistarLeK⟩
    exact ⟨hKi, hKstarKi⟩
  refine ⟨Mi, hMiFam, ?_⟩
  simpa [section14_7_KstarOfOvergroupFamily, Ki] using
    section14_7_xi_le_kstar_of_xstar
      (G := G) (M := M) (K := K) (Xi := X) (Mi := Mi) (Ki := Ki)
      (Xstar := Xstar) hM hK hX hMi hMiSpec.1 hMiSpec.2 hXstar

private theorem CFSG.section14_7_primeOrder_le_base_or_overgroupFamily_kstar_of_z
    {M K X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hX : X ∈ section12PrimeOrderSubgroups (section14Z M K)) :
    X ≤ section14KStar M K ∨
      ∃ Mi : Subgroup G, ∃ hMiFam : Mi ∈ section14_7_overgroupFamily K,
        X ≤ section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam := by
  rcases
      section14_7_primeOrder_le_k_or_kstar_of_z
        (G := G) (M := M) (K := K) (X := X) hM hK hX with
    hXK | hXKstar
  · have hXK' : X ∈ section12PrimeOrderSubgroups K := ⟨hXK, hX.2⟩
    right
    exact
      section14_7_exists_overgroupFamily_kstar_cover_of_k
        (G := G) (M := M) (K := K) (X := X) hM hK hXK'
  · exact Or.inl hXKstar

private theorem CFSG.section14_7_base_kstar_hall_sigma_in_z
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section12HallSubgroupIn
      (section10SigmaPrimes M) (section14KStar M K) (section14Z M K) := by
  classical
  obtain ⟨q, Xi, hXiPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
  have hXi : Xi ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXiPrime
  have hZdp : section12InternalDirectProduct K (section14KStar M K) (section14Z M K) := by
    simpa [section14ZInternalDirectProduct] using
      (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK Xi hXi).2.2
  let Z : Subgroup G := section14Z M K
  refine ⟨le_sup_right, ?_⟩
  refine isHallSubgroup_of (G := Z) (section10SigmaPrimes M)
    ((section14KStar M K).subgroupOf Z) ?_ ?_
  · intro p hpKstar
    have hpMsigma : p.val ∣ Nat.card (section10Msigma M) := by
      have hpKstar' : p.val ∣ Nat.card (section14KStar M K) := by
        simpa [natCard_subgroupOf_eq (section14KStar M K) Z le_sup_right] using hpKstar
      exact hpKstar'.trans <| Subgroup.card_dvd_of_le (by
        intro x hx
        exact hx.1)
    have hpMsigmaSub : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      have hcardMsigma :
          Nat.card (section10MsigmaSubgroup M) = Nat.card (section10Msigma M) := by
        simpa [section14_msigma_subgroupOf_eq (M := M)] using
          (section12_card_subgroupOf_eq (section14_msigma_le M))
      rw [hcardMsigma]
      exact hpMsigma
    exact ((theorem_10_2_b hM.1).2).p_in_pi_of_p_dvd_card p hpMsigmaSub
  · intro p hpσ hpidx
    have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
      intro x hxK
      exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hxK)
    have hcompKstar :
        ((section14KStar M K).subgroupOf Z).IsComplement' (K.subgroupOf Z) := by
      change
        ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).IsComplement'
          (K.subgroupOf (K ⊔ section14KStar M K))
      exact
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := section14KStar M K) (R := K) hK_norm_Kstar
          (by simpa [disjoint_iff, inf_comm] using hZdp.2.2.2.1)
    have hidx : ((section14KStar M K).subgroupOf Z).index = Nat.card K := by
      calc
        ((section14KStar M K).subgroupOf Z).index = Nat.card (K.subgroupOf Z) := by
          exact hcompKstar.symm.index_eq_card
        _ = Nat.card K := natCard_subgroupOf_eq K Z le_sup_left
    have hpK : p.val ∣ Nat.card K := by
      simpa [hidx] using hpidx
    have hpKsub : p.val ∣ Nat.card (K.subgroupOf M) := by
      simpa [section12_card_subgroupOf_eq hK.1] using hpK
    have hpκ : p ∈ section14KappaPrimes M :=
      hK.2.p_in_pi_of_p_dvd_card p hpKsub
    exact section14_kappa_subset_not_sigma (M := M) hpκ hpσ

private theorem CFSG.section14_7_kstarOfOvergroupFamily_hall_sigma_in_z
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    section12HallSubgroupIn
      (section10SigmaPrimes Mi)
      (section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam)
      (section14Z M K) := by
  classical
  let Xi := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Kistar : Subgroup G := section14KStar Mi Ki
  have hMiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
    simpa [Xi, Ki] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  rcases hMiSpec with
    ⟨_hXi, _hMi, hKi, hKstarKi, hMiP, _hMi_not_conj, hZeqZi, _hXiLeKistar, hKiLeZ,
      hKistarLeK⟩
  obtain ⟨q, Xstar, hXstarPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := section14KStar M K)
      (section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK)
  have hXstar : Xstar ∈ section12PrimeOrderSubgroups (section14KStar M K) :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXstarPrime
  have hXstarKi : Xstar ∈ section12PrimeOrderSubgroups Ki := by
    exact ⟨hXstar.1.trans hKstarKi, hXstar.2⟩
  have hZdp : section12InternalDirectProduct Ki Kistar (section14Z Mi Ki) := by
    change section14ZInternalDirectProduct Mi Ki
    exact (proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi Xstar hXstarKi).2.2
  refine ⟨hKistarLeK.trans le_sup_left, ?_⟩
  refine isHallSubgroup_of (G := section14Z M K) (section10SigmaPrimes Mi)
    (Kistar.subgroupOf (section14Z M K)) ?_ ?_
  · intro p hpKistar
    have hpMsigma : p.val ∣ Nat.card (section10Msigma Mi) := by
      have hpKistar' : p.val ∣ Nat.card Kistar := by
        simpa [Kistar, natCard_subgroupOf_eq Kistar (section14Z M K) (hKistarLeK.trans le_sup_left)]
          using hpKistar
      exact hpKistar'.trans <| Subgroup.card_dvd_of_le (by
        intro x hx
        exact hx.1)
    have hpMsigmaSub : p.val ∣ Nat.card (section10MsigmaSubgroup Mi) := by
      have hcardMsigma :
          Nat.card (section10MsigmaSubgroup Mi) = Nat.card (section10Msigma Mi) := by
        simpa [section14_msigma_subgroupOf_eq (M := Mi)] using
          (section12_card_subgroupOf_eq (section14_msigma_le Mi))
      rw [hcardMsigma]
      exact hpMsigma
    exact ((theorem_10_2_b hMiP.1).2).p_in_pi_of_p_dvd_card p hpMsigmaSub
  · intro p hpσ hpidx
    have hKi_norm_Kistar : Ki ≤ Subgroup.normalizer (Kistar : Set G) := by
      intro x hxKi
      exact (centralizer_le_normalizer Kistar) (hZdp.2.2.2.2 hxKi)
    have hcompKistar :
        (Kistar.subgroupOf (section14Z Mi Ki)).IsComplement' (Ki.subgroupOf (section14Z Mi Ki)) := by
      change
        ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)).IsComplement'
          (Ki.subgroupOf (Ki ⊔ section14KStar Mi Ki))
      exact
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := section14KStar Mi Ki) (R := Ki) hKi_norm_Kistar
          (by simpa [disjoint_iff, Kistar, inf_comm] using hZdp.2.2.2.1)
    have hcompKistar' :
        (Kistar.subgroupOf (section14Z M K)).IsComplement' (Ki.subgroupOf (section14Z M K)) := by
      simpa using (hZeqZi.symm ▸ hcompKistar)
    have hidx : (Kistar.subgroupOf (section14Z M K)).index = Nat.card Ki := by
      calc
        (Kistar.subgroupOf (section14Z M K)).index =
            Nat.card (Ki.subgroupOf (section14Z M K)) := by
              exact hcompKistar'.symm.index_eq_card
        _ = Nat.card Ki := natCard_subgroupOf_eq Ki (section14Z M K) hKiLeZ
    have hpKi : p.val ∣ Nat.card Ki := by
      simpa [hidx] using hpidx
    have hpKiSub : p.val ∣ Nat.card (Ki.subgroupOf Mi) := by
      simpa [section12_card_subgroupOf_eq hKi.1] using hpKi
    have hpκ : p ∈ section14KappaPrimes Mi :=
      hKi.2.p_in_pi_of_p_dvd_card p hpKiSub
    exact section14_kappa_subset_not_sigma (M := Mi) hpκ hpσ

private noncomputable def CFSG.section14_7_totalKstarJoin
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) : Subgroup G :=
  section14KStar M K ⊔
    sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
      section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2)

private theorem CFSG.section14_7_totalKstarJoin_eq_z
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14_7_totalKstarJoin (G := G) (M := M) (K := K) hM hK = section14Z M K := by
  classical
  let Z : Subgroup G := section14Z M K
  let J : Subgroup G := section14_7_totalKstarJoin (G := G) (M := M) (K := K) hM hK
  have hJleZ : J ≤ Z := by
    refine sup_le le_sup_right ?_
    refine sSup_le ?_
    rintro H ⟨⟨Mi, hMiFam⟩, rfl⟩
    rcases
        (section14_7_XiKiOfOvergroupFamily_spec
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
      ⟨_hXi, _hMi', _hKi, _hKstarKi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
        _hKiLeZ, hKistarLeK⟩
    exact hKistarLeK.trans le_sup_left
  let Jsub : Subgroup Z := J.subgroupOf Z
  have hJsub_top : Jsub = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hpprime hpJidx
    let q : Nat.Primes := ⟨p, hpprime⟩
    have hpZcard : p ∣ Nat.card Z := hpJidx.trans (Subgroup.index_dvd_card (H := Jsub))
    obtain ⟨X, hXIn⟩ :=
      section14_exists_primeOrderSubgroupIn_of_dvd_card
        (G := G) (A := Z) (p := q) hpZcard
    rcases hXIn with ⟨hXZ, hXcard⟩
    have hX : X ∈ section12PrimeOrderSubgroups Z :=
      ⟨hXZ, ⟨q, hXcard⟩⟩
    rcases
        section14_7_primeOrder_le_base_or_overgroupFamily_kstar_of_z
          (G := G) (M := M) (K := K) (X := X) hM hK hX with
      hXBase | ⟨Mi, hMiFam, hXKistar⟩
    · rcases
        section14_7_base_kstar_hall_sigma_in_z
          (G := G) (M := M) (K := K) hM hK with
        ⟨hBaseLeZ, hBaseHall⟩
      have hBaseLeJ : section14KStar M K ≤ J := le_sup_left
      have hBaseSubLeJsub : (section14KStar M K).subgroupOf Z ≤ Jsub := by
        intro x hx
        exact hBaseLeJ hx
      have hpBaseIdx : q.val ∣ ((section14KStar M K).subgroupOf Z).index := by
        have hmul :
            ((section14KStar M K).subgroupOf Z).relIndex Jsub * Jsub.index =
              ((section14KStar M K).subgroupOf Z).index :=
          Subgroup.relIndex_mul_index hBaseSubLeJsub
        rw [← hmul]
        exact dvd_mul_of_dvd_right hpJidx _
      have hpXcard : q.val ∣ Nat.card X := by
        rw [hXcard]
      have hpBaseCard : q.val ∣ Nat.card (section14KStar M K) := by
        exact hpXcard.trans (Subgroup.card_dvd_of_le hXBase)
      have hpBaseSubCard : q.val ∣ Nat.card ((section14KStar M K).subgroupOf Z) := by
        simpa [natCard_subgroupOf_eq (section14KStar M K) Z hBaseLeZ] using hpBaseCard
      have hpSigma : q ∈ section10SigmaPrimes M :=
        hBaseHall.p_in_pi_of_p_dvd_card q hpBaseSubCard
      exact (hBaseHall.p_in_pi_of_p_dvd_index q hpBaseIdx) hpSigma
    · let Kistar : Subgroup G :=
        section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
      rcases
          section14_7_kstarOfOvergroupFamily_hall_sigma_in_z
            (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam with
        ⟨hKistarLeZ, hKistarHall⟩
      have hKistarMem :
          Kistar ∈ Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
            section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 := by
        exact ⟨⟨Mi, hMiFam⟩, rfl⟩
      have hKistarLeJ : Kistar ≤ J := by
        intro x hx
        have hxSup :
            x ∈ sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
              section14_7_KstarOfOvergroupFamily
                (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) :=
          le_sSup hKistarMem hx
        exact
          (show
              sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
                section14_7_KstarOfOvergroupFamily
                  (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) ≤
                section14KStar M K ⊔
                  sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
                    section14_7_KstarOfOvergroupFamily
                  (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) from
            le_sup_right) hxSup
      have hKistarSubLeJsub : Kistar.subgroupOf Z ≤ Jsub := by
        intro x hx
        exact hKistarLeJ hx
      have hpKistarIdx : q.val ∣ (Kistar.subgroupOf Z).index := by
        have hmul :
            (Kistar.subgroupOf Z).relIndex Jsub * Jsub.index =
              (Kistar.subgroupOf Z).index :=
          Subgroup.relIndex_mul_index hKistarSubLeJsub
        rw [← hmul]
        exact dvd_mul_of_dvd_right hpJidx _
      have hpXcard : q.val ∣ Nat.card X := by
        rw [hXcard]
      have hpKistarCard : q.val ∣ Nat.card Kistar := by
        exact hpXcard.trans (Subgroup.card_dvd_of_le hXKistar)
      have hpKistarSubCard : q.val ∣ Nat.card (Kistar.subgroupOf Z) := by
        simpa [Kistar, natCard_subgroupOf_eq Kistar Z hKistarLeZ] using hpKistarCard
      have hpSigma : q ∈ section10SigmaPrimes Mi :=
        hKistarHall.p_in_pi_of_p_dvd_card q hpKistarSubCard
      exact (hKistarHall.p_in_pi_of_p_dvd_index q hpKistarIdx) hpSigma
  exact le_antisymm hJleZ ((Subgroup.subgroupOf_eq_top).1 hJsub_top)

private noncomputable def CFSG.section14_7_overgroupFamilyKstarJoin
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) : Subgroup G :=
  sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
    section14_7_KstarOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2)

private theorem CFSG.section14_7_overgroupFamilyKstarJoin_eq_k
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14_7_overgroupFamilyKstarJoin (G := G) (M := M) (K := K) hM hK = K := by
  classical
  let Z : Subgroup G := section14Z M K
  let Jfam : Subgroup G := section14_7_overgroupFamilyKstarJoin
    (G := G) (M := M) (K := K) hM hK
  obtain ⟨q, Xi, hXiPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
  have hXi : Xi ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXiPrime
  have hZdp : section12InternalDirectProduct K (section14KStar M K) Z := by
    simpa [Z, section14ZInternalDirectProduct] using
      (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK Xi hXi).2.2
  have hJfamLeK : Jfam ≤ K := by
    refine sSup_le ?_
    rintro H ⟨⟨Mi, hMiFam⟩, rfl⟩
    rcases
        (section14_7_XiKiOfOvergroupFamily_spec
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
      ⟨_hXi, _hMi', _hKi, _hKstarKi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
        _hKiLeZ, hKistarLeK⟩
    exact hKistarLeK
  have htop : section14KStar M K ⊔ Jfam = Z := by
    simpa [section14_7_totalKstarJoin, section14_7_overgroupFamilyKstarJoin, Jfam, Z] using
      section14_7_totalKstarJoin_eq_z (G := G) (M := M) (K := K) hM hK
  have hdisjFam :
      Disjoint (section14KStar M K) Jfam := by
    rw [disjoint_iff]
    apply le_antisymm
    · exact
        (inf_le_inf le_rfl hJfamLeK).trans <|
          by simpa [disjoint_iff, inf_comm] using hZdp.2.2.2.1
    · exact bot_le
  have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
    intro x hxK
    exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hxK)
  have hJfam_norm_Kstar : Jfam ≤ Subgroup.normalizer (section14KStar M K : Set G) :=
    hJfamLeK.trans hK_norm_Kstar
  have htop' : Jfam ⊔ section14KStar M K = Z := by
    simpa [sup_comm] using htop
  have hcompFam0 :
      ((section14KStar M K).subgroupOf (Jfam ⊔ section14KStar M K)).IsComplement'
        (Jfam.subgroupOf (Jfam ⊔ section14KStar M K)) := by
    simpa [Jfam] using
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := section14KStar M K) (R := Jfam) hJfam_norm_Kstar
        (by simpa [disjoint_iff, Jfam] using hdisjFam)
  have hcompFam :
      ((section14KStar M K).subgroupOf Z).IsComplement' (Jfam.subgroupOf Z) := by
    simpa using (htop'.symm ▸ hcompFam0)
  have hcompK :
      ((section14KStar M K).subgroupOf Z).IsComplement' (K.subgroupOf Z) := by
    change
      ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).IsComplement'
        (K.subgroupOf (K ⊔ section14KStar M K))
    exact
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := section14KStar M K) (R := K) hK_norm_Kstar
        (by simpa [disjoint_iff, inf_comm] using hZdp.2.2.2.1)
  have hcardJfam : Nat.card Jfam = Nat.card K := by
    have hidxFam : ((section14KStar M K).subgroupOf Z).index = Nat.card (Jfam.subgroupOf Z) := by
      exact hcompFam.symm.index_eq_card
    calc
      Nat.card Jfam = Nat.card (Jfam.subgroupOf Z) := by
        symm
        exact natCard_subgroupOf_eq Jfam Z (show Jfam ≤ Z from by
          rw [← htop]
          exact le_sup_right)
      _ = ((section14KStar M K).subgroupOf Z).index := hidxFam.symm
      _ = Nat.card K := by
        calc
          ((section14KStar M K).subgroupOf Z).index = Nat.card (K.subgroupOf Z) := by
            exact hcompK.symm.index_eq_card
          _ = Nat.card K := natCard_subgroupOf_eq K Z le_sup_left
  exact Subgroup.eq_of_le_of_card_ge hJfamLeK hcardJfam.ge

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_centralizer_conjBy
    (X : Subgroup G) (a : G) :
    (Subgroup.centralizer (X : Set G)).conjBy a =
      Subgroup.centralizer (X.conjBy a : Set G) := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro x hxX
    rcases Subgroup.mem_map.mp hxX with ⟨x0, hx0, rfl⟩
    have hcomm := hz x0 hx0
    have hcomm' := congrArg (fun t : G => a * t * a⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hy
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨a⁻¹ * y * a, ?_, by simp [mul_assoc, MulAut.conj_apply]⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hxX
    have hxX' : a * x * a⁻¹ ∈ X.conjBy a := by
      exact Subgroup.mem_map.mpr ⟨x, hxX, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hcomm := hy (a * x * a⁻¹) hxX'
    have hcomm' := congrArg (fun t : G => a⁻¹ * t * a) hcomm
    simpa [mul_assoc] using hcomm'

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_maximalSubgroupsContaining_centralizer_conjBy
    {X M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (g : G)
    (huniq : section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X.conjBy g : Set G)) =
      {M.conjBy g} := by
  ext H
  constructor
  · intro hH
    have hHinv :
        H.conjBy g⁻¹ ∈
          section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      refine ⟨section14_maximal_conjBy (G := G) hH.1 g⁻¹, ?_⟩
      intro x hxC
      have hxCgMap :
          g * x * g⁻¹ ∈ (Subgroup.centralizer (X : Set G)).conjBy g := by
        exact Subgroup.mem_map.mpr ⟨x, hxC, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hxCg : g * x * g⁻¹ ∈ Subgroup.centralizer (X.conjBy g : Set G) := by
        simpa [section14_centralizer_conjBy (G := G) X g] using hxCgMap
      have hxH : g * x * g⁻¹ ∈ H := hH.2 hxCg
      exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hxH, by simp [mul_assoc]⟩
    have hHinv_eq : H.conjBy g⁻¹ = M := by
      have hmem : H.conjBy g⁻¹ ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq] using hHinv
      simpa using hmem
    have hHeq : H = M.conjBy g := by
      calc
        H = (H.conjBy g⁻¹).conjBy g := (section11_conjBy_inv' (G := G) H g).symm
        _ = M.conjBy g := by rw [hHinv_eq]
    simp [hHeq]
  · intro hH
    simp at hH
    subst hH
    have hMcent :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      simp [huniq]
    refine ⟨section14_maximal_conjBy (G := G) hM g, ?_⟩
    intro x hxC
    have hxBackMap :
        g⁻¹ * x * g ∈ (Subgroup.centralizer (X.conjBy g : Set G)).conjBy g⁻¹ := by
      exact Subgroup.mem_map.mpr ⟨x, hxC, by simp [mul_assoc]⟩
    have hxBack : g⁻¹ * x * g ∈ Subgroup.centralizer (X : Set G) := by
      have hxBack' :
          g⁻¹ * x * g ∈ Subgroup.centralizer (((X.conjBy g).conjBy g⁻¹) : Set G) := by
        simpa [section14_centralizer_conjBy (G := G) (X := X.conjBy g) (a := g⁻¹)] using
          hxBackMap
      simpa [section11_conjBy_inv] using hxBack'
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hMcent.2 hxBack, by
      simp [MulAut.conj_apply, mul_assoc]⟩

private theorem CFSG.section14_7_not_conjugate_of_distinct_overgroupFamily
    {M K Mi Mj : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hMjFam : Mj ∈ section14_7_overgroupFamily K)
    (hij : Mi ≠ Mj) :
    ¬ section14ConjugateSubgroups Mj Mi := by
  classical
  let Xi := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Kj := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  let Kistar : Subgroup G := section14KStar Mi Ki
  let Kjstar : Subgroup G := section14KStar Mj Kj
  have hMiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
    simpa [Xi, Ki] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hMjSpec :
      section12HallSubgroupIn (section14KappaPrimes Mj) Kj Mj ∧
        Mj ∈ section14MFamilyP G := by
    rcases
        (section14_7_XiKiOfOvergroupFamily_spec
          (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam) with
      ⟨_hXj, _hMj, hKj, _hKstarKj, hMjP, _hMj_not_conj, _hZeqZj, _hXjLeKjstar, _hKjLeZ,
        _hKjstarLeK⟩
    exact ⟨hKj, hMjP⟩
  rcases hMiSpec with
    ⟨hXi, _hMi, hKi, _hKstarKi, hMiP, _hMi_not_conj, hZeqZi, hXiLeKistar, _hKiLeZ,
      _hKistarLeK⟩
  rcases hMjSpec with ⟨hKj, hMjP⟩
  rcases section14_7_kstarOfOvergroupFamily_hall_sigma_in_z
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam with
    ⟨hKistarLeZ, hHallI⟩
  rcases section14_7_kstarOfOvergroupFamily_hall_sigma_in_z
      (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam with
    ⟨hKjstarLeZ, hHallJraw⟩
  have hXiPrimeI : Xi ∈ section12PrimeOrderSubgroups Kistar := by
    exact ⟨hXiLeKistar, hXi.2⟩
  intro hconj
  rcases hconj with ⟨g, hMjEq⟩
  let Z : Subgroup G := section14Z M K
  have hσeq : section10SigmaPrimes Mj = section10SigmaPrimes Mi := by
    simpa [hMjEq] using section14_sigmaPrimes_conjBy (G := G) Mi g
  have hHallJ : IsHallSubgroup (section10SigmaPrimes Mi) (Kjstar.subgroupOf Z) := by
    rw [← hσeq]
    change
      IsHallSubgroup (section10SigmaPrimes Mj)
        ((section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam).subgroupOf
            (section14Z M K))
    exact hHallJraw
  have hZleMi : Z ≤ Mi := by
    change section14Z M K ≤ Mi
    rw [hZeqZi]
    exact sup_le hKi.1 <|
      (inf_le_left : section14KStar Mi Ki ≤ section10Msigma Mi).trans (section14_msigma_le Mi)
  have hZneTop : Z ≠ ⊤ := by
    intro hZtop
    have htop_le : (⊤ : Subgroup G) ≤ Mi := by simpa [Z, hZtop] using hZleMi
    exact hMiP.1.1 (top_le_iff.mp htop_le)
  have hsolvZ : IsSolvable Z :=
    IsMinCE.proper_subgroups_solvable Z (lt_top_iff_ne_top.mpr hZneTop)
  obtain ⟨z, hz⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := Z) hsolvZ hHallI hHallJ
  have hXiLeZ : Xi ≤ Z := hXiLeKistar.trans hKistarLeZ
  have hXiSubConjLe :
      (Xi.subgroupOf Z).map (MulAut.conj z).toMonoidHom ≤ Kjstar.subgroupOf Z := by
    calc
      (Xi.subgroupOf Z).map (MulAut.conj z).toMonoidHom ≤
          (Kistar.subgroupOf Z).map (MulAut.conj z).toMonoidHom := by
            exact Subgroup.map_mono (by
              intro x hx
              exact hXiLeKistar hx)
      _ = Kjstar.subgroupOf Z := by
        change
          Kjstar.subgroupOf Z =
            (Kistar.subgroupOf Z).map (MulAut.conj z).toMonoidHom at hz
        exact hz.symm
  have hXiConjLeKjstar : Xi.conjBy (z : G) ≤ Kjstar := by
    exact
      section14_conjBy_le_of_subgroupOf_conjBy_le
        (G := G) (H := Xi) (K := Kjstar) (M := Z) (g := (z : G))
        z.property hXiLeZ hXiSubConjLe
  have hXiConjPrimeJ : Xi.conjBy (z : G) ∈ section12PrimeOrderSubgroups Kjstar := by
    rcases hXi.2 with ⟨q, hXiCard⟩
    refine ⟨hXiConjLeKjstar, ⟨q, ?_⟩⟩
    simpa [section14_card_conjBy (G := G) Xi (z : G)] using hXiCard
  have huniqI0 :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Xi : Set G)) = {Mi} := by
    simpa [Kistar] using
      (proposition_14_2_c (G := G) (M := Mi) (K := Ki) hMiP hKi).2 Xi hXiPrimeI
  have hzMi : (z : G) ∈ Mi := hZleMi z.property
  have hMiConj : Mi.conjBy (z : G) = Mi := by
    exact
      section11_conjBy_eq_of_mem_normalizer
        (H := Mi) (Subgroup.le_normalizer hzMi)
  have huniqI :
      section9MaximalSubgroupsContaining
          (Subgroup.centralizer ((Xi.conjBy (z : G)) : Set G)) = {Mi} := by
    simpa [hMiConj] using
      section14_maximalSubgroupsContaining_centralizer_conjBy
        (G := G) hMiP.1 (z : G) huniqI0
  have huniqJ :
      section9MaximalSubgroupsContaining
          (Subgroup.centralizer ((Xi.conjBy (z : G)) : Set G)) = {Mj} := by
    simpa [Kjstar] using
      (proposition_14_2_c (G := G) (M := Mj) (K := Kj) hMjP hKj).2
        (Xi.conjBy (z : G)) hXiConjPrimeJ
  have hMjMem :
      Mj ∈ section9MaximalSubgroupsContaining
        (Subgroup.centralizer ((Xi.conjBy (z : G)) : Set G)) := by
    rw [huniqJ]
    simp
  have hMjEqMi : Mj = Mi := by
    have hsingle : Mj ∈ ({Mi} : Set (Subgroup G)) := by
      simpa [huniqI] using hMjMem
    simpa using hsingle
  exact hij hMjEqMi.symm

private theorem CFSG.section14_7_kstarOfOvergroupFamily_le_ki_of_distinct
    {M K Mi Mj : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hMjFam : Mj ∈ section14_7_overgroupFamily K)
    (hij : Mi ≠ Mj) :
    section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam ≤
      section14_7_KiOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam := by
  classical
  let Xi := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Xj := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  let Kj := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  let Kistar : Subgroup G := section14KStar Mi Ki
  let Kjstar : Subgroup G := section14KStar Mj Kj
  let Z : Subgroup G := section14Z M K
  have hMiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
    simpa [Xi, Ki] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hMjSpec :
      Xj ∈ section12PrimeOrderSubgroups K ∧
        Mj ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xj : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mj) Kj Mj ∧
        section14KStar M K ≤ Kj ∧
        Mj ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mj M ∧
        section14Z M K = section14Z Mj Kj ∧
        Xj ≤ section14KStar Mj Kj ∧
        Kj ≤ section14Z M K ∧
        section14KStar Mj Kj ≤ K := by
    simpa [Xj, Kj] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  rcases hMiSpec with
    ⟨_hXi, _hMi, hKi, _hKstarKi, hMiP, _hMi_not_conj, hZeqZi, _hXiLeKistar, hKiLeZ,
      _hKistarLeK⟩
  rcases hMjSpec with
    ⟨_hXj, _hMj, _hKj, _hKstarKj, hMjP, _hMj_not_conj, _hZeqZj, _hXjLeKjstar, _hKjLeZ,
      _hKjstarLeK⟩
  have hnotconj : ¬ section14ConjugateSubgroups Mj Mi :=
    section14_7_not_conjugate_of_distinct_overgroupFamily
      (G := G) (M := M) (K := K) hM hK hMiFam hMjFam hij
  have hnot : section12NotConjugate Mj Mi := by
    intro a hMa
    exact hnotconj ⟨a⁻¹, by
      simpa [section11_conjBy_inv] using congrArg (fun H => H.conjBy a⁻¹) hMa⟩
  have hσdis : Disjoint (section10SigmaPrimes Mi) (section10SigmaPrimes Mj) :=
    theorem_13_9 (G := G) hMiP.1 hMjP.1 hnot
  rcases
      section14_7_kstarOfOvergroupFamily_hall_sigma_in_z
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam with
    ⟨hKistarLeZ, hHallI⟩
  rcases
      section14_7_kstarOfOvergroupFamily_hall_sigma_in_z
        (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam with
    ⟨hKjstarLeZ, hHallJ⟩
  obtain ⟨q, X0, hX0PrimeIn⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := Ki) (section14_hall_kappa_ne_bot (G := G) hMiP hKi)
  have hX0 : X0 ∈ section12PrimeOrderSubgroups Ki :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
  have hZdp : section12InternalDirectProduct Ki Kistar (section14Z Mi Ki) := by
    change section14ZInternalDirectProduct Mi Ki
    exact (proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi X0 hX0).2.2
  have hKi_norm_Kistar : Ki ≤ Subgroup.normalizer (Kistar : Set G) := by
    intro x hxKi
    exact (centralizer_le_normalizer Kistar) (hZdp.2.2.2.2 hxKi)
  have hKistar_norm_Ki : Kistar ≤ Subgroup.normalizer (Ki : Set G) := by
    intro x hxKistar
    apply centralizer_le_normalizer Ki
    rw [Subgroup.mem_centralizer_iff]
    intro y hyKi
    exact (Subgroup.mem_centralizer_iff.mp (hZdp.2.2.2.2 hyKi) x hxKistar).symm
  have hcompKistar :
      (Kistar.subgroupOf (section14Z Mi Ki)).IsComplement' (Ki.subgroupOf (section14Z Mi Ki)) := by
    change
      ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)).IsComplement'
        (Ki.subgroupOf (Ki ⊔ section14KStar Mi Ki))
    exact
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := section14KStar Mi Ki) (R := Ki) hKi_norm_Kistar
        (by simpa [disjoint_iff, Kistar, inf_comm] using hZdp.2.2.2.1)
  have hcompKistar' :
      (Kistar.subgroupOf Z).IsComplement' (Ki.subgroupOf Z) := by
    change (Kistar.subgroupOf (section14Z M K)).IsComplement' (Ki.subgroupOf (section14Z M K))
    simpa using (hZeqZi.symm ▸ hcompKistar)
  have hKiNormal0Aux : (Ki.subgroupOf (Kistar ⊔ Ki)).Normal := by
    exact
      Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := Kistar) (N := Ki) hKistar_norm_Ki
  have hEqSup : Kistar ⊔ Ki = Ki ⊔ Kistar := sup_comm _ _
  have hKiNormal0' : (Ki.subgroupOf (Ki ⊔ Kistar)).Normal := by
    exact hEqSup ▸ hKiNormal0Aux
  have hKiNormal0 : (Ki.subgroupOf (section14Z Mi Ki)).Normal := by
    change (Ki.subgroupOf (Ki ⊔ Kistar)).Normal
    exact hKiNormal0'
  have hKiNormal : (Ki.subgroupOf Z).Normal := by
    change (Ki.subgroupOf (section14Z M K)).Normal
    simpa using (hZeqZi.symm ▸ hKiNormal0)
  letI : (Ki.subgroupOf Z).Normal := hKiNormal
  let φ : Z →* Z ⧸ (Ki.subgroupOf Z) := QuotientGroup.mk' (Ki.subgroupOf Z)
  have hMap_card_one : Nat.card ((Kjstar.subgroupOf Z).map φ) = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hpprime hpMap
    let r : Nat.Primes := ⟨p, hpprime⟩
    have hpKjSub : p ∣ Nat.card (Kjstar.subgroupOf Z) := by
      exact hpMap.trans (Subgroup.card_map_dvd (H := Kjstar.subgroupOf Z) φ)
    have hpSigmaJ : r ∈ section10SigmaPrimes Mj :=
      hHallJ.p_in_pi_of_p_dvd_card r hpKjSub
    have hpQuot :
        p ∣ Nat.card (Z ⧸ (Ki.subgroupOf Z)) := by
      exact hpMap.trans (Subgroup.card_subgroup_dvd_card ((Kjstar.subgroupOf Z).map φ))
    have hQuotCard :
        Nat.card (Z ⧸ (Ki.subgroupOf Z)) = Nat.card (Kistar.subgroupOf Z) := by
      exact Nat.card_congr hcompKistar'.QuotientMulEquiv.toEquiv
    have hpKistarSub : p ∣ Nat.card (Kistar.subgroupOf Z) := by
      rw [← hQuotCard]
      exact hpQuot
    have hpSigmaI : r ∈ section10SigmaPrimes Mi :=
      hHallI.p_in_pi_of_p_dvd_card r hpKistarSub
    have : r ∈ (⊥ : Set Nat.Primes) := hσdis.le_bot ⟨hpSigmaI, hpSigmaJ⟩
    simp at this
  have hMap_bot : (Kjstar.subgroupOf Z).map φ = ⊥ := by
    exact (Subgroup.eq_bot_iff_card (H := (Kjstar.subgroupOf Z).map φ)).2 hMap_card_one
  exact
    section14_7_subgroup_le_of_subgroupOf_quotient_map_eq_bot
      (G := G) (N := Ki) (L := Z) (C := Kjstar)
      hKjstarLeZ (by simpa [φ] using hMap_bot)

private noncomputable def CFSG.section14_7_otherKstarJoinOfOvergroupFamily
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hMiFam : Mi ∈ section14_7_overgroupFamily K) : Subgroup G :=
  section14KStar M K ⊔
    sSup (Set.range fun j : {Mj // Mj ∈ section14_7_overgroupFamily K ∧ Mj ≠ Mi} =>
      section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := j.1) hM hK j.2.1)

private theorem CFSG.section14_7_otherKstarJoinOfOvergroupFamily_le_ki
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    section14_7_otherKstarJoinOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam ≤
      section14_7_KiOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam := by
  classical
  let Xi := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hMiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
    simpa [Xi, Ki] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  rcases hMiSpec with
    ⟨_hXi, _hMi, _hKi, hKstarKi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar, _hKiLeZ,
      _hKistarLeK⟩
  refine sup_le hKstarKi ?_
  refine sSup_le ?_
  rintro H ⟨⟨Mj, hMjFam, hMjNe⟩, rfl⟩
  exact
    section14_7_kstarOfOvergroupFamily_le_ki_of_distinct
      (G := G) (M := M) (K := K) (Mi := Mi) (Mj := Mj) hM hK hMiFam hMjFam hMjNe.symm

private theorem CFSG.section14_7_otherKstarJoinOfOvergroupFamily_eq_ki
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    section14_7_otherKstarJoinOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam =
      section14_7_KiOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam := by
  classical
  let Xi := section14_7_XiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki := section14_7_KiOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Kistar : Subgroup G := section14KStar Mi Ki
  let J : Subgroup G := section14_7_otherKstarJoinOfOvergroupFamily
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Z : Subgroup G := section14Z M K
  have hMiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ section14KStar Mi Ki ∧
        Ki ≤ section14Z M K ∧
        section14KStar Mi Ki ≤ K := by
    simpa [Xi, Ki] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  rcases hMiSpec with
    ⟨_hXi, _hMi, hKi, _hKstarKi, hMiP, _hMi_not_conj, hZeqZi, _hXiLeKistar, hKiLeZ,
      _hKistarLeK⟩
  rcases
      section14_7_kstarOfOvergroupFamily_hall_sigma_in_z
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam with
    ⟨hKistarLeZ, _hHallI⟩
  obtain ⟨q, X0, hX0PrimeIn⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := Ki) (section14_hall_kappa_ne_bot (G := G) hMiP hKi)
  have hX0 : X0 ∈ section12PrimeOrderSubgroups Ki :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
  have hZdp : section12InternalDirectProduct Ki Kistar (section14Z Mi Ki) := by
    change section14ZInternalDirectProduct Mi Ki
    exact (proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi X0 hX0).2.2
  have hJleKi : J ≤ Ki :=
    section14_7_otherKstarJoinOfOvergroupFamily_le_ki
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hKi_norm_Kistar : Ki ≤ Subgroup.normalizer (Kistar : Set G) := by
    intro x hxKi
    exact (centralizer_le_normalizer Kistar) (hZdp.2.2.2.2 hxKi)
  have hJ_norm_Kistar : J ≤ Subgroup.normalizer (Kistar : Set G) :=
    hJleKi.trans hKi_norm_Kistar
  have hJleTotal :
      J ≤ section14_7_totalKstarJoin (G := G) (M := M) (K := K) hM hK := by
    refine sup_le ?_ ?_
    · exact le_sup_left
    · refine sSup_le ?_
      rintro H ⟨⟨Mj, hMjFam, _hMjNe⟩, rfl⟩
      intro x hx
      have hMem :
          section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam ∈
            Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
              section14_7_KstarOfOvergroupFamily
                (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 := by
        exact ⟨⟨Mj, hMjFam⟩, rfl⟩
      have hxSup :
          x ∈ sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
            section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) :=
        le_sSup hMem hx
      exact (show
          sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
            section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) ≤
            section14_7_totalKstarJoin (G := G) (M := M) (K := K) hM hK from
        le_sup_right) hxSup
  have hKistarLeTotal :
      Kistar ≤ section14_7_totalKstarJoin (G := G) (M := M) (K := K) hM hK := by
    intro x hx
    have hMem :
        section14_7_KstarOfOvergroupFamily
            (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam ∈
          Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
            section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 := by
      exact ⟨⟨Mi, hMiFam⟩, rfl⟩
    have hxSup :
        x ∈ sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
          section14_7_KstarOfOvergroupFamily
            (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) :=
      le_sSup hMem hx
    exact (show
        sSup (Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
          section14_7_KstarOfOvergroupFamily
            (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) ≤
          section14_7_totalKstarJoin (G := G) (M := M) (K := K) hM hK from
      le_sup_right) hxSup
  have hTotalLe :
      section14_7_totalKstarJoin (G := G) (M := M) (K := K) hM hK ≤ J ⊔ Kistar := by
    refine sup_le ?_ ?_
    · exact le_sup_of_le_left le_sup_left
    · refine sSup_le ?_
      rintro H ⟨⟨Mj, hMjFam⟩, rfl⟩
      by_cases hEq : Mj = Mi
      · subst hEq
        exact le_sup_right
      · have hMjLeJ :
            section14_7_KstarOfOvergroupFamily
                (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam ≤ J := by
          intro x hx
          have hMem :
              section14_7_KstarOfOvergroupFamily
                  (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam ∈
                Set.range fun j : {Mj // Mj ∈ section14_7_overgroupFamily K ∧ Mj ≠ Mi} =>
                  section14_7_KstarOfOvergroupFamily
                    (G := G) (M := M) (K := K) (Mi := j.1) hM hK j.2.1 := by
            exact ⟨⟨Mj, hMjFam, hEq⟩, rfl⟩
          have hxSup :
              x ∈ sSup (Set.range fun j : {Mj // Mj ∈ section14_7_overgroupFamily K ∧ Mj ≠ Mi} =>
                section14_7_KstarOfOvergroupFamily
                  (G := G) (M := M) (K := K) (Mi := j.1) hM hK j.2.1) :=
            le_sSup hMem hx
          exact (show
              sSup (Set.range fun j : {Mj // Mj ∈ section14_7_overgroupFamily K ∧ Mj ≠ Mi} =>
                section14_7_KstarOfOvergroupFamily
                  (G := G) (M := M) (K := K) (Mi := j.1) hM hK j.2.1) ≤ J from
            le_sup_right) hxSup
        exact hMjLeJ.trans le_sup_left
  have hJsupEqTotal :
      J ⊔ Kistar = section14_7_totalKstarJoin (G := G) (M := M) (K := K) hM hK := by
    exact le_antisymm (sup_le hJleTotal hKistarLeTotal) hTotalLe
  have hJsupEqZ : J ⊔ Kistar = Z := by
    rw [hJsupEqTotal]
    simpa [Z] using section14_7_totalKstarJoin_eq_z (G := G) (M := M) (K := K) hM hK
  have hdisjJ : Disjoint Kistar J := by
    rw [disjoint_iff]
    apply le_antisymm
    · exact
        (inf_le_inf le_rfl hJleKi).trans <|
          by simpa [disjoint_iff, Kistar, inf_comm] using hZdp.2.2.2.1
    · exact bot_le
  have hcompJ0 :
      (Kistar.subgroupOf (J ⊔ Kistar)).IsComplement' (J.subgroupOf (J ⊔ Kistar)) := by
    simpa [J, inf_comm] using
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := Kistar) (R := J) hJ_norm_Kistar
        (by simpa [disjoint_iff, J, inf_comm] using hdisjJ)
  have hcompJ :
      (Kistar.subgroupOf Z).IsComplement' (J.subgroupOf Z) := by
    exact hJsupEqZ ▸ hcompJ0
  have hcompKistar :
      (Kistar.subgroupOf Z).IsComplement' (Ki.subgroupOf Z) := by
    change (Kistar.subgroupOf (section14Z M K)).IsComplement'
      (Ki.subgroupOf (section14Z M K))
    have hcomp :
        (Kistar.subgroupOf (section14Z Mi Ki)).IsComplement' (Ki.subgroupOf (section14Z Mi Ki)) := by
      change
        ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)).IsComplement'
          (Ki.subgroupOf (Ki ⊔ section14KStar Mi Ki))
      exact
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := section14KStar Mi Ki) (R := Ki) hKi_norm_Kistar
          (by simpa [disjoint_iff, Kistar, inf_comm] using hZdp.2.2.2.1)
    simpa using (hZeqZi.symm ▸ hcomp)
  have hcardJ : Nat.card J = Nat.card Ki := by
    calc
      Nat.card J = Nat.card (J.subgroupOf Z) := by
        symm
        exact natCard_subgroupOf_eq J Z (hJleKi.trans hKiLeZ)
      _ = (Kistar.subgroupOf Z).index := hcompJ.symm.index_eq_card.symm
      _ = Nat.card Ki := by
        calc
          (Kistar.subgroupOf Z).index = Nat.card (Ki.subgroupOf Z) := by
            exact hcompKistar.symm.index_eq_card
          _ = Nat.card Ki := natCard_subgroupOf_eq Ki Z hKiLeZ
  exact Subgroup.eq_of_le_of_card_ge hJleKi hcardJ.ge

private noncomputable def CFSG.section14_7_factorUnion
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) : Set G :=
  (section14KStar M K : Set G) ∪
    ⋃ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
      (section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 : Set G)

public def CFSG.section14_7_TSet
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) : Set G :=
  (section14Z M K : Set G) \ section14_7_factorUnion (G := G) (M := M) (K := K) hM hK

omit [IsMinCE G] in
private theorem CFSG.section14_isPiElement_of_mem_hall
    {M K : Subgroup G} {π : Set Nat.Primes}
    (hK : section12HallSubgroupIn π K M)
    {x : G} (hx : x ∈ K) :
    section14IsPiElement π x := by
  intro p hpSupp
  have hpK : p ∈ subgroupPrimeSet K :=
    section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hx) hpSupp
  have hpKcard : p.val ∣ Nat.card K := by
    simpa [subgroupPrimeSet] using hpK
  have hpKsub : p.val ∣ Nat.card (K.subgroupOf M) := by
    simpa [section12_card_subgroupOf_eq hK.1] using hpKcard
  exact hK.2.p_in_pi_of_p_dvd_card p hpKsub

private theorem CFSG.section14_7_exists_alt2_of_mem_TSet
    {M K : Subgroup G} {t : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (ht : t ∈ section14_7_TSet (G := G) (M := M) (K := K) hM hK) :
    ∃ y y' : G, ∃ M0 K0 : Subgroup G,
      M0 ∈ section14MFamilyP G ∧
        section12HallSubgroupIn (section14KappaPrimes M0) K0 M0 ∧
        section14Z M K = section14Z M0 K0 ∧
        t = y * y' ∧
        section14SigmaLength y = 1 ∧
        y' ≠ 1 ∧
        section14IsPiElement (section14KappaPrimes M0) y' ∧
        y' ∈ elementCentralizerIn M0 y ∧
        M0 ∈ section14MsigmaElement y ∧
        y ∈ section14KStar M0 K0 ∧
        y' ∈ K0 := by
  classical
  have htZ : t ∈ section14Z M K := ht.1
  have htNotUnion :
      t ∉ section14_7_factorUnion (G := G) (M := M) (K := K) hM hK := ht.2
  have htNotBase : t ∉ section14KStar M K := by
    intro htBase
    exact htNotUnion (Or.inl htBase)
  have htNotFam :
      ∀ Mi : Subgroup G, ∀ hMiFam : Mi ∈ section14_7_overgroupFamily K,
        t ∉ section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam := by
    intro Mi hMiFam htMi
    exact htNotUnion <|
      Or.inr <| Set.mem_iUnion.2 ⟨⟨Mi, hMiFam⟩, by simpa using htMi⟩
  have htne : t ≠ 1 := by
    intro ht1
    exact htNotBase (by simp [ht1])
  obtain ⟨q, z, hz_zpowt, _hzZ, hzne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G)
      (B := section14Z M K) htZ htne
  let X : Subgroup G := Subgroup.zpowers z
  have hX :
      X ∈ section12PrimeOrderSubgroups (section14Z M K) := by
    simpa [X] using
      section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
  rcases
      section14_7_primeOrder_le_base_or_overgroupFamily_kstar_of_z
        (G := G) (M := M) (K := K) (X := X) hM hK hX with
    hXBase | ⟨Mi, hMiFam, hXFam⟩
  · obtain ⟨r, X0, hX0PrimeIn⟩ :=
      section14_c_exists_primeOrderSubgroupIn_of_ne_bot
        (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
    have hX0 : X0 ∈ section12PrimeOrderSubgroups K :=
      section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
    have hZdp : section12InternalDirectProduct K (section14KStar M K) (section14Z M K) := by
      simpa [section14ZInternalDirectProduct] using
        (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK X0 hX0).2.2
    let Z : Subgroup G := section14Z M K
    have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
      intro x hxK
      exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hxK)
    have hKstarNormal : ((section14KStar M K).subgroupOf Z).Normal := by
      change ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).Normal
      exact
        Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := K) (N := section14KStar M K) hK_norm_Kstar
    letI : ((section14KStar M K).subgroupOf Z).Normal := hKstarNormal
    have htop0 :
        (K.subgroupOf Z) ⊔ ((section14KStar M K).subgroupOf Z) = ⊤ := by
      change
        (K.subgroupOf (K ⊔ section14KStar M K)) ⊔
            ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)) = ⊤
      simpa only [Subgroup.subgroupOf_self] using
        (Subgroup.subgroupOf_sup
          (A := K) (A' := section14KStar M K) (B := K ⊔ section14KStar M K)
          le_sup_left le_sup_right).symm
    have htop :
        ((section14KStar M K).subgroupOf Z) ⊔ (K.subgroupOf Z) = ⊤ := by
      simpa [sup_comm] using htop0
    let tZ : Z := ⟨t, htZ⟩
    have htTop : tZ ∈ ((section14KStar M K).subgroupOf Z) ⊔ (K.subgroupOf Z) := by
      simp [htop]
    rcases
        (Subgroup.mem_sup_of_normal_left
          (x := tZ) (s := (section14KStar M K).subgroupOf Z) (t := K.subgroupOf Z)).1
          htTop with
      ⟨yKstar, hyKstar0, yK, hyK0, htEq0⟩
    let y : G := yKstar
    let y' : G := yK
    have hyKstar : y ∈ section14KStar M K := by
      simpa [y, Subgroup.mem_subgroupOf] using hyKstar0
    have hyK : y' ∈ K := by
      simpa [y', Subgroup.mem_subgroupOf] using hyK0
    have htEq : t = y * y' := by
      simpa [y, y'] using congrArg Subtype.val htEq0.symm
    have hy'ne : y' ≠ 1 := by
      intro hy'1
      exact htNotBase (by simpa [htEq, y, y', hy'1] using hyKstar)
    have hyne : y ≠ 1 := by
      intro hy1
      have htK : t ∈ K := by
        simpa [htEq, y, y', hy1] using hyK
      have hzK : z ∈ K := (Subgroup.zpowers_le.2 htK) hz_zpowt
      have hzKstar : z ∈ section14KStar M K := hXBase (Subgroup.mem_zpowers z)
      have hzbot : z ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hZdp.2.2.2.1 hzK hzKstar
      exact hzne (Subgroup.mem_bot.mp hzbot)
    have hyMσ : y ∈ section10Msigma M := hyKstar.1
    have hylen : section14SigmaLength y = 1 :=
      section14_sigmaLength_one_of_mem_msigma (G := G) hM.1 hyMσ hyne
    have hy'κ : section14IsPiElement (section14KappaPrimes M) y' :=
      section14_isPiElement_of_mem_hall (G := G) hK hyK
    have hy'cent : y' ∈ elementCentralizerIn M y := by
      refine ⟨hK.1 hyK, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr <|
        Subgroup.mem_centralizer_iff.mp hyKstar.2 y' hyK
    have hMy : M ∈ section14MsigmaElement y := by
      refine ⟨hM.1, ?_⟩
      simpa using hyMσ
    exact ⟨y, y', M, K, hM, hK, rfl, htEq, hylen, hy'ne, hy'κ, hy'cent, hMy, hyKstar, hyK⟩
  · let Ki : Subgroup G :=
      section14_7_KiOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
    let Kistar : Subgroup G := section14KStar Mi Ki
    have hMiSpec :
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
          Mi ∈ section14MFamilyP G ∧
          section14Z M K = section14Z Mi Ki := by
      rcases
          (section14_7_XiKiOfOvergroupFamily_spec
            (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
        ⟨_hXi, _hMi, hKi, _hKstarKi, hMiP, _hMi_not_conj, hZeqZi, _hXiLeKistar, _hKiLeZ,
          _hKistarLeK⟩
      exact ⟨hKi, hMiP, hZeqZi⟩
    rcases hMiSpec with ⟨hKi, hMiP, hZeqZi⟩
    obtain ⟨r, X0, hX0PrimeIn⟩ :=
      section14_c_exists_primeOrderSubgroupIn_of_ne_bot
        (G := G) (A := Ki) (section14_hall_kappa_ne_bot (G := G) hMiP hKi)
    have hX0 : X0 ∈ section12PrimeOrderSubgroups Ki :=
      section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
    have hZdp : section12InternalDirectProduct Ki Kistar (section14Z Mi Ki) := by
      change section14ZInternalDirectProduct Mi Ki
      exact (proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi X0 hX0).2.2
    let Z : Subgroup G := section14Z Mi Ki
    have htZi : t ∈ Z := by
      simpa [Z, hZeqZi] using htZ
    have hKi_norm_Kistar : Ki ≤ Subgroup.normalizer (Kistar : Set G) := by
      intro x hxKi
      exact (centralizer_le_normalizer Kistar) (hZdp.2.2.2.2 hxKi)
    have hKistarNormal : (Kistar.subgroupOf Z).Normal := by
      change ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)).Normal
      exact
        Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := Ki) (N := section14KStar Mi Ki) hKi_norm_Kistar
    letI : (Kistar.subgroupOf Z).Normal := hKistarNormal
    have htop0 : (Ki.subgroupOf Z) ⊔ (Kistar.subgroupOf Z) = ⊤ := by
      change
        (Ki.subgroupOf (Ki ⊔ section14KStar Mi Ki)) ⊔
            ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)) = ⊤
      simpa only [Subgroup.subgroupOf_self] using
        (Subgroup.subgroupOf_sup
          (A := Ki) (A' := section14KStar Mi Ki) (B := Ki ⊔ section14KStar Mi Ki)
          le_sup_left le_sup_right).symm
    have htop : (Kistar.subgroupOf Z) ⊔ (Ki.subgroupOf Z) = ⊤ := by
      simpa [sup_comm] using htop0
    let tZ : Z := ⟨t, htZi⟩
    have htTop : tZ ∈ (Kistar.subgroupOf Z) ⊔ (Ki.subgroupOf Z) := by
      simp [htop]
    rcases
        (Subgroup.mem_sup_of_normal_left
          (x := tZ) (s := Kistar.subgroupOf Z) (t := Ki.subgroupOf Z)).1 htTop with
      ⟨yKstar, hyKstar0, yK, hyK0, htEq0⟩
    let y : G := yKstar
    let y' : G := yK
    have hyKstar : y ∈ Kistar := by
      simpa [y, Kistar, Subgroup.mem_subgroupOf] using hyKstar0
    have hyK : y' ∈ Ki := by
      simpa [y', Subgroup.mem_subgroupOf] using hyK0
    have htEq : t = y * y' := by
      simpa [y, y'] using congrArg Subtype.val htEq0.symm
    have hy'ne : y' ≠ 1 := by
      intro hy'1
      exact htNotFam Mi hMiFam <|
        by simpa [section14_7_KstarOfOvergroupFamily, Ki, Kistar, htEq, y, y', hy'1] using hyKstar
    have hyne : y ≠ 1 := by
      intro hy1
      have htKi : t ∈ Ki := by
        simpa [htEq, y, y', hy1] using hyK
      have hzKi : z ∈ Ki := (Subgroup.zpowers_le.2 htKi) hz_zpowt
      have hzKstar : z ∈ Kistar := by
        simpa [section14_7_KstarOfOvergroupFamily, Ki, Kistar] using
          hXFam (Subgroup.mem_zpowers z)
      have hzbot : z ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hZdp.2.2.2.1 hzKi hzKstar
      exact hzne (Subgroup.mem_bot.mp hzbot)
    have hyMiσ : y ∈ section10Msigma Mi := by
      simpa [Kistar] using hyKstar.1
    have hylen : section14SigmaLength y = 1 :=
      section14_sigmaLength_one_of_mem_msigma (G := G) hMiP.1 hyMiσ hyne
    have hy'κ : section14IsPiElement (section14KappaPrimes Mi) y' :=
      section14_isPiElement_of_mem_hall (G := G) hKi hyK
    have hy'cent : y' ∈ elementCentralizerIn Mi y := by
      refine ⟨hKi.1 hyK, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr <|
        Subgroup.mem_centralizer_iff.mp hyKstar.2 y' hyK
    have hMiy : Mi ∈ section14MsigmaElement y := by
      refine ⟨hMiP.1, ?_⟩
      simpa using hyMiσ
    exact
      ⟨y, y', Mi, Ki, hMiP, hKi, hZeqZi, htEq, hylen, hy'ne, hy'κ, hy'cent, hMiy,
        hyKstar, hyK⟩

private theorem CFSG.section14_7_TSet_disjoint_tilde
    {M K H : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hH : H ∈ section9MaximalSubgroups G) :
    section14_7_TSet (G := G) (M := M) (K := K) hM hK ∩ section14Tilde H = ∅ := by
  ext t
  constructor
  · intro ht
    exfalso
    rcases ht with ⟨htT, htTilde⟩
    have htne : t ≠ 1 := by
      intro ht1
      exact htT.2 (Or.inl (by simp [ht1]))
    rcases htTilde with ⟨x, hxHσ, hxne, x', hx'R, htEq⟩
    have hAlt1 :
        ∃ a a' : G,
          t = a * a' ∧ section14SigmaLength a = 1 ∧ a' ∈ section14R a := by
      refine ⟨x, x', htEq, ?_, hx'R⟩
      exact section14_sigmaLength_one_of_mem_msigma (G := G) hH hxHσ hxne
    have hAlt2 :
      ∃ y y' : G, ∃ M0 : Subgroup G,
        t = y * y' ∧ section14SigmaLength y = 1 ∧ y' ≠ 1 ∧
          section14IsPiElement (section14KappaPrimes M0) y' ∧
          y' ∈ elementCentralizerIn M0 y ∧
          M0 ∈ section14MsigmaElement y := by
      rcases
          section14_7_exists_alt2_of_mem_TSet
            (G := G) (M := M) (K := K) hM hK htT with
        ⟨y, y', M0, _K0, _hM0, _hK0, _hZeq, htEq0, hylen0, hy'ne0, hy'κ0, hy'cent0, hM0y,
          _hyKstar0, _hyK0⟩
      exact ⟨y, y', M0, htEq0, hylen0, hy'ne0, hy'κ0, hy'cent0, hM0y⟩
    exact (lemma_14_6 (G := G) (g := t) htne).2 ⟨hAlt1, hAlt2⟩
  · intro ht
    simp at ht

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_zpowers_conjBy_inv
    (x g : G) :
    Subgroup.zpowers (g⁻¹ * x * g) = (Subgroup.zpowers x).conjBy g⁻¹ := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    exact Subgroup.mem_map.mpr ⟨x ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, by
      simpa [MulAut.conj_apply, mul_assoc] using
        (conj_zpow (i := n) (a := g⁻¹) (b := x)).symm⟩
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
      simpa [MulAut.conj_apply, mul_assoc] using
        (conj_zpow (i := n) (a := g⁻¹) (b := x))⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_isPiElement_conjBy_inv
    {π : Set Nat.Primes} {x g : G}
    (hx : section14IsPiElement π x) :
    section14IsPiElement π (g⁻¹ * x * g) := by
  intro p hp
  have hp' : p ∈ section14ElementPrimeSupport x := by
    have hcard :
        Nat.card (Subgroup.zpowers (g⁻¹ * x * g)) = Nat.card (Subgroup.zpowers x) := by
      rw [section14_zpowers_conjBy_inv (G := G) x g]
      simpa using section14_card_conjBy (G := G) (Subgroup.zpowers x) g⁻¹
    simpa [section14ElementPrimeSupport, subgroupPrimeSet, hcard] using hp
  exact hx hp'

private theorem CFSG.section14_7_mem_z_of_mem_TSet_of_conj_mem_z
    {M K : Subgroup G} {t g : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (ht : t ∈ section14_7_TSet (G := G) (M := M) (K := K) hM hK)
    (htgZ : g⁻¹ * t * g ∈ section14Z M K) :
    g ∈ section14Z M K := by
  classical
  rcases
      section14_7_exists_alt2_of_mem_TSet
        (G := G) (M := M) (K := K) hM hK ht with
    ⟨y, y', M0, K0, hM0, hK0, hZeqZ0, htEq, hylen, hy'ne, hy'κ, hy'cent, hM0y, hyK0star,
      hyK0⟩
  let K0star : Subgroup G := section14KStar M0 K0
  let Z0 : Subgroup G := section14Z M0 K0
  have hyne : y ≠ 1 := section14_sigmaLength_one_ne_one hylen
  have hyσ : section14ElementPrimeSupport y ⊆ section10SigmaPrimes M0 :=
    section14_primeSupport_subset_sigma_of_msigmaMember hM0y
  have hy'σc : section14ElementPrimeSupport y' ⊆ (section10SigmaPrimes M0)ᶜ := by
    intro p hpY' hpσ
    exact section14_kappa_subset_not_sigma (hy'κ hpY') hpσ
  have hyy'Comm : Commute y y' :=
    (Subgroup.mem_centralizer_singleton_iff.mp hy'cent.2).symm
  have hcop : Nat.Coprime (orderOf y) (orderOf y') := by
    simpa [Nat.coprime_comm] using
      section14_coprime_order_of_support_split hy'σc hyσ
  have hyT : y ∈ Subgroup.zpowers t := by
    have hyT0 : y ∈ Subgroup.zpowers (y * y') :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order hyy'Comm hcop
    simpa [htEq] using hyT0
  have hy'T : y' ∈ Subgroup.zpowers t := by
    have hy'T0 : y' ∈ Subgroup.zpowers (y' * y) :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order
        hyy'Comm.symm (by simpa [Nat.coprime_comm] using hcop)
    have hy'T1 : y' ∈ Subgroup.zpowers (y * y') := by
      simpa [hyy'Comm.eq] using hy'T0
    simpa [htEq] using hy'T1
  have hygT : g⁻¹ * y * g ∈ Subgroup.zpowers (g⁻¹ * t * g) := by
    rw [section14_zpowers_conjBy_inv (G := G) t g]
    exact Subgroup.mem_map.mpr ⟨y, hyT, by simp [mul_assoc]⟩
  have hy'gT : g⁻¹ * y' * g ∈ Subgroup.zpowers (g⁻¹ * t * g) := by
    rw [section14_zpowers_conjBy_inv (G := G) t g]
    exact Subgroup.mem_map.mpr ⟨y', hy'T, by simp [mul_assoc]⟩
  have hygσ : section14ElementPrimeSupport (g⁻¹ * y * g) ⊆ section10SigmaPrimes M0 :=
    section14_isPiElement_conjBy_inv (G := G) hyσ
  have hy'gσc :
      section14ElementPrimeSupport (g⁻¹ * y' * g) ⊆ (section10SigmaPrimes M0)ᶜ :=
    section14_isPiElement_conjBy_inv (G := G) hy'σc
  obtain ⟨r, X0, hX0PrimeIn⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K0) (section14_hall_kappa_ne_bot (G := G) hM0 hK0)
  have hX0 : X0 ∈ section12PrimeOrderSubgroups K0 :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
  have hZdp : section12InternalDirectProduct K0 K0star Z0 := by
    change section14ZInternalDirectProduct M0 K0
    exact (proposition_14_2_b1 (G := G) (M := M0) (K := K0) hM0 hK0 X0 hX0).2.2
  have htgZ0 : g⁻¹ * t * g ∈ Z0 := by
    simpa [hZeqZ0, Z0] using htgZ
  have hK0star_norm_K0 : K0star ≤ Subgroup.normalizer (K0 : Set G) := by
    intro x hxK0star
    apply centralizer_le_normalizer K0
    rw [Subgroup.mem_centralizer_iff]
    intro z hzK0
    exact Subgroup.mem_centralizer_iff.mp hxK0star.2 z hzK0
  have hK0Normal : (K0.subgroupOf Z0).Normal := by
    have hK0Normal0' : (K0.subgroupOf (K0star ⊔ K0)).Normal := by
      simpa [K0star, section14Z] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := K0star) (N := K0) hK0star_norm_K0)
    have hK0Normal0 : (K0.subgroupOf (K0 ⊔ K0star)).Normal := by
      exact (sup_comm K0star K0) ▸ hK0Normal0'
    change (K0.subgroupOf (K0 ⊔ K0star)).Normal
    exact hK0Normal0
  letI : (K0.subgroupOf Z0).Normal := hK0Normal
  have htop0 : (K0.subgroupOf Z0) ⊔ (K0star.subgroupOf Z0) = ⊤ := by
    change
      (K0.subgroupOf (K0 ⊔ section14KStar M0 K0)) ⊔
          ((section14KStar M0 K0).subgroupOf (K0 ⊔ section14KStar M0 K0)) = ⊤
    simpa only [Subgroup.subgroupOf_self] using
      (Subgroup.subgroupOf_sup
        (A := K0) (A' := section14KStar M0 K0) (B := K0 ⊔ section14KStar M0 K0)
        le_sup_left le_sup_right).symm
  let tgZ0 : Z0 := ⟨g⁻¹ * t * g, htgZ0⟩
  have htgTop : tgZ0 ∈ (K0.subgroupOf Z0) ⊔ (K0star.subgroupOf Z0) := by
    simp [htop0]
  rcases
      (Subgroup.mem_sup_of_normal_left
        (x := tgZ0) (s := K0.subgroupOf Z0) (t := K0star.subgroupOf Z0)).1
        htgTop with
    ⟨uK0, huK00, vK0star, hvK0star0, htgEq0⟩
  let u : G := uK0
  let v : G := vK0star
  have huK0 : u ∈ K0 := by
    simpa [u, Subgroup.mem_subgroupOf] using huK00
  have hvK0star : v ∈ K0star := by
    simpa [v, K0star, Subgroup.mem_subgroupOf] using hvK0star0
  have htgEq : g⁻¹ * t * g = u * v := by
    simpa [u, v] using congrArg Subtype.val htgEq0.symm
  have huσc : section14ElementPrimeSupport u ⊆ (section10SigmaPrimes M0)ᶜ := by
    intro p hpU hpσ
    exact section14_kappa_subset_not_sigma
      ((section14_isPiElement_of_mem_hall (G := G) hK0 huK0) hpU) hpσ
  have hM0v : M0 ∈ section14MsigmaElement v := by
    refine ⟨hM0.1, ?_⟩
    simpa [K0star] using hvK0star.1
  have hvσ : section14ElementPrimeSupport v ⊆ section10SigmaPrimes M0 :=
    section14_primeSupport_subset_sigma_of_msigmaMember hM0v
  have huvComm : Commute u v := by
    exact Subgroup.mem_centralizer_iff.mp hvK0star.2 u huK0
  have huvCop : Nat.Coprime (orderOf u) (orderOf v) :=
    section14_coprime_order_of_support_split huσc hvσ
  have hygK0star : g⁻¹ * y * g ∈ K0star := by
    have hygZv : g⁻¹ * y * g ∈ Subgroup.zpowers v := by
      exact
        section14_mem_zpowers_right_of_support_subset
          huvComm huvCop huσc hvσ
          (by simpa [htgEq] using hygT) hygσ
    exact (Subgroup.zpowers_le.2 hvK0star) hygZv
  have hy'gK0 : g⁻¹ * y' * g ∈ K0 := by
    have hy'gZu : g⁻¹ * y' * g ∈ Subgroup.zpowers u := by
      exact
        section14_mem_zpowers_left_of_support_subset
          huvComm huvCop huσc hvσ
          (by simpa [htgEq] using hy'gT) hy'gσc
    exact (Subgroup.zpowers_le.2 huK0) hy'gZu
  have hygNe : g⁻¹ * y * g ≠ 1 := by
    intro hy1
    apply hyne
    have hconj := congrArg (fun z : G => g * z * g⁻¹) hy1
    simpa [mul_assoc] using hconj
  have hy'gNe : g⁻¹ * y' * g ≠ 1 := by
    intro hy1
    apply hy'ne
    have hconj := congrArg (fun z : G => g * z * g⁻¹) hy1
    simpa [mul_assoc] using hconj
  have hyM0 : y ∈ M0 := section14_msigma_le M0 (hM0y.2 (by simp))
  have hgM0 : g ∈ M0 := by
    by_contra hgNotM0
    have hgInvNotM0 : g⁻¹ ∉ M0 := by
      intro hgInvM0
      exact hgNotM0 (by simpa using M0.inv_mem hgInvM0)
    have hdisj :
        K0star ⊓ M0.conjBy g⁻¹ = ⊥ :=
      (proposition_14_2_d (G := G) (M := M0) (K := K0) hM0 hK0).1 g⁻¹ hgInvNotM0
    have hygMgInv : g⁻¹ * y * g ∈ M0.conjBy g⁻¹ := by
      exact Subgroup.mem_map.mpr ⟨y, hyM0, by simp [mul_assoc]⟩
    have hygInf : g⁻¹ * y * g ∈ K0star ⊓ M0.conjBy g⁻¹ := ⟨hygK0star, hygMgInv⟩
    have hygBot : g⁻¹ * y * g ∈ (⊥ : Subgroup G) := by
      simpa [hdisj] using hygInf
    exact hygNe (Subgroup.mem_bot.mp hygBot)
  have hgZ0 : g ∈ Z0 := by
    by_contra hgNotZ0
    have hgInvNotZ0 : g⁻¹ ∉ Z0 := by
      intro hgInvZ0
      exact hgNotZ0 (by simpa using Z0.inv_mem hgInvZ0)
    have hdisj :
        K0 ⊓ K0.conjBy g⁻¹ = ⊥ :=
      (proposition_14_2_d (G := G) (M := M0) (K := K0) hM0 hK0).2
        g⁻¹ (M0.inv_mem hgM0) hgInvNotZ0
    have hy'gKgInv : g⁻¹ * y' * g ∈ K0.conjBy g⁻¹ := by
      exact Subgroup.mem_map.mpr ⟨y', hyK0, by simp [mul_assoc]⟩
    have hy'gInf : g⁻¹ * y' * g ∈ K0 ⊓ K0.conjBy g⁻¹ := ⟨hy'gK0, hy'gKgInv⟩
    have hy'gBot : g⁻¹ * y' * g ∈ (⊥ : Subgroup G) := by
      simpa [hdisj] using hy'gInf
    exact hy'gNe (Subgroup.mem_bot.mp hy'gBot)
  simpa [hZeqZ0, Z0] using hgZ0

private theorem CFSG.section14_7_TSet_nonempty
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    (section14_7_TSet (G := G) (M := M) (K := K) hM hK).Nonempty := by
  classical
  obtain ⟨q, X0, hX0PrimeIn⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
  have hX0 : X0 ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
  have hZdp : section12InternalDirectProduct K (section14KStar M K) (section14Z M K) := by
    simpa [section14ZInternalDirectProduct] using
      (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK X0 hX0).2.2
  have hKstarNe : section14KStar M K ≠ ⊥ :=
    (proposition_14_2_c (G := G) (M := M) (K := K) hM hK).1
  haveI : Nontrivial ↥(section14KStar M K) :=
    (Subgroup.nontrivial_iff_ne_bot (H := section14KStar M K)).2 hKstarNe
  have hKNe : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM hK
  haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot (H := K)).2 hKNe
  obtain ⟨y, hyKstar, hyne⟩ := Subgroup.exists_ne_one_of_nontrivial (section14KStar M K)
  obtain ⟨y', hyK, hy'ne⟩ := Subgroup.exists_ne_one_of_nontrivial K
  let t : G := y * y'
  have hyy'Comm : Commute y y' := by
    exact (Subgroup.mem_centralizer_iff.mp hyKstar.2 y' hyK).symm
  have htZ : t ∈ section14Z M K := by
    change y * y' ∈ K ⊔ section14KStar M K
    simpa [t, hyy'Comm.eq] using Subgroup.mul_mem_sup hyK hyKstar
  have hyNotK : y ∉ K := by
    intro hyK'
    have hyBot : y ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hZdp.2.2.2.1 hyK' hyKstar
    exact hyne (Subgroup.mem_bot.mp hyBot)
  have htNotBase : t ∉ section14KStar M K := by
    intro htBase
    have hy'Kstar : y' ∈ section14KStar M K := by
      have hy'Eq : y' = y⁻¹ * t := by
        dsimp [t]
        group
      rw [hy'Eq]
      exact (section14KStar M K).mul_mem ((section14KStar M K).inv_mem hyKstar) htBase
    have hy'Bot : y' ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hZdp.2.2.2.1 hyK hy'Kstar
    exact hy'ne (Subgroup.mem_bot.mp hy'Bot)
  have htNotFam :
      ∀ Mi : Subgroup G, ∀ hMiFam : Mi ∈ section14_7_overgroupFamily K,
        t ∉ section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam := by
    intro Mi hMiFam htMi
    rcases
        (section14_7_XiKiOfOvergroupFamily_spec
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
      ⟨_hXi, _hMi, _hKi, _hKstarKi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar, _hKiLeZ,
        hKistarLeK⟩
    have htK : t ∈ K := by
      simpa [section14_7_KstarOfOvergroupFamily] using hKistarLeK htMi
    have hyK' : y ∈ K := by
      have hyEq : y = t * y'⁻¹ := by
        dsimp [t]
        group
      rw [hyEq]
      exact K.mul_mem htK (K.inv_mem hyK)
    exact hyNotK hyK'
  refine ⟨t, ?_⟩
  exact ⟨htZ, by
    intro htUnion
    rcases htUnion with htBase | htFam
    · exact htNotBase htBase
    · rcases Set.mem_iUnion.mp htFam with ⟨i, hi⟩
      exact htNotFam i.1 i.2 (by simpa using hi)⟩

private theorem CFSG.section14_7_TSet_inter_setConjBy_eq_empty_of_not_mem_z
    {M K : Subgroup G} {g : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hgZ : g ∉ section14Z M K) :
    section14_7_TSet (G := G) (M := M) (K := K) hM hK ∩
        section14SetConjBy (section14_7_TSet (G := G) (M := M) (K := K) hM hK) g = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro t ht
  rcases ht with ⟨htT, htConj⟩
  rcases htConj with ⟨t0, ht0T, rfl⟩
  exact hgZ <|
    section14_7_mem_z_of_mem_TSet_of_conj_mem_z
      (G := G) (M := M) (K := K) hM hK ht0T htT.1

private theorem CFSG.section14_7_normalizer_TSet_le_z
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Subgroup.normalizer (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ≤
      section14Z M K := by
  rcases section14_7_TSet_nonempty (G := G) (M := M) (K := K) hM hK with ⟨t, htT⟩
  intro g hgNorm
  have htConj : g⁻¹ * t * g ∈ section14_7_TSet (G := G) (M := M) (K := K) hM hK := by
    have hnorm :
        g⁻¹ ∈ Subgroup.normalizer
          (section14_7_TSet (G := G) (M := M) (K := K) hM hK) :=
      (Subgroup.normalizer
        (section14_7_TSet (G := G) (M := M) (K := K) hM hK)).inv_mem hgNorm
    change
        ∀ n : G,
          n ∈ section14_7_TSet (G := G) (M := M) (K := K) hM hK ↔
            g⁻¹ * n * (g⁻¹)⁻¹ ∈ section14_7_TSet (G := G) (M := M) (K := K) hM hK at hnorm
    simpa using (hnorm t).1 htT
  exact
    section14_7_mem_z_of_mem_TSet_of_conj_mem_z
      (G := G) (M := M) (K := K) hM hK htT htConj.1

private theorem CFSG.section14_7_factorUnion_conj_iff_of_mem_z
    {M K : Subgroup G} {g x : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hgZ : g ∈ section14Z M K) :
    x ∈ section14_7_factorUnion (G := G) (M := M) (K := K) hM hK ↔
      g * x * g⁻¹ ∈ section14_7_factorUnion (G := G) (M := M) (K := K) hM hK := by
  classical
  have hBaseNorm :
      section14Z M K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
    obtain ⟨q, X0, hX0PrimeIn⟩ :=
      section14_c_exists_primeOrderSubgroupIn_of_ne_bot
        (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
    have hX0 : X0 ∈ section12PrimeOrderSubgroups K :=
      section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
    have hZdp : section12InternalDirectProduct K (section14KStar M K) (section14Z M K) := by
      simpa [section14ZInternalDirectProduct] using
        (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK X0 hX0).2.2
    have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
      intro y hyK
      exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hyK)
    have hBaseNormal : ((section14KStar M K).subgroupOf (section14Z M K)).Normal := by
      change ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).Normal
      exact
        Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := K) (N := section14KStar M K) hK_norm_Kstar
    letI : ((section14KStar M K).subgroupOf (section14Z M K)).Normal := hBaseNormal
    exact
      Subgroup.le_normalizer_of_normal_subgroupOf
        (H := section14KStar M K) (K := section14Z M K) le_sup_right
  have hFamNorm :
      ∀ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
        section14Z M K ≤ Subgroup.normalizer
          ((section14_7_KstarOfOvergroupFamily
            (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 : Subgroup G) : Set G) := by
    intro i
    let Mi : Subgroup G := i.1
    let Ki : Subgroup G :=
      section14_7_KiOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK i.2
    let Kistar : Subgroup G :=
      section14_7_KstarOfOvergroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK i.2
    rcases
        (section14_7_XiKiOfOvergroupFamily_spec
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK i.2) with
      ⟨_hXi, _hMi, hKi, _hKstarLeKi, hMiP, _hMi_not_conj, hZeqZi, _hXiLeKistar, _hKiLeZ,
        _hKistarLeK⟩
    obtain ⟨r, X0, hX0PrimeIn⟩ :=
      section14_c_exists_primeOrderSubgroupIn_of_ne_bot
        (G := G) (A := Ki) (section14_hall_kappa_ne_bot (G := G) hMiP hKi)
    have hX0 : X0 ∈ section12PrimeOrderSubgroups Ki :=
      section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
    have hZdp : section12InternalDirectProduct Ki Kistar (section14Z Mi Ki) := by
      change section14ZInternalDirectProduct Mi Ki
      exact (proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi X0 hX0).2.2
    have hKi_norm_Kistar : Ki ≤ Subgroup.normalizer (Kistar : Set G) := by
      intro y hyKi
      exact (centralizer_le_normalizer Kistar) (hZdp.2.2.2.2 hyKi)
    have hKistarNormal : (Kistar.subgroupOf (section14Z Mi Ki)).Normal := by
      change ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)).Normal
      exact
        Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := Ki) (N := section14KStar Mi Ki) hKi_norm_Kistar
    letI : (Kistar.subgroupOf (section14Z Mi Ki)).Normal := hKistarNormal
    have hNormZi : section14Z Mi Ki ≤ Subgroup.normalizer (Kistar : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf
        (H := Kistar) (K := section14Z Mi Ki) le_sup_right
    simpa [hZeqZi, Mi, Ki, Kistar] using hNormZi
  constructor
  · intro hx
    rcases hx with hxBase | hxFam
    · exact Or.inl <| (Subgroup.mem_normalizer_iff.mp (hBaseNorm hgZ) x).1 hxBase
    · rcases Set.mem_iUnion.mp hxFam with ⟨i, hi⟩
      exact Or.inr <| Set.mem_iUnion.mpr ⟨i, (Subgroup.mem_normalizer_iff.mp (hFamNorm i hgZ) x).1 hi⟩
  · intro hx
    rcases hx with hxBase | hxFam
    · exact Or.inl <| (Subgroup.mem_normalizer_iff.mp (hBaseNorm hgZ) x).2 hxBase
    · rcases Set.mem_iUnion.mp hxFam with ⟨i, hi⟩
      exact Or.inr <| Set.mem_iUnion.mpr ⟨i, (Subgroup.mem_normalizer_iff.mp (hFamNorm i hgZ) x).2 hi⟩

private theorem CFSG.section14_7_z_le_normalizer_TSet
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14Z M K ≤
      Subgroup.normalizer (section14_7_TSet (G := G) (M := M) (K := K) hM hK) := by
  intro g hgZ
  change
      ∀ t : G,
        t ∈ section14_7_TSet (G := G) (M := M) (K := K) hM hK ↔
          g * t * g⁻¹ ∈ section14_7_TSet (G := G) (M := M) (K := K) hM hK
  intro t
  have hZNorm : g ∈ Subgroup.normalizer (section14Z M K) :=
    (section14Z M K).le_normalizer hgZ
  have hUnionNorm :
      t ∈ section14_7_factorUnion (G := G) (M := M) (K := K) hM hK ↔
        g * t * g⁻¹ ∈ section14_7_factorUnion (G := G) (M := M) (K := K) hM hK :=
    section14_7_factorUnion_conj_iff_of_mem_z
      (G := G) (M := M) (K := K) hM hK hgZ
  constructor
  · intro ht
    refine ⟨(Subgroup.mem_normalizer_iff.mp hZNorm t).1 ht.1, ?_⟩
    intro hgtUnion
    exact ht.2 (hUnionNorm.2 hgtUnion)
  · intro hgt
    refine ⟨(Subgroup.mem_normalizer_iff.mp hZNorm t).2 hgt.1, ?_⟩
    intro htUnion
    exact hgt.2 (hUnionNorm.1 htUnion)

private theorem CFSG.section14_7_normalizer_TSet_eq_z
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Subgroup.normalizer (section14_7_TSet (G := G) (M := M) (K := K) hM hK) =
      section14Z M K := by
  exact le_antisymm
    (section14_7_normalizer_TSet_le_z (G := G) (M := M) (K := K) hM hK)
    (section14_7_z_le_normalizer_TSet (G := G) (M := M) (K := K) hM hK)

private theorem CFSG.section14_7_TSet_ti
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14TISet (section14_7_TSet (G := G) (M := M) (K := K) hM hK) := by
  refine ⟨section14_7_TSet_nonempty (G := G) (M := M) (K := K) hM hK, ?_⟩
  intro g hgNorm
  have hgNotZ : g ∉ section14Z M K := by
    intro hgZ
    exact hgNorm ((section14_7_z_le_normalizer_TSet (G := G) (M := M) (K := K) hM hK) hgZ)
  have hEmpty :
      section14_7_TSet (G := G) (M := M) (K := K) hM hK ∩
        section14SetConjBy (section14_7_TSet (G := G) (M := M) (K := K) hM hK) g = ∅ :=
    section14_7_TSet_inter_setConjBy_eq_empty_of_not_mem_z
      (G := G) (M := M) (K := K) hM hK hgNotZ
  simp [hEmpty]

public theorem CFSG.section14_7_conjClosure_TSet_disjoint_conjClosure_tilde
    {M K H : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hH : H ∈ section9MaximalSubgroups G) :
    section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∩
        section14ConjugacyClosure (section14Tilde H) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  rcases hx with ⟨hxT, hxTilde⟩
  rcases hxT with ⟨t, htT, a, hxa⟩
  rcases hxTilde with ⟨u, huTilde, b, hxb⟩
  let g : G := b * a⁻¹
  have htEq : t = g⁻¹ * u * g := by
    have hEq : a⁻¹ * t * a = b⁻¹ * u * b := hxa.symm.trans hxb
    have hconj := congrArg (fun z : G => a * z * a⁻¹) hEq
    simpa [g, mul_assoc] using hconj
  have htTilde : t ∈ section14Tilde (H.conjBy g⁻¹) := by
    simpa [htEq, g] using
      (section14_mem_tilde_conjBy (G := G) (M := H) (g := u) (a := g) huTilde)
  have hHg : H.conjBy g⁻¹ ∈ section9MaximalSubgroups G :=
    section14_maximal_conjBy (G := G) hH g⁻¹
  exact
    (Set.eq_empty_iff_forall_notMem.mp
      (section14_7_TSet_disjoint_tilde (G := G) (M := M) (K := K) (H := H.conjBy g⁻¹)
        hM hK hHg))
      t ⟨htT, htTilde⟩

private theorem CFSG.section14_7_conjClosure_tilde_disjoint_of_distinct_overgroupFamily
    {M K Mi Mj : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hMjFam : Mj ∈ section14_7_overgroupFamily K)
    (hij : Mi ≠ Mj) :
    section14ConjugacyClosure (section14Tilde Mi) ∩
      section14ConjugacyClosure (section14Tilde Mj) = ∅ := by
  have hMiFam' := hMiFam
  have hMjFam' := hMjFam
  rcases hMiFam with ⟨Xi, _hXi, hMi⟩
  rcases hMjFam with ⟨Xj, _hXj, hMj⟩
  simpa [Set.inter_comm] using
    section14_conjClosure_tilde_disjoint_of_not_conjugate
      (G := G) (M₁ := Mi) (M₂ := Mj) hMi.1 hMj.1
      (section14_7_not_conjugate_of_distinct_overgroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) (Mj := Mj) hM hK hMiFam' hMjFam' hij)


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_one_not_mem_conjClosure_of_one_not_mem
    {T : Set G} (hT1 : 1 ∉ T) :
    1 ∉ section14ConjugacyClosure T := by
  intro h1
  rcases h1 with ⟨t, ht, a, hEq⟩
  have ht1 : t = 1 := by
    have hconj := congrArg (fun z : G => a * z * a⁻¹) hEq
    simpa [mul_assoc] using hconj.symm
  exact hT1 (ht1 ▸ ht)

private theorem CFSG.section14_one_not_mem_tilde
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    1 ∉ section14Tilde M := by
  intro h1
  rcases h1 with ⟨x, hxMσ, hxne, r, hr, hEq⟩
  by_cases hr1 : r = 1
  · have hx1 : x = 1 := by simpa [hr1] using hEq.symm
    exact hxne hx1
  · have hrne : r ≠ 1 := hr1
    have hMx : M ∈ section14MsigmaElement x := ⟨hM, by simpa using hxMσ⟩
    obtain ⟨_hx, hσx, hcardx⟩ :=
      section14_nonsingleton_of_mem_R_ne_one (G := G) hr hrne
    let π : Set Nat.Primes := section10SigmaPrimes (section14N x)
    have hxπc : section14ElementPrimeSupport x ⊆ πᶜ := by
      intro p hpX hpπ
      rcases (by
        simpa [π, section12Tau2Primes] using
          section14_primeSupport_subset_tau2N_of_mem_R_ne_one
            (G := G) hr hrne hpX) with
        ⟨hp_not_π, _hprank⟩
      exact hp_not_π hpπ
    have hrπ : section14ElementPrimeSupport r ⊆ π := by
      simpa [π] using section14_primeSupport_subset_sigmaN_of_mem_R (G := G) hr
    have hRdef :
        section14R x =
          elementCentralizerIn (section10Msigma (section14N x)) x := by
      simpa using (theorem_14_4_a (G := G) (x := x) hxne hσx hcardx hMx).1
    have hrCx : r ∈ elementCentralizerIn (section10Msigma (section14N x)) x := by
      simpa [hRdef] using hr
    have hxrComm : Commute x r :=
      (Subgroup.mem_centralizer_singleton_iff.mp hrCx.2).symm
    have hcop : Nat.Coprime (orderOf x) (orderOf r) :=
      section14_coprime_order_of_support_split (π := π) hxπc hrπ
    have hxZpow : x ∈ Subgroup.zpowers (x * r) :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order hxrComm hcop
    have hxOne : x ∈ Subgroup.zpowers (1 : G) := by
      simpa [hEq] using hxZpow
    exact hxne (by simpa using hxOne)

public theorem CFSG.section14_one_not_mem_conjClosure_tilde
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    1 ∉ section14ConjugacyClosure (section14Tilde M) := by
  exact section14_one_not_mem_conjClosure_of_one_not_mem
    (G := G) (T := section14Tilde M) (section14_one_not_mem_tilde (G := G) hM)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_card_conjClosure_eq_card_mul_index_of_ti
    {T : Set G}
    (hT1 : 1 ∉ T)
    (hTti : section14TISet T) :
    Nat.card (section14ConjugacyClosure T) = Nat.card T * (Subgroup.normalizer T).index := by
  classical
  let N : Subgroup G := Subgroup.normalizer T
  let Ω := Quotient (QuotientGroup.rightRel N)
  let T0 := {t : G // t ∈ T}
  let f : Ω × T0 → {x : G // x ∈ section14ConjugacyClosure T} := fun qt =>
    let a : G := Quotient.out qt.1
    ⟨a⁻¹ * qt.2.1 * a, ⟨qt.2.1, qt.2.2, a, rfl⟩⟩
  have hfBij : Function.Bijective f := by
    constructor
    · intro qt1 qt2 hEq
      rcases qt1 with ⟨q1, t1⟩
      rcases qt2 with ⟨q2, t2⟩
      let a1 : G := Quotient.out q1
      let a2 : G := Quotient.out q2
      have hval : a1⁻¹ * t1.1 * a1 = a2⁻¹ * t2.1 * a2 := congrArg Subtype.val hEq
      by_cases hq : q1 = q2
      · have ha : a2 = a1 := by simpa [a1, a2] using congrArg Quotient.out hq.symm
        have ht : t1 = t2 := by
          apply Subtype.ext
          rw [ha] at hval
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, mul_assoc] using hconj
        cases hq
        cases ht
        rfl
      · have hgNotN : a2 * a1⁻¹ ∉ N := by
          intro hgN
          apply hq
          calc
            q1 = Quotient.mk'' a1 := (Quotient.out_eq' q1).symm
            _ = Quotient.mk'' a2 := Quotient.sound' (QuotientGroup.rightRel_apply.mpr hgN)
            _ = q2 := Quotient.out_eq' q2
        have ht1Conj : t1.1 ∈ section14SetConjBy T (a2 * a1⁻¹) := by
          refine ⟨t2.1, t2.2, ?_⟩
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, a2, mul_assoc] using hconj
        have ht1one : t1.1 = 1 := by
          simpa using (hTti.2 (a2 * a1⁻¹) hgNotN ⟨t1.2, ht1Conj⟩)
        exact False.elim (hT1 (ht1one ▸ t1.2))
    · intro x
      rcases x.2 with ⟨t, htT, g, hxg⟩
      let q : Ω := Quotient.mk'' g
      let a : G := Quotient.out q
      have hgaN : g * a⁻¹ ∈ N := by
        have hqa : (Quotient.mk'' a : Ω) = Quotient.mk'' g := by
          simp [q, a]
        exact QuotientGroup.rightRel_apply.mp (Quotient.exact' hqa)
      let n : G := g * a⁻¹
      have hnInvNorm : n⁻¹ ∈ N := N.inv_mem hgaN
      have ht' : n⁻¹ * t * n ∈ T := by
        change ∀ y : G, y ∈ T ↔ n⁻¹ * y * (n⁻¹)⁻¹ ∈ T at hnInvNorm
        simpa [n] using (hnInvNorm t).1 htT
      refine ⟨(q, ⟨n⁻¹ * t * n, ht'⟩), ?_⟩
      apply Subtype.ext
      calc
        ((f (q, ⟨n⁻¹ * t * n, ht'⟩)).1) = g⁻¹ * t * g := by
          simp [f, q, a, n, mul_assoc]
        _ = x := by simpa using hxg.symm
  have hcardOmega : Nat.card Ω = N.index := by
    calc
      Nat.card Ω = Nat.card (G ⧸ N) := by
        exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel N)
      _ = N.index := N.index_eq_card.symm
  calc
    Nat.card (section14ConjugacyClosure T) = Nat.card (Ω × T0) := by
      exact Nat.card_congr (Equiv.ofBijective f hfBij).symm
    _ = Nat.card Ω * Nat.card T0 := Nat.card_prod _ _
    _ = Nat.card Ω * Nat.card T := rfl
    _ = Nat.card T * N.index := by rw [hcardOmega, Nat.mul_comm]

private theorem CFSG.section14_7_one_not_mem_TSet
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    1 ∉ section14_7_TSet (G := G) (M := M) (K := K) hM hK := by
  intro h1
  exact h1.2 (Or.inl (by simp))

private theorem CFSG.section14_7_conjClosure_union_overgroupFamily_subset_nonidentity
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    (section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∪
        ⋃ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
          section14ConjugacyClosure (section14Tilde i.1)) ⊆
      ({g : G | g ≠ 1} : Set G) := by
  intro g hg hg1
  subst hg1
  rcases hg with hgT | hgFam
  · exact
      section14_one_not_mem_conjClosure_of_one_not_mem
        (G := G)
        (T := section14_7_TSet (G := G) (M := M) (K := K) hM hK)
        (section14_7_one_not_mem_TSet (G := G) (M := M) (K := K) hM hK)
        hgT
  · rcases Set.mem_iUnion.1 hgFam with ⟨i, hgi⟩
    rcases i.2 with ⟨Xi, _hXi, hMi⟩
    exact section14_one_not_mem_conjClosure_tilde (G := G) (M := i.1) hMi.1 hgi

omit [IsMinCE G] in
private theorem CFSG.section14_card_nonidentity :
    Nat.card ({g : G | g ≠ 1} : Set G) = Nat.card G - 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  simpa [Nat.card_eq_fintype_card] using (Set.card_ne_eq (1 : G))


private theorem CFSG.section14_7_conjClosure_tilde_disjoint_self_overgroupFamily
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    section14ConjugacyClosure (section14Tilde M) ∩
      section14ConjugacyClosure (section14Tilde Mi) = ∅ := by
  rcases
      (section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
    ⟨_hXi, hMi, _hKi, _hKstarKi, _hMiP, hMi_not_conj, _hZeqZi, _hXiLeKistar,
      _hKiLeZ, _hKistarLeK⟩
  simpa [Set.inter_comm] using
    section14_conjClosure_tilde_disjoint_of_not_conjugate
      (G := G) (M₁ := M) (M₂ := Mi) hM.1 hMi.1 hMi_not_conj

private theorem CFSG.section14_7_card_conjClosure_union_self_overgroupFamily
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Nat.card
        ((section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∪
          section14ConjugacyClosure (section14Tilde M) ∪
          ⋃ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
            section14ConjugacyClosure (section14Tilde i.1)) : Set G) =
      Nat.card
          (section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK)) +
        Nat.card (section14ConjugacyClosure (section14Tilde M)) +
        ∑ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
          Nat.card (section14ConjugacyClosure (section14Tilde i.1)) := by
  classical
  let I := {Mi // Mi ∈ section14_7_overgroupFamily K}
  let U : Option (Option I) → Set G
    | none =>
        section14ConjugacyClosure
          (section14_7_TSet (G := G) (M := M) (K := K) hM hK)
    | some none => section14ConjugacyClosure (section14Tilde M)
    | some (some i) => section14ConjugacyClosure (section14Tilde i.1)
  have hUnion :
      section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∪
          section14ConjugacyClosure (section14Tilde M) ∪
          ⋃ i : I, section14ConjugacyClosure (section14Tilde i.1) =
        ⋃ o : Option (Option I), U o := by
    ext x
    constructor
    · intro hx
      rcases hx with hxLeft | hxFam
      · rcases hxLeft with hxT | hxMtilde
        · exact Set.mem_iUnion.2 ⟨none, by simpa [U] using hxT⟩
        · exact Set.mem_iUnion.2 ⟨some none, by simpa [U] using hxMtilde⟩
      · rcases Set.mem_iUnion.1 hxFam with ⟨i, hxi⟩
        exact Set.mem_iUnion.2 ⟨some (some i), by simpa [U] using hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨o, ho⟩
      cases o with
      | none => exact Or.inl (Or.inl (by simpa [U] using ho))
      | some o =>
          cases o with
          | none => exact Or.inl (Or.inr (by simpa [U] using ho))
          | some i =>
              exact Or.inr <| Set.mem_iUnion.2 ⟨i, by simpa [U] using ho⟩
  have hPairwise : Pairwise (Function.onFun Disjoint U) := by
    intro o₁ o₂ hne
    cases o₁ with
    | none =>
        cases o₂ with
        | none => cases hne rfl
        | some o₂ =>
            cases o₂ with
            | none =>
                simpa [Function.onFun, U, Set.disjoint_iff_inter_eq_empty] using
                  section14_7_conjClosure_TSet_disjoint_conjClosure_tilde
                    (G := G) (M := M) (K := K) (H := M) hM hK hM.1
            | some i =>
                rcases i.2 with ⟨Xi, _hXi, hMi⟩
                simpa [Function.onFun, U, Set.disjoint_iff_inter_eq_empty] using
                  section14_7_conjClosure_TSet_disjoint_conjClosure_tilde
                    (G := G) (M := M) (K := K) (H := i.1) hM hK hMi.1
    | some o₁ =>
        cases o₁ with
        | none =>
            cases o₂ with
            | none =>
                simpa [Function.onFun, U, Set.disjoint_iff_inter_eq_empty, Set.inter_comm] using
                  section14_7_conjClosure_TSet_disjoint_conjClosure_tilde
                    (G := G) (M := M) (K := K) (H := M) hM hK hM.1
            | some o₂ =>
                cases o₂ with
                | none => cases hne rfl
                | some i =>
                    simpa [Function.onFun, U, Set.disjoint_iff_inter_eq_empty] using
                      section14_7_conjClosure_tilde_disjoint_self_overgroupFamily
                        (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2
        | some i =>
            cases o₂ with
            | none =>
                rcases i.2 with ⟨Xi, _hXi, hMi⟩
                simpa [Function.onFun, U, Set.disjoint_iff_inter_eq_empty, Set.inter_comm] using
                  section14_7_conjClosure_TSet_disjoint_conjClosure_tilde
                    (G := G) (M := M) (K := K) (H := i.1) hM hK hMi.1
            | some o₂ =>
                cases o₂ with
                | none =>
                    simpa [Function.onFun, U, Set.disjoint_iff_inter_eq_empty, Set.inter_comm] using
                      section14_7_conjClosure_tilde_disjoint_self_overgroupFamily
                        (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2
                | some j =>
                    have hij : i.1 ≠ j.1 := by
                      intro hEq
                      apply hne
                      exact congrArg some (congrArg some (Subtype.ext hEq))
                    simpa [Function.onFun, U, Set.disjoint_iff_inter_eq_empty] using
                      section14_7_conjClosure_tilde_disjoint_of_distinct_overgroupFamily
                        (G := G) (M := M) (K := K) (Mi := i.1) (Mj := j.1) hM hK i.2 j.2 hij
  have hFinite : ∀ o : Option (Option I), (U o).Finite := by
    intro o
    exact Set.toFinite _
  calc
    Nat.card
        ((section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∪
          section14ConjugacyClosure (section14Tilde M) ∪
          ⋃ i : I, section14ConjugacyClosure (section14Tilde i.1)) : Set G) =
        (⋃ o : Option (Option I), U o).ncard := by
          rw [hUnion, Nat.card_coe_set_eq]
    _ = ∑ᶠ o : Option (Option I), (U o).ncard := by
          exact Set.ncard_iUnion_of_finite hFinite hPairwise
    _ = ∑ o : Option (Option I), Nat.card (U o) := by
          rw [finsum_eq_sum_of_fintype]
          simp [Nat.card_coe_set_eq]
    _ =
        Nat.card
          (section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK)) +
          Nat.card (section14ConjugacyClosure (section14Tilde M)) +
          ∑ i : I, Nat.card (section14ConjugacyClosure (section14Tilde i.1)) := by
          rw [Fintype.sum_option, Fintype.sum_option]
          simp [U, Nat.add_assoc]

private theorem CFSG.section14_7_conjClosure_union_self_overgroupFamily_subset_nonidentity
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    (section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∪
        section14ConjugacyClosure (section14Tilde M) ∪
        ⋃ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
          section14ConjugacyClosure (section14Tilde i.1)) ⊆
      ({g : G | g ≠ 1} : Set G) := by
  intro g hg hg1
  subst hg1
  rcases hg with hgLeft | hgFam
  · rcases hgLeft with hgT | hgMtilde
    · exact section14_7_conjClosure_union_overgroupFamily_subset_nonidentity
        (G := G) (M := M) (K := K) hM hK (Or.inl hgT) rfl
    · exact section14_one_not_mem_conjClosure_tilde (G := G) (M := M) hM.1 hgMtilde
  · exact section14_7_conjClosure_union_overgroupFamily_subset_nonidentity
      (G := G) (M := M) (K := K) hM hK (Or.inr hgFam) rfl

private theorem CFSG.section14_7_card_conjClosure_union_self_overgroupFamily_le_nonidentity
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Nat.card
        ((section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∪
          section14ConjugacyClosure (section14Tilde M) ∪
          ⋃ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
            section14ConjugacyClosure (section14Tilde i.1)) : Set G) ≤
      Nat.card ({g : G | g ≠ 1} : Set G) := by
  classical
  let A : Set G :=
    section14ConjugacyClosure (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∪
      section14ConjugacyClosure (section14Tilde M) ∪
      ⋃ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
        section14ConjugacyClosure (section14Tilde i.1)
  let B : Set G := {g : G | g ≠ 1}
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  let f : A → B := fun a =>
    ⟨a.1, section14_7_conjClosure_union_self_overgroupFamily_subset_nonidentity
      (G := G) (M := M) (K := K) hM hK a.2⟩
  have hf : Function.Injective f := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  have hcard : Nat.card A ≤ Nat.card B := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective f hf
  change Nat.card A ≤ Nat.card B
  exact hcard

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_z_le_of_hall_kappa
    {M K : Subgroup G}
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14Z M K ≤ M := by
  rw [section14Z]
  exact sup_le hK.1
    ((inf_le_left : section14KStar M K ≤ section10Msigma M).trans (section14_msigma_le M))

private theorem CFSG.section14_7_normalizer_primeOrderSubgroup_not_le_M
    {M K X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hX : X ∈ section12PrimeOrderSubgroups K) :
    ¬ Subgroup.normalizer (X : Set G) ≤ M := by
  rcases hX with ⟨hXK, p, hXcard⟩
  have hXPrime : X ∈ section10PrimeOrderSubgroupsIn p K := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXK, hXcard⟩
  intro hNXM
  have hMcontNX :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
    ⟨hM.1, hNXM⟩
  have hpσM : p ∈ section10SigmaPrimes M :=
    section14_b2_prime_mem_sigma_of_primeOrder
      (G := G) (M := M) (K := K) (X := X) (Mstar := M) (p := p)
      hM hK hXPrime hMcontNX
  have hpκ : p ∈ section14KappaPrimes M := by
    have hpX : p.val ∣ Nat.card X := by
      rw [hXcard]
    have hXM : X ≤ M := hXK.trans hK.1
    have hXsub_le_Ksub : X.subgroupOf M ≤ K.subgroupOf M := by
      intro x hx
      exact hXK (by simpa [Subgroup.mem_subgroupOf] using hx)
    have hcardXsub : Nat.card (X.subgroupOf M) = Nat.card X :=
      section12_card_subgroupOf_eq hXM
    have hpXsub : p.val ∣ Nat.card (X.subgroupOf M) := by
      simpa [hcardXsub] using hpX
    exact hK.2.p_in_pi_of_p_dvd_card p
      (hpXsub.trans (Subgroup.card_dvd_of_le hXsub_le_Ksub))
  exact section14_kappa_subset_not_sigma (M := M) hpκ hpσM

private theorem CFSG.section14_7_z_lt_self
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14Z M K < M := by
  obtain ⟨q, Xi, hXiPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
  have hXi : Xi ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXiPrime
  have hNX_not_le_M :=
    section14_7_normalizer_primeOrderSubgroup_not_le_M
      (G := G) (M := M) (K := K) (X := Xi) hM hK hXi
  have hNXZ := proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK Xi hXi
  have hNXeqZ : subgroupNormalizerIn M (Xi : Set G) = section14Z M K :=
    hNXZ.1.trans hNXZ.2.1
  have hZleM : section14Z M K ≤ M := section14_z_le_of_hall_kappa (M := M) (K := K) hK
  have hZne : section14Z M K ≠ M := by
    intro hZM
    have hMleNX : M ≤ Subgroup.normalizer (Xi : Set G) := by
      have hsub :
          subgroupNormalizerIn M (Xi : Set G) ≤ Subgroup.normalizer (Xi : Set G) :=
        subgroupNormalizerIn_le_normalizer M (Xi : Set G)
      simpa [hNXeqZ, hZM] using hsub
    obtain ⟨Mi, hMi⟩ :=
      section14_7_exists_maximal_overgroup_of_primeOrderSubgroup
        (G := G) (M := M) (K := K) (X := Xi) hM hK hXi
    have hMi_eq_M : Mi = M :=
      (hM.1.le_iff_eq hMi.1.1).mp (hMleNX.trans hMi.2)
    have hNX_le_M : Subgroup.normalizer (Xi : Set G) ≤ M := by
      simpa [hMi_eq_M] using hMi.2
    exact hNX_not_le_M hNX_le_M
  exact lt_of_le_of_ne hZleM hZne

private theorem CFSG.section14_7_z_lt_overgroupFamily
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    section14Z M K < Mi := by
  let Xi :=
    section14_7_XiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  rcases
      (section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
    ⟨hXi, hMi, _hKi, _hKstarKi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
      _hKiLeZ, _hKistarLeK⟩
  have hNX_not_le_M :=
    section14_7_normalizer_primeOrderSubgroup_not_le_M
      (G := G) (M := M) (K := K) (X := Xi) hM hK hXi
  have hZleMi :
      section14Z M K ≤ Mi :=
    (section14_7_not_conjugate_and_z_le
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi) hM hK hXi hMi).2
  have hZne : section14Z M K ≠ Mi := by
    intro hZMi
    have hNX_le_M : Subgroup.normalizer (Xi : Set G) ≤ M := by
      calc
        Subgroup.normalizer (Xi : Set G) ≤ Mi := hMi.2
        _ = section14Z M K := by symm; exact hZMi
        _ ≤ M := section14_z_le_of_hall_kappa (M := M) (K := K) hK
    exact hNX_not_le_M hNX_le_M
  exact lt_of_le_of_ne hZleMi hZne

omit [IsMinCE G] in
private theorem CFSG.section14_two_mul_card_of_lt
    {H L : Subgroup G}
    (hHL : H < L) :
    2 * Nat.card H ≤ Nat.card L := by
  let Hsub : Subgroup L := H.subgroupOf L
  have hcardHsub : Nat.card Hsub = Nat.card H :=
    section12_card_subgroupOf_eq hHL.1
  have hidx_ne_one : Hsub.index ≠ 1 := by
    intro hidx
    have hHsub_top : Hsub = ⊤ := Subgroup.index_eq_one.mp hidx
    have hLleH : L ≤ H := (Subgroup.subgroupOf_eq_top).1 hHsub_top
    exact hHL.2 hLleH
  have hidx_pos : 0 < Hsub.index := by
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Hsub))
  have htwo_le_idx : 2 ≤ Hsub.index := by
    omega
  have hmul : Nat.card H * Hsub.index = Nat.card L := by
    calc
      Nat.card H * Hsub.index = Nat.card Hsub * Hsub.index := by rw [hcardHsub]
      _ = Nat.card L := by
            exact Subgroup.card_mul_index (H := Hsub)
  have htwo_mul : 2 * Nat.card H ≤ Nat.card H * Hsub.index := by
    calc
      2 * Nat.card H = Nat.card H * 2 := by simp [Nat.mul_comm]
      _ ≤ Nat.card H * Hsub.index := Nat.mul_le_mul_left _ htwo_le_idx
  exact htwo_mul.trans_eq hmul

private theorem CFSG.section14_7_two_mul_card_z_le_card_self
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    2 * Nat.card (section14Z M K) ≤ Nat.card M := by
  exact
    section14_two_mul_card_of_lt
      (G := G) (H := section14Z M K) (L := M)
      (section14_7_z_lt_self (G := G) (M := M) (K := K) hM hK)

private theorem CFSG.section14_7_two_mul_card_z_le_card_overgroupFamily
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    2 * Nat.card (section14Z M K) ≤ Nat.card Mi := by
  exact
    section14_two_mul_card_of_lt
      (G := G) (H := section14Z M K) (L := Mi)
      (section14_7_z_lt_overgroupFamily
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam)

private theorem CFSG.section14_q_card_formula_of_complement
    {σ k m idx g : ℕ}
    (hk : 0 < k)
    (hσ : 0 < σ)
    (hkm : k * σ = m)
    (hmg : m * idx = g) :
    (((σ - 1) * idx : ℕ) : ℚ) = ((1 : ℚ) / k - 1 / m) * g := by
  have hm0nat : 0 < m := by
    rw [← hkm]
    exact Nat.mul_pos hk hσ
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have hkmQ : (k : ℚ) * σ = m := by exact_mod_cast hkm
  have hmgQ : (m : ℚ) * idx = g := by exact_mod_cast hmg
  have hσidx : (σ : ℚ) * idx = g / k := by
    apply (eq_div_iff hk0).2
    calc
      (σ : ℚ) * idx * k = ((k : ℚ) * σ) * idx := by ring
      _ = m * idx := by rw [hkmQ]
      _ = g := hmgQ
  have hidx : (idx : ℚ) = g / m := by
    apply (eq_div_iff hm0).2
    linarith [hmgQ]
  have hσsub : (((σ - 1 : ℕ) : ℚ)) = (σ : ℚ) - 1 := by
    simpa using (Nat.cast_sub (R := ℚ) (m := 1) (n := σ) hσ)
  calc
    ((((σ - 1) * idx : ℕ) : ℚ)) = (((σ - 1 : ℕ) : ℚ)) * idx := by norm_num
    _ = ((σ : ℚ) - 1) * idx := by rw [hσsub]
    _ = (σ : ℚ) * idx - idx := by ring
    _ = g / k - g / m := by rw [hσidx, hidx]
    _ = ((1 : ℚ) / k - 1 / m) * g := by ring

private theorem CFSG.section14_card_conjClosure_tilde_eq_q_of_complement
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M K) :
    (Nat.card (section14ConjugacyClosure (section14Tilde M)) : ℚ) =
      ((1 : ℚ) / (Nat.card K : ℚ) - (1 : ℚ) / (Nat.card M : ℚ)) *
        (Nat.card G : ℚ) := by
  have hcomp' :
      (K.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
    section14_complement_to_msigma_isComplement' (M := M) (E := K) hcomp
  have hkm :
      Nat.card K * Nat.card (section10Msigma M) = Nat.card M := by
    calc
      Nat.card K * Nat.card (section10Msigma M) =
          Nat.card (K.subgroupOf M) * Nat.card (section10MsigmaSubgroup M) := by
            have hKsub : Nat.card (K.subgroupOf M) = Nat.card K :=
              section12_card_subgroupOf_eq hcomp.2.1
            have hσsub : Nat.card (section10MsigmaSubgroup M) = Nat.card (section10Msigma M) := by
              simpa [section14_msigma_subgroupOf_eq (M := M)] using
                (section12_card_subgroupOf_eq (section14_msigma_le M))
            rw [← hKsub, ← hσsub]
      _ = Nat.card M := by
            simpa using hcomp'.card_mul
  have hmg : Nat.card M * M.index = Nat.card G := by
    exact Subgroup.card_mul_index (H := M)
  have hclosure :
      Nat.card (section14ConjugacyClosure (section14Tilde M)) =
        (Nat.card (section10Msigma M) - 1) * M.index :=
    lemma_14_5_c (G := G) (M := M) hM
  simpa [hclosure] using
    section14_q_card_formula_of_complement
      (σ := Nat.card (section10Msigma M))
      (k := Nat.card K)
      (m := Nat.card M)
      (idx := M.index)
      (g := Nat.card G)
      (Nat.card_pos)
      (Nat.card_pos)
      hkm hmg

private theorem CFSG.section14_7_card_conjClosure_tilde_ge_q_self_of_mem_P1
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP1 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ((1 : ℚ) / (Nat.card K : ℚ) -
        (1 : ℚ) / ((2 * Nat.card (section14Z M K) : ℕ) : ℚ)) *
        (Nat.card G : ℚ) ≤
      (Nat.card (section14ConjugacyClosure (section14Tilde M)) : ℚ) := by
  have hcomp :=
    section14_hall_kappa_complementToMsigma_of_mem_P1
      (G := G) (M := M) (K := K) hM hK
  have hEq :
      (Nat.card (section14ConjugacyClosure (section14Tilde M)) : ℚ) =
        ((1 : ℚ) / (Nat.card K : ℚ) - (1 : ℚ) / (Nat.card M : ℚ)) *
          (Nat.card G : ℚ) :=
    section14_card_conjClosure_tilde_eq_q_of_complement
      (G := G) (M := M) (K := K) hM.1.1 hcomp
  have hsize :
      2 * Nat.card (section14Z M K) ≤ Nat.card M :=
    section14_7_two_mul_card_z_le_card_self
      (G := G) (M := M) (K := K) hM.1 hK
  have hdiv :
      (1 : ℚ) / (Nat.card M : ℚ) ≤
        (1 : ℚ) / ((2 * Nat.card (section14Z M K) : ℕ) : ℚ) := by
    have hcast : (((2 * Nat.card (section14Z M K) : ℕ) : ℚ)) ≤ (Nat.card M : ℚ) := by
      exact_mod_cast hsize
    have hpos : (0 : ℚ) < (((2 * Nat.card (section14Z M K) : ℕ) : ℚ)) := by
      have hposNat : 0 < 2 * Nat.card (section14Z M K) := by
        exact Nat.mul_pos (by decide) Nat.card_pos
      exact_mod_cast hposNat
    simpa using one_div_le_one_div_of_le hpos hcast
  have hcoeff :
      (1 : ℚ) / (Nat.card K : ℚ) -
          (1 : ℚ) / ((2 * Nat.card (section14Z M K) : ℕ) : ℚ) ≤
        (1 : ℚ) / (Nat.card K : ℚ) - (1 : ℚ) / (Nat.card M : ℚ) := by
    linarith
  rw [hEq]
  exact mul_le_mul_of_nonneg_right hcoeff (by positivity)

private theorem CFSG.section14_7_card_conjClosure_tilde_ge_q_overgroupFamily_of_mem_P1
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hMiP1 : Mi ∈ section14MFamilyP1 G) :
    ((1 : ℚ) /
          (Nat.card
            (section14_7_KiOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) : ℚ) -
        (1 : ℚ) / ((2 * Nat.card (section14Z M K) : ℕ) : ℚ)) *
        (Nat.card G : ℚ) ≤
      (Nat.card (section14ConjugacyClosure (section14Tilde Mi)) : ℚ) := by
  let Ki :=
    section14_7_KiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  rcases
      (section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
    ⟨_hXi, hMi, hKi, _hKstarKi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
      _hKiLeZ, _hKistarLeK⟩
  have hcomp :=
    section14_hall_kappa_complementToMsigma_of_mem_P1
      (G := G) (M := Mi) (K := Ki) hMiP1 hKi
  have hEq :
      (Nat.card (section14ConjugacyClosure (section14Tilde Mi)) : ℚ) =
        ((1 : ℚ) / (Nat.card Ki : ℚ) - (1 : ℚ) / (Nat.card Mi : ℚ)) *
          (Nat.card G : ℚ) :=
    section14_card_conjClosure_tilde_eq_q_of_complement
      (G := G) (M := Mi) (K := Ki) hMiP1.1.1 hcomp
  have hsize :
      2 * Nat.card (section14Z M K) ≤ Nat.card Mi :=
    section14_7_two_mul_card_z_le_card_overgroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hdiv :
      (1 : ℚ) / (Nat.card Mi : ℚ) ≤
        (1 : ℚ) / ((2 * Nat.card (section14Z M K) : ℕ) : ℚ) := by
    have hcast : (((2 * Nat.card (section14Z M K) : ℕ) : ℚ)) ≤ (Nat.card Mi : ℚ) := by
      exact_mod_cast hsize
    have hpos : (0 : ℚ) < (((2 * Nat.card (section14Z M K) : ℕ) : ℚ)) := by
      have hposNat : 0 < 2 * Nat.card (section14Z M K) := by
        exact Nat.mul_pos (by decide) Nat.card_pos
      exact_mod_cast hposNat
    simpa using one_div_le_one_div_of_le hpos hcast
  have hcoeff :
      (1 : ℚ) / (Nat.card Ki : ℚ) -
          (1 : ℚ) / ((2 * Nat.card (section14Z M K) : ℕ) : ℚ) ≤
        (1 : ℚ) / (Nat.card Ki : ℚ) - (1 : ℚ) / (Nat.card Mi : ℚ) := by
    linarith
  rw [hEq]
  exact mul_le_mul_of_nonneg_right hcoeff (by positivity)

private theorem CFSG.section14_7_card_conjClosure_TSet
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Nat.card
        (section14ConjugacyClosure
          (section14_7_TSet (G := G) (M := M) (K := K) hM hK)) =
      Nat.card (section14_7_TSet (G := G) (M := M) (K := K) hM hK) *
        (section14Z M K).index := by
  simpa [section14_7_normalizer_TSet_eq_z (G := G) (M := M) (K := K) hM hK] using
    (section14_card_conjClosure_eq_card_mul_index_of_ti
      (G := G)
      (T := section14_7_TSet (G := G) (M := M) (K := K) hM hK)
      (section14_7_one_not_mem_TSet (G := G) (M := M) (K := K) hM hK)
      (section14_7_TSet_ti (G := G) (M := M) (K := K) hM hK))

private theorem CFSG.section14_7_card_factorUnion_add
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Nat.card (section14_7_factorUnion (G := G) (M := M) (K := K) hM hK) +
        Nat.card {Mi // Mi ∈ section14_7_overgroupFamily K} =
      Nat.card (section14KStar M K) +
        ∑ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
          Nat.card
            (section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) := by
  classical
  let I := {Mi // Mi ∈ section14_7_overgroupFamily K}
  change Nat.card (section14_7_factorUnion (G := G) (M := M) (K := K) hM hK) +
        Nat.card I =
      Nat.card (section14KStar M K) +
        ∑ i : I,
          Nat.card
            (section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2)
  let U : Option I → Set G
    | none => (section14KStar M K : Set G) \ ({1} : Set G)
    | some i =>
        ((section14_7_KstarOfOvergroupFamily
            (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 : Subgroup G) : Set G) \
          ({1} : Set G)
  have hFactorDiff :
      section14_7_factorUnion (G := G) (M := M) (K := K) hM hK \ ({1} : Set G) =
        ⋃ o : Option I, U o := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxFactor, hxne1⟩
      rcases hxFactor with hxBase | hxFam
      · exact Set.mem_iUnion.2 ⟨none, by simpa [U] using ⟨hxBase, hxne1⟩⟩
      · rcases Set.mem_iUnion.1 hxFam with ⟨i, hxi⟩
        exact Set.mem_iUnion.2 ⟨some i, by simpa [U] using ⟨hxi, hxne1⟩⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨o, ho⟩
      cases o with
      | none =>
          exact ⟨Or.inl (by simpa [U] using ho.1), by simpa [U] using ho.2⟩
      | some i =>
          exact ⟨Or.inr <| Set.mem_iUnion.2 ⟨i, by simpa [U] using ho.1⟩,
            by simpa [U] using ho.2⟩
  have hPairwise : Pairwise (Function.onFun Disjoint U) := by
    intro o₁ o₂ hne
    cases o₁ with
    | none =>
        cases o₂ with
        | none => cases hne rfl
        | some i =>
            rw [Function.onFun]
            rw [Set.disjoint_left]
            intro x hxBase hxFam
            have hxInf :
                x ∈ section14KStar M K ⊓
                  section14_7_KstarOfOvergroupFamily
                    (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 := ⟨hxBase.1, hxFam.1⟩
            have hxbot : x ∈ (⊥ : Subgroup G) := by
              simpa [section14_7_base_kstar_inf_bot_of_overgroupFamily
                (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2] using hxInf
            exact hxBase.2 (by simpa using hxbot)
    | some i =>
        cases o₂ with
        | none =>
            rw [Function.onFun]
            rw [Set.disjoint_left]
            intro x hxI hxBase
            have hxInf :
                x ∈ section14KStar M K ⊓
                  section14_7_KstarOfOvergroupFamily
                    (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 := ⟨hxBase.1, hxI.1⟩
            have hxbot : x ∈ (⊥ : Subgroup G) := by
              simpa [section14_7_base_kstar_inf_bot_of_overgroupFamily
                (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2] using hxInf
            exact hxBase.2 (by simpa using hxbot)
        | some j =>
            have hij : i.1 ≠ j.1 := by
              intro hEq
              have hijSub : i = j := Subtype.ext hEq
              apply hne
              simp [hijSub]
            rw [Function.onFun]
            rw [Set.disjoint_left]
            intro x hxI hxJ
            have hxInf :
                x ∈ section14_7_KstarOfOvergroupFamily
                      (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 ⊓
                    section14_7_KstarOfOvergroupFamily
                      (G := G) (M := M) (K := K) (Mi := j.1) hM hK j.2 := ⟨hxI.1, hxJ.1⟩
            have hxbot : x ∈ (⊥ : Subgroup G) := by
              simpa [section14_7_kstar_inf_bot_of_distinct_overgroupFamily
                (G := G) (M := M) (K := K) (Mi := i.1) (Mj := j.1) hM hK i.2 j.2 hij] using
                hxInf
            exact hxI.2 (by simpa using hxbot)
  have hFinite : ∀ o : Option I, (U o).Finite := by
    intro o
    exact Set.toFinite _
  have hCardDiff :
      ((section14_7_factorUnion (G := G) (M := M) (K := K) hM hK) \ ({1} : Set G)).ncard =
        (U none).ncard + ∑ i : I, (U (some i)).ncard := by
    calc
      ((section14_7_factorUnion (G := G) (M := M) (K := K) hM hK) \ ({1} : Set G)).ncard =
          (⋃ o : Option I, U o).ncard := by rw [hFactorDiff]
      _ = ∑ᶠ o : Option I, (U o).ncard := by
            exact Set.ncard_iUnion_of_finite hFinite hPairwise
      _ = ∑ o : Option I, (U o).ncard := by
            rw [finsum_eq_sum_of_fintype]
      _ = (U none).ncard + ∑ i : I, (U (some i)).ncard := by
            rw [Fintype.sum_option]
  have hOneFactor :
      1 ∈ section14_7_factorUnion (G := G) (M := M) (K := K) hM hK :=
    Or.inl (by simp)
  have hFactorAddOne :
      ((section14_7_factorUnion (G := G) (M := M) (K := K) hM hK) \ ({1} : Set G)).ncard + 1 =
        Nat.card (section14_7_factorUnion (G := G) (M := M) (K := K) hM hK) := by
    simpa [Nat.card_coe_set_eq] using Set.ncard_sdiff_singleton_add_one hOneFactor
  have hBaseAddOne :
      (U none).ncard + 1 = Nat.card (section14KStar M K) := by
    change
      ((section14KStar M K : Set G) \ ({1} : Set G)).ncard + 1 =
        Nat.card (section14KStar M K)
    rw [Set.ncard_sdiff_singleton_add_one (by simp)]
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
  have hFamAdd :
      (∑ i : I, (U (some i)).ncard) + Nat.card I =
        ∑ i : I,
          Nat.card
            (section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) := by
    calc
      (∑ i : I, (U (some i)).ncard) + Nat.card I =
          (∑ i : I, (U (some i)).ncard) + ∑ i : I, 1 := by simp
      _ = ∑ i : I, ((U (some i)).ncard + 1) := by
            simp [Finset.sum_add_distrib]
      _ = ∑ i : I,
          Nat.card
            (section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) := by
            have hterm :
                ∀ i : I,
                  (U (some i)).ncard + 1 =
                    Nat.card
                      (section14_7_KstarOfOvergroupFamily
                        (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) := by
              intro i
              change
                ((section14_7_KstarOfOvergroupFamily
                      (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 : Set G) \
                    ({1} : Set G)).ncard + 1 =
                  Nat.card
                    (section14_7_KstarOfOvergroupFamily
                      (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2)
              rw [Set.ncard_sdiff_singleton_add_one (by simp)]
              rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
            simp_rw [hterm]
  omega

private theorem CFSG.section14_7_card_TSet_add
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Nat.card (section14_7_TSet (G := G) (M := M) (K := K) hM hK) +
        Nat.card (section14KStar M K) +
        ∑ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
          Nat.card
            (section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) =
      Nat.card (section14Z M K) + Nat.card {Mi // Mi ∈ section14_7_overgroupFamily K} := by
  have hFactorLeZ :
      section14_7_factorUnion (G := G) (M := M) (K := K) hM hK ⊆ section14Z M K := by
    intro x hx
    rcases hx with hxBase | hxFam
    · exact (show section14KStar M K ≤ section14Z M K from le_sup_right) hxBase
    · rcases Set.mem_iUnion.1 hxFam with ⟨i, hxi⟩
      rcases
          (section14_7_XiKiOfOvergroupFamily_spec
            (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) with
        ⟨_hXi, _hMi, _hKi, _hKstarKi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
          _hKiLeZ, hKistarLeK⟩
      exact (show K ≤ section14Z M K from le_sup_left) (hKistarLeK hxi)
  have hCardDiff :
      Nat.card (section14_7_TSet (G := G) (M := M) (K := K) hM hK) +
        Nat.card (section14_7_factorUnion (G := G) (M := M) (K := K) hM hK) =
      Nat.card (section14Z M K) := by
    have hZcard :
        (section14Z M K : Set G).ncard = Nat.card (section14Z M K) := by
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    simpa only [section14_7_TSet, Nat.card_coe_set_eq, hZcard] using
      (Set.ncard_sdiff_add_ncard_of_subset hFactorLeZ)
  have hCardFactor :=
    section14_7_card_factorUnion_add (G := G) (M := M) (K := K) hM hK
  omega

omit [IsMinCE G] in
public theorem CFSG.section14_mem_P1_of_mem_P_and_not_mem_P2
    {M : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hMnotP2 : M ∉ section14MFamilyP2 G) :
    M ∈ section14MFamilyP1 G := by
  refine ⟨hM, ?_⟩
  by_contra hneq
  exact hMnotP2 ⟨hM, hneq⟩

private theorem CFSG.section14_7_card_k_mul_card_kstar_eq_z
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Nat.card K * Nat.card (section14KStar M K) = Nat.card (section14Z M K) := by
  obtain ⟨q, Xi, hXiPrime⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
  have hXi : Xi ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXiPrime
  let Z : Subgroup G := section14Z M K
  have hZdp : section12InternalDirectProduct K (section14KStar M K) Z := by
    simpa [Z, section14ZInternalDirectProduct] using
      (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK Xi hXi).2.2
  have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
    intro x hxK
    exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hxK)
  have hcomp :
      ((section14KStar M K).subgroupOf Z).IsComplement' (K.subgroupOf Z) := by
    change
      ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).IsComplement'
        (K.subgroupOf (K ⊔ section14KStar M K))
    exact
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := section14KStar M K) (R := K) hK_norm_Kstar
        (by simpa [disjoint_iff, inf_comm] using hZdp.2.2.2.1)
  calc
    Nat.card K * Nat.card (section14KStar M K) =
        Nat.card (K.subgroupOf Z) * Nat.card ((section14KStar M K).subgroupOf Z) := by
          rw [← natCard_subgroupOf_eq K Z le_sup_left,
            ← natCard_subgroupOf_eq (section14KStar M K) Z le_sup_right]
    _ = Nat.card Z := by
          simpa [Nat.mul_comm] using hcomp.symm.card_mul
    _ = Nat.card (section14Z M K) := rfl

private theorem CFSG.section14_7_card_ki_mul_card_kistar_eq_z
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K) :
    Nat.card
        (section14_7_KiOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) *
      Nat.card
        (section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) =
        Nat.card (section14Z M K) := by
  let Xi :=
    section14_7_XiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Ki :=
    section14_7_KiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Kistar :=
    section14_7_KstarOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have hMiSpec :
      Xi ∈ section12PrimeOrderSubgroups K ∧
        Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)) ∧
        section12HallSubgroupIn (section14KappaPrimes Mi) Ki Mi ∧
        section14KStar M K ≤ Ki ∧
        Mi ∈ section14MFamilyP G ∧
        ¬ section14ConjugateSubgroups Mi M ∧
        section14Z M K = section14Z Mi Ki ∧
        Xi ≤ Kistar ∧
        Ki ≤ section14Z M K ∧
        Kistar ≤ K := by
    simpa [Xi, Ki, Kistar, section14_7_KstarOfOvergroupFamily] using
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  rcases hMiSpec with
    ⟨_hXi, _hMi, hKi, _hKstarKi, hMiP, _hMi_not_conj, hZeqZi, _hXiLeKistar, _hKiLeZ,
      _hKistarLeK⟩
  obtain ⟨q, X0, hX0PrimeIn⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := Ki) (section14_hall_kappa_ne_bot (G := G) hMiP hKi)
  have hX0 : X0 ∈ section12PrimeOrderSubgroups Ki :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
  have hZdp : section12InternalDirectProduct Ki Kistar (section14Z Mi Ki) := by
    change section14ZInternalDirectProduct Mi Ki
    exact (proposition_14_2_b1 (G := G) (M := Mi) (K := Ki) hMiP hKi X0 hX0).2.2
  have hKi_norm_Kistar : Ki ≤ Subgroup.normalizer (Kistar : Set G) := by
    intro x hxKi
    exact (centralizer_le_normalizer Kistar) (hZdp.2.2.2.2 hxKi)
  have hcomp :
      (Kistar.subgroupOf (section14Z Mi Ki)).IsComplement' (Ki.subgroupOf (section14Z Mi Ki)) := by
    change
      ((section14KStar Mi Ki).subgroupOf (Ki ⊔ section14KStar Mi Ki)).IsComplement'
        (Ki.subgroupOf (Ki ⊔ section14KStar Mi Ki))
    exact
      section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
        (G := G) (H := section14KStar Mi Ki) (R := Ki) hKi_norm_Kistar
        (by
          simpa [disjoint_iff, Ki, Kistar, section14_7_KstarOfOvergroupFamily, inf_comm]
            using hZdp.2.2.2.1)
  calc
    Nat.card Ki * Nat.card Kistar =
        Nat.card (Ki.subgroupOf (section14Z Mi Ki)) *
          Nat.card (Kistar.subgroupOf (section14Z Mi Ki)) := by
          rw [← natCard_subgroupOf_eq Ki (section14Z Mi Ki) (show Ki ≤ section14Z Mi Ki from le_sup_left),
            ← natCard_subgroupOf_eq Kistar (section14Z Mi Ki) le_sup_right]
    _ = Nat.card (section14Z Mi Ki) := by
          simpa [Nat.mul_comm] using hcomp.symm.card_mul
    _ = Nat.card (section14Z M K) := by rw [← hZeqZi]

public theorem CFSG.section14_7_exists_P2_self_or_overgroupFamily
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    M ∈ section14MFamilyP2 G ∨
      ∃ Mi : Subgroup G, Mi ∈ section14_7_overgroupFamily K ∧ Mi ∈ section14MFamilyP2 G := by
  classical
  by_cases hMP2 : M ∈ section14MFamilyP2 G
  · exact Or.inl hMP2
  by_cases hFamP2 : ∃ Mi : Subgroup G, Mi ∈ section14_7_overgroupFamily K ∧ Mi ∈ section14MFamilyP2 G
  · exact Or.inr hFamP2
  have hMP1 : M ∈ section14MFamilyP1 G :=
    section14_mem_P1_of_mem_P_and_not_mem_P2 (G := G) (M := M) hM hMP2
  have hFamP1 :
      ∀ Mi : Subgroup G, Mi ∈ section14_7_overgroupFamily K → Mi ∈ section14MFamilyP1 G := by
    intro Mi hMiFam
    rcases
        (section14_7_XiKiOfOvergroupFamily_spec
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) with
      ⟨_hXi, _hMi, _hKi, _hKstarKi, hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
        _hKiLeZ, _hKistarLeK⟩
    have hMiNotP2 : Mi ∉ section14MFamilyP2 G := by
      intro hMiP2
      exact hFamP2 ⟨Mi, hMiFam, hMiP2⟩
    exact section14_mem_P1_of_mem_P_and_not_mem_P2 (G := G) (M := Mi) hMiP hMiNotP2
  let I := {Mi // Mi ∈ section14_7_overgroupFamily K}
  let T :=
    section14_7_TSet (G := G) (M := M) (K := K) hM hK
  let Z : Subgroup G := section14Z M K
  let Ki : I → Subgroup G := fun i =>
    section14_7_KiOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2
  let Kistar : I → Subgroup G := fun i =>
    section14_7_KstarOfOvergroupFamily
      (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2
  let U : Set G :=
    section14ConjugacyClosure T ∪
      section14ConjugacyClosure (section14Tilde M) ∪
      ⋃ i : I, section14ConjugacyClosure (section14Tilde i.1)
  have hZidxNat : Nat.card Z * Z.index = Nat.card G := by
    exact Subgroup.card_mul_index (H := Z)
  have hZidxQ : (Nat.card Z : ℚ) * (Z.index : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast hZidxNat
  have hTclosureQ :
      (Nat.card (section14ConjugacyClosure T) : ℚ) =
        ((1 : ℚ) + (Nat.card I : ℚ) / (Nat.card Z : ℚ) -
            (1 : ℚ) / (Nat.card K : ℚ) -
            ∑ i : I, (1 : ℚ) / (Nat.card (Ki i) : ℚ)) *
          (Nat.card G : ℚ) := by
    have hTNat :=
      section14_7_card_conjClosure_TSet (G := G) (M := M) (K := K) hM hK
    have hTQ :
        (Nat.card (section14ConjugacyClosure T) : ℚ) =
          (Nat.card T : ℚ) * (Z.index : ℚ) := by
      simpa [T, Z] using (show
        (Nat.card
            (section14ConjugacyClosure
              (section14_7_TSet (G := G) (M := M) (K := K) hM hK)) : ℚ) =
          (Nat.card
              (section14_7_TSet (G := G) (M := M) (K := K) hM hK) : ℚ) *
            ((section14Z M K).index : ℚ) from
        by exact_mod_cast hTNat)
    have hTaddQ :
        (Nat.card T : ℚ) +
            (Nat.card (section14KStar M K) : ℚ) +
            ∑ i : I, (Nat.card (Kistar i) : ℚ) =
          (Nat.card Z : ℚ) + (Nat.card I : ℚ) := by
      have hTaddNat' :
          Nat.card T +
              Nat.card (section14KStar M K) +
              ∑ i : I, Nat.card (Kistar i) =
            Nat.card Z + Nat.card I := by
        simpa [T, Z, I, Kistar] using
          section14_7_card_TSet_add (G := G) (M := M) (K := K) hM hK
      exact_mod_cast hTaddNat'
    have hBaseTerm :
        (Nat.card (section14KStar M K) : ℚ) * (Z.index : ℚ) =
          ((1 : ℚ) / (Nat.card K : ℚ)) * (Nat.card G : ℚ) := by
      have hbaseNat :=
        section14_7_card_k_mul_card_kstar_eq_z (G := G) (M := M) (K := K) hM hK
      have hk0 : (Nat.card K : ℚ) ≠ 0 := by
        have hkpos : 0 < Nat.card K := Nat.card_pos
        exact_mod_cast hkpos.ne'
      have hbaseQ :
          (Nat.card (section14KStar M K) : ℚ) =
            ((1 : ℚ) / (Nat.card K : ℚ)) * (Nat.card Z : ℚ) := by
        have hbaseQdiv :
            (Nat.card (section14KStar M K) : ℚ) =
              (Nat.card Z : ℚ) / (Nat.card K : ℚ) := by
          apply (eq_div_iff hk0).2
          calc
            (Nat.card (section14KStar M K) : ℚ) * (Nat.card K : ℚ) =
                (Nat.card K : ℚ) * (Nat.card (section14KStar M K) : ℚ) := by ring
            _ = Nat.card Z := by
                simpa [Z] using (show
                  ((Nat.card K : ℚ) * (Nat.card (section14KStar M K) : ℚ)) =
                    (Nat.card (section14Z M K) : ℚ) from
                  by exact_mod_cast hbaseNat)
        calc
          (Nat.card (section14KStar M K) : ℚ) = (Nat.card Z : ℚ) / (Nat.card K : ℚ) := hbaseQdiv
          _ = ((1 : ℚ) / (Nat.card K : ℚ)) * (Nat.card Z : ℚ) := by
              field_simp [hk0]
      calc
        (Nat.card (section14KStar M K) : ℚ) * (Z.index : ℚ) =
            (((1 : ℚ) / (Nat.card K : ℚ)) * (Nat.card Z : ℚ)) * (Z.index : ℚ) := by
              rw [hbaseQ]
        _ = ((1 : ℚ) / (Nat.card K : ℚ)) * (Nat.card G : ℚ) := by
              rw [mul_assoc, hZidxQ]
    have hFamTerm :
        ∀ i : I,
          (Nat.card (Kistar i) : ℚ) * (Z.index : ℚ) =
            ((1 : ℚ) / (Nat.card (Ki i) : ℚ)) * (Nat.card G : ℚ) := by
      intro i
      have hcardNat :=
        section14_7_card_ki_mul_card_kistar_eq_z
          (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2
      have hki0 : (Nat.card (Ki i) : ℚ) ≠ 0 := by
        have hkipos : 0 < Nat.card (Ki i) := Nat.card_pos
        exact_mod_cast hkipos.ne'
      have hcardQ :
          (Nat.card (Kistar i) : ℚ) =
            ((1 : ℚ) / (Nat.card (Ki i) : ℚ)) * (Nat.card Z : ℚ) := by
        have hcardQdiv :
            (Nat.card (Kistar i) : ℚ) =
              (Nat.card Z : ℚ) / (Nat.card (Ki i) : ℚ) := by
          apply (eq_div_iff hki0).2
          calc
            (Nat.card (Kistar i) : ℚ) * (Nat.card (Ki i) : ℚ) =
                (Nat.card (Ki i) : ℚ) * (Nat.card (Kistar i) : ℚ) := by ring
            _ = Nat.card Z := by
                simpa [Ki, Kistar, Z] using (show
                  ((Nat.card
                      (section14_7_KiOfOvergroupFamily
                        (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) : ℚ) *
                    (Nat.card
                      (section14_7_KstarOfOvergroupFamily
                        (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) : ℚ)) =
                    (Nat.card (section14Z M K) : ℚ) from
                  by exact_mod_cast hcardNat)
        calc
          (Nat.card (Kistar i) : ℚ) = (Nat.card Z : ℚ) / (Nat.card (Ki i) : ℚ) := hcardQdiv
          _ = ((1 : ℚ) / (Nat.card (Ki i) : ℚ)) * (Nat.card Z : ℚ) := by
              field_simp [hki0]
      calc
        (Nat.card (Kistar i) : ℚ) * (Z.index : ℚ) =
            (((1 : ℚ) / (Nat.card (Ki i) : ℚ)) * (Nat.card Z : ℚ)) * (Z.index : ℚ) := by
              rw [hcardQ]
        _ = ((1 : ℚ) / (Nat.card (Ki i) : ℚ)) * (Nat.card G : ℚ) := by
              rw [mul_assoc, hZidxQ]
    have hIdxTerm :
        (Nat.card I : ℚ) * (Z.index : ℚ) =
          ((Nat.card I : ℚ) / (Nat.card Z : ℚ)) * (Nat.card G : ℚ) := by
      have hz0 : (Nat.card Z : ℚ) ≠ 0 := by
        have hzpos : 0 < Nat.card Z := Nat.card_pos
        exact_mod_cast hzpos.ne'
      have hidxQ : (Z.index : ℚ) = (Nat.card G : ℚ) / (Nat.card Z : ℚ) := by
        apply (eq_div_iff hz0).2
        linarith [hZidxQ]
      rw [hidxQ]
      ring
    have hmul :
        ((Nat.card T : ℚ) * (Z.index : ℚ)) +
            (Nat.card (section14KStar M K) : ℚ) * (Z.index : ℚ) +
            (∑ i : I, (Nat.card (Kistar i) : ℚ)) * (Z.index : ℚ) =
          (Nat.card Z : ℚ) * (Z.index : ℚ) + (Nat.card I : ℚ) * (Z.index : ℚ) := by
      simpa [add_mul, Finset.sum_mul] using
        congrArg (fun q : ℚ => q * (Z.index : ℚ)) hTaddQ
    rw [← hTQ, hBaseTerm, hZidxQ, hIdxTerm] at hmul
    rw [Finset.sum_mul] at hmul
    simp_rw [hFamTerm] at hmul
    rw [← Finset.sum_mul] at hmul
    linarith
  have hFamLowerSum :
      ((∑ i : I, (1 : ℚ) / (Nat.card (Ki i) : ℚ)) -
          (Nat.card I : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ) ≤
        ∑ i : I, (Nat.card (section14ConjugacyClosure (section14Tilde i.1)) : ℚ) := by
    have hraw :
        ∑ i : I,
            (((1 : ℚ) / (Nat.card (Ki i) : ℚ) -
                (1 : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ)) ≤
          ∑ i : I, (Nat.card (section14ConjugacyClosure (section14Tilde i.1)) : ℚ) := by
      refine Finset.sum_le_sum ?_
      intro i _
      simpa [I, Ki, Z] using
        section14_7_card_conjClosure_tilde_ge_q_overgroupFamily_of_mem_P1
          (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 (hFamP1 i.1 i.2)
    calc
      ((∑ i : I, (1 : ℚ) / (Nat.card (Ki i) : ℚ)) -
          (Nat.card I : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ) =
        (((∑ i : I, (1 : ℚ) / (Nat.card (Ki i) : ℚ)) -
            ∑ i : I, (1 : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ)) := by
          have hconst :
              (∑ i : I, (1 : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) =
                (Nat.card I : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            have hIcardQ : (((Finset.univ : Finset I).card : Nat) : ℚ) = Nat.card I := by
              simp [Nat.card_eq_fintype_card]
            rw [hIcardQ]
            ring
          rw [hconst]
      _ =
        ((∑ i : I,
            ((1 : ℚ) / (Nat.card (Ki i) : ℚ) -
              (1 : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ)))) * (Nat.card G : ℚ)) := by
          rw [← Finset.sum_sub_distrib]
      _ =
        ∑ i : I,
          (((1 : ℚ) / (Nat.card (Ki i) : ℚ) -
              (1 : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ)) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ i : I, (Nat.card (section14ConjugacyClosure (section14Tilde i.1)) : ℚ) := hraw
  have hUnionEqQ :
      (Nat.card U : ℚ) =
        (Nat.card (section14ConjugacyClosure T) : ℚ) +
          (Nat.card (section14ConjugacyClosure (section14Tilde M)) : ℚ) +
          ∑ i : I, (Nat.card (section14ConjugacyClosure (section14Tilde i.1)) : ℚ) := by
    have hUnionNat :
        Nat.card U =
          Nat.card (section14ConjugacyClosure T) +
            Nat.card (section14ConjugacyClosure (section14Tilde M)) +
            ∑ i : I, Nat.card (section14ConjugacyClosure (section14Tilde i.1)) := by
      simpa [U, T, I] using
        section14_7_card_conjClosure_union_self_overgroupFamily
          (G := G) (M := M) (K := K) hM hK
    exact_mod_cast hUnionNat
  have hUnionLower :
      ((1 : ℚ) + (((Nat.card I : ℚ) - 1) / (((2 * Nat.card Z : ℕ) : ℚ)))) *
          (Nat.card G : ℚ) ≤
        (Nat.card U : ℚ) := by
    have hbaseLower :=
      section14_7_card_conjClosure_tilde_ge_q_self_of_mem_P1
        (G := G) (M := M) (K := K) hMP1 hK
    have htemp :
        ((1 : ℚ) + (Nat.card I : ℚ) / (Nat.card Z : ℚ) -
            (1 : ℚ) / (Nat.card K : ℚ) -
            ∑ i : I, (1 : ℚ) / (Nat.card (Ki i) : ℚ)) * (Nat.card G : ℚ) +
          (((1 : ℚ) / (Nat.card K : ℚ) -
              (1 : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ)) +
          (((∑ i : I, (1 : ℚ) / (Nat.card (Ki i) : ℚ)) -
              (Nat.card I : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ)) ≤
        (Nat.card (section14ConjugacyClosure T) : ℚ) +
          (Nat.card (section14ConjugacyClosure (section14Tilde M)) : ℚ) +
          ∑ i : I, (Nat.card (section14ConjugacyClosure (section14Tilde i.1)) : ℚ) := by
      linarith [hTclosureQ, hbaseLower, hFamLowerSum]
    rw [hUnionEqQ]
    have hcoeff :
        ((1 : ℚ) + (Nat.card I : ℚ) / (Nat.card Z : ℚ) -
            (1 : ℚ) / (Nat.card K : ℚ) -
            ∑ i : I, (1 : ℚ) / (Nat.card (Ki i) : ℚ)) * (Nat.card G : ℚ) +
          (((1 : ℚ) / (Nat.card K : ℚ) -
              (1 : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ)) +
          (((∑ i : I, (1 : ℚ) / (Nat.card (Ki i) : ℚ)) -
              (Nat.card I : ℚ) / (((2 * Nat.card Z : ℕ) : ℚ))) * (Nat.card G : ℚ)) =
        ((1 : ℚ) + (((Nat.card I : ℚ) - 1) / (((2 * Nat.card Z : ℕ) : ℚ)))) *
          (Nat.card G : ℚ) := by
      have hz0 : (Nat.card Z : ℚ) ≠ 0 := by
        have hzpos : 0 < Nat.card Z := Nat.card_pos
        exact_mod_cast hzpos.ne'
      field_simp [hz0]
      norm_num [Nat.cast_mul]
      ring
    rw [hcoeff] at htemp
    exact htemp
  have hINonempty : Nonempty I := by
    rcases section14_7_overgroupFamily_nonempty (G := G) (M := M) (K := K) hM hK with
      ⟨Mi, hMiFam⟩
    exact ⟨⟨Mi, hMiFam⟩⟩
  have hIcardPos : 0 < Nat.card I := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr hINonempty
  have hIgeOne : 1 ≤ Nat.card I := Nat.succ_le_of_lt hIcardPos
  have hLowerGeG :
      (Nat.card G : ℚ) ≤
        ((1 : ℚ) + (((Nat.card I : ℚ) - 1) / (((2 * Nat.card Z : ℕ) : ℚ)))) *
          (Nat.card G : ℚ) := by
    have hnum : 0 ≤ (Nat.card I : ℚ) - 1 := by
      have hIgeOneQ : (1 : ℚ) ≤ (Nat.card I : ℚ) := by
        exact_mod_cast hIgeOne
      linarith
    have hden : 0 ≤ (((2 * Nat.card Z : ℕ) : ℚ)) := by positivity
    have hextra :
        0 ≤ ((Nat.card I : ℚ) - 1) / (((2 * Nat.card Z : ℕ) : ℚ)) := by
      exact div_nonneg hnum hden
    have hprod :
        0 ≤ (((Nat.card I : ℚ) - 1) / (((2 * Nat.card Z : ℕ) : ℚ))) *
            (Nat.card G : ℚ) := by
      exact mul_nonneg hextra (by positivity)
    calc
      (Nat.card G : ℚ) ≤
          (Nat.card G : ℚ) +
            (((Nat.card I : ℚ) - 1) / (((2 * Nat.card Z : ℕ) : ℚ))) *
              (Nat.card G : ℚ) := by linarith
      _ =
          ((1 : ℚ) + (((Nat.card I : ℚ) - 1) / (((2 * Nat.card Z : ℕ) : ℚ)))) *
            (Nat.card G : ℚ) := by ring
  have hUGeG : (Nat.card G : ℚ) ≤ (Nat.card U : ℚ) :=
    hLowerGeG.trans hUnionLower
  have hUleNonid :
      (Nat.card U : ℚ) ≤ (Nat.card ({g : G | g ≠ 1} : Set G) : ℚ) := by
    have hUleNonidNat :
        Nat.card U ≤ Nat.card ({g : G | g ≠ 1} : Set G) := by
      change
        Nat.card
            ((section14ConjugacyClosure
                (section14_7_TSet (G := G) (M := M) (K := K) hM hK) ∪
              section14ConjugacyClosure (section14Tilde M) ∪
              ⋃ i : {Mi // Mi ∈ section14_7_overgroupFamily K},
                section14ConjugacyClosure (section14Tilde i.1)) : Set G) ≤
          Nat.card ({g : G | g ≠ 1} : Set G)
      exact
        section14_7_card_conjClosure_union_self_overgroupFamily_le_nonidentity
          (G := G) (M := M) (K := K) hM hK
    exact_mod_cast hUleNonidNat
  have hNonidQ :
      (Nat.card ({g : G | g ≠ 1} : Set G) : ℚ) = (Nat.card G : ℚ) - 1 := by
    have hNonidNat := section14_card_nonidentity (G := G)
    rw [hNonidNat]
    norm_num
  linarith

omit [IsMinCE G] in
public theorem CFSG.section14_subgroup_eq_of_le_prime_card
    {H K : Subgroup G}
    (hHK : H ≤ K)
    (hKprime : Nat.Prime (Nat.card K))
    (hHne : H ≠ ⊥) :
    H = K := by
  have hdiv : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK
  rcases (Nat.dvd_prime hKprime).mp hdiv with hHcard1 | hHcardEq
  · exact False.elim (hHne (Subgroup.eq_bot_of_card_eq (H := H) hHcard1))
  · exact Subgroup.eq_of_le_of_card_ge hHK (le_of_eq hHcardEq.symm)

private theorem CFSG.section14_7_overgroupFamily_subsingleton_of_self_P2
    {M K Mi Mj : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMP2 : M ∈ section14MFamilyP2 G)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hMjFam : Mj ∈ section14_7_overgroupFamily K) :
    Mj = Mi := by
  classical
  by_cases hEq : Mj = Mi
  · exact hEq
  have hKprime : Nat.Prime (Nat.card K) :=
    (proposition_14_2_g (G := G) (M := M) (K := K) hMP2 hK).2.1
  let KiMi : Subgroup G :=
    section14_7_KiOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let KistarMi : Subgroup G :=
    section14_7_KstarOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let KiMj : Subgroup G :=
    section14_7_KiOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  let KistarMj : Subgroup G :=
    section14_7_KstarOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  rcases
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam with
    ⟨_hXiMi, _hMi, hKiMi, _hKstarKiMi, hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
      _hKiLeZ, hKistarMiLeK⟩
  rcases
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam with
    ⟨_hXiMj, _hMj, hKj, _hKstarKj, hMjP, _hMj_not_conj, _hZeqZj, _hXiLeKistar, _hKjLeZ,
      hKistarMjLeK⟩
  have hKistarMiEqK :
      KistarMi = K := by
    exact section14_subgroup_eq_of_le_prime_card hKistarMiLeK hKprime
      (section14_c_kstar_ne_bot (G := G) (M := Mi) (K := KiMi) hMiP hKiMi)
  have hKistarMjEqK :
      KistarMj = K := by
    exact section14_subgroup_eq_of_le_prime_card hKistarMjLeK hKprime
      (section14_c_kstar_ne_bot (G := G) (M := Mj) (K := KiMj) hMjP hKj)
  have hdisj :
      KistarMi ⊓ KistarMj = ⊥ := by
    have hNe : Mi ≠ Mj := by
      intro hEq'
      exact hEq hEq'.symm
    exact section14_7_kstar_inf_bot_of_distinct_overgroupFamily
      (G := G) (M := M) (K := K) (Mi := Mi) (Mj := Mj) hM hK hMiFam hMjFam hNe
  have hKbot : K = ⊥ := by
    simpa [hKistarMiEqK, hKistarMjEqK] using hdisj
  exact False.elim ((section14_hall_kappa_ne_bot (G := G) hM hK) hKbot)

private theorem CFSG.section14_7_overgroupFamily_subsingleton_of_member_P2
    {M K Mi Mj : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hMiP2 : Mi ∈ section14MFamilyP2 G)
    (hMjFam : Mj ∈ section14_7_overgroupFamily K) :
    Mj = Mi := by
  classical
  by_cases hEq : Mj = Mi
  · exact hEq
  let KiMi : Subgroup G :=
    section14_7_KiOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let KistarMj : Subgroup G :=
    section14_7_KstarOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  let KiMj : Subgroup G :=
    section14_7_KiOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  rcases
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam with
    ⟨_hXiMi, _hMi, hKiMi, hKstarKiMi, _hMiP, _hMi_not_conj, _hZeqZi, _hXiLeKistar,
      _hKiLeZ, _hKistarLeK⟩
  rcases
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam with
    ⟨_hXiMj, _hMj, hKj, _hKstarKj, hMjP, _hMj_not_conj, _hZeqZj, _hXiLeKistar, _hKjLeZ,
      _hKistarLeK⟩
  have hKiPrime : Nat.Prime (Nat.card KiMi) :=
    (proposition_14_2_g (G := G) (M := Mi) (K := KiMi) hMiP2 hKiMi).2.1
  have hBaseEqKiMi : section14KStar M K = KiMi := by
    exact section14_subgroup_eq_of_le_prime_card hKstarKiMi hKiPrime
      (section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK)
  have hNe : Mi ≠ Mj := by
    intro hEq'
    exact hEq hEq'.symm
  have hKistarMjLeKiMi :
      KistarMj ≤ KiMi := by
    exact section14_7_kstarOfOvergroupFamily_le_ki_of_distinct
      (G := G) (M := M) (K := K) (Mi := Mi) (Mj := Mj) hM hK hMiFam hMjFam hNe
  have hKistarMjEqKiMi : KistarMj = KiMi := by
    exact section14_subgroup_eq_of_le_prime_card hKistarMjLeKiMi hKiPrime
      (section14_c_kstar_ne_bot (G := G) (M := Mj) (K := KiMj) hMjP hKj)
  have hdisj :
      section14KStar M K ⊓ KistarMj = ⊥ := by
    exact section14_7_base_kstar_inf_bot_of_overgroupFamily
      (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
  have hKiMiBot : KiMi = ⊥ := by
    simpa [hBaseEqKiMi, hKistarMjEqKiMi] using hdisj
  have hKstarBot : section14KStar M K = ⊥ := by
    rw [hBaseEqKiMi, hKiMiBot]
  exact False.elim ((section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK) hKstarBot)

public theorem CFSG.section14_7_singleton_collapse_of_P2_witness
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hP2 :
      M ∈ section14MFamilyP2 G ∨
        ∃ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K ∧ Mj ∈ section14MFamilyP2 G) :
    (∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi) ∧
      section14_7_KiOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam =
        section14KStar M K ∧
      section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = K ∧
      (M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G) := by
  classical
  let Ki : Subgroup G :=
    section14_7_KiOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Kistar : Subgroup G :=
    section14_7_KstarOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  have huniq : ∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi := by
    intro Mj hMjFam
    rcases hP2 with hMP2 | ⟨Mw, hMwFam, hMwP2⟩
    · exact section14_7_overgroupFamily_subsingleton_of_self_P2
        (G := G) (M := M) (K := K) (Mi := Mi) (Mj := Mj) hM hK hMP2 hMiFam hMjFam
    · have hMiEqMw : Mi = Mw := by
        exact section14_7_overgroupFamily_subsingleton_of_member_P2
          (G := G) (M := M) (K := K) (Mi := Mw) (Mj := Mi) hM hK hMwFam hMwP2 hMiFam
      have hMjEqMw : Mj = Mw := by
        exact section14_7_overgroupFamily_subsingleton_of_member_P2
          (G := G) (M := M) (K := K) (Mi := Mw) (Mj := Mj) hM hK hMwFam hMwP2 hMjFam
      exact hMjEqMw.trans hMiEqMw.symm
  have hP2Mi :
      M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G := by
    rcases hP2 with hMP2 | ⟨Mw, hMwFam, hMwP2⟩
    · exact Or.inl hMP2
    · have hMiEqMw : Mi = Mw := (huniq Mw hMwFam).symm
      exact Or.inr (hMiEqMw ▸ hMwP2)
  have hNoOtherRange :
      Set.range
          (fun j : {Mj // Mj ∈ section14_7_overgroupFamily K ∧ Mj ≠ Mi} =>
            section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := j.1) hM hK j.2.1) = ∅ := by
    ext H
    constructor
    · rintro ⟨j, rfl⟩
      exact j.2.2 (huniq j.1 j.2.1)
    · intro hH
      cases hH
  have hOtherJoinEqBase :
      section14_7_otherKstarJoinOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam =
        section14KStar M K := by
    simp [section14_7_otherKstarJoinOfOvergroupFamily, hNoOtherRange]
  have hKiEqBase :
      Ki = section14KStar M K := by
    simpa [Ki] using
      (section14_7_otherKstarJoinOfOvergroupFamily_eq_ki
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam).symm.trans hOtherJoinEqBase
  have hKistarLeFam :
      Kistar ≤ section14_7_overgroupFamilyKstarJoin (G := G) (M := M) (K := K) hM hK := by
    intro x hx
    have hMem :
        Kistar ∈
          Set.range fun i : {Mi // Mi ∈ section14_7_overgroupFamily K} =>
            section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 := by
      exact ⟨⟨Mi, hMiFam⟩, rfl⟩
    exact le_sSup hMem hx
  have hFamLeKistar :
      section14_7_overgroupFamilyKstarJoin (G := G) (M := M) (K := K) hM hK ≤ Kistar := by
    refine sSup_le ?_
    rintro H ⟨i, rfl⟩
    have hi : i = ⟨Mi, hMiFam⟩ := by
      apply Subtype.ext
      exact huniq i.1 i.2
    simp [Kistar, hi]
  have hKistarEqK :
      Kistar = K := by
    have hFamEqKistar :
        section14_7_overgroupFamilyKstarJoin (G := G) (M := M) (K := K) hM hK = Kistar :=
      le_antisymm hFamLeKistar hKistarLeFam
    exact hFamEqKistar.symm.trans
      (section14_7_overgroupFamilyKstarJoin_eq_k (G := G) (M := M) (K := K) hM hK)
  exact ⟨huniq, hKiEqBase, hKistarEqK, hP2Mi⟩

private theorem CFSG.section14_7_partner_core_fields
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (hKi :
      section12HallSubgroupIn (section14KappaPrimes Mi)
        (section14_7_KiOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) Mi)
    (hMiP : Mi ∈ section14MFamilyP G)
    (hMi_not_conj : ¬ section14ConjugateSubgroups Mi M)
    (hKiEqBase :
      section14_7_KiOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam =
        section14KStar M K)
    (hKistarEqK :
      section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = K)
    (hP2Mi : M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G) :
    Mi ∈ section14MFamilyP G ∧
      ¬ section14ConjugateSubgroups Mi M ∧
      (∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups K →
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {Mi}) ∧
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi ∧
      K = section14KStar Mi (section14KStar M K) ∧
      section14ZInternalDirectProduct M K ∧
      ((M ∈ section14MFamilyP2 G ∧ Nat.Prime (Nat.card K)) ∨
        (Mi ∈ section14MFamilyP2 G ∧
          Nat.Prime (Nat.card (section14KStar M K)))) := by
  rcases
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam with
    ⟨hXi, _hMi, _hKi0, _hKstarKi, _hMiP0, _hMi_not_conj0, _hZeqZi, _hXiLeKistar,
      _hKiLeZ, _hKistarLeK⟩
  have hPrimeOrderUnique :
      ∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups K →
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {Mi} := by
    intro X hX
    have hXKistar :
        X ∈ section12PrimeOrderSubgroups
          (section14_7_KstarOfOvergroupFamily
            (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam) := by
      simpa [hKistarEqK] using hX
    exact
      (proposition_14_2_c
        (G := G) (M := Mi)
        (K := section14_7_KiOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam)
        hMiP hKi).2 X hXKistar
  have hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi := by
    simpa [hKiEqBase] using hKi
  have hKstarEq :
      section14KStar Mi (section14KStar M K) = K := by
    simpa [section14_7_KstarOfOvergroupFamily, hKiEqBase] using hKistarEqK
  have hZdp :
      section14ZInternalDirectProduct M K := by
    exact (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK _ hXi).2.2
  have hPrimeAlt :
      (M ∈ section14MFamilyP2 G ∧ Nat.Prime (Nat.card K)) ∨
        (Mi ∈ section14MFamilyP2 G ∧
          Nat.Prime (Nat.card (section14KStar M K))) := by
    rcases hP2Mi with hMP2 | hMiP2
    · exact Or.inl ⟨hMP2, (proposition_14_2_g (G := G) (M := M) (K := K) hMP2 hK).2.1⟩
    · exact Or.inr ⟨hMiP2, by
        simpa [hKiEqBase] using
          (proposition_14_2_g
            (G := G) (M := Mi)
            (K := section14_7_KiOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam)
            hMiP2 hKi).2.1⟩
  exact ⟨hMiP, hMi_not_conj, hPrimeOrderUnique, hHallKappaBase, hKstarEq.symm, hZdp, hPrimeAlt⟩

private theorem CFSG.section14_7_factorUnion_eq_kstar_union_k_of_singleton
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (huniqFam : ∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi)
    (hKistarEqK :
      section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = K) :
    section14_7_factorUnion (G := G) (M := M) (K := K) hM hK =
      ((section14KStar M K : Set G) ∪ (K : Set G)) := by
  classical
  have hFamUnion :
      (⋃ i : {Mj // Mj ∈ section14_7_overgroupFamily K},
          (section14_7_KstarOfOvergroupFamily
            (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2 : Set G)) =
        (K : Set G) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      have hiEq : i.1 = Mi := huniqFam i.1 i.2
      have hiSub : i = ⟨Mi, hMiFam⟩ := Subtype.ext hiEq
      simpa [hiSub, hKistarEqK] using hxi
    · intro hxK
      exact Set.mem_iUnion.mpr ⟨⟨Mi, hMiFam⟩, by simpa [hKistarEqK] using hxK⟩
  simp [section14_7_factorUnion, hFamUnion]

public theorem CFSG.section14_7_TSet_eq_widehatZ_of_singleton
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (huniqFam : ∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi)
    (hKistarEqK :
      section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = K) :
    section14_7_TSet (G := G) (M := M) (K := K) hM hK = section14WidehatZ M K := by
  simp [section14_7_TSet, section14WidehatZ,
    section14_7_factorUnion_eq_kstar_union_k_of_singleton
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK,
    Set.union_comm]

omit [IsMinCE G] in
private theorem CFSG.section14_7_overgroupFamily_card_eq_one_of_singleton
    {M K Mi : Subgroup G}
    (_hM : M ∈ section14MFamilyP G)
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (huniqFam : ∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi) :
    Nat.card {Mj // Mj ∈ section14_7_overgroupFamily K} = 1 := by
  refine Nat.card_eq_one_iff_unique.mpr ⟨?_, ⟨⟨Mi, hMiFam⟩⟩⟩
  constructor
  intro i j
  apply Subtype.ext
  exact (huniqFam i.1 i.2).trans (huniqFam j.1 j.2).symm

private theorem CFSG.section14_7_card_TSet_add_eq_z_add_one_of_singleton
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (huniqFam : ∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi)
    (hKistarEqK :
      section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = K) :
    Nat.card (section14_7_TSet (G := G) (M := M) (K := K) hM hK) +
        Nat.card (section14KStar M K) + Nat.card K =
      Nat.card (section14Z M K) + 1 := by
  classical
  let I : Type _ := {Mj // Mj ∈ section14_7_overgroupFamily K}
  have hSum :
      ∑ i : I,
          Nat.card
            (section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) =
        Nat.card K := by
    have hterm :
        ∀ i : I,
          Nat.card
              (section14_7_KstarOfOvergroupFamily
                (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) =
            Nat.card K := by
      intro i
      have hiEq : i.1 = Mi := huniqFam i.1 i.2
      have hiSub : i = ⟨Mi, hMiFam⟩ := Subtype.ext hiEq
      simp [hiSub, hKistarEqK]
    calc
      ∑ i : I,
            Nat.card
              (section14_7_KstarOfOvergroupFamily
                (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) =
          ∑ _i : I, Nat.card K := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact hterm i
      _ = Fintype.card I * Nat.card K := by
        simp
      _ = Nat.card K := by
        rw [show Fintype.card I = 1 by
          simpa [I, Nat.card_eq_fintype_card] using
            section14_7_overgroupFamily_card_eq_one_of_singleton
              (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam]
        simp
  have hCard :=
    section14_7_card_TSet_add (G := G) (M := M) (K := K) hM hK
  have hFamCard :
      Nat.card I = 1 := by
    simpa [I] using
    section14_7_overgroupFamily_card_eq_one_of_singleton
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam
  have hSum' :
      ∑ i : I,
          Nat.card
            (section14_7_KstarOfOvergroupFamily
              (G := G) (M := M) (K := K) (Mi := i.1) hM hK i.2) =
        Nat.card K := by
    simpa [I] using hSum
  have hFamCard' :
      Nat.card I = 1 := by
    simpa using hFamCard
  have hCard' := hCard
  rw [hFamCard'] at hCard'
  rw [← hSum']
  simpa using hCard'

private theorem CFSG.section14_q_card_formula_of_widehat
    {k kstar z idx g t : ℕ}
    (hk : 0 < k)
    (hkstar : 0 < kstar)
    (hkz : k * kstar = z)
    (hzg : z * idx = g)
    (ht : t + kstar + k = z + 1) :
    (((t * idx : ℕ) : ℚ)) =
      (1 - (1 : ℚ) / (k : ℚ) - (1 : ℚ) / (kstar : ℚ) +
        (1 : ℚ) / ((k : ℚ) * (kstar : ℚ))) * (g : ℚ) := by
  have hz : 0 < z := by
    rw [← hkz]
    exact Nat.mul_pos hk hkstar
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have hkstar0 : (kstar : ℚ) ≠ 0 := by positivity
  have hz0 : (z : ℚ) ≠ 0 := by positivity
  have hkzQ : (k : ℚ) * (kstar : ℚ) = z := by
    exact_mod_cast hkz
  have hzgQ : (z : ℚ) * idx = g := by
    exact_mod_cast hzg
  have htQ : (t : ℚ) = z + 1 - kstar - k := by
    have htQ' : (t : ℚ) + kstar + k = z + 1 := by
      exact_mod_cast ht
    linarith
  have hidxQ : (idx : ℚ) = (g : ℚ) / z := by
    apply (eq_div_iff hz0).2
    linarith [hzgQ]
  have hkidxQ : (k : ℚ) * idx = (g : ℚ) / kstar := by
    apply (eq_div_iff hkstar0).2
    calc
      ((k : ℚ) * idx) * kstar = ((k : ℚ) * kstar) * idx := by ring
      _ = z * idx := by rw [hkzQ]
      _ = g := hzgQ
  have hkstaridxQ : (kstar : ℚ) * idx = (g : ℚ) / k := by
    apply (eq_div_iff hk0).2
    calc
      ((kstar : ℚ) * idx) * k = ((k : ℚ) * kstar) * idx := by ring
      _ = z * idx := by rw [hkzQ]
      _ = g := hzgQ
  calc
    (((t * idx : ℕ) : ℚ)) = (t : ℚ) * idx := by norm_num
    _ = (((z : ℚ) + 1 - kstar - k) * idx) := by rw [htQ]
    _ = (z : ℚ) * idx + idx - (kstar : ℚ) * idx - (k : ℚ) * idx := by ring
    _ = (g : ℚ) + (g : ℚ) / z - (g : ℚ) / k - (g : ℚ) / kstar := by
      rw [hzgQ, hkstaridxQ, hkidxQ, hidxQ]
    _ = (1 - (1 : ℚ) / (k : ℚ) - (1 : ℚ) / (kstar : ℚ) +
        (1 : ℚ) / ((k : ℚ) * (kstar : ℚ))) * (g : ℚ) := by
      field_simp [hk0, hkstar0, hz0, hkzQ]
      nlinarith [hkzQ]

private theorem CFSG.section14_7_widehat_ti_of_singleton
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (huniqFam : ∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi)
    (hKistarEqK :
      section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = K) :
    section14TISet (section14WidehatZ M K) := by
  simpa [section14_7_TSet_eq_widehatZ_of_singleton
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK] using
    section14_7_TSet_ti (G := G) (M := M) (K := K) hM hK

private theorem CFSG.section14_7_widehat_normalizer_eq_z_of_singleton
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (huniqFam : ∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi)
    (hKistarEqK :
      section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = K) :
    Subgroup.normalizer (section14WidehatZ M K) = section14Z M K := by
  simpa [section14_7_TSet_eq_widehatZ_of_singleton
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK] using
    section14_7_normalizer_TSet_eq_z (G := G) (M := M) (K := K) hM hK

private theorem CFSG.section14_7_card_conjClosure_widehat_of_singleton
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiFam : Mi ∈ section14_7_overgroupFamily K)
    (huniqFam : ∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mi)
    (hKistarEqK :
      section14_7_KstarOfOvergroupFamily
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam = K) :
    (Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ) =
      (1 - (1 : ℚ) / (Nat.card K : ℚ) -
          (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
          (1 : ℚ) / ((Nat.card K : ℚ) *
            (Nat.card (section14KStar M K) : ℚ))) * (Nat.card G : ℚ) := by
  let T : Set G := section14_7_TSet (G := G) (M := M) (K := K) hM hK
  let Z : Subgroup G := section14Z M K
  have hk : 0 < Nat.card K := Nat.card_pos
  have hkstar : 0 < Nat.card (section14KStar M K) := Nat.card_pos
  have hkz :
      Nat.card K * Nat.card (section14KStar M K) = Nat.card Z := by
    simpa [Z, Nat.mul_comm] using
      section14_7_card_k_mul_card_kstar_eq_z (G := G) (M := M) (K := K) hM hK
  have hzg :
      Nat.card Z * Z.index = Nat.card G := by
    exact Subgroup.card_mul_index (H := Z)
  have ht :
      Nat.card T + Nat.card (section14KStar M K) + Nat.card K =
        Nat.card Z + 1 := by
    simpa [T, Z] using
      section14_7_card_TSet_add_eq_z_add_one_of_singleton
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK
  have hCardNat :
      Nat.card (section14ConjugacyClosure T) = Nat.card T * Z.index := by
    simpa [T, Z] using
      section14_7_card_conjClosure_TSet (G := G) (M := M) (K := K) hM hK
  have hCardQ :
      (Nat.card (section14ConjugacyClosure T) : ℚ) =
        (1 - (1 : ℚ) / (Nat.card K : ℚ) -
            (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
            (1 : ℚ) / ((Nat.card K : ℚ) *
              (Nat.card (section14KStar M K) : ℚ))) * (Nat.card G : ℚ) := by
    have hCardQ0 :
        (Nat.card (section14ConjugacyClosure T) : ℚ) =
          ((Nat.card T * Z.index : ℕ) : ℚ) := by
      exact_mod_cast hCardNat
    rw [hCardQ0]
    exact
      section14_q_card_formula_of_widehat
        (k := Nat.card K)
        (kstar := Nat.card (section14KStar M K))
        (z := Nat.card Z)
        (idx := Z.index)
        (g := Nat.card G)
        (t := Nat.card T)
        hk hkstar hkz hzg ht
  simpa [T, section14_7_TSet_eq_widehatZ_of_singleton
    (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK] using hCardQ

private theorem CFSG.section14_7_msigma_inf_bot_of_partner
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiP : Mi ∈ section14MFamilyP G)
    (hMi_not_conj : ¬ section14ConjugateSubgroups Mi M)
    (hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi)
    (hP2Mi : M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G) :
    section10Msigma M ⊓ section10Msigma Mi = ⊥ := by
  rcases hP2Mi with hMP2 | hMiP2
  · have hconj : ∀ g : G, Mi.conjBy g ≠ M := by
      intro g hMg
      exact hMi_not_conj ⟨g⁻¹, by
        simpa [section11_conjBy_inv] using congrArg (fun H => H.conjBy g⁻¹) hMg⟩
    have hnil : Group.IsNilpotent (section10Msigma M) :=
      (proposition_14_2_g (G := G) (M := M) (K := K) hMP2 hK).2.2.1
    exact disjoint_iff.mp (lemma_10_12_b (G := G) hM.1 hMiP.1 hconj hnil).1
  · have hconj : ∀ g : G, M.conjBy g ≠ Mi := by
      intro g hMg
      exact hMi_not_conj ⟨g, hMg.symm⟩
    have hnil : Group.IsNilpotent (section10Msigma Mi) :=
      (proposition_14_2_g
        (G := G) (M := Mi) (K := section14KStar M K) hMiP2 hHallKappaBase).2.2.1
    exact disjoint_iff.mp (Disjoint.symm <| (lemma_10_12_b (G := G) hMiP.1 hM.1 hconj hnil).1)

private theorem CFSG.section14_7_partner_hall_sigma
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hMiP : Mi ∈ section14MFamilyP G)
    (hMi_not_conj : ¬ section14ConjugateSubgroups Mi M)
    (hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi)
    (hP2Mi : M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G) :
    section12HallSubgroupIn (section10SigmaPrimes M) (section14KStar M K) Mi := by
  have hKstarLeMi : section14KStar M K ≤ Mi := hHallKappaBase.1
  have hKstarSigma :
      IsPiSubgroup (G := G) (section10SigmaPrimes M) (section14KStar M K) := by
    intro p hpKstar
    obtain ⟨X, hX⟩ :=
      section14_exists_primeOrderSubgroupIn_of_dvd_card
        (G := G) (A := section14KStar M K) (p := p) hpKstar
    exact section14_c_sigma_of_primeOrder_le_kstar (G := G) (M := M) (K := K) hM hX
  letI : MulDistribMulAction Unit Mi := {
    smul := fun _ y => y
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hKstarSubSigma :
      IsPiSubgroup (G := Mi) (section10SigmaPrimes M)
        ((section14KStar M K).subgroupOf Mi) := by
    intro p hp
    have hcard :
        Nat.card ((section14KStar M K).subgroupOf Mi) = Nat.card (section14KStar M K) :=
      section12_card_subgroupOf_eq hKstarLeMi
    exact hKstarSigma p (by simpa [hcard] using hp)
  have hKstarSubInv : IsInvariant Unit Mi ((section14KStar M K).subgroupOf Mi) := by
    refine ⟨?_⟩
    intro _ y
    simp
  have hsolvMi : IsSolvable Mi :=
    IsMinCE.proper_subgroups_solvable Mi (lt_top_iff_ne_top.mpr hMi.1.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card Mi) := by simp
  obtain ⟨Ysub, hYsubHall, _hYsubInv, hKstarSubLeY⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := Mi) (A := Unit) hsolvMi hcop (section10SigmaPrimes M)
      ((section14KStar M K).subgroupOf Mi) hKstarSubSigma hKstarSubInv
  let Y : Subgroup G := Ysub.map Mi.subtype
  have hY : section12HallSubgroupIn (section10SigmaPrimes M) Y Mi :=
    section14_hallSubgroupIn_map_subtype hYsubHall
  have hKstarLeY : section14KStar M K ≤ Y := by
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hKstarLeMi hy⟩, hKstarSubLeY
        (show (⟨y, hKstarLeMi hy⟩ : Mi) ∈ (section14KStar M K).subgroupOf Mi from hy),
        rfl⟩
  have hYSigma : IsPiSubgroup (G := G) (section10SigmaPrimes M) Y := by
    intro p hpY
    have hpYsub : p.val ∣ Nat.card (Y.subgroupOf Mi) := by
      simpa [Y, section12_card_subgroupOf_eq hY.1] using hpY
    exact hY.2.p_in_pi_of_p_dvd_card p hpYsub
  have hYinfKstar : Y ⊓ section14KStar M K ≠ ⊥ := by
    intro hbot
    have hle : section14KStar M K ≤ ⊥ := by
      intro z hz
      have hzinf : z ∈ Y ⊓ section14KStar M K := ⟨hKstarLeY hz, hz⟩
      simpa [hbot] using hzinf
    exact
      (section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK)
        (le_bot_iff.mp hle)
  have hYleMsigma : Y ≤ section10Msigma M :=
    proposition_14_2_f (G := G) (M := M) (K := K) hM hK Y hYSigma hYinfKstar
  obtain ⟨U, h14a⟩ := proposition_14_2_a (G := G) (M := M) (K := K) hM hK
  have hKnormSigma : K ≤ Subgroup.normalizer (section10Msigma M : Set G) := h14a.1.1
  have hXiLeMsigmaMi : Xi ≤ section10Msigma Mi :=
    proposition_14_2_b2 (G := G) (M := M) (K := K) hM hK Xi hXi Mi hMi
  have hMsigmaInfBot :=
    section14_7_msigma_inf_bot_of_partner
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiP hMi_not_conj
      hHallKappaBase hP2Mi
  have hCentEq :
      subgroupCentralizerIn (section10Msigma M) Xi = section14KStar M K :=
    section14_b1_centralizer_eq_kstar_of_prime_manner
      (G := G) (M := M) (K := K) (X := Xi) h14a.1 hXi
  have hYleCent : Y ≤ subgroupCentralizerIn (section10Msigma M) Xi := by
    intro y hyY
    refine ⟨hYleMsigma hyY, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr <| by
      intro x hxXi
      have hyMi : y ∈ Mi := hY.1 hyY
      have hxK : x ∈ K := hXi.1 hxXi
      have hxNormSigma : x ∈ Subgroup.normalizer (section10Msigma M : Set G) := hKnormSigma hxK
      have hyInvSigma : y⁻¹ ∈ section10Msigma M := (section10Msigma M).inv_mem (hYleMsigma hyY)
      have hxyInvxSigma : x * y⁻¹ * x⁻¹ ∈ section10Msigma M :=
        ((Subgroup.mem_normalizer_iff.mp hxNormSigma) _).1 hyInvSigma
      have hcommSigma : y * x * y⁻¹ * x⁻¹ ∈ section10Msigma M := by
        simpa [mul_assoc] using (section10Msigma M).mul_mem (hYleMsigma hyY) hxyInvxSigma
      have hyNormSigmaMi : y ∈ Subgroup.normalizer (section10Msigma Mi : Set G) :=
        (section12_le_normalizer_msigma (M := Mi)) hyMi
      have hyxyInvSigmaMi : y * x * y⁻¹ ∈ section10Msigma Mi :=
        ((Subgroup.mem_normalizer_iff.mp hyNormSigmaMi) _).1 (hXiLeMsigmaMi hxXi)
      have hxInvSigmaMi : x⁻¹ ∈ section10Msigma Mi :=
        (section10Msigma Mi).inv_mem (hXiLeMsigmaMi hxXi)
      have hcommSigmaMi : y * x * y⁻¹ * x⁻¹ ∈ section10Msigma Mi := by
        simpa [mul_assoc] using (section10Msigma Mi).mul_mem hyxyInvSigmaMi hxInvSigmaMi
      have hcommBot : y * x * y⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hMsigmaInfBot]
        exact ⟨hcommSigma, hcommSigmaMi⟩
      have hcommOne : y * x * y⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp hcommBot
      have hyx : y * x = x * y := by
        have hmul := congrArg (fun t : G => t * (x * y)) hcommOne
        simpa [mul_assoc] using hmul
      exact hyx.symm
  have hYleKstar : Y ≤ section14KStar M K := by
    simpa [hCentEq] using hYleCent
  have hYeq : Y = section14KStar M K := le_antisymm hYleKstar hKstarLeY
  simpa [hYeq] using hY

omit [IsMinCE G] in
private theorem CFSG.section14_7_cyclic_of_isZGroup_of_le_nilpotent
    {H N : Subgroup G}
    (hHZ : IsZGroup H)
    (hHN : H ≤ N)
    (hNnil : Group.IsNilpotent N) :
    IsCyclic H := by
  let Hsub : Subgroup N := H.subgroupOf N
  let e : Hsub ≃* H := Subgroup.subgroupOfEquivOfLe (H := H) (K := N) hHN
  letI : IsZGroup H := hHZ
  letI : IsZGroup Hsub := IsZGroup.of_injective (f := e.toMonoidHom) e.injective
  letI : Group.IsNilpotent N := hNnil
  letI : Group.IsNilpotent Hsub := inferInstance
  exact e.isCyclic.1 inferInstance

private theorem CFSG.section14_7_k_cyclic_of_partner
    {M K Mi : Subgroup G}
    (_hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hMiP : Mi ∈ section14MFamilyP G)
    (hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi)
    (hKEqPartnerKstar : K = section14KStar Mi (section14KStar M K))
    (hP2Mi : M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G) :
    IsCyclic K := by
  rcases hP2Mi with hMP2 | hMiP2
  · letI : Fact (Nat.card K).Prime :=
        ⟨(proposition_14_2_g (G := G) (M := M) (K := K) hMP2 hK).2.1⟩
    exact isCyclic_of_prime_card (p := Nat.card K) rfl
  · have hKleMsigmaMi : K ≤ section10Msigma Mi := by
      rw [hKEqPartnerKstar]
      exact inf_le_left
    exact
      section14_7_cyclic_of_isZGroup_of_le_nilpotent
        (G := G) (H := K) (N := section10Msigma Mi)
        (section14_hall_kappa_isZGroup (G := G) hK)
        hKleMsigmaMi
        ((proposition_14_2_g
          (G := G) (M := Mi) (K := section14KStar M K) hMiP2 hHallKappaBase).2.2.1)

private theorem CFSG.section14_7_kstar_cyclic_of_partner
    {M K Mi : Subgroup G}
    (_hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi)
    (hP2Mi : M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G) :
    IsCyclic (section14KStar M K) := by
  rcases hP2Mi with hMP2 | hMiP2
  · exact
      section14_7_cyclic_of_isZGroup_of_le_nilpotent
        (G := G) (H := section14KStar M K) (N := section10Msigma M)
        (section14_hall_kappa_isZGroup (G := G) hHallKappaBase)
        (show section14KStar M K ≤ section10Msigma M from inf_le_left)
        ((proposition_14_2_g (G := G) (M := M) (K := K) hMP2 hK).2.2.1)
  · letI : Fact (Nat.card (section14KStar M K)).Prime :=
        ⟨(proposition_14_2_g
          (G := G) (M := Mi) (K := section14KStar M K) hMiP2 hHallKappaBase).2.1⟩
    exact isCyclic_of_prime_card (p := Nat.card (section14KStar M K)) rfl

private theorem CFSG.section14_7_card_coprime_k_kstar
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    Nat.Coprime (Nat.card K) (Nat.card (section14KStar M K)) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqK hqKstar
  let p : Nat.Primes := ⟨q, hqprime⟩
  have hpKsub : p.val ∣ Nat.card (K.subgroupOf M) := by
    simpa [section12_card_subgroupOf_eq hK.1] using hqK
  have hpκ : p ∈ section14KappaPrimes M :=
    hK.2.p_in_pi_of_p_dvd_card p hpKsub
  have hpMsigma : p.val ∣ Nat.card (section10Msigma M) := by
    exact hqKstar.trans <| Subgroup.card_dvd_of_le (by
      intro x hx
      exact hx.1)
  have hpMsigmaSub : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
    have hcardMsigma :
        Nat.card (section10MsigmaSubgroup M) = Nat.card (section10Msigma M) := by
      simpa [section14_msigma_subgroupOf_eq (M := M)] using
        (section12_card_subgroupOf_eq (section14_msigma_le M))
    rw [hcardMsigma]
    exact hpMsigma
  have hpσ : p ∈ section10SigmaPrimes M :=
    ((theorem_10_2_b hM.1).2).p_in_pi_of_p_dvd_card p hpMsigmaSub
  exact section14_kappa_subset_not_sigma (M := M) hpκ hpσ

private theorem CFSG.section14_7_z_cyclic_of_partner
    {M K Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiP : Mi ∈ section14MFamilyP G)
    (hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi)
    (hKEqPartnerKstar : K = section14KStar Mi (section14KStar M K))
    (hP2Mi : M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G)
    (hZdp : section14ZInternalDirectProduct M K) :
    IsCyclic (section14Z M K) := by
  let Z : Subgroup G := section14Z M K
  let Ksub : Subgroup Z := K.subgroupOf Z
  let Kstarsub : Subgroup Z := (section14KStar M K).subgroupOf Z
  have hKcyc :
      IsCyclic K :=
    section14_7_k_cyclic_of_partner
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiP hHallKappaBase
      hKEqPartnerKstar hP2Mi
  have hKstarcyc :
      IsCyclic (section14KStar M K) :=
    section14_7_kstar_cyclic_of_partner
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hHallKappaBase hP2Mi
  have hKsubcyc : IsCyclic Ksub := by
    exact
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := Z) le_sup_left).isCyclic.2
        hKcyc
  have hKstarsubcyc : IsCyclic Kstarsub := by
    exact
      (Subgroup.subgroupOfEquivOfLe
        (H := section14KStar M K) (K := Z) le_sup_right).isCyclic.2 hKstarcyc
  have hcop :
      Nat.Coprime (Nat.card Ksub) (Nat.card Kstarsub) := by
    simpa [Ksub, Kstarsub, natCard_subgroupOf_eq K Z le_sup_left,
      natCard_subgroupOf_eq (section14KStar M K) Z le_sup_right] using
      section14_7_card_coprime_k_kstar (G := G) (M := M) (K := K) hM hK
  have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
    intro x hxK
    exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hxK)
  have hcomp :
      Ksub.IsComplement' Kstarsub := by
    have hcompKstar :
        ((section14KStar M K).subgroupOf Z).IsComplement' (K.subgroupOf Z) := by
      change
        ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).IsComplement'
          (K.subgroupOf (K ⊔ section14KStar M K))
      exact
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := section14KStar M K) (R := K) hK_norm_Kstar
          (by simpa [disjoint_iff, inf_comm] using hZdp.2.2.2.1)
    exact hcompKstar.symm
  let φ : Ksub × Kstarsub →* Z := {
    toFun := fun x => x.1 * x.2
    map_one' := by
      ext
      simp
    map_mul' := by
      intro x y
      change ((x.1 * y.1) * (x.2 * y.2) : Z) = (x.1 * x.2) * (y.1 * y.2)
      have hcomm :
          Commute (y.1 : Z) (x.2 : Z) := by
        show (y.1 : Z) * x.2 = x.2 * y.1
        apply Subtype.ext
        exact
          (Subgroup.mem_centralizer_iff.mp (hZdp.2.2.2.2 y.1.2) (x.2 : Z) x.2.2).symm
      calc
        ((x.1 * y.1) * (x.2 * y.2) : Z) = x.1 * (y.1 * x.2) * y.2 := by
          simp [mul_assoc]
        _ =
            x.1 * (x.2 * y.1) * y.2 := by
          rw [hcomm.eq]
        _ =
            (x.1 * x.2) * (y.1 * y.2) := by
          simp [mul_assoc]
    }
  have hφ_bij : Function.Bijective φ := by
    simpa [φ] using
      (Subgroup.isComplement_iff_bijective (s := Ksub) (t := Kstarsub)).1
        ((Subgroup.isComplement'_def).1 hcomp)
  have hprodcyc : IsCyclic (Ksub × Kstarsub) := by
    exact (Group.isCyclic_prod_iff).2 ⟨hKsubcyc, hKstarsubcyc, hcop⟩
  exact isCyclic_of_surjective φ hφ_bij.2

private theorem CFSG.section14_7_u_le_ambientDerived
    {M K U : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hUhall :
      section12HallSubgroupIn
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M)
    (hUreg : section14ActsRegularlyOn K U) :
    U ≤ ambientDerivedSubgroup M := by
  have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM hK
  have hfix : subgroupCentralizerIn U K = ⊥ :=
    section14_subgroupCentralizerIn_eq_bot_of_regular (G := G) hKne hUreg
  rcases hK with ⟨hKM, hHallK⟩
  rcases hUhall with ⟨hUM, hHallU⟩
  have hcop : Nat.Coprime (Nat.card K) (Nat.card U) := by
    refine Nat.coprime_of_dvd ?_
    intro q hqprime hqK hqU
    let q' : Nat.Primes := ⟨q, hqprime⟩
    have hqκ : q' ∈ section14KappaPrimes M :=
      hHallK.p_in_pi_of_p_dvd_card q'
        (by simpa [section12_card_subgroupOf_eq hKM, q'] using hqK)
    have hqπ :
        q' ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) :=
      hHallU.p_in_pi_of_p_dvd_card q'
        (by simpa [section12_card_subgroupOf_eq hUM, q'] using hqU)
    exact hqπ (Or.inl hqκ)
  have hsolvU : IsSolvable U :=
    section14_solvable_of_le_maximal hM.1 hUM
  have hUleComm : U ≤ ⁅U, K⁆ :=
    section8_le_commutator_of_subgroupCentralizerIn_eq_bot
      (Y := U) (R := K) hsolvU hUreg.1 hcop hfix
  have hcommLeDer : ⁅U, K⁆ ≤ ambientDerivedSubgroup M := by
    have hcommLe : ⁅U, K⁆ ≤ ⁅M, M⁆ :=
      Subgroup.commutator_mono hUM hKM
    simpa [section12_ambientDerivedSubgroup_eq_commutator] using hcommLe
  exact hUleComm.trans hcommLeDer

private theorem CFSG.section14_7_msigma_le_ambientDerived
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    section10Msigma M ≤ ambientDerivedSubgroup M := by
  have hσsubLe : section10MsigmaSubgroup M ≤ derivedSubgroup M :=
    (theorem_10_2_c (G := G) hM).2
  intro x hx
  refine Subgroup.mem_map.mpr ?_
  refine ⟨⟨x, section14_msigma_le M hx⟩, ?_, rfl⟩
  have hxsub0 : (⟨x, section14_msigma_le M hx⟩ : M) ∈ (section10Msigma M).subgroupOf M := by
    exact hx
  have hxsub : (⟨x, section14_msigma_le M hx⟩ : M) ∈ section10MsigmaSubgroup M := by
    simpa [section14_msigma_subgroupOf_eq (G := G) (M := M)] using hxsub0
  exact hσsubLe hxsub

private theorem CFSG.section14_7_complement_ambientDerived_of_k_cyclic
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKcyc : IsCyclic K) :
    section12ComplementIn M K (ambientDerivedSubgroup M) := by
  classical
  obtain ⟨U, h14a⟩ := proposition_14_2_a (G := G) (M := M) (K := K) hM hK
  let N : Subgroup G := U ⊔ section10Msigma M
  have hcomp : section14NormalComplementIn M K N := by
    simpa [N] using h14a.2.2.2.2
  have hNleDer : N ≤ ambientDerivedSubgroup M := by
    refine sup_le ?_ ?_
    · exact
        section14_7_u_le_ambientDerived
          (G := G) (M := M) (K := K) (U := U) hM hK h14a.2.2.1 h14a.2.2.2.1
    · exact section14_7_msigma_le_ambientDerived (G := G) hM.1
  have hDerLeN : ambientDerivedSubgroup M ≤ N := by
    rcases hcomp with ⟨hcompIn, hNnorm⟩
    rcases hcompIn with ⟨hKM, hNM, hMeq, hdisj⟩
    rcases hNnorm with ⟨_hNM', hNnormal⟩
    let Ksub : Subgroup M := K.subgroupOf M
    let Nsub : Subgroup M := N.subgroupOf M
    have hMnormN : M ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).1 hNnormal
    have hKNnorm : K ≤ Subgroup.normalizer (N : Set G) := hKM.trans hMnormN
    have hcompSub : Ksub.IsComplement' Nsub := by
      have hcomp0 :
          (N.subgroupOf (K ⊔ N)).IsComplement' (K.subgroupOf (K ⊔ N)) := by
        simpa [inf_comm] using
          section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
            (G := G) (H := N) (R := K) hKNnorm
            (by simpa [disjoint_iff, inf_comm] using hdisj)
      change (K.subgroupOf M).IsComplement' (N.subgroupOf M)
      rw [hMeq]
      exact hcomp0.symm
    have hKsubcyc : IsCyclic Ksub := by
      exact (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hKM).isCyclic.2 hKcyc
    have hquotcyc : IsCyclic (M ⧸ Nsub) :=
      hcompSub.QuotientMulEquiv.isCyclic.2 hKsubcyc
    letI : IsCyclic (M ⧸ Nsub) := hquotcyc
    letI : CommGroup (M ⧸ Nsub) := hquotcyc.commGroup
    let q : M →* M ⧸ Nsub := QuotientGroup.mk' Nsub
    have hderLeKer : derivedSubgroup M ≤ q.ker :=
      Abelianization.commutator_subset_ker q
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨d, hd, rfl⟩
    have hdKer : (d : M) ∈ q.ker := hderLeKer hd
    have hdNsub : (d : M) ∈ Nsub := by
      simpa [q, QuotientGroup.ker_mk'] using hdKer
    simpa [Nsub, Subgroup.mem_subgroupOf] using hdNsub
  have hEq : N = ambientDerivedSubgroup M := le_antisymm hNleDer hDerLeN
  simpa [hEq] using hcomp.1

omit [IsMinCE G] in
private theorem CFSG.section14_7_kappa_eq_tau1_of_complement_ambientDerived
    {M K : Subgroup G}
    (_hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hComp : section12ComplementIn M K (ambientDerivedSubgroup M)) :
    section14KappaPrimes M = section12Tau1Primes M := by
  classical
  rcases hComp with ⟨hKM, hDM, hMeq, hdisj⟩
  let Ksub : Subgroup M := K.subgroupOf M
  let Dsub : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  have hMnormD : M ≤ Subgroup.normalizer (ambientDerivedSubgroup M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (section12_ambientDerivedSubgroup_le (G := G) (E := M))).1
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hKDnorm : K ≤ Subgroup.normalizer (ambientDerivedSubgroup M : Set G) := hKM.trans hMnormD
  let S : Subgroup G := K ⊔ ambientDerivedSubgroup M
  have hcompSub : Ksub.IsComplement' Dsub := by
    have hcomp0 :
        ((ambientDerivedSubgroup M).subgroupOf S).IsComplement'
          (K.subgroupOf S) := by
      simpa [S, inf_comm] using
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := ambientDerivedSubgroup M) (R := K) hKDnorm
          (by simpa [disjoint_iff, inf_comm] using hdisj)
    have hMeq' : S = M := by
      simpa [S] using hMeq.symm
    have hdisjSub : Disjoint Ksub Dsub := by
      rw [Subgroup.disjoint_def]
      intro x hxK hxD
      apply Subtype.ext
      exact (Subgroup.disjoint_def.mp hdisj) hxK hxD
    have hcardMul0 :
        Nat.card K * Nat.card (ambientDerivedSubgroup M) =
          Nat.card S := by
      calc
        Nat.card K * Nat.card (ambientDerivedSubgroup M) =
            Nat.card (K.subgroupOf S) *
              Nat.card ((ambientDerivedSubgroup M).subgroupOf S) := by
                rw [natCard_subgroupOf_eq K S le_sup_left,
                  natCard_subgroupOf_eq (ambientDerivedSubgroup M) S le_sup_right]
        _ = Nat.card S := hcomp0.symm.card_mul
    have hcardMul :
        Nat.card Ksub * Nat.card Dsub = Nat.card M := by
      calc
        Nat.card Ksub * Nat.card Dsub =
            Nat.card K * Nat.card (ambientDerivedSubgroup M) := by
              rw [section12_card_subgroupOf_eq hKM, section12_card_subgroupOf_eq hDM]
        _ = Nat.card S := hcardMul0
        _ = Nat.card M := by rw [hMeq']
    exact Subgroup.isComplement'_of_card_mul_and_disjoint hcardMul hdisjSub
  apply Set.Subset.antisymm
  · intro p hpκ
    refine ⟨section14_kappa_subset_not_sigma (M := M) hpκ, ?_, ?_⟩
    · intro hpD
      have hpDsubCard : p.val ∣ Nat.card Dsub := by
        have hcardD :
            Nat.card Dsub = Nat.card (ambientDerivedSubgroup M) := by
          simpa [Dsub] using
            (section12_card_subgroupOf_eq
              (section12_ambientDerivedSubgroup_le (G := G) (E := M)))
        have hpAmbD : p.val ∣ Nat.card (ambientDerivedSubgroup M) := by
          have hcardMap :
              Nat.card (ambientDerivedSubgroup M) = Nat.card (derivedSubgroup M) := by
            simpa [ambientDerivedSubgroup] using
              (Subgroup.card_map_of_injective
                (K := derivedSubgroup M) (f := M.subtype) M.subtype_injective)
          rw [hcardMap]
          simpa [subgroupPrimeSet] using hpD
        rw [hcardD]
        exact hpAmbD
      have hpIdx : p.val ∣ Ksub.index := by
        have hidx : Ksub.index = Nat.card Dsub := hcompSub.symm.index_eq_card
        rw [hidx]
        exact hpDsubCard
      exact (hK.2.p_in_pi_of_p_dvd_index p hpIdx) hpκ
    · exact section12_tau13_primeRank_eq_one (section14_kappa_subset_tau13 hpκ)
  · intro p hpτ1
    have hpM : p.val ∣ Nat.card M :=
      section14_prime_dvd_card_of_primeRank_pos
        (R := M) (p := p) (by simp [hpτ1.2.2])
    have hcardK : Nat.card Ksub = Nat.card K := section12_card_subgroupOf_eq hKM
    have hcardD : Nat.card Dsub = Nat.card (ambientDerivedSubgroup M) := by
      simpa [Dsub] using
        (section12_card_subgroupOf_eq
          (section12_ambientDerivedSubgroup_le (G := G) (E := M)))
    have hcardMap :
        Nat.card (ambientDerivedSubgroup M) = Nat.card (derivedSubgroup M) := by
      simpa [ambientDerivedSubgroup] using
        (Subgroup.card_map_of_injective
          (K := derivedSubgroup M) (f := M.subtype) M.subtype_injective)
    have hmul : Nat.card Ksub * Nat.card Dsub = Nat.card M := hcompSub.card_mul
    have hpKsub : p.val ∣ Nat.card Ksub := by
      have hpProd : p.val ∣ Nat.card Ksub * Nat.card Dsub := by
        rw [hmul]
        exact hpM
      rcases p.2.dvd_mul.mp hpProd with hpKsub | hpDsub
      · exact hpKsub
      · have hpDer : p.val ∣ Nat.card (derivedSubgroup M) := by
          rw [← hcardMap, ← hcardD]
          exact hpDsub
        exact False.elim (hpτ1.2.1 <| by simpa [subgroupPrimeSet] using hpDer)
    exact hK.2.p_in_pi_of_p_dvd_card p hpKsub

private theorem CFSG.section14_7_msigma_inf_partner_eq_kstar
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hMiP : Mi ∈ section14MFamilyP G)
    (hMi_not_conj : ¬ section14ConjugateSubgroups Mi M)
    (hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi)
    (hHallSigmaBase :
      section12HallSubgroupIn (section10SigmaPrimes M) (section14KStar M K) Mi)
    (hP2Mi : M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G) :
    section10Msigma M ⊓ Mi = section14KStar M K := by
  obtain ⟨U, h14a⟩ := proposition_14_2_a (G := G) (M := M) (K := K) hM hK
  have hKnormSigma : K ≤ Subgroup.normalizer (section10Msigma M : Set G) := h14a.1.1
  have hXiLeMsigmaMi : Xi ≤ section10Msigma Mi :=
    proposition_14_2_b2 (G := G) (M := M) (K := K) hM hK Xi hXi Mi hMi
  have hMsigmaInfBot :=
    section14_7_msigma_inf_bot_of_partner
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiP hMi_not_conj
      hHallKappaBase hP2Mi
  have hCentEq :
      subgroupCentralizerIn (section10Msigma M) Xi = section14KStar M K :=
    section14_b1_centralizer_eq_kstar_of_prime_manner
      (G := G) (M := M) (K := K) (X := Xi) h14a.1 hXi
  apply le_antisymm
  · intro y hy
    have hyMi : y ∈ Mi := hy.2
    have hyCent : y ∈ subgroupCentralizerIn (section10Msigma M) Xi := by
      refine ⟨hy.1, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr <| by
        intro x hxXi
        have hxK : x ∈ K := hXi.1 hxXi
        have hxNormSigma : x ∈ Subgroup.normalizer (section10Msigma M : Set G) := hKnormSigma hxK
        have hyInvSigma : y⁻¹ ∈ section10Msigma M := (section10Msigma M).inv_mem hy.1
        have hxyInvxSigma : x * y⁻¹ * x⁻¹ ∈ section10Msigma M :=
          ((Subgroup.mem_normalizer_iff.mp hxNormSigma) _).1 hyInvSigma
        have hcommSigma : y * x * y⁻¹ * x⁻¹ ∈ section10Msigma M := by
          simpa [mul_assoc] using (section10Msigma M).mul_mem hy.1 hxyInvxSigma
        have hyNormSigmaMi : y ∈ Subgroup.normalizer (section10Msigma Mi : Set G) :=
          section12_le_normalizer_msigma (M := Mi) hyMi
        have hyxyInvSigmaMi : y * x * y⁻¹ ∈ section10Msigma Mi :=
          ((Subgroup.mem_normalizer_iff.mp hyNormSigmaMi) _).1 (hXiLeMsigmaMi hxXi)
        have hxInvSigmaMi : x⁻¹ ∈ section10Msigma Mi :=
          (section10Msigma Mi).inv_mem (hXiLeMsigmaMi hxXi)
        have hcommSigmaMi : y * x * y⁻¹ * x⁻¹ ∈ section10Msigma Mi := by
          simpa [mul_assoc] using (section10Msigma Mi).mul_mem hyxyInvSigmaMi hxInvSigmaMi
        have hcommBot : y * x * y⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := by
          rw [← hMsigmaInfBot]
          exact ⟨hcommSigma, hcommSigmaMi⟩
        have hcommOne : y * x * y⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp hcommBot
        have hyx : y * x = x * y := by
          have hmul := congrArg (fun t : G => t * (x * y)) hcommOne
          simpa [mul_assoc] using hmul
        exact hyx.symm
    simpa [hCentEq] using hyCent
  · intro y hy
    exact ⟨hy.1, hHallSigmaBase.1 hy⟩

private theorem CFSG.section14_7_inter_partner_eq_z
    {M K Xi Mi : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hXi : Xi ∈ section12PrimeOrderSubgroups K)
    (hMi : Mi ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Xi : Set G)))
    (hMiP : Mi ∈ section14MFamilyP G)
    (hMi_not_conj : ¬ section14ConjugateSubgroups Mi M)
    (hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi)
    (hHallSigmaBase :
      section12HallSubgroupIn (section10SigmaPrimes M) (section14KStar M K) Mi)
    (hKEqPartnerKstar : K = section14KStar Mi (section14KStar M K))
    (hP2Mi : M ∈ section14MFamilyP2 G ∨ Mi ∈ section14MFamilyP2 G) :
    M ⊓ Mi = section14Z M K := by
  have hMsigmaInf :
      section10Msigma M ⊓ Mi = section14KStar M K :=
    section14_7_msigma_inf_partner_eq_kstar
      (G := G) (M := M) (K := K) (Xi := Xi) (Mi := Mi)
      hM hK hXi hMi hMiP hMi_not_conj hHallKappaBase hHallSigmaBase hP2Mi
  have hKstarLeInf : section14KStar M K ≤ M ⊓ Mi := by
    intro y hy
    exact ⟨section14_msigma_le M hy.1, hHallSigmaBase.1 hy⟩
  have hKLeInf : K ≤ M ⊓ Mi := by
    intro y hy
    refine ⟨hK.1 hy, ?_⟩
    have hyPartner : y ∈ section14KStar Mi (section14KStar M K) := by
      rw [← hKEqPartnerKstar]
      exact hy
    exact section14_msigma_le Mi hyPartner.1
  have hZLeInf : section14Z M K ≤ M ⊓ Mi := sup_le hKLeInf hKstarLeInf
  have hKstarNormalInInf :
      M ⊓ Mi ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyKstar
      have hyInf : y ∈ section10Msigma M ⊓ Mi := ⟨hyKstar.1, hHallSigmaBase.1 hyKstar⟩
      have hgyInf : g * y * g⁻¹ ∈ section10Msigma M ⊓ Mi := by
        refine ⟨?_, ?_⟩
        · have hgNormMsigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
            section12_le_normalizer_msigma (M := M) hg.1
          exact ((Subgroup.mem_normalizer_iff.mp hgNormMsigma) _).1 hyInf.1
        · exact Mi.mul_mem hg.2 hyInf.2 |> fun h => by simpa [mul_assoc] using Mi.mul_mem h (Mi.inv_mem hg.2)
      simpa [hMsigmaInf] using hgyInf
    · intro hgyKstar
      have hginv : g⁻¹ ∈ M ⊓ Mi := ⟨M.inv_mem hg.1, Mi.inv_mem hg.2⟩
      have hgyInf : g * y * g⁻¹ ∈ section10Msigma M ⊓ Mi :=
        ⟨hgyKstar.1, hHallSigmaBase.1 hgyKstar⟩
      have hyInf : g⁻¹ * (g * y * g⁻¹) * g ∈ section10Msigma M ⊓ Mi := by
        refine ⟨?_, ?_⟩
        · have hginvNormMsigma : g⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
            section12_le_normalizer_msigma (M := M) hginv.1
          simpa [mul_assoc] using ((Subgroup.mem_normalizer_iff.mp hginvNormMsigma) _).1 hgyInf.1
        · exact Mi.mul_mem hginv.2 hgyInf.2 |> fun h => by
            simpa [mul_assoc] using Mi.mul_mem h hg.2
      simpa [mul_assoc, hMsigmaInf] using hyInf
  obtain ⟨p, X0, hX0PrimeIn⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := section14KStar M K)
      (section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK)
  have hX0 : X0 ∈ section12PrimeOrderSubgroups (section14KStar M K) :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX0PrimeIn
  have hNormKstarEqZi :
      subgroupNormalizerIn Mi (section14KStar M K : Set G) =
        section14Z Mi (section14KStar M K) := by
    exact ((proposition_14_2_b1
      (G := G) (M := Mi) (K := section14KStar M K) hMiP hHallKappaBase X0 hX0).2).1
  have hInfLeZi : M ⊓ Mi ≤ section14Z Mi (section14KStar M K) := by
    intro g hg
    have hgNormKstar : g ∈ subgroupNormalizerIn Mi (section14KStar M K : Set G) := by
      exact ⟨hKstarNormalInInf hg, hg.2⟩
    simpa [hNormKstarEqZi] using hgNormKstar
  have hZiEqZ : section14Z Mi (section14KStar M K) = section14Z M K := by
    calc
      section14Z Mi (section14KStar M K) =
          section14KStar Mi (section14KStar M K) ⊔ section14KStar M K := by
            rw [section14Z, sup_comm]
      _ = K ⊔ section14KStar M K := by rw [← hKEqPartnerKstar]
      _ = section14Z M K := by rw [section14Z]
  exact le_antisymm (hInfLeZi.trans (by simp [hZiEqZ])) hZLeInf

private theorem CFSG.section14_7_elementCentralizer_eq_z_of_mem_k
    {M K : Subgroup G} {x : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hKcyc : IsCyclic K)
    (hxK : x ∈ K)
    (hxne : x ≠ 1) :
    elementCentralizerIn M x = section14Z M K := by
  obtain ⟨q, z, hz_zpowx, hzK, _hzne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G) (B := K) hxK hxne
  let X : Subgroup G := Subgroup.zpowers z
  have hX : X ∈ section12PrimeOrderSubgroups K := by
    simpa [X] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
  have hNormXeqZ : subgroupNormalizerIn M (X : Set G) = section14Z M K := by
    exact
      (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK X hX).1.trans
        (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK X hX).2.1
  apply le_antisymm
  · intro g hg
    have hgNormX : g ∈ subgroupNormalizerIn M (X : Set G) := by
      refine ⟨?_, hg.1⟩
      apply centralizer_le_normalizer X
      rw [Subgroup.mem_centralizer_iff]
      intro w hwX
      have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      have hwx : w ∈ Subgroup.zpowers x := (Subgroup.zpowers_le.2 hz_zpowx) hwX
      rcases Subgroup.mem_zpowers_iff.mp hwx with ⟨n, rfl⟩
      exact (hgx.zpow_right n).eq.symm
    simpa [hNormXeqZ] using hgNormX
  · refine sup_le ?_ ?_
    · letI : CommGroup K := hKcyc.commGroup
      intro g hgK
      refine ⟨hK.1 hgK, ?_⟩
      have hgx : g * x = x * g := congrArg Subtype.val (mul_comm (⟨g, hgK⟩ : K) ⟨x, hxK⟩)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hgx
    · intro g hgKstar
      refine ⟨section14_msigma_le M hgKstar.1, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr <|
        (Subgroup.mem_centralizer_iff.mp hgKstar.2 x hxK).symm

private theorem CFSG.section14_7_elementCentralizer_partner_eq_z
    {M K Mi : Subgroup G} {y : G}
    (_hM : M ∈ section14MFamilyP G)
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMiP : Mi ∈ section14MFamilyP G)
    (hHallKappaBase :
      section12HallSubgroupIn (section14KappaPrimes Mi) (section14KStar M K) Mi)
    (hKEqPartnerKstar : K = section14KStar Mi (section14KStar M K))
    (hKstarcyc : IsCyclic (section14KStar M K))
    (hyKstar : y ∈ section14KStar M K)
    (hyne : y ≠ 1) :
    elementCentralizerIn Mi y = section14Z M K := by
  obtain ⟨q, z, hz_zpowy, hzKstar, _hzne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in
      (G := G) (B := section14KStar M K) hyKstar hyne
  let Y : Subgroup G := Subgroup.zpowers z
  have hY :
      Y ∈ section12PrimeOrderSubgroups (section14KStar M K) := by
    simpa [Y] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
  have hNormYeqZi :
      subgroupNormalizerIn Mi (Y : Set G) = section14Z Mi (section14KStar M K) := by
    exact
      (proposition_14_2_b1
        (G := G) (M := Mi) (K := section14KStar M K) hMiP hHallKappaBase Y hY).1.trans
        ((proposition_14_2_b1
          (G := G) (M := Mi) (K := section14KStar M K) hMiP hHallKappaBase Y hY).2.1)
  have hZiEqZ : section14Z Mi (section14KStar M K) = section14Z M K := by
    calc
      section14Z Mi (section14KStar M K) =
          section14KStar Mi (section14KStar M K) ⊔ section14KStar M K := by
            rw [section14Z, sup_comm]
      _ = K ⊔ section14KStar M K := by rw [← hKEqPartnerKstar]
      _ = section14Z M K := by rw [section14Z]
  apply le_antisymm
  · intro g hg
    have hgNormY : g ∈ subgroupNormalizerIn Mi (Y : Set G) := by
      refine ⟨?_, hg.1⟩
      apply centralizer_le_normalizer Y
      rw [Subgroup.mem_centralizer_iff]
      intro w hwY
      have hgy : Commute g y := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      have hwy : w ∈ Subgroup.zpowers y := (Subgroup.zpowers_le.2 hz_zpowy) hwY
      rcases Subgroup.mem_zpowers_iff.mp hwy with ⟨n, rfl⟩
      exact (hgy.zpow_right n).eq.symm
    simpa [hNormYeqZi, hZiEqZ] using hgNormY
  · refine sup_le ?_ ?_
    · intro g hgK
      have hgPartner :
          g ∈ section14KStar Mi (section14KStar M K) := by
        exact hKEqPartnerKstar ▸ hgK
      refine ⟨section14_msigma_le Mi hgPartner.1, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr <|
        (Subgroup.mem_centralizer_iff.mp hgPartner.2 y hyKstar).symm
    · letI : CommGroup (section14KStar M K) := hKstarcyc.commGroup
      intro g hgKstar
      refine ⟨hHallKappaBase.1 hgKstar, ?_⟩
      have hgy : g * y = y * g := by
        exact congrArg Subtype.val (mul_comm (⟨g, hgKstar⟩ : section14KStar M K) ⟨y, hyKstar⟩)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hgy

private theorem CFSG.section14_7_centralizer_mul_eq_z
    {M K Mi : Subgroup G} {x y : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hPrimeOrderUnique :
      ∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups K →
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {Mi})
    (_hMiP : Mi ∈ section14MFamilyP G)
    (hInfEqZ : M ⊓ Mi = section14Z M K)
    (hKcyc : IsCyclic K)
    (hKstarcyc : IsCyclic (section14KStar M K))
    (hxK : x ∈ K)
    (hxne : x ≠ 1)
    (hyKstar : y ∈ section14KStar M K)
    (hyne : y ≠ 1) :
    Subgroup.centralizer ({x * y} : Set G) = section14Z M K := by
  have hxyComm : Commute x y :=
    Subgroup.mem_centralizer_iff.mp hyKstar.2 x hxK
  have hxKappa : section14IsPiElement (section14KappaPrimes M) x :=
    section14_isPiElement_of_mem_hall (G := G) hK hxK
  have hxSigmaCompl :
      section14ElementPrimeSupport x ⊆ (section10SigmaPrimes M)ᶜ := by
    intro p hp hxSigma
    exact section14_kappa_subset_not_sigma (M := M) (hxKappa hp) hxSigma
  have hMy : M ∈ section14MsigmaElement y := by
    refine ⟨hM.1, ?_⟩
    simpa using hyKstar.1
  have hySigma :
      section14ElementPrimeSupport y ⊆ section10SigmaPrimes M :=
    section14_primeSupport_subset_sigma_of_msigmaMember hMy
  have hcop : Nat.Coprime (orderOf x) (orderOf y) :=
    section14_coprime_order_of_support_split hxSigmaCompl hySigma
  have hxZpow : x ∈ Subgroup.zpowers (x * y) :=
    section14_mem_zpowers_mul_of_commute_of_coprime_order hxyComm hcop
  have hyZpow : y ∈ Subgroup.zpowers (x * y) := by
    have hyZpow0 : y ∈ Subgroup.zpowers (y * x) :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order
        hxyComm.symm (by simpa [Nat.coprime_comm] using hcop)
    simpa [hxyComm.eq] using hyZpow0
  obtain ⟨q, zx, hzx_zpowx, _hzxK, _hzxne, hzxprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G) (B := K) hxK hxne
  let X : Subgroup G := Subgroup.zpowers zx
  have hX : X ∈ section12PrimeOrderSubgroups K := by
    simpa [X] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzxprime
  obtain ⟨r, zy, hzy_zpowy, _hzyKstar, _hzyne, hzyprime⟩ :=
    section14_exists_primeOrder_zpowers_in
      (G := G) (B := section14KStar M K) hyKstar hyne
  let Y : Subgroup G := Subgroup.zpowers zy
  have hY :
      Y ∈ section12PrimeOrderSubgroups (section14KStar M K) := by
    simpa [Y] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzyprime
  apply le_antisymm
  · intro g hg
    have hgxy : Commute g (x * y) := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgx : Commute g x := by
      rcases Subgroup.mem_zpowers_iff.mp hxZpow with ⟨n, hn⟩
      simpa [hn] using (hgxy.zpow_right n)
    have hgy : Commute g y := by
      rcases Subgroup.mem_zpowers_iff.mp hyZpow with ⟨n, hn⟩
      simpa [hn] using (hgxy.zpow_right n)
    have hgCentX : g ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hwX
      have hwx : w ∈ Subgroup.zpowers x := (Subgroup.zpowers_le.2 hzx_zpowx) hwX
      rcases Subgroup.mem_zpowers_iff.mp hwx with ⟨n, rfl⟩
      exact (hgx.zpow_right n).eq.symm
    have hCentX_le_Mi : Subgroup.centralizer (X : Set G) ≤ Mi := by
      have hMiMem :
          Mi ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
        rw [hPrimeOrderUnique X hX]
        simp
      exact hMiMem.2
    have hgMi : g ∈ Mi := hCentX_le_Mi hgCentX
    have hCentYEq :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} :=
      (proposition_14_2_c (G := G) (M := M) (K := K) hM hK).2 Y hY
    have hCentY_le_M : Subgroup.centralizer (Y : Set G) ≤ M := by
      have hMMem :
          M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) := by
        rw [hCentYEq]
        simp
      exact hMMem.2
    have hgCentY : g ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hwY
      have hwy : w ∈ Subgroup.zpowers y := (Subgroup.zpowers_le.2 hzy_zpowy) hwY
      rcases Subgroup.mem_zpowers_iff.mp hwy with ⟨n, rfl⟩
      exact (hgy.zpow_right n).eq.symm
    have hgM : g ∈ M := hCentY_le_M hgCentY
    simpa [hInfEqZ] using (show g ∈ M ⊓ Mi from ⟨hgM, hgMi⟩)
  · refine sup_le ?_ ?_
    · letI : CommGroup K := hKcyc.commGroup
      intro g hgK
      have hgx : g * x = x * g := congrArg Subtype.val (mul_comm (⟨g, hgK⟩ : K) ⟨x, hxK⟩)
      have hgy : g * y = y * g := by
        exact Subgroup.mem_centralizer_iff.mp hyKstar.2 g hgK
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc
        g * (x * y) = (g * x) * y := by simp [mul_assoc]
        _ = (x * g) * y := by rw [hgx]
        _ = x * (g * y) := by simp [mul_assoc]
        _ = x * (y * g) := by rw [hgy]
        _ = (x * y) * g := by simp [mul_assoc]
    · intro g hgKstar
      letI : CommGroup (section14KStar M K) := hKstarcyc.commGroup
      have hgy : g * y = y * g := congrArg Subtype.val
        (mul_comm (⟨g, hgKstar⟩ : section14KStar M K) ⟨y, hyKstar⟩)
      have hgx : g * x = x * g := by
        exact (Subgroup.mem_centralizer_iff.mp hgKstar.2 x hxK).symm
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc
        g * (x * y) = (g * x) * y := by simp [mul_assoc]
        _ = (x * g) * y := by rw [hgx]
        _ = x * (g * y) := by simp [mul_assoc]
        _ = x * (y * g) := by rw [hgy]
        _ = (x * y) * g := by simp [mul_assoc]

private theorem CFSG.section14_7_widehat_inter_conj_eq_empty_of_not_mem
    {M K : Subgroup G} {g : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hZdp : section14ZInternalDirectProduct M K)
    (_hKcyc : IsCyclic K)
    (hgM : g ∉ M) :
    section14WidehatZ M K ∩ (M.conjBy g : Set G) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro t ht
  rcases ht with ⟨htWidehat, htMg⟩
  let Z : Subgroup G := section14Z M K
  have htZ : t ∈ Z := htWidehat.1
  have htNotK : t ∉ K := by
    intro htK
    exact htWidehat.2 (Or.inl htK)
  have htNotKstar : t ∉ section14KStar M K := by
    intro htKstar
    exact htWidehat.2 (Or.inr htKstar)
  have hK_norm_Kstar : K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
    intro x hxK
    exact (centralizer_le_normalizer (section14KStar M K)) (hZdp.2.2.2.2 hxK)
  have hKstarNormal : ((section14KStar M K).subgroupOf Z).Normal := by
    change ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)).Normal
    exact
      Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := K) (N := section14KStar M K) hK_norm_Kstar
  letI : ((section14KStar M K).subgroupOf Z).Normal := hKstarNormal
  have htop0 : (K.subgroupOf Z) ⊔ ((section14KStar M K).subgroupOf Z) = ⊤ := by
    change
      (K.subgroupOf (K ⊔ section14KStar M K)) ⊔
          ((section14KStar M K).subgroupOf (K ⊔ section14KStar M K)) = ⊤
    simpa only [Subgroup.subgroupOf_self] using
      (Subgroup.subgroupOf_sup
        (A := K) (A' := section14KStar M K) (B := K ⊔ section14KStar M K)
        le_sup_left le_sup_right).symm
  have htop :
      ((section14KStar M K).subgroupOf Z) ⊔ (K.subgroupOf Z) = ⊤ := by
    simpa [sup_comm] using htop0
  let tZ : Z := ⟨t, htZ⟩
  have htTop : tZ ∈ ((section14KStar M K).subgroupOf Z) ⊔ (K.subgroupOf Z) := by
    simp [htop]
  rcases
      (Subgroup.mem_sup_of_normal_left
        (x := tZ) (s := (section14KStar M K).subgroupOf Z) (t := K.subgroupOf Z)).1
        htTop with
    ⟨yKstar, hyKstar0, yK, hyK0, htEq0⟩
  let y : G := yKstar
  let y' : G := yK
  have hyKstar : y ∈ section14KStar M K := by
    simpa [y, Subgroup.mem_subgroupOf] using hyKstar0
  have hyK : y' ∈ K := by
    simpa [y', Subgroup.mem_subgroupOf] using hyK0
  have htEq : t = y * y' := by
    simpa [y, y'] using congrArg Subtype.val htEq0.symm
  have hyne : y ≠ 1 := by
    intro hy1
    have htK : t ∈ K := by
      simpa [htEq, y, y', hy1] using hyK
    exact htNotK htK
  have hy'ne : y' ≠ 1 := by
    intro hy'1
    have htKstar : t ∈ section14KStar M K := by
      simpa [htEq, y, y', hy'1] using hyKstar
    exact htNotKstar htKstar
  have hMy : M ∈ section14MsigmaElement y := by
    refine ⟨hM.1, ?_⟩
    simpa using hyKstar.1
  have hySigma :
      section14ElementPrimeSupport y ⊆ section10SigmaPrimes M :=
    section14_primeSupport_subset_sigma_of_msigmaMember hMy
  have hy'Kappa : section14IsPiElement (section14KappaPrimes M) y' :=
    section14_isPiElement_of_mem_hall (G := G) hK hyK
  have hy'SigmaCompl :
      section14ElementPrimeSupport y' ⊆ (section10SigmaPrimes M)ᶜ := by
    intro p hp hpSigma
    exact section14_kappa_subset_not_sigma (M := M) (hy'Kappa hp) hpSigma
  have hyy'Comm : Commute y y' :=
    (Subgroup.mem_centralizer_iff.mp hyKstar.2 y' hyK).symm
  have hcop : Nat.Coprime (orderOf y) (orderOf y') :=
    by
      simpa [Nat.coprime_comm] using
        (section14_coprime_order_of_support_split hy'SigmaCompl hySigma :
          Nat.Coprime (orderOf y') (orderOf y))
  have hyT : y ∈ Subgroup.zpowers t := by
    have hyT0 : y ∈ Subgroup.zpowers (y * y') :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order hyy'Comm hcop
    simpa [htEq] using hyT0
  have hyMg : y ∈ M.conjBy g := (Subgroup.zpowers_le.2 htMg) hyT
  have hdisj :
      section14KStar M K ⊓ M.conjBy g = ⊥ :=
    (proposition_14_2_d (G := G) (M := M) (K := K) hM hK).1 g hgM
  have hyBot : y ∈ (⊥ : Subgroup G) := by
    simpa [hdisj] using (show y ∈ section14KStar M K ⊓ M.conjBy g from ⟨hyKstar, hyMg⟩)
  exact hyne (Subgroup.mem_bot.mp hyBot)

private theorem CFSG.section14_7_half_lt_card_conjClosure_widehat
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hWidehatCard :
      (Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ) =
        (1 - (1 : ℚ) / (Nat.card K : ℚ) -
            (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
            (1 : ℚ) / ((Nat.card K : ℚ) *
              (Nat.card (section14KStar M K) : ℚ))) * (Nat.card G : ℚ))
    (hPrimeCard :
      Nat.Prime (Nat.card K) ∨ Nat.Prime (Nat.card (section14KStar M K))) :
    ((Nat.card G : ℚ) / 2 <
      (Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ)) := by
  have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM hK
  have hKstarNe : section14KStar M K ≠ ⊥ :=
    (proposition_14_2_c (G := G) (M := M) (K := K) hM hK).1
  have hkGt1 : 1 < Nat.card K := by
    have hkpos : 0 < Nat.card K := Nat.card_pos
    have hkne1 : Nat.card K ≠ 1 := by
      intro hk1
      exact hKne ((Subgroup.card_eq_one (H := K)).1 hk1)
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.ne_of_gt hkpos, hkne1⟩
  have hkstarGt1 : 1 < Nat.card (section14KStar M K) := by
    have hkstarpos : 0 < Nat.card (section14KStar M K) := Nat.card_pos
    have hkstarne1 : Nat.card (section14KStar M K) ≠ 1 := by
      intro hkstar1
      exact hKstarNe ((Subgroup.card_eq_one (H := section14KStar M K)).1 hkstar1)
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.ne_of_gt hkstarpos, hkstarne1⟩
  have hkOdd : Odd (Nat.card K) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card K)
  have hkstarOdd : Odd (Nat.card (section14KStar M K)) :=
    odd_of_card_dvd IsMinCE.odd_order
      (Subgroup.card_subgroup_dvd_card (section14KStar M K))
  have hkGe3 : 3 ≤ Nat.card K := by
    rcases hkOdd with ⟨m, hm⟩
    omega
  have hkstarGe3 : 3 ≤ Nat.card (section14KStar M K) := by
    rcases hkstarOdd with ⟨m, hm⟩
    omega
  have hcop :
      Nat.Coprime (Nat.card K) (Nat.card (section14KStar M K)) :=
    section14_7_card_coprime_k_kstar (G := G) (M := M) (K := K) hM hK
  have hCoeffLower :
      (8 : ℚ) / 15 ≤
        1 - (1 : ℚ) / (Nat.card K : ℚ) -
          (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
          (1 : ℚ) / ((Nat.card K : ℚ) * (Nat.card (section14KStar M K) : ℚ)) := by
    rcases hPrimeCard with hKprime | hKstarPrime
    · by_cases hk5 : 5 ≤ Nat.card K
      · have hkQ : (5 : ℚ) ≤ (Nat.card K : ℚ) := by exact_mod_cast hk5
        have hkstarQ : (3 : ℚ) ≤ (Nat.card (section14KStar M K) : ℚ) := by
          exact_mod_cast hkstarGe3
        have hkpos : (0 : ℚ) < (Nat.card K : ℚ) := by positivity
        have hkstarpos : (0 : ℚ) < (Nat.card (section14KStar M K) : ℚ) := by positivity
        field_simp [hkpos.ne', hkstarpos.ne']
        nlinarith
      · have hkEq3 : Nat.card K = 3 := by
          rcases hkOdd with ⟨m, hm⟩
          have hkLt5 : Nat.card K < 5 := Nat.not_le.mp hk5
          omega
        have hcop3 : Nat.Coprime 3 (Nat.card (section14KStar M K)) := by
          simpa [hkEq3] using hcop
        have h3ndiv : ¬ 3 ∣ Nat.card (section14KStar M K) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop3
        have hkstarGe5 : 5 ≤ Nat.card (section14KStar M K) := by
          by_contra hkstar5
          have hkstarLt5 : Nat.card (section14KStar M K) < 5 := Nat.not_le.mp hkstar5
          rcases hkstarOdd with ⟨m, hm⟩
          have hkstarEq3 : Nat.card (section14KStar M K) = 3 := by
            omega
          exact h3ndiv (hkstarEq3 ▸ dvd_rfl)
        have hkQ : (3 : ℚ) ≤ (Nat.card K : ℚ) := by exact_mod_cast hkGe3
        have hkstarQ : (5 : ℚ) ≤ (Nat.card (section14KStar M K) : ℚ) := by
          exact_mod_cast hkstarGe5
        have hkpos : (0 : ℚ) < (Nat.card K : ℚ) := by positivity
        have hkstarpos : (0 : ℚ) < (Nat.card (section14KStar M K) : ℚ) := by positivity
        field_simp [hkpos.ne', hkstarpos.ne']
        nlinarith [hkQ]
    · by_cases hkstar5 : 5 ≤ Nat.card (section14KStar M K)
      · have hkQ : (3 : ℚ) ≤ (Nat.card K : ℚ) := by exact_mod_cast hkGe3
        have hkstarQ : (5 : ℚ) ≤ (Nat.card (section14KStar M K) : ℚ) := by
          exact_mod_cast hkstar5
        have hkpos : (0 : ℚ) < (Nat.card K : ℚ) := by positivity
        have hkstarpos : (0 : ℚ) < (Nat.card (section14KStar M K) : ℚ) := by positivity
        field_simp [hkpos.ne', hkstarpos.ne']
        nlinarith
      · have hkstarEq3 : Nat.card (section14KStar M K) = 3 := by
          rcases hkstarOdd with ⟨m, hm⟩
          have hkstarLt5 : Nat.card (section14KStar M K) < 5 := Nat.not_le.mp hkstar5
          omega
        have hcop3 : Nat.Coprime (Nat.card K) 3 := by
          simpa [hkstarEq3] using hcop
        have h3ndiv : ¬ 3 ∣ Nat.card K := by
          simpa [Nat.coprime_comm] using
            (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
              (by simpa [Nat.coprime_comm] using hcop3)
        have hkGe5 : 5 ≤ Nat.card K := by
          by_contra hk5
          have hkLt5 : Nat.card K < 5 := Nat.not_le.mp hk5
          rcases hkOdd with ⟨m, hm⟩
          have hkEq3 : Nat.card K = 3 := by
            omega
          exact h3ndiv (hkEq3 ▸ dvd_rfl)
        have hkQ : (5 : ℚ) ≤ (Nat.card K : ℚ) := by exact_mod_cast hkGe5
        have hkstarQ : (3 : ℚ) ≤ (Nat.card (section14KStar M K) : ℚ) := by
          exact_mod_cast hkstarGe3
        have hkpos : (0 : ℚ) < (Nat.card K : ℚ) := by positivity
        have hkstarpos : (0 : ℚ) < (Nat.card (section14KStar M K) : ℚ) := by positivity
        field_simp [hkpos.ne', hkstarpos.ne']
        nlinarith [hkstarQ]
  have hCoeffHalf :
      (1 / 2 : ℚ) <
        1 - (1 : ℚ) / (Nat.card K : ℚ) -
          (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
          (1 : ℚ) / ((Nat.card K : ℚ) * (Nat.card (section14KStar M K) : ℚ)) := by
    have hEightFifths : (1 / 2 : ℚ) < (8 : ℚ) / 15 := by norm_num
    linarith
  have hGpos : (0 : ℚ) < (Nat.card G : ℚ) := by
    exact_mod_cast (Nat.card_pos (α := G))
  calc
    (Nat.card G : ℚ) / 2 = (1 / 2 : ℚ) * (Nat.card G : ℚ) := by ring
    _ <
        (1 - (1 : ℚ) / (Nat.card K : ℚ) -
            (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
            (1 : ℚ) / ((Nat.card K : ℚ) * (Nat.card (section14KStar M K) : ℚ))) *
          (Nat.card G : ℚ) := by
            exact mul_lt_mul_of_pos_right hCoeffHalf hGpos
    _ = (Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ) := by
      rw [hWidehatCard]

private def CFSG.section14Theorem14_7PrecoverData
    (M K Mstar : Subgroup G) : Prop :=
  Mstar ∈ section14MFamilyP G ∧
    ¬ section14ConjugateSubgroups Mstar M ∧
    (∀ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K → Mj = Mstar) ∧
    (∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups K →
      section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {Mstar}) ∧
    section12HallSubgroupIn (section14KappaPrimes Mstar) (section14KStar M K) Mstar ∧
    section12HallSubgroupIn (section10SigmaPrimes M) (section14KStar M K) Mstar ∧
    K = section14KStar Mstar (section14KStar M K) ∧
    section14KappaPrimes M = section12Tau1Primes M ∧
    section14ZInternalDirectProduct M K ∧
    IsCyclic (section14Z M K) ∧
    (∀ x y : G, x ∈ K → x ≠ 1 → y ∈ section14KStar M K → y ≠ 1 →
      M ⊓ Mstar = section14Z M K ∧
        elementCentralizerIn M x = section14Z M K ∧
        elementCentralizerIn Mstar y = section14Z M K ∧
        Subgroup.centralizer ({x * y} : Set G) = section14Z M K) ∧
    section14TISet (section14WidehatZ M K) ∧
    Subgroup.normalizer (section14WidehatZ M K) = section14Z M K ∧
    (∀ g : G, g ∉ M →
      section14WidehatZ M K ∩ (M.conjBy g : Set G) = ∅) ∧
    ((Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ) =
      (1 - (1 : ℚ) / (Nat.card K : ℚ) -
          (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
          (1 : ℚ) / ((Nat.card K : ℚ) *
            (Nat.card (section14KStar M K) : ℚ))) * (Nat.card G : ℚ)) ∧
    ((Nat.card G : ℚ) / 2 <
      (Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ)) ∧
    ((M ∈ section14MFamilyP2 G ∧ Nat.Prime (Nat.card K)) ∨
      (Mstar ∈ section14MFamilyP2 G ∧
        Nat.Prime (Nat.card (section14KStar M K)))) ∧
    section12ComplementIn M K (ambientDerivedSubgroup M)

private theorem CFSG.section14_7_precover_exists
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∃ Mstar : Subgroup G,
      section14Theorem14_7PrecoverData (G := G) M K Mstar := by
  classical
  obtain ⟨Xi0, Mi, _Ki0, hXi0, hMi0, _hKi0, _hKstarKi0, _hMi_not_conj0, _hZleMi0⟩ :=
    section14_7_exists_initial_overgroup_data
      (G := G) (M := M) (K := K) hM hK
  have hMiFam : Mi ∈ section14_7_overgroupFamily K := ⟨Xi0, hXi0, hMi0⟩
  let Ki : Subgroup G :=
    section14_7_KiOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  let Kistar : Subgroup G :=
    section14_7_KstarOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam
  rcases
      section14_7_XiKiOfOvergroupFamily_spec
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam with
    ⟨_hXi, _hMi, hKi, _hKstarKi, hMiP, hMi_not_conj, hZeqZi, hXiLeKistar, hKiLeZ,
      hKistarLeK⟩
  have hP2 :
      M ∈ section14MFamilyP2 G ∨
        ∃ Mj : Subgroup G, Mj ∈ section14_7_overgroupFamily K ∧ Mj ∈ section14MFamilyP2 G :=
    section14_7_exists_P2_self_or_overgroupFamily (G := G) (M := M) (K := K) hM hK
  rcases
      section14_7_singleton_collapse_of_P2_witness
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam hP2 with
    ⟨huniqFam, hKiEqBase, hKistarEqK, hP2Mi⟩
  rcases
      section14_7_partner_core_fields
        (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam hKi hMiP hMi_not_conj
        hKiEqBase hKistarEqK hP2Mi with
    ⟨_hMiP, _hMi_not_conj, hPrimeOrderUnique, hHallKappaBase, hKEqPartnerKstar, hZdp,
      hPrimeAlt⟩
  have hHallSigmaBase :
      section12HallSubgroupIn (section10SigmaPrimes M) (section14KStar M K) Mi :=
    section14_7_partner_hall_sigma
      (G := G) (M := M) (K := K) (Xi := Xi0) (Mi := Mi)
      hM hK hXi0 hMi0 hMiP hMi_not_conj hHallKappaBase hP2Mi
  have hKcyc : IsCyclic K :=
    section14_7_k_cyclic_of_partner
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiP hHallKappaBase
      hKEqPartnerKstar hP2Mi
  have hCompDer :
      section12ComplementIn M K (ambientDerivedSubgroup M) :=
    section14_7_complement_ambientDerived_of_k_cyclic
      (G := G) (M := M) (K := K) hM hK hKcyc
  have hKappaEqTau1 :
      section14KappaPrimes M = section12Tau1Primes M :=
    section14_7_kappa_eq_tau1_of_complement_ambientDerived
      (G := G) (M := M) (K := K) hM hK hCompDer
  have hZcyc : IsCyclic (section14Z M K) :=
    section14_7_z_cyclic_of_partner
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiP hHallKappaBase
      hKEqPartnerKstar hP2Mi hZdp
  have hKstarcyc : IsCyclic (section14KStar M K) :=
    section14_7_kstar_cyclic_of_partner
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hHallKappaBase hP2Mi
  have hWidehatTI : section14TISet (section14WidehatZ M K) :=
    section14_7_widehat_ti_of_singleton
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK
  have hWidehatNorm :
      Subgroup.normalizer (section14WidehatZ M K) = section14Z M K :=
    section14_7_widehat_normalizer_eq_z_of_singleton
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK
  have hWidehatCard :
      (Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ) =
        (1 - (1 : ℚ) / (Nat.card K : ℚ) -
            (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
            (1 : ℚ) / ((Nat.card K : ℚ) *
              (Nat.card (section14KStar M K) : ℚ))) * (Nat.card G : ℚ) :=
    section14_7_card_conjClosure_widehat_of_singleton
      (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiFam huniqFam hKistarEqK
  have hInfEqZ : M ⊓ Mi = section14Z M K :=
    section14_7_inter_partner_eq_z
      (G := G) (M := M) (K := K) (Xi := Xi0) (Mi := Mi)
      hM hK hXi0 hMi0 hMiP hMi_not_conj hHallKappaBase hHallSigmaBase
      hKEqPartnerKstar hP2Mi
  have hCentral :
      ∀ x y : G, x ∈ K → x ≠ 1 → y ∈ section14KStar M K → y ≠ 1 →
        M ⊓ Mi = section14Z M K ∧
          elementCentralizerIn M x = section14Z M K ∧
            elementCentralizerIn Mi y = section14Z M K ∧
              Subgroup.centralizer ({x * y} : Set G) = section14Z M K := by
    intro x y hxK hxne hyKstar hyne
    refine ⟨hInfEqZ, ?_, ?_, ?_⟩
    · exact
        section14_7_elementCentralizer_eq_z_of_mem_k
          (G := G) (M := M) (K := K) hM hK hKcyc hxK hxne
    · exact
        section14_7_elementCentralizer_partner_eq_z
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hMiP hHallKappaBase
          hKEqPartnerKstar hKstarcyc hyKstar hyne
    · exact
        section14_7_centralizer_mul_eq_z
          (G := G) (M := M) (K := K) (Mi := Mi) hM hK hPrimeOrderUnique hMiP
          hInfEqZ hKcyc hKstarcyc hxK hxne hyKstar hyne
  have hOutside :
      ∀ g : G, g ∉ M →
        section14WidehatZ M K ∩ (M.conjBy g : Set G) = ∅ := by
    intro g hgM
    exact
      section14_7_widehat_inter_conj_eq_empty_of_not_mem
        (G := G) (M := M) (K := K) hM hK hZdp hKcyc hgM
  have hHalf :
      (Nat.card G : ℚ) / 2 <
        (Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ) :=
    section14_7_half_lt_card_conjClosure_widehat
      (G := G) (M := M) (K := K) hM hK hWidehatCard
      (hPrimeAlt.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  exact ⟨Mi, hMiP, hMi_not_conj, huniqFam, hPrimeOrderUnique, hHallKappaBase,
    hHallSigmaBase, hKEqPartnerKstar, hKappaEqTau1, hZdp, hZcyc, hCentral, hWidehatTI,
    hWidehatNorm, hOutside, hWidehatCard, hHalf, hPrimeAlt, hCompDer⟩

/-- Theorem 14.7, existence of the nonconjugate partner `M*`. -/
public theorem CFSG.theorem_14_7_exists
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∃ Mstar : Subgroup G, section14Theorem14_7Data M K Mstar := by
  classical
  rcases section14_7_precover_exists (G := G) (M := M) (K := K) hM hK with
    ⟨Mi, hMiP, hMi_not_conj, huniqFam, hPrimeOrderUnique, hHallKappaBase,
      hHallSigmaBase, hKEqPartnerKstar, hKappaEqTau1, hZdp, hZcyc, hCentral, hWidehatTI,
      hWidehatNorm, hOutside, hWidehatCard, hHalf, hPrimeAlt, hCompDer⟩
  have hCover :
      ∀ H : Subgroup G, H ∈ section14MFamilyP G →
        section14ConjugateSubgroups H M ∨ section14ConjugateSubgroups H Mi := by
    intro H hH
    have hsolvH : IsSolvable H :=
      IsMinCE.proper_subgroups_solvable H (lt_top_iff_ne_top.mpr hH.1.1)
    obtain ⟨L, hL⟩ :=
      section14_exists_hallSubgroupIn (G := G) hsolvH (section14KappaPrimes H)
    rcases section14_7_precover_exists (G := G) (M := H) (K := L) hH hL with
      ⟨_Hstar, _hHstarP, _hHstar_not_conj, _huniqFamH, _hPrimeOrderUniqueH,
        _hHallKappaPartnerH, _hHallSigmaPartnerH, _hLEqPartnerKstar, _hHKappaEqTau1,
        hHZdp, _hHZcyc, _hHCentral, _hHwidehatTI, _hHwidehatNorm, _hHOutside,
        _hHwidehatCard, hHalfH, _hHPrimeAlt, _hHCompDer⟩
    let T : Set G := section14ConjugacyClosure (section14WidehatZ M K)
    let S : Set G := section14ConjugacyClosure (section14WidehatZ H L)
    have hTS : (T ∩ S).Nonempty := by
      by_contra hEmpty
      have hdisj : Disjoint T S := by
        rw [Set.disjoint_left]
        intro x hxT hxS
        exact hEmpty ⟨x, ⟨hxT, hxS⟩⟩
      have hUnionEq : (T ∪ S).ncard = T.ncard + S.ncard := by
        simpa [T, S] using Set.ncard_union_eq hdisj
      have hUnionLe : (T ∪ S).ncard ≤ Nat.card G :=
        Set.ncard_le_card (T ∪ S)
      have hHalfT : (Nat.card G : ℚ) / 2 < (T.ncard : ℚ) := by
        simpa [T, Nat.card_coe_set_eq] using hHalf
      have hHalfS : (Nat.card G : ℚ) / 2 < (S.ncard : ℚ) := by
        simpa [S, Nat.card_coe_set_eq] using hHalfH
      have hUnionEqQ : ((T ∪ S).ncard : ℚ) = (T.ncard : ℚ) + (S.ncard : ℚ) := by
        exact_mod_cast hUnionEq
      have hUnionLeQ : ((T ∪ S).ncard : ℚ) ≤ (Nat.card G : ℚ) := by
        exact_mod_cast hUnionLe
      have hUnionGtQ : (Nat.card G : ℚ) < ((T ∪ S).ncard : ℚ) := by
        linarith
      linarith
    rcases hTS with ⟨g, hgT, hgS⟩
    rcases hgT with ⟨t, htWidehat, a, hga⟩
    rcases hgS with ⟨s, hsWidehat, b, hgb⟩
    let c : G := b * a⁻¹
    have htEq : t = c⁻¹ * s * c := by
      have hEq : a⁻¹ * t * a = b⁻¹ * s * b := hga.symm.trans hgb
      have hconj := congrArg (fun z : G => a * z * a⁻¹) hEq
      simpa [c, mul_assoc] using hconj
    let ZH : Subgroup G := section14Z H L
    have hsZ : s ∈ ZH := hsWidehat.1
    have hsNotL : s ∉ L := by
      intro hsL
      exact hsWidehat.2 (Or.inl hsL)
    have hsNotLstar : s ∉ section14KStar H L := by
      intro hsLstar
      exact hsWidehat.2 (Or.inr hsLstar)
    have hL_norm_Lstar : L ≤ Subgroup.normalizer (section14KStar H L : Set G) := by
      intro x hxL
      exact (centralizer_le_normalizer (section14KStar H L)) (hHZdp.2.2.2.2 hxL)
    have hLstarNormal : ((section14KStar H L).subgroupOf ZH).Normal := by
      change ((section14KStar H L).subgroupOf (L ⊔ section14KStar H L)).Normal
      exact
        Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := L) (N := section14KStar H L) hL_norm_Lstar
    letI : ((section14KStar H L).subgroupOf ZH).Normal := hLstarNormal
    have htop0 : (L.subgroupOf ZH) ⊔ ((section14KStar H L).subgroupOf ZH) = ⊤ := by
      change
        (L.subgroupOf (L ⊔ section14KStar H L)) ⊔
            ((section14KStar H L).subgroupOf (L ⊔ section14KStar H L)) = ⊤
      simpa only [Subgroup.subgroupOf_self] using
        (Subgroup.subgroupOf_sup
          (A := L) (A' := section14KStar H L) (B := L ⊔ section14KStar H L)
          le_sup_left le_sup_right).symm
    have htop : ((section14KStar H L).subgroupOf ZH) ⊔ (L.subgroupOf ZH) = ⊤ := by
      simpa [sup_comm] using htop0
    let sZ : ZH := ⟨s, hsZ⟩
    have hsTop : sZ ∈ ((section14KStar H L).subgroupOf ZH) ⊔ (L.subgroupOf ZH) := by
      simp [htop]
    rcases
        (Subgroup.mem_sup_of_normal_left
          (x := sZ) (s := (section14KStar H L).subgroupOf ZH) (t := L.subgroupOf ZH)).1 hsTop
      with ⟨xLstar, hxLstar0, xL, hxL0, hsEq0⟩
    let x : G := xLstar
    let x' : G := xL
    have hxLstar : x ∈ section14KStar H L := by
      simpa [x, Subgroup.mem_subgroupOf] using hxLstar0
    have hxL : x' ∈ L := by
      simpa [x', Subgroup.mem_subgroupOf] using hxL0
    have hsEq : s = x * x' := by
      simpa [x, x'] using congrArg Subtype.val hsEq0.symm
    have hxne : x ≠ 1 := by
      intro hx1
      have hsL : s ∈ L := by
        simpa [hsEq, x, x', hx1] using hxL
      exact hsNotL hsL
    have hx'ne : x' ≠ 1 := by
      intro hx'1
      have hsLstar : s ∈ section14KStar H L := by
        simpa [hsEq, x, x', hx'1] using hxLstar
      exact hsNotLstar hsLstar
    have hHx : H ∈ section14MsigmaElement x := by
      refine ⟨hH.1, ?_⟩
      simpa using hxLstar.1
    have hxSigma :
        section14ElementPrimeSupport x ⊆ section10SigmaPrimes H :=
      section14_primeSupport_subset_sigma_of_msigmaMember hHx
    have hx'Kappa : section14IsPiElement (section14KappaPrimes H) x' :=
      section14_isPiElement_of_mem_hall (G := G) hL hxL
    have hx'SigmaCompl :
        section14ElementPrimeSupport x' ⊆ (section10SigmaPrimes H)ᶜ := by
      intro p hp hpSigma
      exact section14_kappa_subset_not_sigma (M := H) (hx'Kappa hp) hpSigma
    have hxx'Comm : Commute x x' :=
      (Subgroup.mem_centralizer_iff.mp hxLstar.2 x' hxL).symm
    have hcop : Nat.Coprime (orderOf x) (orderOf x') := by
      simpa [Nat.coprime_comm] using
        (section14_coprime_order_of_support_split hx'SigmaCompl hxSigma :
          Nat.Coprime (orderOf x') (orderOf x))
    have hxZpow : x ∈ Subgroup.zpowers s := by
      have hxZpow0 : x ∈ Subgroup.zpowers (x * x') :=
        section14_mem_zpowers_mul_of_commute_of_coprime_order hxx'Comm hcop
      simpa [hsEq] using hxZpow0
    obtain ⟨q, z, hz_zpowx, _hzLstar, _hzne, hzprime⟩ :=
      section14_exists_primeOrder_zpowers_in (G := G) (B := section14KStar H L) hxLstar hxne
    let Y : Subgroup G := Subgroup.zpowers z
    have hY : Y ∈ section12PrimeOrderSubgroups (section14KStar H L) := by
      simpa [Y] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
    have hzZpowS : z ∈ Subgroup.zpowers s :=
      (Subgroup.zpowers_le.2 hxZpow) hz_zpowx
    have hYcLeZ : Y.conjBy c⁻¹ ≤ section14Z M K := by
      intro u huYc
      rcases Subgroup.mem_map.mp huYc with ⟨u0, huY, rfl⟩
      have huZpowS : u0 ∈ Subgroup.zpowers s :=
        (Subgroup.zpowers_le.2 hzZpowS) huY
      have huMap : c⁻¹ * u0 * c ∈ (Subgroup.zpowers s).conjBy c⁻¹ := by
        exact Subgroup.mem_map.mpr ⟨u0, huZpowS, by simp [mul_assoc]⟩
      have hzpowEq : Subgroup.zpowers t = (Subgroup.zpowers s).conjBy c⁻¹ := by
        simpa [htEq] using section14_zpowers_conjBy_inv (G := G) s c
      have huZpowT : c⁻¹ * u0 * c ∈ Subgroup.zpowers t := by
        simpa [hzpowEq] using huMap
      simpa [mul_assoc] using (Subgroup.zpowers_le.2 htWidehat.1) huZpowT
    have hYcard : Nat.card Y = q.val := by
      rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with ⟨_hzle, hqcard⟩
      simp [Y, hqcard]
    have hYcCard : Nat.card (Y.conjBy c⁻¹) = q.val := by
      calc
        Nat.card (Y.conjBy c⁻¹) = Nat.card Y := section14_card_conjBy (G := G) Y c⁻¹
        _ = q.val := hYcard
    have hYc : Y.conjBy c⁻¹ ∈ section12PrimeOrderSubgroups (section14Z M K) := by
      exact ⟨hYcLeZ, ⟨q, hYcCard⟩⟩
    have hHCent :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {H} :=
      (proposition_14_2_c (G := G) (M := H) (K := L) hH hL).2 Y hY
    have hHcCent :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (Y.conjBy c⁻¹ : Set G)) =
          {H.conjBy c⁻¹} := by
      simpa using
        section14_maximalSubgroupsContaining_centralizer_conjBy
          (G := G) (X := Y) (M := H) hH.1 c⁻¹ hHCent
    rcases
        section14_7_primeOrder_le_base_or_overgroupFamily_kstar_of_z
          (G := G) (M := M) (K := K) (X := Y.conjBy c⁻¹) hM hK hYc with
      hYcBase | ⟨Mj, hMjFam, hYcMj⟩
    · have hYcBasePrime :
          Y.conjBy c⁻¹ ∈ section12PrimeOrderSubgroups (section14KStar M K) := by
        exact ⟨hYcBase, ⟨q, hYcCard⟩⟩
      have hMCent :
          section9MaximalSubgroupsContaining (Subgroup.centralizer (Y.conjBy c⁻¹ : Set G)) =
            {M} :=
        (proposition_14_2_c (G := G) (M := M) (K := K) hM hK).2 (Y.conjBy c⁻¹) hYcBasePrime
      have hHcMem :
          H.conjBy c⁻¹ ∈
            section9MaximalSubgroupsContaining (Subgroup.centralizer (Y.conjBy c⁻¹ : Set G)) := by
        rw [hHcCent]
        simp
      have hHcEqM : H.conjBy c⁻¹ = M := by
        have hmem : H.conjBy c⁻¹ ∈ ({M} : Set (Subgroup G)) := by
          simpa [hMCent] using hHcMem
        simpa using hmem
      left
      exact ⟨c, by
        calc
          H = (H.conjBy c⁻¹).conjBy c := (section11_conjBy_inv' (G := G) H c).symm
          _ = M.conjBy c := by rw [hHcEqM]⟩
    · let Kj : Subgroup G :=
        section14_7_KiOfOvergroupFamily (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam
      have hMjData :
          section12HallSubgroupIn (section14KappaPrimes Mj) Kj Mj ∧
            Mj ∈ section14MFamilyP G := by
        rcases
            (section14_7_XiKiOfOvergroupFamily_spec
              (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam) with
          ⟨_hXj, _hMj, hKj, _hKstarKj, hMjP, _hMj_not_conj, _hZeqZj, _hXjLeKjstar,
            _hKjLeZ, _hKjstarLeK⟩
        exact ⟨hKj, hMjP⟩
      rcases hMjData with ⟨hKj, hMjP⟩
      have hYcMjPrime :
          Y.conjBy c⁻¹ ∈
            section12PrimeOrderSubgroups
              (section14_7_KstarOfOvergroupFamily
                (G := G) (M := M) (K := K) (Mi := Mj) hM hK hMjFam) := by
        exact ⟨hYcMj, ⟨q, hYcCard⟩⟩
      have hMjCent :
          section9MaximalSubgroupsContaining (Subgroup.centralizer (Y.conjBy c⁻¹ : Set G)) =
            {Mj} :=
        (proposition_14_2_c (G := G) (M := Mj) (K := Kj) hMjP hKj).2
          (Y.conjBy c⁻¹) hYcMjPrime
      have hHcMem :
          H.conjBy c⁻¹ ∈
            section9MaximalSubgroupsContaining (Subgroup.centralizer (Y.conjBy c⁻¹ : Set G)) := by
        rw [hHcCent]
        simp
      have hHcEqMj : H.conjBy c⁻¹ = Mj := by
        have hmem : H.conjBy c⁻¹ ∈ ({Mj} : Set (Subgroup G)) := by
          simpa [hMjCent] using hHcMem
        simpa using hmem
      have hMjEqMi : Mj = Mi := huniqFam Mj hMjFam
      have hHcEqMi : H.conjBy c⁻¹ = Mi := hHcEqMj.trans hMjEqMi
      right
      exact ⟨c, by
        calc
          H = (H.conjBy c⁻¹).conjBy c := (section11_conjBy_inv' (G := G) H c).symm
          _ = Mi.conjBy c := by rw [hHcEqMi]⟩
  refine ⟨Mi, ?_⟩
  refine ⟨hMiP, hMi_not_conj, hPrimeOrderUnique, hHallKappaBase, hHallSigmaBase,
    hKEqPartnerKstar, hKappaEqTau1, hZdp, hZcyc, hCentral, hWidehatTI, hWidehatNorm,
    hOutside, hWidehatCard, hHalf, hPrimeAlt, hCover, hCompDer⟩

/-- The subgroup `M*` paired with `M` and `K` in Theorem 14.7. -/
@[expose] public noncomputable def CFSG.section14Theorem14_7Partner
    (M K : Subgroup G) : Subgroup G := by
  classical
  by_cases h :
      M ∈ section14MFamilyP G ∧
        section12HallSubgroupIn (section14KappaPrimes M) K M
  · exact Classical.choose (theorem_14_7_exists (M := M) (K := K) h.1 h.2)
  · exact ⊥

/-- Theorem 14.7 data for the chosen partner. -/
public theorem CFSG.theorem_14_7_data
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14Theorem14_7Data M K (section14Theorem14_7Partner M K) := by
  classical
  have h :
      M ∈ section14MFamilyP G ∧
        section12HallSubgroupIn (section14KappaPrimes M) K M := ⟨hM, hK⟩
  simpa [section14Theorem14_7Partner, h] using
    (Classical.choose_spec (theorem_14_7_exists (G := G) (M := M) (K := K) hM hK))

/-- Theorem 14.7(a). -/
public theorem CFSG.theorem_14_7_a
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups K →
      section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) =
        {section14Theorem14_7Partner M K} := by
  simpa using (theorem_14_7_data (G := G) (M := M) (K := K) hM hK).2.2.1

/-- Theorem 14.7(b). -/
public theorem CFSG.theorem_14_7_b
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section12HallSubgroupIn
        (section14KappaPrimes (section14Theorem14_7Partner M K))
        (section14KStar M K) (section14Theorem14_7Partner M K) ∧
      section12HallSubgroupIn (section10SigmaPrimes M) (section14KStar M K)
        (section14Theorem14_7Partner M K) := by
  let hdata := theorem_14_7_data (G := G) (M := M) (K := K) hM hK
  exact ⟨hdata.2.2.2.1, hdata.2.2.2.2.1⟩

/-- Theorem 14.7(c). -/
public theorem CFSG.theorem_14_7_c
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    K = section14KStar (section14Theorem14_7Partner M K) (section14KStar M K) ∧
      section14KappaPrimes M = section12Tau1Primes M := by
  let hdata := theorem_14_7_data (G := G) (M := M) (K := K) hM hK
  exact ⟨hdata.2.2.2.2.2.1, hdata.2.2.2.2.2.2.1⟩

/-- Fixed-complement form of Proposition 14.2(a): if a chosen complement
to `M_σ` contains the Hall `κ(M)` subgroup `K`, then the abelian regular
complement `U` may be chosen inside that fixed complement. -/
public theorem CFSG.proposition_14_2_a_of_fixed_sigma_complement
    {M K E : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hEcomp : section12ComplementToMsigma M E)
    (hKE : K ≤ E) :
    ∃ U : Subgroup G, U ≤ E ∧ section14Proposition14_2AData M K U := by
  classical
  rcases hK with ⟨hKM, hKHallM⟩
  have hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M := by
    intro p hpκ
    exact (theorem_14_7_c (G := G) (M := M) (K := K) hM
      ⟨hKM, hKHallM⟩).2 ▸ hpκ
  have hsolvE : IsSolvable E :=
    section14_solvable_of_le_maximal hM.1 hEcomp.2.1
  letI : MulDistribMulAction Unit E := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let KsubE : Subgroup E := K.subgroupOf E
  have hKsubE_pi12 :
      IsPiSubgroup (G := E) (section12Tau1Primes M ∪ section12Tau2Primes M)
        KsubE := by
    intro p hpKsubE
    have hcardE : Nat.card KsubE = Nat.card K :=
      section12_card_subgroupOf_eq hKE
    have hcardM : Nat.card (K.subgroupOf M) = Nat.card K :=
      section12_card_subgroupOf_eq hKM
    have hpκ : p ∈ section14KappaPrimes M :=
      hKHallM.p_in_pi_of_p_dvd_card p
        (by simpa [KsubE, hcardE, hcardM] using hpKsubE)
    exact Or.inl (hκτ1 hpκ)
  have hKsubE_inv : IsInvariant Unit E KsubE := by
    refine ⟨?_⟩
    intro _ x
    simp [KsubE]
  have hcopE : Nat.Coprime (Nat.card Unit) (Nat.card E) := by simp
  obtain ⟨E₁₂sub, hE₁₂Hall, _hE₁₂Inv, hKsubE_E₁₂sub⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := E) (A := Unit) hsolvE hcopE
      (section12Tau1Primes M ∪ section12Tau2Primes M)
      KsubE hKsubE_pi12 hKsubE_inv
  let E₁₂ : Subgroup G := E₁₂sub.map E.subtype
  have hE₁₂ : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E := by
    simpa [E₁₂] using section14_hallSubgroupIn_map_subtype (G := G) hE₁₂Hall
  have hKE₁₂ : K ≤ E₁₂ := by
    intro x hxK
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hKE hxK⟩,
        hKsubE_E₁₂sub (show (⟨x, hKE hxK⟩ : E) ∈ KsubE from hxK), rfl⟩
  have hE₁₂M : E₁₂ ≤ M := hE₁₂.1.trans hEcomp.2.1
  have hsolvE₁₂ : IsSolvable E₁₂ :=
    section14_solvable_of_le_maximal hM.1 hE₁₂M
  letI : MulDistribMulAction Unit E₁₂ := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let KsubE₁₂ : Subgroup E₁₂ := K.subgroupOf E₁₂
  have hKsubE₁₂_pi1 :
      IsPiSubgroup (G := E₁₂) (section12Tau1Primes M) KsubE₁₂ := by
    intro p hpKsubE₁₂
    have hcardE₁₂ : Nat.card KsubE₁₂ = Nat.card K :=
      section12_card_subgroupOf_eq hKE₁₂
    have hcardM : Nat.card (K.subgroupOf M) = Nat.card K :=
      section12_card_subgroupOf_eq hKM
    have hpκ : p ∈ section14KappaPrimes M :=
      hKHallM.p_in_pi_of_p_dvd_card p
        (by simpa [KsubE₁₂, hcardE₁₂, hcardM] using hpKsubE₁₂)
    exact hκτ1 hpκ
  have hKsubE₁₂_inv : IsInvariant Unit E₁₂ KsubE₁₂ := by
    refine ⟨?_⟩
    intro _ x
    simp [KsubE₁₂]
  have hcopE₁₂ : Nat.Coprime (Nat.card Unit) (Nat.card E₁₂) := by simp
  obtain ⟨E₁sub, hE₁Hall, _hE₁Inv, hKsubE₁₂_E₁sub⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := E₁₂) (A := Unit) hsolvE₁₂ hcopE₁₂
      (section12Tau1Primes M) KsubE₁₂ hKsubE₁₂_pi1 hKsubE₁₂_inv
  let E₁ : Subgroup G := E₁sub.map E₁₂.subtype
  have hE₁ : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂ := by
    simpa [E₁] using section14_hallSubgroupIn_map_subtype (G := G) hE₁Hall
  have hKE₁ : K ≤ E₁ := by
    intro x hxK
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hKE₁₂ hxK⟩,
        hKsubE₁₂_E₁sub (show (⟨x, hKE₁₂ hxK⟩ : E₁₂) ∈ KsubE₁₂ from hxK),
        rfl⟩
  obtain ⟨E₂, hE₂⟩ :=
    section14_exists_hallSubgroupIn
      (G := G) hsolvE₁₂ (section12Tau2Primes M)
  obtain ⟨E₃, hE₃⟩ :=
    section14_exists_hallSubgroupIn
      (G := G) hsolvE (section12Tau3Primes M)
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hEcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  refine ⟨E₂ ⊔ E₃, ?_, ?_⟩
  · exact sup_le (hE₂.1.trans hE₁₂.1) hE₃.1
  · exact
      section14_tau1_case_data
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM ⟨hKM, hKHallM⟩ hEdata hKE₁ hκτ1

/-- Theorem 14.7(d). -/
public theorem CFSG.theorem_14_7_d
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14ZInternalDirectProduct M K ∧
      IsCyclic (section14Z M K) ∧
      ∀ x y : G, x ∈ K → x ≠ 1 → y ∈ section14KStar M K → y ≠ 1 →
        M ⊓ section14Theorem14_7Partner M K = section14Z M K ∧
          elementCentralizerIn M x = section14Z M K ∧
          elementCentralizerIn (section14Theorem14_7Partner M K) y =
            section14Z M K ∧
          Subgroup.centralizer ({x * y} : Set G) = section14Z M K := by
  let hdata := theorem_14_7_data (G := G) (M := M) (K := K) hM hK
  exact
    ⟨hdata.2.2.2.2.2.2.2.1, hdata.2.2.2.2.2.2.2.2.1, hdata.2.2.2.2.2.2.2.2.2.1⟩

/-- Theorem 14.7(e). -/
public theorem CFSG.theorem_14_7_e
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14TISet (section14WidehatZ M K) ∧
      Subgroup.normalizer (section14WidehatZ M K) = section14Z M K ∧
      (∀ g : G, g ∉ M →
        section14WidehatZ M K ∩ (M.conjBy g : Set G) = ∅) ∧
      ((Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ) =
        (1 - (1 : ℚ) / (Nat.card K : ℚ) -
            (1 : ℚ) / (Nat.card (section14KStar M K) : ℚ) +
            (1 : ℚ) / ((Nat.card K : ℚ) *
              (Nat.card (section14KStar M K) : ℚ))) * (Nat.card G : ℚ)) ∧
      ((Nat.card G : ℚ) / 2 <
        (Nat.card (section14ConjugacyClosure (section14WidehatZ M K)) : ℚ)) := by
  let hdata := theorem_14_7_data (G := G) (M := M) (K := K) hM hK
  exact
    ⟨hdata.2.2.2.2.2.2.2.2.2.2.1, hdata.2.2.2.2.2.2.2.2.2.2.2.1,
      hdata.2.2.2.2.2.2.2.2.2.2.2.2.1, hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Theorem 14.7(f). -/
public theorem CFSG.theorem_14_7_f
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    (M ∈ section14MFamilyP2 G ∧ Nat.Prime (Nat.card K)) ∨
      (section14Theorem14_7Partner M K ∈ section14MFamilyP2 G ∧
        Nat.Prime (Nat.card (section14KStar M K))) := by
  simpa using (theorem_14_7_data (G := G) (M := M) (K := K) hM hK).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Theorem 14.7(g). -/
public theorem CFSG.theorem_14_7_g
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∀ H : Subgroup G, H ∈ section14MFamilyP G →
      section14ConjugateSubgroups H M ∨
        section14ConjugateSubgroups H (section14Theorem14_7Partner M K) := by
  simpa using (theorem_14_7_data (G := G) (M := M) (K := K) hM hK).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Theorem 14.7(h). -/
public theorem CFSG.theorem_14_7_h
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section12ComplementIn M K (ambientDerivedSubgroup M) := by
  exact (theorem_14_7_data (G := G) (M := M) (K := K) hM hK).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Section14
