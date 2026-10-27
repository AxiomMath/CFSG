module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootTwoCoreStatement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthNodeScalar
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthNodeLinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthNodeCyclic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthNodeSplit
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimePointCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairStabilizerInvolution
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicFull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelStatement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G]

theorem pointTwoCoreImage_eq_self_of_isPGroup (C : Subgroup G) (hC : IsPGroup 2 C) :
    TwoCoreGrowth.pointTwoCoreImage C = C := by
  have htop : CFSG.pCore 2 C = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hC.of_equiv Subgroup.topEquiv.symm⟩)
  rw [TwoCoreGrowth.pointTwoCoreImage, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable [Finite G]

theorem false_of_involutions_mem_root
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearPointKernelConclusion H z beta t)
    (hQM : minimalLocalFailurePairActionPointHull H z < TwoCoreGrowth.pointTwoCoreImage H)
    (hInv : ∀ m : G, m ∈ TwoCoreGrowth.pointTwoCoreImage H → orderOf m = 2 →
      m ∈ minimalLocalFailurePairActionPointHull H z) : False := by
  dsimp only [LinearPointKernelConclusion] at hker
  have hcyc := CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  dsimp only at hcyc
  set Q := minimalLocalFailurePairActionPointHull H z
  set M := TwoCoreGrowth.pointTwoCoreImage H
  set B := pairPointStabilizer H beta
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  set K := minimalLocalFailureProperPairHull H z beta t
  set J := Subgroup.centralizer (K : Set G)
  set C := H ⊓ Subgroup.centralizer (Q : Set G)
  obtain ⟨⟨k, _, _, hk, ⟨eK⟩⟩, -, hindex, -, hQB, hJeq, -, hQJ, hJQ, hCidx, ⟨fJ, hfJ⟩,
    hBinvJ, hQMle, -, hCcore, ⟨k₀, _, _, hk₀, φ, ι, hιker, hact, hιX⟩, hodd⟩ := hker
  obtain ⟨hQel, hQ4, hQclass, -, -, -, -, hIB, hXI, hXK, hXcyc, hXodd, hXm, -⟩ := hcyc
  have hXB : X ≤ B := hXI.trans hIB
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hXH : X ≤ H := hXB.trans hBH
  have hJB : J ≤ B := by
    rw [hJeq]
    exact inf_le_left
  have hJH : J ≤ H := hJB.trans hBH
  have hJX : J ≤ Subgroup.centralizer (X : Set G) := Subgroup.centralizer_le hXK
  have hQH : Q ≤ H :=
    minimalLocalFailurePairActionPointHull_le_point H h.local_datum.distinguished_mem
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp
      (minimalLocalFailurePairActionPointHull_normal_in_point H h.local_datum.distinguished_mem)
  have hQproper : ¬ M ≤ Q := fun hle => hQM.ne (le_antisymm hQM.le hle)
  have hXcard : Nat.card X = Nat.card Q - 1 := by
    rw [hXm, ← hQclass, PairInvolutionFixedField.card_diff_one]
  have hdis : Disjoint X J :=
    disjoint_of_scalar_image hXB ι hιker hιX (by rw [hXcard, hk₀])
  have hscalar0 := scalar_fixed_eq_one hXB φ ι hιker hact hιX hdis
  have hscalar : ∀ x : G, x ∈ X → x ≠ 1 →
      ∀ m : G, m ∈ M → m ∈ Q → x * m * x⁻¹ = m → m = 1 :=
    fun x hx hx1 m _ hmQ hxm => hscalar0 x hx hx1 m hmQ hxm
  have hJkernel : ∀ y : G, y ∈ J → y ≠ 1 → Odd (orderOf y) →
      ∀ m : G, m ∈ M → y * m * y⁻¹ = m → m ∈ Q := by
    intro y hy hy1 hyodd m hm hym
    obtain ⟨-, -, hMy⟩ := hodd y hy hy1 hyodd
    rw [← hMy]
    refine ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc
      m * y = (y * m * y⁻¹) * y := by rw [hym]
      _ = y * m := by group
  have hcop : Nat.Coprime (Nat.card X) (Nat.card J) :=
    TwoCoreGrowthCoprime.point_two_core_scalar_centralizer_orders_coprime H Q X J hHQ hQMle
      hQproper hXH hJH hInv hXcard hJX hJQ hdis hscalar hJkernel
  obtain ⟨u, huB, hu⟩ := ProperPairModel.proper_pair_stabilizer_exists_involution
    h hcomm hbeta ht hproper
  have huJ : u ∈ J := hBinvJ u huB hu
  have hu1 : u ≠ 1 := (orderOf_eq_prime_iff.mp hu).2
  have huQ : u ∉ Q := by
    intro huQ
    have hmem : u ∈ Q ⊓ B := ⟨huQ, huB⟩
    rw [hQB, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  have hMtwo : IsPGroup 2 M := TwoCoreGrowth.pointTwoCoreImage_isPGroup H
  have hQtwo : IsPGroup 2 Q := hMtwo.to_le hQMle
  obtain ⟨e, he⟩ := hQtwo.exists_card_eq
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [he, pow_zero] at hQ4
    omega
  have hqeven : Even (Nat.card Q) := by
    rw [he]
    exact (Nat.even_pow' he0).mpr even_two
  have hkeven : Even (Nat.card k) := by
    rw [hk]
    exact hqeven
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    exact hQ4
  let fP : J →* PSL2MatrixGroup k := eK.toMonoidHom.comp fJ
  have hfP : Function.Injective fP := eK.injective.comp hfJ
  have hplus : ∀ p : ℕ, p.Prime → p ∣ Nat.card J → ¬ p ∣ Nat.card Q + 1 := by
    intro p hp hpJ hpPlus
    obtain ⟨-, hpodd, -, -, -, hMB, -⟩ :=
      TwoCoreGrowthCoprime.point_two_core_extra_prime_full_product_data H Q X J B hHQ hQMle
        hQproper hXH hJH hBH hInv hQB hindex hXcard hJX hJQ hdis hscalar hJkernel hp hpJ hpPlus
    have hJeven : Even (Nat.card J) := by
      rw [even_iff_two_dvd, ← hu]
      exact Subgroup.orderOf_dvd_natCard J huJ
    have hcopk : Nat.Coprime (Nat.card J) (Nat.card k - 1) := by
      rw [hk, ← hXcard]
      exact hcop.symm
    have hnot : ¬ ∃ n : ℕ, Nat.card J = 2 ^ n := by
      rintro ⟨n, hn⟩
      rw [hn] at hpJ
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpJ)
      rw [hp2] at hpodd
      exact Nat.not_odd_iff_even.mpr even_two hpodd
    have hJsmall :=
      two_subgroup_card_le_two_of_injective_psl2 hkeven hk4 fP hfP hJeven hcopk hnot
    have hk₀odd : Odd (Nat.card k₀ - 1) := by
      rw [hk₀, ← hXcard]
      exact hXodd
    exact false_of_split_two_core h hbeta hQclass hInv hMB
      (fun P hPB hP => two_subgroup_isCyclic_of_semilinear hPB hP hk₀odd ι hιker hBinvJ hJsmall)
      huB hu
  have hJtwo : IsPGroup 2 J := by
    have hprime : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card J → d = 2 := by
      intro d hd hdJ
      rcases hd.eq_two_or_odd' with hd2 | hdodd
      · exact hd2
      · exfalso
        rcases odd_prime_dvd_sub_or_add_of_injective_psl2 hkeven hk4 fP hfP hd hdodd hdJ with
          hminus | hplus'
        · rw [hk, ← hXcard] at hminus
          exact hd.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hminus hdJ)
        · rw [hk] at hplus'
          exact hplus d hd hdJ hplus'
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprime)
  have hQabel : Q ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcomm' := hQel.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩
    exact congrArg Subtype.val hcomm'
  have hQJC : Q ⊔ J ≤ C := sup_le (le_inf hQH hQabel) (le_inf hJH hJQ)
  have hQJcard : Nat.card (Q ⊔ J : Subgroup G) = Nat.card Q * Nat.card J :=
    TwoCoreGrowthCoprime.commuting_disjoint_join_card Q J hJQ (disjoint_iff.mpr hQJ)
  have hCcard : (Q ⊔ J).relIndex C * (Nat.card Q * Nat.card J) = Nat.card C := by
    have h1 := (Q ⊔ J).relIndex_mul_card C
    rw [inf_eq_left.mpr hQJC, hQJcard] at h1
    exact h1
  have hCtwo : IsPGroup 2 C := by
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show (Q ⊔ J).relIndex C ∣ 2 ^ (2 * e) by rw [pow_mul', ← he]; exact hCidx)
    obtain ⟨j, hj⟩ := hJtwo.exists_card_eq
    apply IsPGroup.of_card (n := a + (e + j))
    rw [← hCcard, ha, he, hj, pow_add, pow_add]
  have hCM : C = M := by
    rw [← hCcore]
    exact (pointTwoCoreImage_eq_self_of_isPGroup C hCtwo).symm
  have huC : u ∈ C := ⟨hJH huJ, hJQ huJ⟩
  rw [hCM] at huC
  exact huQ (hInv u huC hu)

theorem minimalLocalFailure_two_core_involution_subgroup_growth_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearPointKernelConclusion H z beta t) :
    TwoCoreInvolutionGrowthConclusion H z := by
  intro hQM
  have hgrow : ∃ m ∈ TwoCoreGrowth.pointTwoCoreImage H, orderOf m = 2 ∧
      m ∉ minimalLocalFailurePairActionPointHull H z := by
    by_contra hcon
    push Not at hcon
    exact false_of_involutions_mem_root h hcomm hsmallerR1 hbeta ht hproper hker hQM hcon
  obtain ⟨m, hmM, hm2, hmQ⟩ := hgrow
  obtain ⟨hQel, -⟩ := CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  refine ⟨lt_of_le_of_ne ?_ ?_, m, hmM, hm2, hmQ⟩
  · intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨hQM.le hx, orderOf_eq_prime (hQel.2 x hx) hx1⟩
  · intro heq
    apply hmQ
    rw [heq]
    exact Subgroup.subset_closure ⟨hmM, hm2⟩

end CFSG.ShultStronglyClosedTI.LinearChain.TwoCoreGrowthNode
