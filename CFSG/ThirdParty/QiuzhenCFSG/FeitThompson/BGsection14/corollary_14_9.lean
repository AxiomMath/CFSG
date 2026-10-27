module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.corollary_14_8

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 14 9 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Corollary 14.9(a): if `𝓜_P` is empty, `G#` is the disjoint union of
the conjugacy closures of the `M̃_i`. -/
public theorem CFSG.section14_msigmaElement_nonempty_of_sigmaLength_one
    {x : G} (hx : section14SigmaLength x = 1) :
    (section14MsigmaElement x).Nonempty := by
  have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one (G := G) hx
  obtain ⟨y, y', M, hEq, hy, hy'sigma', hcomm, hMy⟩ :=
    section14_exists_msigma_factor_of_ne_one (G := G) hxne
  let B : Set Nat.Primes := section10SigmaPrimes M
  have hyB : section14ElementPrimeSupport y ⊆ B :=
    section14_primeSupport_subset_sigma_of_msigmaMember hMy
  have hy'Bc : section14ElementPrimeSupport y' ⊆ Bᶜ := hy'sigma'
  have hcop : Nat.Coprime (orderOf y) (orderOf y') :=
    section14_coprime_order_of_support_split
      (π := Bᶜ) (by simpa using hyB) hy'Bc
  have support_mono {a b : G} (hab : a ∈ Subgroup.zpowers b) :
      section14ElementPrimeSupport a ⊆ section14ElementPrimeSupport b := by
    intro p hp
    exact section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hab) hp
  have sigmaSupport_mono {a b : G}
      (hab : section14ElementPrimeSupport a ⊆ section14ElementPrimeSupport b) :
      section14SigmaSupport a ⊆ section14SigmaSupport b := by
    intro π hπ
    rcases hπ with ⟨hπblock, ⟨p, hpA, hpπ⟩⟩
    exact ⟨hπblock, ⟨p, hab hpA, hpπ⟩⟩
  have sigma_unique :
      ∀ {π₁ π₂ : Set Nat.Primes},
        π₁ ∈ section14SigmaSupport x →
        π₂ ∈ section14SigmaSupport x → π₁ = π₂ := by
    obtain ⟨π0, hπ0, huniq⟩ :=
      section14_unique_sigma_block_of_length_one (G := G) hx
    intro π₁ π₂ h₁ h₂
    exact (huniq _ h₁).trans (huniq _ h₂).symm
  have hB_y : B ∈ section14SigmaSupport y := by
    rw [section14_sigmaSupport_eq_singleton_of_length_one (G := G) hy hMy]
    simp [B]
  have hyG0 : y ∈ Subgroup.zpowers (y * y') :=
    section14_mem_zpowers_mul_of_commute_of_coprime_order hcomm hcop
  have hyG : y ∈ Subgroup.zpowers x := by
    simpa [hEq] using hyG0
  have hB_x : B ∈ section14SigmaSupport x :=
    sigmaSupport_mono (support_mono hyG) hB_y
  have hy'1 : y' = 1 := by
    by_contra hy'ne
    have hy'G0 : y' ∈ Subgroup.zpowers (y' * y) :=
      section14_mem_zpowers_mul_of_commute_of_coprime_order
        hcomm.symm (by simpa [Nat.coprime_comm] using hcop)
    have hy'G1 : y' ∈ Subgroup.zpowers (y * y') := by
      simpa [hcomm.eq] using hy'G0
    have hy'G : y' ∈ Subgroup.zpowers x := by
      simpa [hEq] using hy'G1
    obtain ⟨M1, hM1, hMeet1⟩ :=
      section14_exists_sigma_support_witness (G := G) hy'ne
    let B1 : Set Nat.Primes := section10SigmaPrimes M1
    have hB1_y' : B1 ∈ section14SigmaSupport y' := by
      exact ⟨⟨M1, hM1, rfl⟩, hMeet1⟩
    have hB1_x : B1 ∈ section14SigmaSupport x :=
      sigmaSupport_mono (support_mono hy'G) hB1_y'
    have hEqB : B1 = B := sigma_unique hB1_x hB_x
    rcases hB1_y' with ⟨_hB1block, ⟨q, hqSupp, hqB1⟩⟩
    exact (hy'Bc hqSupp) (hEqB ▸ hqB1)
  refine ⟨M, ?_⟩
  have hyx : y = x := by
    simpa [hy'1] using hEq.symm
  simpa [hyx] using hMy

public theorem CFSG.corollary_14_9_a
    {n : ℕ} {Ms : Fin n → Subgroup G}
    (hMs : section14ConjugacyClassRepresentatives Ms)
    (hPempty : section14MFamilyP G = ∅) :
    (∀ i j : Fin n, i ≠ j →
      section14ConjugacyClosure (section14Tilde (Ms i)) ∩
        section14ConjugacyClosure (section14Tilde (Ms j)) = ∅) ∧
      ({g : G | g ≠ 1} : Set G) =
        ⋃ i : Fin n, section14ConjugacyClosure (section14Tilde (Ms i)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hMi : Ms i ∈ section9MaximalSubgroups G := hMs.1 i
    have hMj : Ms j ∈ section9MaximalSubgroups G := hMs.1 j
    have hnotconj : ¬ section14ConjugateSubgroups (Ms i) (Ms j) := by
      intro hconj
      obtain ⟨k, hk, huniq⟩ := hMs.2 (Ms i) hMi
      have hik : i = k := huniq i ⟨1, (section8_conjBy_one (G := G) (Ms i)).symm⟩
      have hjk : j = k := huniq j hconj
      exact hij (hik.trans hjk.symm)
    exact section14_conjClosure_tilde_disjoint_of_not_conjugate
      (G := G) hMj hMi hnotconj
  · apply Set.Subset.antisymm
    · intro g hg
      rcases (lemma_14_6 (G := G) (g := g) hg).1 with hAlt1 | hAlt2
      · rcases hAlt1 with ⟨x, r, rfl, hxlen, hr⟩
        have hxne : x ≠ 1 := section14_sigmaLength_one_ne_one (G := G) hxlen
        have hσx : (section14MsigmaElement x).Nonempty :=
          section14_msigmaElement_nonempty_of_sigmaLength_one (G := G) hxlen
        let Mx : Subgroup G := Classical.choose hσx
        have hMx : Mx ∈ section14MsigmaElement x := Classical.choose_spec hσx
        obtain ⟨i, hiConj, _hiuniq⟩ := hMs.2 Mx hMx.1
        have hxConj : x ∈ section14ConjClosureMsigmaNonid (Ms i) :=
          section14_mem_conjClosureMsigmaNonid_of_mem_msigma_of_conjugate
            (G := G) (M := Ms i) (L := Mx) hiConj (hMx.2 (by simp)) hxne
        have hxr :
            x * r ∈ section14ConjugacyClosure (section14Tilde (Ms i)) :=
          section14_mul_mem_conjClosureTilde_of_mem_conjClosureMsigmaNonid
            (G := G) (M := Ms i) hxConj hr
        exact Set.mem_iUnion.mpr ⟨i, hxr⟩
      · rcases hAlt2 with ⟨y, y', M, _hEq, _hylen, hy'ne, hy'κ, hy'cent, hMy⟩
        obtain ⟨q, z, hz_zpowy', _hzY', _hz_ne, hzprime⟩ :=
          section14_exists_primeOrder_zpowers_in (G := G)
            (B := Subgroup.zpowers y') (Subgroup.mem_zpowers y') hy'ne
        have hqSupp : q ∈ section14ElementPrimeSupport y' := by
          have hqz : q ∈ subgroupPrimeSet (Subgroup.zpowers z) := by
            rw [subgroupPrimeSet]
            rcases (by simpa [section10PrimeOrderSubgroupsIn] using hzprime) with
              ⟨_hzle, hqcard⟩
            simp [hqcard]
          simpa [section14ElementPrimeSupport] using
            section8_subgroupPrimeSet_mono
              (Subgroup.zpowers_le.2 hz_zpowy') hqz
        have hMP : M ∈ section14MFamilyP G := ⟨hMy.1, ⟨q, hy'κ hqSupp⟩⟩
        simp [hPempty] at hMP
    · intro g hg
      rcases Set.mem_iUnion.mp hg with ⟨i, hgi⟩
      intro hg1
      exact section14_one_not_mem_conjClosure_tilde (G := G) (M := Ms i) (hMs.1 i) (hg1 ▸ hgi)


public theorem CFSG.section14_mem_kstar_of_mem_msigma_of_mem_hall_of_commute
    {M K : Subgroup G} {x y : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hyMσ : y ∈ section10Msigma M)
    (hxK : x ∈ K)
    (hxne : x ≠ 1)
    (hcomm : Commute y x) :
    y ∈ section14KStar M K := by
  classical
  obtain ⟨q, z, hz_zpowx, _hzK, _hzne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G) (B := K) hxK hxne
  let X : Subgroup G := Subgroup.zpowers z
  have hX : X ∈ section12PrimeOrderSubgroups K := by
    simpa [X] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
  obtain ⟨U, h14a⟩ := proposition_14_2_a (G := G) (M := M) (K := K) hM hK
  have hyCentX : y ∈ subgroupCentralizerIn (section10Msigma M) X := by
    refine ⟨hyMσ, ?_⟩
    change y ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hwX
    have hwx : w ∈ Subgroup.zpowers x := (Subgroup.zpowers_le.2 hz_zpowx) hwX
    rcases Subgroup.mem_zpowers_iff.mp hwx with ⟨n, rfl⟩
    exact (hcomm.zpow_right n).eq.symm
  simpa [section14_b1_centralizer_eq_kstar_of_prime_manner
    (G := G) (M := M) (K := K) (X := X) h14a.1 hX] using hyCentX

public theorem CFSG.section14_mul_mem_widehatZ_of_mem_hall_of_mem_kstar
    {M K : Subgroup G} {x y : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hxK : x ∈ K)
    (hxne : x ≠ 1)
    (hyKstar : y ∈ section14KStar M K)
    (hyne : y ≠ 1) :
    x * y ∈ section14WidehatZ M K := by
  classical
  obtain ⟨q, z, hz_zpowx, _hzK, _hzne, hzprime⟩ :=
    section14_exists_primeOrder_zpowers_in (G := G) (B := K) hxK hxne
  let X : Subgroup G := Subgroup.zpowers z
  have hX : X ∈ section12PrimeOrderSubgroups K := by
    simpa [X] using section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprime
  have hZdp : section14ZInternalDirectProduct M K :=
    (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK X hX).2.2
  have hxNotKstar : x ∉ section14KStar M K := by
    intro hxKstar
    have hxBot : x ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hZdp.2.2.2.1 hxK hxKstar
    exact hxne (Subgroup.mem_bot.mp hxBot)
  have hyNotK : y ∉ K := by
    intro hyK
    have hyBot : y ∈ (⊥ : Subgroup G) :=
      Subgroup.disjoint_def.mp hZdp.2.2.2.1 hyK hyKstar
    exact hyne (Subgroup.mem_bot.mp hyBot)
  have hxyZ : x * y ∈ section14Z M K := by
    change x * y ∈ K ⊔ section14KStar M K
    simpa [section14Z] using Subgroup.mul_mem_sup hxK hyKstar
  have hxyNotK : x * y ∉ K := by
    intro hxyK
    have hyK : y ∈ K := by
      have hyEq : y = x⁻¹ * (x * y) := by
        group
      rw [hyEq]
      exact K.mul_mem (K.inv_mem hxK) hxyK
    exact hyNotK hyK
  have hxyNotKstar : x * y ∉ section14KStar M K := by
    intro hxyKstar
    have hxKstar : x ∈ section14KStar M K := by
      have hxEq : x = (x * y) * y⁻¹ := by
        group
      rw [hxEq]
      exact (section14KStar M K).mul_mem hxyKstar ((section14KStar M K).inv_mem hyKstar)
    exact hxNotKstar hxKstar
  exact ⟨hxyZ, by
    intro hxyUnion
    rcases hxyUnion with hxyK | hxyKstar
    · exact hxyNotK hxyK
    · exact hxyNotKstar hxyKstar⟩


end Section14
