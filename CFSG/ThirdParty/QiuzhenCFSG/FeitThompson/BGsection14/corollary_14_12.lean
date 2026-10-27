module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.lemma_14_11

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 14 12 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
private theorem CFSG.section14_ambientSylow_isSylow_of_hall
    {H K : Subgroup G} {π : Set Nat.Primes} {q : Nat.Primes}
    (hHall : section12HallSubgroupIn π K H) (hqπ : q ∈ π)
    (Q : Sylow q.val K) :
    ∃ S : Sylow q.val H,
      section10AmbientSylowSubgroup H S = section10AmbientSylowSubgroup K Q := by
  classical
  rcases hHall with ⟨hKH, hHallK⟩
  haveI : Fact q.val.Prime := ⟨q.2⟩
  have hQamb_le_H : section10AmbientSylowSubgroup K Q ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact hKH y.2
  let R : Subgroup H := (section10AmbientSylowSubgroup K Q).subgroupOf H
  have hR_p : IsPGroup q.val R := by
    have hRG : IsPGroup q.val (section10AmbientSylowSubgroup K Q) :=
      section14_ambientSylow_isPGroup (M := K) Q
    exact hRG.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (H := section10AmbientSylowSubgroup K Q) (K := H) hQamb_le_H).symm
  have hR_map : R.map H.subtype = section10AmbientSylowSubgroup K Q := by
    simp [R, inf_eq_left.2 hQamb_le_H]
  have hR_not_dvd : ¬ q.val ∣ R.index := by
    intro hidx
    have hR_card : Nat.card R = Nat.card (Q : Subgroup K) := by
      calc
        Nat.card R = Nat.card (section10AmbientSylowSubgroup K Q) := by
          simpa [R] using section12_card_subgroupOf_eq hQamb_le_H
        _ = Nat.card (Q : Subgroup K) := by
          simpa [section10AmbientSylowSubgroup] using
            (Subgroup.card_map_of_injective
              (K := (Q : Subgroup K)) (f := K.subtype) K.subtype_injective)
    have hK_card : Nat.card (K.subgroupOf H) = Nat.card K :=
      section12_card_subgroupOf_eq hKH
    have hidx2 :
        R.index = (Q : Subgroup K).index * (K.subgroupOf H).index := by
      have hmul :
          Nat.card R * R.index =
            Nat.card (Q : Subgroup K) * ((Q : Subgroup K).index * (K.subgroupOf H).index) := by
        calc
          Nat.card R * R.index = Nat.card H := R.card_mul_index
          _ = Nat.card (K.subgroupOf H) * (K.subgroupOf H).index := by
            rw [Subgroup.card_mul_index]
          _ = Nat.card K * (K.subgroupOf H).index := by rw [hK_card]
          _ = (Nat.card (Q : Subgroup K) * (Q : Subgroup K).index) *
                (K.subgroupOf H).index := by rw [Subgroup.card_mul_index]
          _ = Nat.card (Q : Subgroup K) * ((Q : Subgroup K).index *
                (K.subgroupOf H).index) := by ring
      rw [hR_card] at hmul
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    have hq_dvd_mul : q.val ∣ (Q : Subgroup K).index * (K.subgroupOf H).index := by
      simpa [hidx2] using hidx
    rcases q.2.dvd_mul.mp hq_dvd_mul with hqQ | hqK
    · exact Q.not_dvd_index hqQ
    · exact (hHallK.p_in_pi_of_p_dvd_index q hqK) hqπ
  let S : Sylow q.val H := IsPGroup.toSylow (p := q.val) hR_p hR_not_dvd
  refine ⟨S, ?_⟩
  calc
    section10AmbientSylowSubgroup H S = R.map H.subtype := by
      simp [S, section10AmbientSylowSubgroup]
    _ = section10AmbientSylowSubgroup K Q := hR_map

omit [IsMinCE G] in
private theorem CFSG.section14_regular_normalizes_ambientSylow
    {K U : Subgroup G} {r : Nat.Primes}
    (hUcomm : IsMulCommutative U)
    (hUreg : section14ActsRegularlyOn K U)
    (R : Sylow r.val U) :
    K ≤ Subgroup.normalizer (section10AmbientSylowSubgroup U R : Set G) := by
  classical
  let P : Subgroup G := section10AmbientSylowSubgroup U R
  have hP_le_U : P ≤ U := section14_ambientSylow_le (M := U) R
  have hP_p : IsPGroup r.val P := section14_ambientSylow_isPGroup (M := U) R
  haveI : Fact r.val.Prime := ⟨r.2⟩
  haveI : IsMulCommutative U := hUcomm
  have hR_normal : ((R : Subgroup U)).Normal := by
    infer_instance
  haveI : Unique (Sylow r.val U) := Sylow.unique_of_normal R hR_normal
  refine subgroup_le_normalizer_of_conj_mem P K ?_
  intro k x hxP
  have hkNormU : (k : G) ∈ Subgroup.normalizer (U : Set G) := hUreg.1 k.2
  have hPk_le_U : P.conjBy (k : G) ≤ U := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hyP, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hkNormU y).1 (hP_le_U hyP)
  let Y : Subgroup U := (P.conjBy (k : G)).subgroupOf U
  have hY_p : IsPGroup r.val Y := by
    have hPk_p : IsPGroup r.val (P.conjBy (k : G)) := by
      change IsPGroup r.val (P.map (MulAut.conj (k : G)).toMonoidHom)
      exact IsPGroup.map (p := r.val) (H := P) hP_p (MulAut.conj (k : G)).toMonoidHom
    exact hPk_p.of_equiv (Subgroup.subgroupOfEquivOfLe hPk_le_U).symm
  obtain ⟨S, hYS⟩ := IsPGroup.exists_le_sylow (G := U) (p := r.val) hY_p
  have hS_eq : S = R := Subsingleton.elim _ _
  have hxPk : (k : G) * x * (k : G)⁻¹ ∈ P.conjBy (k : G) := by
    exact Subgroup.mem_map.mpr ⟨x, hxP, by simp [MulAut.conj_apply]⟩
  have hxY : (⟨(k : G) * x * (k : G)⁻¹, hPk_le_U hxPk⟩ : U) ∈ Y := by
    change (k : G) * x * (k : G)⁻¹ ∈ P.conjBy (k : G)
    exact hxPk
  have hxS : (⟨(k : G) * x * (k : G)⁻¹, hPk_le_U hxPk⟩ : U) ∈ (S : Subgroup U) := hYS hxY
  have hxR : (⟨(k : G) * x * (k : G)⁻¹, hPk_le_U hxPk⟩ : U) ∈ (R : Subgroup U) := by
    simpa [hS_eq] using hxS
  exact Subgroup.mem_map.mpr ⟨⟨(k : G) * x * (k : G)⁻¹, hPk_le_U hxPk⟩, hxR, rfl⟩

private theorem CFSG.section14_cor14_12_not_le_partner
    {M K Mstar U : Subgroup G}
    (hM : M ∈ section14MFamilyP2 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (h14 : section14Theorem14_7Data M K Mstar)
    (hU : section14Proposition14_2AData M K U)
    {r : Nat.Primes} (hr : r ∈ subgroupPrimeSet U) :
    ¬ U ≤ Mstar := by
  have hMP : M ∈ section14MFamilyP G := hM.1
  rcases h14 with
    ⟨hMstarP, _hMstar_not_conj, _hPrimeOrderUnique, _hKstarHall, _hKsigmaHall, _hKeq,
      _hKappaEq, _hZdp, _hZcyc, hInterData, _hWidehatTI, _hWidehatNorm, _hWidehatDisj,
      _hWidehatCard, _hWidehatHalf, _hP2prime, _hPconj, _hDerCompl⟩
  rcases hU with ⟨_hPrimeManner, _hUcomm, hUhall, _hUreg, _hUcomp⟩
  have hKcardPrime : Nat.Prime (Nat.card K) :=
    (proposition_14_2_g (G := G) (M := M) (K := K) hM hK).2.1
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hcard1 : Nat.card K = 1 := by simp [hKbot]
    exact hKcardPrime.ne_one hcard1
  obtain ⟨x0, hx0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  have hKstarne : section14KStar M K ≠ ⊥ :=
    (proposition_14_2_c (G := G) (M := M) (K := K) hMP hK).1
  obtain ⟨y0, hy0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKstarne
  have hInter : M ⊓ Mstar = section14Z M K :=
    (hInterData x0 y0 x0.2 (by simpa using hx0ne) y0.2 (by simpa using hy0ne)).1
  intro hUMstar
  have hUZ : U ≤ section14Z M K := by
    intro u hu
    rw [← hInter]
    exact ⟨hUhall.1 hu, hUMstar hu⟩
  have hrZ : r ∈ subgroupPrimeSet (section14Z M K) :=
    section8_subgroupPrimeSet_mono hUZ hr
  obtain ⟨X, hXprimeIn⟩ :=
    section14_exists_primeOrderSubgroupIn_of_dvd_card
      (G := G) (A := section14Z M K) (p := r) hrZ
  have hXprime : X ∈ section12PrimeOrderSubgroups (section14Z M K) :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hXprimeIn
  have hrUsub : r.val ∣ Nat.card (U.subgroupOf M) := by
    simpa [subgroupPrimeSet, section12_card_subgroupOf_eq hUhall.1] using hr
  have hrUπ :
      r ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) :=
    hUhall.2.p_in_pi_of_p_dvd_card r hrUsub
  rcases hXprimeIn with ⟨_hXZ, hXcard⟩
  rcases
      section14_7_primeOrder_le_k_or_kstar_of_z
        (G := G) (M := M) (K := K) (X := X) hMP hK hXprime with
    hXK | hXKstar
  · have hrK : r.val ∣ Nat.card K := by
      exact (by simpa [hXcard] using Subgroup.card_dvd_of_le hXK)
    have hrKsub : r.val ∣ Nat.card (K.subgroupOf M) := by
      simpa [section12_card_subgroupOf_eq hK.1] using hrK
    have hrKappa : r ∈ section14KappaPrimes M :=
      hK.2.p_in_pi_of_p_dvd_card r hrKsub
    exact hrUπ (Or.inl hrKappa)
  · have hrKstar : r.val ∣ Nat.card (section14KStar M K) := by
      exact (by simpa [hXcard] using Subgroup.card_dvd_of_le hXKstar)
    have hrMsigma : r.val ∣ Nat.card (section10Msigma M) :=
      hrKstar.trans (Subgroup.card_dvd_of_le (show section14KStar M K ≤ section10Msigma M from
        inf_le_left))
    have hrMsigmaSub : r.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      have hcardMsigma :
          Nat.card (section10MsigmaSubgroup M) = Nat.card (section10Msigma M) := by
        simpa [section14_msigma_subgroupOf_eq (M := M)] using
          (section12_card_subgroupOf_eq (section14_msigma_le M))
      rw [hcardMsigma]
      exact hrMsigma
    have hrSigma : r ∈ section10SigmaPrimes M :=
      ((theorem_10_2_b hM.1.1).2).p_in_pi_of_p_dvd_card r hrMsigmaSub
    exact hrUπ (Or.inr hrSigma)

private theorem CFSG.section14_cor14_12_H_in_F
    {M K Mstar U : Subgroup G}
    (hM : M ∈ section14MFamilyP2 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (h14 : section14Theorem14_7Data M K Mstar)
    (hU : section14Proposition14_2AData M K U)
    {r : Nat.Primes} (hr : r ∈ subgroupPrimeSet U)
    (R : Sylow r.val U)
    {H : Subgroup G}
    (hH : H ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (section10AmbientSylowSubgroup U R : Set G))) :
    H ∈ section14MFamilyF G := by
  have hMP : M ∈ section14MFamilyP G := hM.1
  have h14Data := h14
  have hUData := hU
  rcases h14 with
    ⟨hMstarP, _hMstar_not_conj, _hPrimeOrderUnique, hKstarHall, _hKsigmaHall, hKeq,
      _hKappaEq, _hZdp, _hZcyc, _hInterData, _hWidehatTI, _hWidehatNorm, _hWidehatDisj,
      _hWidehatCard, _hWidehatHalf, _hP2prime, hPconj, _hDerCompl⟩
  rcases hU with ⟨hPrimeManner, hUcomm, hUhall, hUreg, hUcomp⟩
  let P : Subgroup G := section10AmbientSylowSubgroup U R
  have hP_le_U : P ≤ U := by
    intro x hxP
    rcases Subgroup.mem_map.mp hxP with ⟨y, _hyR, rfl⟩
    exact y.2
  have hUH : U ≤ H := by
    have hUHcent : U ≤ Subgroup.centralizer (P : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro x hxP
      haveI : IsMulCommutative U := hUcomm
      letI : CommGroup U := IsMulCommutative.instCommGroup
      exact congrArg Subtype.val (mul_comm (⟨x, hP_le_U hxP⟩ : U) ⟨u, hu⟩)
    exact hUHcent.trans (centralizer_le_normalizer P) |>.trans hH.2
  have hKH : K ≤ H :=
    (section14_regular_normalizes_ambientSylow
      (K := K) (U := U) (r := r) hUcomm hUreg R).trans hH.2
  have hHnotM : ¬ section14ConjugateSubgroups H M := by
    intro hHM
    rcases hHM with ⟨a, hHa⟩
    let π : Set Nat.Primes := (section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ
    have hcardHM : Nat.card H = Nat.card M := by
      rw [hHa]
      exact section14_card_conjBy M a
    have hcardUH : Nat.card (U.subgroupOf H) = Nat.card U :=
      section12_card_subgroupOf_eq hUH
    have hcardUM : Nat.card (U.subgroupOf M) = Nat.card U :=
      section12_card_subgroupOf_eq hUhall.1
    have hidxUH : (U.subgroupOf H).index = (U.subgroupOf M).index := by
      have hmul :
          Nat.card (U.subgroupOf H) * (U.subgroupOf H).index =
            Nat.card (U.subgroupOf M) * (U.subgroupOf M).index := by
        calc
          Nat.card (U.subgroupOf H) * (U.subgroupOf H).index = Nat.card H := by
            simp
          _ = Nat.card M := hcardHM
          _ = Nat.card (U.subgroupOf M) * (U.subgroupOf M).index := by
            simp
      rw [hcardUH, hcardUM] at hmul
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul
    have hUhallH : section12HallSubgroupIn π U H := by
      refine ⟨hUH, isHallSubgroup_of (G := H) (π := π) (H := U.subgroupOf H) ?_ ?_⟩
      · intro p hpUH
        have hpUM : p.val ∣ Nat.card (U.subgroupOf M) := by
          simpa [hcardUH, hcardUM] using hpUH
        exact hUhall.2.p_in_pi_of_p_dvd_card p hpUM
      · intro p hpπ hpidx
        have hpidxM : p.val ∣ (U.subgroupOf M).index := by
          simpa [hidxUH] using hpidx
        exact (hUhall.2.p_in_pi_of_p_dvd_index p hpidxM) hpπ
    have hrπ : r ∈ π := by
      have hrUH : r.val ∣ Nat.card (U.subgroupOf H) := by
        simpa [subgroupPrimeSet, section12_card_subgroupOf_eq hUH] using hr
      exact hUhallH.2.p_in_pi_of_p_dvd_card r hrUH
    obtain ⟨S, hP_eq⟩ :=
      section14_ambientSylow_isSylow_of_hall
        (H := H) (K := U) (π := π) hUhallH hrπ R
    have hrSigmaH : r ∈ section10SigmaPrimes H := by
      refine ⟨hr.trans (Subgroup.card_dvd_of_le hUH), S, ?_⟩
      simpa [P, hP_eq] using hH.2
    have hrSigmaHa : r ∈ section10SigmaPrimes (M.conjBy a) := by
      simpa [hHa] using hrSigmaH
    have hrSigmaM :
        r ∈ section10SigmaPrimes ((M.conjBy a).conjBy a⁻¹) :=
      section14_sigma_mem_conjBy (L := M.conjBy a) hrSigmaHa a⁻¹
    have hrSigma : r ∈ section10SigmaPrimes M := by
      simpa [section11_conjBy_inv] using hrSigmaM
    have hrUM : r.val ∣ Nat.card (U.subgroupOf M) := by
      simpa [subgroupPrimeSet, section12_card_subgroupOf_eq hUhall.1] using hr
    have hrPiM : r ∈ π := hUhall.2.p_in_pi_of_p_dvd_card r hrUM
    exact hrPiM (Or.inr hrSigma)
  have hHnotMstar : ¬ section14ConjugateSubgroups H Mstar := by
    intro hHMstar
    rcases hHMstar with ⟨a, hHa⟩
    have hKcardPrime : Nat.Prime (Nat.card K) :=
      (proposition_14_2_g (G := G) (M := M) (K := K) hM hK).2.1
    have hKne : K ≠ ⊥ := by
      intro hKbot
      have hcard1 : Nat.card K = 1 := by simp [hKbot]
      exact hKcardPrime.ne_one hcard1
    have haMstar : a ∈ Mstar := by
      by_contra haNotMstar
      have hKleHg : K ≤ Mstar.conjBy a := by simpa [hHa] using hKH
      have hKstarleHg : section14KStar Mstar (section14KStar M K) ≤ Mstar.conjBy a := by
        rw [← hKeq]
        exact hKleHg
      have hKstarEqBot : section14KStar Mstar (section14KStar M K) = ⊥ := by
        calc
          section14KStar Mstar (section14KStar M K) =
              section14KStar Mstar (section14KStar M K) ⊓ Mstar.conjBy a :=
            (inf_eq_left.2 hKstarleHg).symm
          _ = ⊥ :=
            (proposition_14_2_d
              (G := G) (M := Mstar) (K := section14KStar M K) hMstarP hKstarHall).1 a haNotMstar
      exact hKne (hKeq.trans hKstarEqBot)
    have hHeq : H = Mstar := by
      calc
        H = Mstar.conjBy a := hHa
        _ = Mstar := section11_conjBy_eq_of_mem_normalizer
          (H := Mstar) (Subgroup.le_normalizer haMstar)
    exact
      section14_cor14_12_not_le_partner
        (G := G) (M := M) (K := K) (Mstar := Mstar) (U := U)
        hM hK h14Data hUData hr (by simpa [hHeq] using hUH)
  have hHnotP : H ∉ section14MFamilyP G := by
    intro hHP
    rcases hPconj H hHP with hHM | hHMstar
    · exact hHnotM hHM
    · exact hHnotMstar hHMstar
  refine ⟨hH.1, ?_⟩
  ext p
  simp
  intro hp
  exact hHnotP ⟨hH.1, ⟨p, hp⟩⟩

private theorem CFSG.section14_cor14_12_k_in_fitting_of_complement
    {M K Mstar H : Subgroup G}
    (hM : M ∈ section14MFamilyP2 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (h14 : section14Theorem14_7Data M K Mstar)
    (hHF : H ∈ section14MFamilyF G)
    (hKH : K ≤ H) :
    ∃ D : Subgroup G,
      section12ComplementToMsigma H D ∧
        K ≤ D ∧
        K ≤ section8FittingSubgroup D := by
  have hMP : M ∈ section14MFamilyP G := hM.1
  have hHnotP : H ∉ section14MFamilyP G := by
    intro hHP
    rcases hHP.2 with ⟨p, hp⟩
    simp [hHF.2] at hp
  rcases h14 with
    ⟨hMstarP, _hMstar_not_conj, hPrimeOrderUnique, _hKstarHall, _hKsigmaHall, hKeq,
      _hKappaEq, _hZdp, _hZcyc, _hInterData, _hWidehatTI, _hWidehatNorm, _hWidehatDisj,
      _hWidehatCard, _hWidehatHalf, _hP2prime, hPconj, _hDerCompl⟩
  have hMstar_not_H : section12NotConjugate Mstar H := by
    intro a ha
    apply hHnotP
    simpa [ha] using section14_mem_P_conjBy (G := G) (M := Mstar) a hMstarP
  have hSigmaDisj : Disjoint (section10SigmaPrimes H) (section10SigmaPrimes Mstar) :=
    theorem_13_9 (G := G) hHF.1 hMstarP.1 hMstar_not_H
  have hK_le_sigmaStar : K ≤ section10Msigma Mstar := by
    rw [hKeq]
    exact inf_le_left
  have hKpiH : IsPiSubgroup (G := G) (section10SigmaPrimes H)ᶜ K := by
    refine section8_isPiSubgroup_of_subgroupPrimeSet_subset ?_
    intro p hpK
    have hpSigmaStar : p ∈ section10SigmaPrimes Mstar := by
      have hpMsigma : p.val ∣ Nat.card (section10Msigma Mstar) :=
        hpK.trans (Subgroup.card_dvd_of_le hK_le_sigmaStar)
      exact ((theorem_10_2_b (G := G) hMstarP.1).1).p_in_pi_of_p_dvd_card p hpMsigma
    exact fun hpSigmaH => (Set.disjoint_left.mp hSigmaDisj) hpSigmaH hpSigmaStar
  obtain ⟨D, hDcomp, hKD⟩ :=
    section14_exists_sigma_complement_containing
      (G := G) (M := H) (K := K) hHF.1 hKH hKpiH
  have hKcardPrime : Nat.Prime (Nat.card K) :=
    (proposition_14_2_g (G := G) (M := M) (K := K) hM hK).2.1
  let q : Nat.Primes := ⟨Nat.card K, hKcardPrime⟩
  have hqD : q ∈ subgroupPrimeSet D := by
    show q.val ∣ Nat.card D
    simpa [q] using (Subgroup.card_dvd_of_le hKD : Nat.card K ∣ Nat.card D)
  have hKprimeD : K ∈ section10PrimeOrderSubgroupsIn q D := by
    exact ⟨hKD, by simp [q]⟩
  have hqSigmaMstar : q ∈ section10SigmaPrimes Mstar := by
    have hqMsigma : q.val ∣ Nat.card (section10Msigma Mstar) := by
      simpa [q] using (Subgroup.card_dvd_of_le hK_le_sigmaStar :
        Nat.card K ∣ Nat.card (section10Msigma Mstar))
    exact ((theorem_10_2_b (G := G) hMstarP.1).1).p_in_pi_of_p_dvd_card q hqMsigma
  have hKprimeSub : K ∈ section12PrimeOrderSubgroups K := by
    exact ⟨le_rfl, ⟨q, by simp [q]⟩⟩
  by_cases hKF : K ≤ section8FittingSubgroup D
  · exact ⟨D, hDcomp, hKD, hKF⟩
  · obtain ⟨Hstar, hHstarMax, hAlt, _hSituation⟩ :=
      lemma_14_11
        (G := G) (M := H) (E := D) (Q := K) (q := q)
        hHF hDcomp hqD hKprimeD hKF
    rcases hAlt with hTau2 | hKappa
    · rcases hTau2 with ⟨hqTau2, hCentUnique⟩
      have hUniqueMstar :
          section9MaximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mstar} :=
        hPrimeOrderUnique K hKprimeSub
      have hMstarMem :
          Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) := by
        rw [hUniqueMstar]
        simp
      rw [hCentUnique] at hMstarMem
      have hHstarEq : Hstar = Mstar := by simpa using hMstarMem.symm
      exact False.elim (hqTau2.1 (hHstarEq ▸ hqSigmaMstar))
    · rcases hKappa with ⟨hqKappa, hHstarP1⟩
      have hHstar_not_conj_Mstar : ¬ section14ConjugateSubgroups Hstar Mstar := by
        intro hconj
        rcases hconj with ⟨a, ha⟩
        have hqMstarKappa : q ∈ section14KappaPrimes Mstar := by
          simpa [ha, section14_kappaPrimes_conjBy (G := G) Mstar a] using hqKappa
        exact section14_kappa_subset_not_sigma (M := Mstar) hqMstarKappa hqSigmaMstar
      rcases hPconj Hstar hHstarP1.1 with hHstarM | hHstarMstar
      · exact False.elim ((section14_mem_P2_of_conjugate (G := G) hHstarM hM).2 hHstarP1.2)
      · exact False.elim (hHstar_not_conj_Mstar hHstarMstar)

private theorem CFSG.section14_cor14_12_subnormal_le_partner
    {M K Mstar P : Subgroup G}
    (hM : M ∈ section14MFamilyP2 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (h14 : section14Theorem14_7Data M K Mstar)
    (hSub : IsSubnormalIn K P) :
    P ≤ Mstar := by
  rcases h14 with
    ⟨hMstarP, _hMstar_not_conj, _hPrimeOrderUnique, hKstarHall, _hKsigmaHall, hKeq,
      _hKappaEq, _hZdp, _hZcyc, _hInterData, _hWidehatTI, _hWidehatNorm, _hWidehatDisj,
      _hWidehatCard, _hWidehatHalf, _hP2prime, _hPconj, _hDerCompl⟩
  have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM.1 hK
  have hKleMstar : K ≤ Mstar := by
    rw [hKeq]
    intro x hx
    exact section14_msigma_le Mstar hx.1
  rcases hSub with ⟨n, chain, h0, hlast, hstep, hnorm⟩
  have hKle_chain : ∀ i : Fin (n + 1), K ≤ chain i := by
    intro i
    have hmono : chain 0 ≤ chain i := by
      induction i using Fin.induction with
      | zero =>
          exact le_rfl
      | succ i ih =>
          exact ih.trans (hstep i)
    simpa [h0] using hmono
  have hchain_le_Mstar : ∀ i : Fin (n + 1), chain i ≤ Mstar := by
    intro i
    induction i using Fin.induction with
    | zero =>
        simpa [h0] using hKleMstar
    | succ i ih =>
        intro x hx
        by_contra hxNotMstar
        have hsucc_norm :
            chain i.succ ≤ Subgroup.normalizer (chain i.castSucc : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer (hstep i)).1 (hnorm i)
        have hxNorm : x ∈ Subgroup.normalizer (chain i.castSucc : Set G) :=
          hsucc_norm hx
        have hxInvNorm : x⁻¹ ∈ Subgroup.normalizer (chain i.castSucc : Set G) :=
          Subgroup.inv_mem _ hxNorm
        have hKleConj : K ≤ Mstar.conjBy x := by
          intro y hyK
          have hyi : y ∈ chain i.castSucc := hKle_chain i.castSucc hyK
          have hyConj : x⁻¹ * y * x ∈ chain i.castSucc := by
            simpa using (Subgroup.mem_normalizer_iff.mp hxInvNorm y).1 hyi
          have hyMstar : x⁻¹ * y * x ∈ Mstar := ih hyConj
          exact Subgroup.mem_map.mpr ⟨x⁻¹ * y * x, hyMstar, by
            change x * (x⁻¹ * y * x) * x⁻¹ = y
            group⟩
        have hKstarEq : section14KStar Mstar (section14KStar M K) = K := hKeq.symm
        have hKstarLeConj :
            section14KStar Mstar (section14KStar M K) ≤ Mstar.conjBy x := by
          simpa [hKstarEq] using hKleConj
        have hKstarNeBot : section14KStar Mstar (section14KStar M K) ≠ ⊥ := by
          intro hbot
          exact hKne (by simpa [hKstarEq] using hbot)
        have hdisj :=
          (proposition_14_2_d
            (G := G) (M := Mstar) (K := section14KStar M K) hMstarP hKstarHall).1 x hxNotMstar
        have hKstarLeBot : section14KStar Mstar (section14KStar M K) ≤ ⊥ := by
          rw [← hdisj]
          exact le_inf le_rfl hKstarLeConj
        exact hKstarNeBot (le_bot_iff.mp hKstarLeBot)
  simpa [hlast] using hchain_le_Mstar (Fin.last n)

/-- Corollary 14.12: the maximal subgroup normalizing a Sylow subgroup of
`U` has type `𝓕` and the listed intersections/complements. -/
public theorem CFSG.corollary_14_12
    {M K Mstar U : Subgroup G}
    (hM : M ∈ section14MFamilyP2 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (h14 : section14Theorem14_7Data M K Mstar)
    (hU : section14Proposition14_2AData M K U)
    {r : Nat.Primes} (hr : r ∈ subgroupPrimeSet U)
    (R : Sylow r.val U)
    {H : Subgroup G}
    (hH : H ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (section10AmbientSylowSubgroup U R : Set G))) :
    H ∈ section14MFamilyF G ∧
      U ≤ section10Msigma H ∧
      ((M ⊓ H : Subgroup G) : Set G) = (U : Set G) * (K : Set G) ∧
      ¬ subgroupNormalizerIn H (U : Set G) ≤ M ∧
      K ≤ section8FittingSubgroup (H ⊓ Mstar) ∧
      section12ComplementIn H (section10Msigma H) (H ⊓ Mstar) := by
  have hHF :=
    section14_cor14_12_H_in_F
      (G := G) (M := M) (K := K) (Mstar := Mstar) (U := U)
      hM hK h14 hU hr R hH
  rcases hU with ⟨hPrimeManner, hUcomm, hUhall, hUreg, hUcomp⟩
  let P : Subgroup G := section10AmbientSylowSubgroup U R
  have hP_le_U : P ≤ U := by
    intro x hxP
    rcases Subgroup.mem_map.mp hxP with ⟨y, _hyR, rfl⟩
    exact y.2
  have hUH : U ≤ H := by
    have hUHcent : U ≤ Subgroup.centralizer (P : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro x hxP
      haveI : IsMulCommutative U := hUcomm
      letI : CommGroup U := IsMulCommutative.instCommGroup
      exact congrArg Subtype.val (mul_comm (⟨x, hP_le_U hxP⟩ : U) ⟨u, hu⟩)
    exact hUHcent.trans (centralizer_le_normalizer P) |>.trans hH.2
  have hKH : K ≤ H :=
    (section14_regular_normalizes_ambientSylow
      (K := K) (U := U) (r := r) hUcomm hUreg R).trans hH.2
  obtain ⟨D, hDcomp, hKD, hKF⟩ :=
    section14_cor14_12_k_in_fitting_of_complement
      (G := G) (M := M) (K := K) (Mstar := Mstar) (H := H)
      hM hK h14 hHF hKH
  have hTail :
      U ≤ section10Msigma H ∧
        ((M ⊓ H : Subgroup G) : Set G) = (U : Set G) * (K : Set G) ∧
        ¬ subgroupNormalizerIn H (U : Set G) ≤ M ∧
        K ≤ section8FittingSubgroup (H ⊓ Mstar) ∧
        section12ComplementIn H (section10Msigma H) (H ⊓ Mstar) := by
    have hKcardPrime : Nat.Prime (Nat.card K) :=
      (proposition_14_2_g (G := G) (M := M) (K := K) hM hK).2.1
    let q : Nat.Primes := ⟨Nat.card K, hKcardPrime⟩
    have hKp : IsPGroup q.val K := by
      refine IsPGroup.of_card (p := q.val) (G := K) (n := 1) ?_
      simp [q, pow_one]
    have hKsubF : IsSubnormalIn K (section8FittingSubgroup D) := by
      letI : Group.IsNilpotent (section8FittingSubgroup D) :=
        section8FittingSubgroup_isNilpotent D
      exact section8_isSubnormalIn_of_nilpotent hKF
    have hFsubD : IsSubnormalIn (section8FittingSubgroup D) D := by
      letI : ((section8FittingSubgroup D).subgroupOf D).Normal := by
        simpa using section8FittingSubgroup_normal_in D
      exact section8_isSubnormalIn_of_normal_subgroupOf (section8FittingSubgroup_le D)
    have hDleMstar : D ≤ Mstar := by
      have hKsubD : IsSubnormalIn K D := by
        let Fsub : Subgroup D := (section8FittingSubgroup D).subgroupOf D
        have hKFsub : K.subgroupOf D ≤ Fsub := by
          intro x hx
          exact hKF hx
        have hKsubFsub : (K.subgroupOf D).IsSubnormal := by
          have hnilFsub : Group.IsNilpotent Fsub := by
            letI : Group.IsNilpotent (section8FittingSubgroup D) :=
              section8FittingSubgroup_isNilpotent D
            exact
              Group.nilpotent_of_mulEquiv
                (Subgroup.subgroupOfEquivOfLe
                  (H := section8FittingSubgroup D) (K := D) (section8FittingSubgroup_le D)).symm
          have hKsubFsub' : ((K.subgroupOf D).subgroupOf Fsub).IsSubnormal := by
            letI : Group.IsNilpotent Fsub := hnilFsub
            exact
              section8_isSubnormal_of_normalizerCondition
                (G := Fsub) Group.normalizerCondition_of_isNilpotent
                ((K.subgroupOf D).subgroupOf Fsub)
          have hFsubSubnormal : Fsub.IsSubnormal := by
            letI : Fsub.Normal := by
              simpa [Fsub] using section8FittingSubgroup_normal_in D
            exact Subgroup.Normal.isSubnormal (H := Fsub) inferInstance
          exact Subgroup.IsSubnormal.trans hKFsub hKsubFsub' hFsubSubnormal
        exact section8_isSubnormalIn_of_subgroupOf_isSubnormal hKD hKsubFsub
      exact
        section14_cor14_12_subnormal_le_partner
          (G := G) (M := M) (K := K) (Mstar := Mstar) hM hK h14
          hKsubD
    have hUleσ : U ≤ section10Msigma H := by
      have hKne : K ≠ ⊥ := by
        intro hKbot
        have hcard1 : Nat.card K = 1 := by simp [hKbot]
        exact hKcardPrime.ne_one hcard1
      have hCbot : subgroupCentralizerIn U K = ⊥ :=
        section14_subgroupCentralizerIn_eq_bot_of_regular (G := G) hKne hUreg
      rcases hUhall with ⟨hUM, hHallU⟩
      have hσH : section10Msigma H ≤ H := hDcomp.1
      have hDH : D ≤ H := hDcomp.2.1
      have hσDdisj : Disjoint (section10Msigma H) D := hDcomp.2.2.2
      let OqD : Subgroup G := piCoreIn ({q} : Set Nat.Primes) D
      have hOqDleD : OqD ≤ D := by
        simpa [OqD] using piCoreIn_le (G := G) ({q} : Set Nat.Primes) D
      have hDnormOqD : D ≤ Subgroup.normalizer (OqD : Set G) := by
        simpa [OqD] using
          section8_le_normalizer_piCoreIn_of_le_normalizer
            (G := G) (π := ({q} : Set Nat.Primes)) (H := D) (P := D)
            (Subgroup.le_normalizer : D ≤ Subgroup.normalizer (D : Set G))
      have hOqDnormInD : section10NormalIn OqD D := by
        exact
          ⟨hOqDleD,
            (Subgroup.normal_subgroupOf_iff_le_normalizer hOqDleD).2 hDnormOqD⟩
      have hKleOqD : K ≤ OqD := by
        letI : Group.IsNilpotent (section8FittingSubgroup D) :=
          section8FittingSubgroup_isNilpotent D
        have hKleF : K ≤ section8FittingSubgroup D := hKF
        have hFnormD : D ≤ Subgroup.normalizer (section8FittingSubgroup D : Set G) := by
          letI : ((section8FittingSubgroup D).subgroupOf D).Normal := by
            simpa using section8FittingSubgroup_normal_in D
          exact Subgroup.le_normalizer_of_normal_subgroupOf (section8FittingSubgroup_le D)
        have hKleOqF :
            K ≤ piCoreIn ({q} : Set Nat.Primes) (section8FittingSubgroup D) :=
          section8_isPGroup_le_piCoreIn_singleton_of_le_nilpotent
            (G := G) (H := K) (K := section8FittingSubgroup D) hKleF q hKp
        exact
          hKleOqF.trans
            (section8_piCoreIn_singleton_le_of_le_normalizer
              (G := G) (Y := section8FittingSubgroup D) (H := D)
              (section8FittingSubgroup_le D) hFnormD q)
      let N : Subgroup G := section10Msigma H ⊔ OqD
      have hNnormH : section10NormalIn N H := by
        exact
          section14_msigma_sup_normalIn_of_complement_normal
            (G := G) (M := H) (E := D) (U := OqD) hDcomp hOqDnormInD
      have hKN : K ≤ N := by
        intro x hxK
        exact Subgroup.mem_sup_right (hKleOqD hxK)
      have hsolvU : IsSolvable U :=
        section14_solvable_of_le_maximal hH.1 hUH
      have hcopKU : Nat.Coprime (Nat.card K) (Nat.card U) := by
        refine Nat.coprime_of_dvd ?_
        intro p hpprime hpKcard hpUcard
        let p' : Nat.Primes := ⟨p, hpprime⟩
        have hpκ : p' ∈ section14KappaPrimes M :=
          hK.2.p_in_pi_of_p_dvd_card p'
            (by simpa [section12_card_subgroupOf_eq hK.1, p'] using hpKcard)
        have hpπc :
            p' ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) :=
          hHallU.p_in_pi_of_p_dvd_card p'
            (by simpa [section12_card_subgroupOf_eq hUM, p'] using hpUcard)
        exact hpπc (Or.inl hpκ)
      have hUleComm : U ≤ ⁅U, K⁆ :=
        section8_le_commutator_of_subgroupCentralizerIn_eq_bot
          (G := G) (Y := U) (R := K) hsolvU hUreg.1 hcopKU hCbot
      have hcommLeN : ⁅U, K⁆ ≤ N := by
        have hHnormN : H ≤ Subgroup.normalizer (N : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hNnormH.1).1 hNnormH.2
        exact
          Subgroup.commutator_le.mpr (fun x hxU y hyK => by
            have hyN : y ∈ N := hKN hyK
            have hconjN : x * y * x⁻¹ ∈ N :=
              (Subgroup.mem_normalizer_iff.mp (hHnormN (hUH hxU)) y).1 hyN
            exact N.mul_mem hconjN (N.inv_mem hyN))
      have hUN : U ≤ N := hUleComm.trans hcommLeN
      have hUqcompl : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ U := by
        intro p hpUcard
        let p' : Nat.Primes := p
        have hpπc :
            p' ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) :=
          hHallU.p_in_pi_of_p_dvd_card p'
            (by simpa [section12_card_subgroupOf_eq hUM] using hpUcard)
        have hpκ' : p' ∉ section14KappaPrimes M := by
          intro hpκ
          exact hpπc (Or.inl hpκ)
        intro hpq
        have hp_eq_q : p' = q := by
          simpa [p'] using hpq
        have hqκ : q ∈ section14KappaPrimes M := by
          have hqK : q.val ∣ Nat.card K := by simp [q]
          exact hK.2.p_in_pi_of_p_dvd_card q
            (by simp [section12_card_subgroupOf_eq hK.1, q])
        exact hpκ' (by simpa [hp_eq_q] using hqκ)
      have hOqDq : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) OqD := by
        simpa [OqD] using piCoreIn_isPiSubgroup (G := G) ({q} : Set Nat.Primes) D
      have hUinf_bot : U ⊓ OqD = ⊥ :=
        section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
          (G := G) (π := ({q} : Set Nat.Primes))
          (H := U ⊓ OqD) (Y := U) (C := OqD) inf_le_left inf_le_right hUqcompl hOqDq
      have hHnormσ : H ≤ Subgroup.normalizer (section10Msigma H : Set G) := by
        simpa using section12_le_normalizer_msigma (M := H)
      have hOqDnormσ : OqD ≤ Subgroup.normalizer (section10Msigma H : Set G) :=
        hOqDleD.trans hDH |>.trans hHnormσ
      have hσOqDdisj : Disjoint (section10Msigma H) OqD := by
        rw [Subgroup.disjoint_def]
        intro x hxσ hxOqD
        exact Subgroup.disjoint_def.mp hσDdisj hxσ (hOqDleD hxOqD)
      let N' : Subgroup G := OqD ⊔ section10Msigma H
      have hUN' : U ≤ N' := by
        simpa [N', N, sup_comm] using hUN
      let Nσ : Subgroup N' := (section10Msigma H).subgroupOf N'
      let OqDN : Subgroup N' := OqD.subgroupOf N'
      have hNσnormal : Nσ.Normal := by
        simpa [N', Nσ] using
          (Subgroup.normal_subgroupOf_sup_of_le_normalizer
            (H := OqD) (N := section10Msigma H) hOqDnormσ)
      letI : Nσ.Normal := hNσnormal
      have hcompN : OqDN.IsComplement' Nσ := by
        simpa [N', Nσ, OqDN] using
          (section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
            (G := G) (H := section10Msigma H) (R := OqD) hOqDnormσ hσOqDdisj.eq_bot).symm
      have hOqDNq : IsPiSubgroup (G := N') ({q} : Set Nat.Primes) OqDN := by
        intro p hp
        have hcard : Nat.card OqDN = Nat.card OqD :=
          section12_card_subgroupOf_eq (show OqD ≤ N' from le_sup_left)
        exact hOqDq p (by rwa [hcard] at hp)
      have hquotq : IsPiGroup ({q} : Set Nat.Primes) (N' ⧸ Nσ) := by
        exact
          IsPiGroup.of_equiv
            (IsPiSubgroup.isPiGroup OqDN hOqDNq)
            hcompN.QuotientMulEquiv
      have hUNqcompl : IsPiSubgroup (G := N') ({q} : Set Nat.Primes)ᶜ (U.subgroupOf N') := by
        intro p hp
        have hcard : Nat.card (U.subgroupOf N') = Nat.card U :=
          section12_card_subgroupOf_eq hUN'
        exact hUqcompl p (by rwa [hcard] at hp)
      have hUmap_bot :
          (U.subgroupOf N').map (QuotientGroup.mk' Nσ) = ⊥ := by
        by_contra hmap_ne_bot
        have hcard_ne_one :
            Nat.card ((U.subgroupOf N').map (QuotientGroup.mk' Nσ)) ≠ 1 := by
          intro hcard
          exact hmap_ne_bot ((Subgroup.card_eq_one (H := (U.subgroupOf N').map
            (QuotientGroup.mk' Nσ))).1 hcard)
        obtain ⟨p, hpPrime, hpMap⟩ := Nat.exists_prime_and_dvd hcard_ne_one
        let p' : Nat.Primes := ⟨p, hpPrime⟩
        have hp_mem : p' ∈ ({q} : Set Nat.Primes) := by
          exact (IsPiGroup_iff ({q} : Set Nat.Primes) (N' ⧸ Nσ)).1 hquotq p'
            (hpMap.trans (Subgroup.card_subgroup_dvd_card
              ((U.subgroupOf N').map (QuotientGroup.mk' Nσ))))
        have hp_not_mem : p' ∉ ({q} : Set Nat.Primes) := by
          simpa using
            (section14_isPiSubgroup_map hUNqcompl (QuotientGroup.mk' Nσ)) p' hpMap
        exact hp_not_mem hp_mem
      exact
        section14_7_subgroup_le_of_subgroupOf_quotient_map_eq_bot
          (G := G) (N := section10Msigma H) (L := N') (C := U) hUN'
          (by simpa [Nσ] using hUmap_bot)
    rcases h14 with
      ⟨hMstarP, _hMstar_not_conj, _hPrimeOrderUnique, _hKstarHall, _hKsigmaHall, hKeq,
        _hKappaEq, _hZdp, _hZcyc, _hInterData, _hWidehatTI, _hWidehatNorm, _hWidehatDisj,
        _hWidehatCard, _hWidehatHalf, _hP2prime, _hPconj, _hDerCompl⟩
    have hKleσMstar : K ≤ section10Msigma Mstar := by
      rw [hKeq]
      exact inf_le_left
    have hσMstarσ_bot : section10Msigma H ⊓ section10Msigma Mstar = ⊥ := by
      have hHnotMstar : ¬ section14ConjugateSubgroups H Mstar := by
        intro hHMstar
        rcases hHMstar with ⟨a, hHa⟩
        have hHP : H ∈ section14MFamilyP G := by
          simpa [hHa] using section14_mem_P_conjBy (G := G) (M := Mstar) a hMstarP
        simpa [hHF.2] using hHP.2
      have hnotconj : ∀ g : G, Mstar.conjBy g ≠ H := by
        intro g hEq
        exact hHnotMstar ⟨g, hEq.symm⟩
      have hqH : q ∈ subgroupPrimeSet H := by
        show q.val ∣ Nat.card H
        have hqK : q.val ∣ Nat.card K := by simp [q]
        exact hqK.trans (Subgroup.card_dvd_of_le hKH)
      have hqD : q ∈ subgroupPrimeSet D := by
        show q.val ∣ Nat.card D
        simpa [q] using (Subgroup.card_dvd_of_le hKD : Nat.card K ∣ Nat.card D)
      have hq_not_sigmaH : q ∉ section10SigmaPrimes H :=
        section12_not_sigma_of_mem_complement (G := G) (M := H) (E := D) hHF.1 hDcomp hqD
      have hHnotP1 : H ∉ section14MFamilyP1 G := by
        intro hHP1
        have hHP : H ∈ section14MFamilyP G := hHP1.1
        simpa [hHF.2] using hHP.2
      let S : Sylow q.val H := Classical.choice (Sylow.nonempty (p := q.val) (G := H))
      have hnilH : Group.IsNilpotent (section10Msigma H) := by
        exact
          (lemma_14_1 (G := G) (M := H) hHF.1 hHnotP1
            ⟨hqH, by
              intro hqbad
              rcases hqbad with hqσ | hqκ
              · exact hq_not_sigmaH hqσ
              · simp [hHF.2] at hqκ⟩ S).2.2
      exact
        disjoint_iff.mp
          (lemma_10_12_b (G := G) (M := H) (H := Mstar) hHF.1 hMstarP.1 hnotconj hnilH).1
    have hDleHMstar : D ≤ H ⊓ Mstar := by
      intro x hxD
      exact ⟨hDcomp.2.1 hxD, hDleMstar hxD⟩
    have hD_eq_of_msigma_inf_bot :
        section10Msigma H ⊓ Mstar = ⊥ → D = H ⊓ Mstar := by
      intro hσHMstar_bot
      apply le_antisymm hDleHMstar
      intro x hxHMstar
      let σHsub : Subgroup H := (section10Msigma H).subgroupOf H
      let Dsub : Subgroup H := D.subgroupOf H
      let xH : H := ⟨x, hxHMstar.1⟩
      haveI : σHsub.Normal := by
        simpa [σHsub, section14_msigma_subgroupOf_eq] using
          (section14_msigma_normalIn (G := G) (M := H)).2
      have htop : σHsub ⊔ Dsub = ⊤ := by
        calc
          σHsub ⊔ Dsub = ((section10Msigma H) ⊔ D).subgroupOf H := by
            symm
            exact
              Subgroup.subgroupOf_sup
                (A := section10Msigma H) (A' := D) (B := H) hDcomp.1 hDcomp.2.1
          _ = ⊤ := by
            apply Subgroup.subgroupOf_eq_top.mpr
            exact hDcomp.2.2.1.le
      have hxTop : xH ∈ σHsub ⊔ Dsub := by
        simp [htop]
      rcases
          (Subgroup.mem_sup_of_normal_left
            (s := σHsub) (t := Dsub) (x := xH)).1 hxTop with
        ⟨s, hsσsub, d, hdDsub, hsd⟩
      have hsσ : (s : G) ∈ section10Msigma H := by
        simpa [σHsub, Subgroup.mem_subgroupOf] using hsσsub
      have hdD : (d : G) ∈ D := by
        simpa [Dsub, Subgroup.mem_subgroupOf] using hdDsub
      have hsdG : (s : G) * d = x := by
        simpa [xH] using congrArg (fun z : H => (z : G)) hsd
      have hsMstar : (s : G) ∈ Mstar := by
        have hsEq : (s : G) = x * (d : G)⁻¹ := by
          calc
            (s : G) = (s : G) * ((d : G) * (d : G)⁻¹) := by simp
            _ = ((s : G) * (d : G)) * (d : G)⁻¹ := by simp [mul_assoc]
            _ = x * (d : G)⁻¹ := by rw [hsdG]
        rw [hsEq]
        exact Mstar.mul_mem hxHMstar.2 (Mstar.inv_mem (hDleMstar hdD))
      have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
        rw [← hσHMstar_bot]
        exact ⟨hsσ, hsMstar⟩
      have hsOne : (s : G) = 1 := Subgroup.mem_bot.mp hsBot
      have hxEq : x = (d : G) := by
        calc
          x = (s : G) * d := hsdG.symm
          _ = d := by simp [hsOne]
      exact hxEq ▸ hdD
    have hD_eq : D = H ⊓ Mstar := by
      by_contra hDneq
      have hσHMstar_ne_bot : section10Msigma H ⊓ Mstar ≠ ⊥ := by
        intro hσHMstar_bot
        exact hDneq (hD_eq_of_msigma_inf_bot hσHMstar_bot)
      obtain ⟨y, hyne⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hσHMstar_ne_bot
      have hyσHMstar : (y : G) ∈ section10Msigma H ⊓ Mstar := y.2
      have hyneG : (y : G) ≠ 1 := by
        intro hy
        exact hyne (Subtype.ext hy)
      have hσHMstar_le_CK :
          section10Msigma H ⊓ Mstar ≤ subgroupCentralizerIn (section10Msigma H) K := by
        intro z hzσHMstar
        refine ⟨hzσHMstar.1, ?_⟩
        change z ∈ Subgroup.centralizer (K : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro k hkK
        have hHnormσ : H ≤ Subgroup.normalizer (section10Msigma H : Set G) := by
          simpa using section12_le_normalizer_msigma (M := H)
        have hkNormσ : k ∈ Subgroup.normalizer (section10Msigma H : Set G) :=
          hHnormσ (hKH hkK)
        have hzσH : z ∈ section10Msigma H := hzσHMstar.1
        have hzMstar : z ∈ Mstar := hzσHMstar.2
        have hcommσH : z * k * z⁻¹ * k⁻¹ ∈ section10Msigma H := by
          have hkzInv : k * z⁻¹ * k⁻¹ ∈ section10Msigma H :=
            (Subgroup.mem_normalizer_iff.mp hkNormσ z⁻¹).1
              ((section10Msigma H).inv_mem hzσH)
          have hmem : z * (k * z⁻¹ * k⁻¹) ∈ section10Msigma H :=
            (section10Msigma H).mul_mem hzσH hkzInv
          simpa [mul_assoc] using hmem
        have hMstarNormσ : Mstar ≤ Subgroup.normalizer (section10Msigma Mstar : Set G) := by
          simpa using section12_le_normalizer_msigma (M := Mstar)
        have hzkzInv : z * k * z⁻¹ ∈ section10Msigma Mstar :=
          (Subgroup.mem_normalizer_iff.mp (hMstarNormσ hzMstar) k).1
            (hKleσMstar hkK)
        have hcommσMstar : z * k * z⁻¹ * k⁻¹ ∈ section10Msigma Mstar := by
          exact
            (section10Msigma Mstar).mul_mem hzkzInv
              ((section10Msigma Mstar).inv_mem (hKleσMstar hkK))
        have hbot : z * k * z⁻¹ * k⁻¹ ∈ (⊥ : Subgroup G) := by
          rw [← hσMstarσ_bot]
          exact ⟨hcommσH, hcommσMstar⟩
        have hone : z * k * z⁻¹ * k⁻¹ = 1 := Subgroup.mem_bot.mp hbot
        have hzk : z * k = k * z := by
          calc
            z * k = (z * k * z⁻¹ * k⁻¹) * k * z := by group
            _ = k * z := by rw [hone]; simp
        simpa using hzk.symm
      have hyCK : (y : G) ∈ subgroupCentralizerIn (section10Msigma H) K :=
        hσHMstar_le_CK hyσHMstar
      have hCne : subgroupCentralizerIn (section10Msigma H) K ≠ ⊥ := by
        intro hCbot
        have hyBot : (y : G) ∈ (⊥ : Subgroup G) := by
          simpa [hCbot] using hyCK
        exact hyneG (Subgroup.mem_bot.mp hyBot)
      have hKprimeH : K ∈ section10PrimeOrderSubgroupsIn q H := by
        exact ⟨hKH, by simp [q]⟩
      have hqH : q ∈ subgroupPrimeSet H := by
        show q.val ∣ Nat.card H
        simpa [q] using (Subgroup.card_dvd_of_le hKH : Nat.card K ∣ Nat.card H)
      have hqD : q ∈ subgroupPrimeSet D := by
        show q.val ∣ Nat.card D
        simpa [q] using (Subgroup.card_dvd_of_le hKD : Nat.card K ∣ Nat.card D)
      have hq_not_sigmaH : q ∉ section10SigmaPrimes H :=
        section12_not_sigma_of_mem_complement (G := G) (M := H) (E := D) hHF.1 hDcomp hqD
      have hqτ2 : q ∈ section12Tau2Primes H := by
        rcases section14_tau_split_of_not_sigma (G := G) hHF.1 hqH hq_not_sigmaH with
          hqτ2 | hqτ13
        · exact hqτ2
        · have hqκH : q ∈ section14KappaPrimes H := ⟨hqτ13, ⟨K, hKprimeH, hCne⟩⟩
          have : q ∈ (∅ : Set Nat.Primes) := by
            simp [hHF.2] at hqκH
          simp at this
      obtain ⟨E₁₂, E₁, E₂, E₃, hEdata⟩ :=
        section14_exists_EData_of_complement (G := G) (M := H) (E := D) hHF.1 hDcomp
      obtain ⟨A, hA⟩ :=
        section12_exists_rankTwo_in_E_of_tau2
          (G := G) (M := H) (E := D) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hHF.1 hEdata hqτ2
      have hA_H : A ∈ section12RankTwoElementaryAbelianIn q H :=
        section12_rankTwo_of_EData hEdata hA
      have hA_Mstar : Mstar ∈ section9MaximalSubgroupsContaining A := by
        refine ⟨hMstarP.1, ?_⟩
        exact (section12_rankTwo_le hA).trans hDleMstar
      have hMstar_ne_H : Mstar ≠ H := by
        intro hEq
        have hκnonempty : (section14KappaPrimes H).Nonempty := by
          simpa [hEq] using hMstarP.2
        simp [hHF.2] at hκnonempty
      have hσHMstar_bot : section10Msigma H ⊓ Mstar = ⊥ :=
        theorem_12_5_e (G := G) (M := H) (A := A) (p := q)
          hHF.1 hqτ2 hA_H Mstar hA_Mstar hMstar_ne_H
      exact hσHMstar_ne_bot hσHMstar_bot
    have hCbotUσM :
        subgroupCentralizerIn (section10Msigma M) U = ⊥ := by
      obtain ⟨p, P, hP⟩ :=
        section14_c_exists_primeOrderSubgroupIn_of_ne_bot (G := G) (A := U) (by
          intro hUbot
          have hrCard : r.val ∣ Nat.card U := by simpa [subgroupPrimeSet] using hr
          have hnot : ¬ r.val ∣ Nat.card U := by
            simpa [hUbot] using r.2.not_dvd_one
          exact hnot hrCard)
      haveI : Fact p.val.Prime := ⟨p.2⟩
      have hpU : p.val ∣ Nat.card U := by
        rw [← hP.2]
        exact Subgroup.card_dvd_of_le hP.1
      rcases hUhall with ⟨hUM, hHallU⟩
      have hpπc :
          p ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
        exact hHallU.p_in_pi_of_p_dvd_card p (by
          simpa [section12_card_subgroupOf_eq hUM] using hpU)
      have hp_not_sigma : p ∉ section10SigmaPrimes M := by
        exact fun hpσ => hpπc (Or.inr hpσ)
      have hp_not_kappa : p ∉ section14KappaPrimes M := by
        exact fun hpκ => hpπc (Or.inl hpκ)
      have hpM : p ∈ subgroupPrimeSet M := by
        simpa [subgroupPrimeSet] using hpU.trans (Subgroup.card_dvd_of_le hUM)
      let Usub : Subgroup M := U.subgroupOf M
      let T : Sylow p.val Usub := Classical.choice (Sylow.nonempty (p := p.val) (G := Usub))
      let Tmap : Subgroup M := (T : Subgroup Usub).map Usub.subtype
      have hTmap_p : IsPGroup p.val Tmap := by
        simpa [Tmap] using
          IsPGroup.map (p := p.val) (H := (T : Subgroup Usub)) T.isPGroup' Usub.subtype
      have hUsub_not_index : ¬ p.val ∣ Usub.index := by
        intro hpUidx
        exact (hHallU.p_in_pi_of_p_dvd_index p hpUidx) hpπc
      have hTmap_not_index : ¬ p.val ∣ Tmap.index := by
        have hidx :
            Tmap.index = (T : Subgroup Usub).index * Usub.index := by
          simpa [Tmap] using
            (Subgroup.index_map_subtype (H := Usub) (K := (T : Subgroup Usub)))
        rw [hidx]
        exact Nat.Prime.not_dvd_mul p.2 T.not_dvd_index hUsub_not_index
      let S : Sylow p.val M := hTmap_p.toSylow hTmap_not_index
      have hTmap_eq : (S : Subgroup M) = Tmap := by
        simp [S, Tmap]
      have hPamb_le_U : section10AmbientSylowSubgroup M S ≤ U := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hyTmap : y ∈ Tmap := by simpa [hTmap_eq] using hy
        rcases Subgroup.mem_map.mp hyTmap with ⟨z, hz, rfl⟩
        exact z.2
      have hΩ_le_Pamb :
          section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S) ≤
            section10AmbientSylowSubgroup M S := by
        simpa [section12OmegaOneSubgroup] using
          (Subgroup.map_subtype_le
            (omega₁ (G := section10AmbientSylowSubgroup M S) (p := p.val)))
      have hΩ_le_U :
          section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S) ≤ U :=
        hΩ_le_Pamb.trans hPamb_le_U
      have hMnotP1 : M ∉ section14MFamilyP1 G := by
        intro hMP1
        exact hM.2 hMP1.2
      have h14p :=
        lemma_14_1 (G := G) (M := M) hM.1.1 hMnotP1
          ⟨hpM, by
            intro hpbad
            rcases hpbad with hpσ | hpκ
            · exact hp_not_sigma hpσ
            · exact hp_not_kappa hpκ⟩ S
      have hle :
          subgroupCentralizerIn (section10Msigma M) U ≤
            subgroupCentralizerIn (section10Msigma M)
              (section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S)) := by
        intro x hx
        rcases (by simpa [subgroupCentralizerIn] using hx) with ⟨hxσ, hxCentU⟩
        have hxCentΩ :
            x ∈ Subgroup.centralizer
              ((section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M S)) : Set G) := by
          rw [Subgroup.mem_centralizer_iff] at hxCentU ⊢
          intro y hy
          exact hxCentU y (hΩ_le_U hy)
        exact by simpa [subgroupCentralizerIn] using ⟨hxσ, hxCentΩ⟩
      exact le_bot_iff.mp (by simpa [h14p.2.1] using hle)
    have hUinfσM : U ⊓ section10Msigma M = ⊥ := by
      rcases hUhall with ⟨hUM, hHallU⟩
      have hUσcompl : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ U := by
        intro p hpU
        have hpπc :
            p ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) :=
          hHallU.p_in_pi_of_p_dvd_card p (by
            simpa [section12_card_subgroupOf_eq hUM] using hpU)
        exact fun hpσ => hpπc (Or.inr hpσ)
      have hσMσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) (section10Msigma M) := by
        exact (theorem_10_2_b (G := G) hM.1.1).1.p_in_pi_of_p_dvd_card
      exact
        section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
          (G := G) (π := section10SigmaPrimes M)
          (H := U ⊓ section10Msigma M) (Y := U) (C := section10Msigma M)
          inf_le_left inf_le_right hUσcompl hσMσ
    rcases hUcomp with ⟨⟨hKM, hNM, hM_eq, hKdisjN⟩, hNnormIn⟩
    have hK_norm_U : K ≤ Subgroup.normalizer (U : Set G) := hUreg.1
    have hU_norm_σM : U ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
      hUhall.1.trans (section12_le_normalizer_msigma (M := M))
    have hNU_eq_U :
        subgroupNormalizerIn (U ⊔ section10Msigma M) (U : Set G) = U := by
      let N0 : Subgroup G := U ⊔ section10Msigma M
      apply le_antisymm
      · intro n hn
        rcases mem_subgroupNormalizerIn.mp hn with ⟨hnNorm, hnN0⟩
        let Usub : Subgroup N0 := U.subgroupOf N0
        let σsub : Subgroup N0 := (section10Msigma M).subgroupOf N0
        haveI : σsub.Normal := by
          simpa [N0, σsub] using
            (Subgroup.normal_subgroupOf_sup_of_le_normalizer
              (H := U) (N := section10Msigma M) hU_norm_σM)
        let nN0 : N0 := ⟨n, hnN0⟩
        have htop : Usub ⊔ σsub = ⊤ := by
          calc
            Usub ⊔ σsub = (U ⊔ section10Msigma M).subgroupOf N0 := by
              symm
              exact
                Subgroup.subgroupOf_sup
                  (A := U) (A' := section10Msigma M) (B := N0)
                  le_sup_left le_sup_right
            _ = ⊤ := by
              simp [N0]
        have hnTop : nN0 ∈ Usub ⊔ σsub := by
          simp [htop]
        rcases
            (Subgroup.mem_sup_of_normal_right
              (s := Usub) (t := σsub) (x := nN0)).1 hnTop with
          ⟨uN0, huUsub, sN0, hsσsub, hus⟩
        let u : G := uN0
        let s : G := sN0
        have huU : u ∈ U := by
          simpa [u, Usub, Subgroup.mem_subgroupOf] using huUsub
        have hsσ : s ∈ section10Msigma M := by
          simpa [s, σsub, Subgroup.mem_subgroupOf] using hsσsub
        have husG : u * s = n := by
          simpa [u, s, nN0] using congrArg (fun z : N0 => (z : G)) hus
        have huNorm : u ∈ Subgroup.normalizer (U : Set G) :=
          Subgroup.le_normalizer huU
        have huInvNorm : u⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
          Subgroup.inv_mem _ huNorm
        have hsNorm : s ∈ Subgroup.normalizer (U : Set G) := by
          have hmul :
              u⁻¹ * n ∈ Subgroup.normalizer (U : Set G) :=
            Subgroup.mul_mem _ huInvNorm hnNorm
          have hsEq : u⁻¹ * n = s := by
            rw [← husG]
            group
          simpa [hsEq] using hmul
        have hsCent : s ∈ Subgroup.centralizer (U : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hyU
          have hsyInvU : s * y * s⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp hsNorm y).1 hyU
          have hcommU : s * y * s⁻¹ * y⁻¹ ∈ U :=
            U.mul_mem hsyInvU (U.inv_mem hyU)
          have hysInvσM : y * s⁻¹ * y⁻¹ ∈ section10Msigma M :=
            (Subgroup.mem_normalizer_iff.mp (hU_norm_σM hyU) s⁻¹).1
              ((section10Msigma M).inv_mem hsσ)
          have hcommσM : s * y * s⁻¹ * y⁻¹ ∈ section10Msigma M := by
            have hmem : s * (y * s⁻¹ * y⁻¹) ∈ section10Msigma M :=
              (section10Msigma M).mul_mem hsσ hysInvσM
            simpa [mul_assoc] using hmem
          have hbot : s * y * s⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
            rw [← hUinfσM]
            exact ⟨hcommU, hcommσM⟩
          have hone : s * y * s⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.mp hbot
          have hcomm : s * y = y * s := by
            calc
              s * y = (s * y * s⁻¹ * y⁻¹) * y * s := by group
              _ = y * s := by rw [hone]; simp
          exact hcomm.symm
        have hsC : s ∈ subgroupCentralizerIn (section10Msigma M) U := by
          exact ⟨hsσ, hsCent⟩
        have hsBot : s ∈ (⊥ : Subgroup G) := by
          simpa [hCbotUσM] using hsC
        have hsOne : s = 1 := Subgroup.mem_bot.mp hsBot
        have hnEq : n = u := by
          calc
            n = u * s := husG.symm
            _ = u := by simp [hsOne]
        exact hnEq ▸ huU
      · intro u hu
        exact mem_subgroupNormalizerIn.mpr
          ⟨Subgroup.le_normalizer hu, Subgroup.mem_sup_left hu⟩
    have hNMU : subgroupNormalizerIn M (U : Set G) = K ⊔ U := by
      let N0 : Subgroup G := U ⊔ section10Msigma M
      have hMnormN0 : M ≤ Subgroup.normalizer (N0 : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNnormIn.1).1 hNnormIn.2
      apply le_antisymm
      · intro x hx
        rcases mem_subgroupNormalizerIn.mp hx with ⟨hxNorm, hxM⟩
        let Ksub : Subgroup M := K.subgroupOf M
        let Nsub : Subgroup M := N0.subgroupOf M
        haveI : Nsub.Normal := by
          simpa [N0, Nsub] using hNnormIn.2
        let xM : M := ⟨x, hxM⟩
        have htop : Ksub ⊔ Nsub = ⊤ := by
          calc
            Ksub ⊔ Nsub = (K ⊔ N0).subgroupOf M := by
              symm
              exact
                Subgroup.subgroupOf_sup
                  (A := K) (A' := N0) (B := M) hKM hNM
            _ = ⊤ := by
              apply Subgroup.subgroupOf_eq_top.mpr
              simpa [N0, sup_assoc] using hM_eq.le
        have hxTop : xM ∈ Ksub ⊔ Nsub := by
          simp [htop]
        rcases
            (Subgroup.mem_sup_of_normal_right
              (s := Ksub) (t := Nsub) (x := xM)).1 hxTop with
          ⟨kM, hkKsub, nM, hnNsub, hkn⟩
        let k : G := kM
        let n : G := nM
        have hkK : k ∈ K := by
          simpa [k, Ksub, Subgroup.mem_subgroupOf] using hkKsub
        have hnN0 : n ∈ N0 := by
          simpa [n, Nsub, N0, Subgroup.mem_subgroupOf] using hnNsub
        have hknG : k * n = x := by
          simpa [k, n, xM] using congrArg (fun z : M => (z : G)) hkn
        have hkInvNorm : k⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
          Subgroup.inv_mem _ (hK_norm_U hkK)
        have hnNorm : n ∈ Subgroup.normalizer (U : Set G) := by
          have hmul :
              k⁻¹ * x ∈ Subgroup.normalizer (U : Set G) :=
            Subgroup.mul_mem _ hkInvNorm hxNorm
          have hnEq : k⁻¹ * x = n := by
            rw [← hknG]
            group
          simpa [hnEq] using hmul
        have hnNU : n ∈ subgroupNormalizerIn N0 (U : Set G) :=
          mem_subgroupNormalizerIn.mpr ⟨hnNorm, hnN0⟩
        have hnU : n ∈ U := by
          simpa [N0, hNU_eq_U] using hnNU
        change x ∈ K ⊔ U
        rw [← hknG]
        exact Subgroup.mul_mem_sup hkK hnU
      · apply sup_le
        · intro k hk
          exact mem_subgroupNormalizerIn.mpr ⟨hK_norm_U hk, hKM hk⟩
        · intro u hu
          exact mem_subgroupNormalizerIn.mpr ⟨Subgroup.le_normalizer hu, hUhall.1 hu⟩
    have hHnotM : ¬ section14ConjugateSubgroups H M := by
      intro hHM
      have hHP : H ∈ section14MFamilyP2 G :=
        section14_mem_P2_of_conjugate (G := G) hHM hM
      have : H ∈ section14MFamilyP G := hHP.1
      simpa [hHF.2] using this.2
    have hnotconjHM : ∀ g : G, H.conjBy g ≠ M := by
      intro g hEq
      have hEq' : H = M.conjBy g⁻¹ := by
        calc
          H = (H.conjBy g).conjBy g⁻¹ := by
            simp [section11_conjBy_inv]
          _ = M.conjBy g⁻¹ := by rw [hEq]
      exact hHnotM ⟨g⁻¹, hEq'⟩
    have hσMσH_bot : section10Msigma M ⊓ section10Msigma H = ⊥ := by
      have hnilMσ : Group.IsNilpotent (section10Msigma M) :=
        (proposition_14_2_g (G := G) (M := M) (K := K) hM hK).2.2.1
      exact
        disjoint_iff.mp
          (lemma_10_12_b (G := G) (M := M) (H := H) hM.1.1 hHF.1 hnotconjHM hnilMσ).1
    have hqD : q ∈ subgroupPrimeSet D := by
      show q.val ∣ Nat.card D
      simpa [q] using (Subgroup.card_dvd_of_le hKD : Nat.card K ∣ Nat.card D)
    have hq_not_sigmaH : q ∉ section10SigmaPrimes H :=
      section12_not_sigma_of_mem_complement (G := G) (M := H) (E := D) hHF.1 hDcomp hqD
    have hMHσ_eq : M ⊓ section10Msigma H = U := by
      apply le_antisymm
      · intro x hx
        have hxM : x ∈ M := hx.1
        have hxσH : x ∈ section10Msigma H := hx.2
        let N0 : Subgroup G := U ⊔ section10Msigma M
        have hMnormN0 : M ≤ Subgroup.normalizer (N0 : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hNnormIn.1).1 hNnormIn.2
        let Ksub : Subgroup M := K.subgroupOf M
        let Nsub : Subgroup M := N0.subgroupOf M
        haveI : Nsub.Normal := by
          simpa [N0, Nsub] using hNnormIn.2
        have hKNnorm : K ≤ Subgroup.normalizer (N0 : Set G) := hKM.trans hMnormN0
        have hcompSub : Ksub.IsComplement' Nsub := by
          have hcomp0 :
              (N0.subgroupOf (K ⊔ N0)).IsComplement' (K.subgroupOf (K ⊔ N0)) := by
            simpa [inf_comm] using
              section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
                (G := G) (H := N0) (R := K) hKNnorm
                (by simpa [N0, disjoint_iff, inf_comm] using hKdisjN)
          change (K.subgroupOf M).IsComplement' (N0.subgroupOf M)
          rw [hM_eq]
          exact hcomp0.symm
        have hNsub_index : Nsub.index = q.val := by
          calc
            Nsub.index = Nat.card Ksub := hcompSub.index_eq_card
            _ = Nat.card K := section12_card_subgroupOf_eq hKM
            _ = q.val := by simp [q]
        have hcardQuot : Nat.card (M ⧸ Nsub) = q.val := by
          calc
            Nat.card (M ⧸ Nsub) = Nsub.index := by simp [Subgroup.index_eq_card]
            _ = q.val := hNsub_index
        let xM : M := ⟨x, hxM⟩
        let xQ : M ⧸ Nsub := QuotientGroup.mk' Nsub xM
        have hxQ_eq_one : xQ = 1 := by
          by_contra hxQ_ne
          have hxQ_order_ne_one : orderOf xQ ≠ 1 := by
            intro h1
            exact hxQ_ne ((orderOf_eq_one_iff).mp h1)
          have hxQ_order_dvd : orderOf xQ ∣ q.val := by
            rw [← hcardQuot]
            exact orderOf_dvd_natCard xQ
          have hxQ_order_eq : orderOf xQ = q.val := by
            rcases (Nat.dvd_prime hKcardPrime).1 hxQ_order_dvd with h1 | hq'
            · exact False.elim (hxQ_order_ne_one h1)
            · simpa [q] using hq'
          have hq_order_xM : q.val ∣ orderOf xM := by
            exact hxQ_order_eq.symm ▸ orderOf_map_dvd (ψ := QuotientGroup.mk' Nsub) xM
          have hq_order_x : q.val ∣ orderOf x := by
            simpa [xM, Subgroup.orderOf_coe] using hq_order_xM
          have hqSupp : q ∈ section14ElementPrimeSupport x := by
            simpa [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers] using hq_order_x
          have hHx : H ∈ section14MsigmaElement x := by
            exact ⟨hHF.1, by simpa using hxσH⟩
          have hxSigma :
              section14ElementPrimeSupport x ⊆ section10SigmaPrimes H :=
            section14_primeSupport_subset_sigma_of_msigmaMember hHx
          exact hq_not_sigmaH (hxSigma hqSupp)
        have hxNsub : xM ∈ Nsub := by
          simpa [xQ, QuotientGroup.ker_mk'] using
            (MonoidHom.mem_ker (f := QuotientGroup.mk' Nsub) (x := xM)).2 hxQ_eq_one
        have hxN0 : x ∈ N0 := by
          simpa [xM, Nsub, N0, Subgroup.mem_subgroupOf] using hxNsub
        let Usub : Subgroup N0 := U.subgroupOf N0
        let σsub : Subgroup N0 := (section10Msigma M).subgroupOf N0
        haveI : σsub.Normal := by
          simpa [N0, σsub] using
            (Subgroup.normal_subgroupOf_sup_of_le_normalizer
              (H := U) (N := section10Msigma M) hU_norm_σM)
        let xN0 : N0 := ⟨x, hxN0⟩
        have htop : Usub ⊔ σsub = ⊤ := by
          calc
            Usub ⊔ σsub = (U ⊔ section10Msigma M).subgroupOf N0 := by
              symm
              exact
                Subgroup.subgroupOf_sup
                  (A := U) (A' := section10Msigma M) (B := N0) le_sup_left le_sup_right
            _ = ⊤ := by
              apply Subgroup.subgroupOf_eq_top.mpr
              simp [N0]
        have hxTop : xN0 ∈ Usub ⊔ σsub := by
          simp [htop]
        rcases
            (Subgroup.mem_sup_of_normal_right
              (s := Usub) (t := σsub) (x := xN0)).1 hxTop with
          ⟨uN0, huUsub, sN0, hsσsub, hus⟩
        let u : G := uN0
        let s : G := sN0
        have huU : u ∈ U := by
          simpa [u, Usub, Subgroup.mem_subgroupOf] using huUsub
        have hsσM : s ∈ section10Msigma M := by
          simpa [s, σsub, Subgroup.mem_subgroupOf] using hsσsub
        have husG : u * s = x := by
          simpa [u, s, xN0] using congrArg (fun z : N0 => (z : G)) hus
        have hsσH : s ∈ section10Msigma H := by
          have huσH : u ∈ section10Msigma H := hUleσ huU
          have hmem : u⁻¹ * x ∈ section10Msigma H :=
            (section10Msigma H).mul_mem ((section10Msigma H).inv_mem huσH) hxσH
          have hsEq : u⁻¹ * x = s := by
            rw [← husG]
            group
          simpa [hsEq] using hmem
        have hsBot : s ∈ (⊥ : Subgroup G) := by
          rw [← hσMσH_bot]
          exact ⟨hsσM, hsσH⟩
        have hsOne : s = 1 := Subgroup.mem_bot.mp hsBot
        have hxEq : x = u := by
          calc
            x = u * s := husG.symm
            _ = u := by simp [hsOne]
        exact hxEq ▸ huU
      · intro x hxU
        exact ⟨hUhall.1 hxU, hUleσ hxU⟩
    refine ⟨hUleσ, ?_, ?_, ?_, ?_⟩
    · have hMH_le_NMU : M ⊓ H ≤ subgroupNormalizerIn M (U : Set G) := by
        intro x hx
        refine mem_subgroupNormalizerIn.mpr ?_
        refine ⟨?_, hx.1⟩
        rw [Subgroup.mem_normalizer_iff]
        intro u
        constructor
        · intro hu
          have hxuM : x * u * x⁻¹ ∈ M := by
            exact M.mul_mem (M.mul_mem hx.1 (hUhall.1 hu)) (M.inv_mem hx.1)
          have hxNormσH : x ∈ Subgroup.normalizer (section10Msigma H : Set G) :=
            section12_le_normalizer_msigma (M := H) hx.2
          have hxuσH : x * u * x⁻¹ ∈ section10Msigma H :=
            (Subgroup.mem_normalizer_iff.mp hxNormσH u).1 (hUleσ hu)
          have hxuMHσ : x * u * x⁻¹ ∈ M ⊓ section10Msigma H := ⟨hxuM, hxuσH⟩
          simpa [hMHσ_eq] using hxuMHσ
        · intro hxu
          have hxNormσH : x ∈ Subgroup.normalizer (section10Msigma H : Set G) :=
            section12_le_normalizer_msigma (M := H) hx.2
          have hxInvNormσH : x⁻¹ ∈ Subgroup.normalizer (section10Msigma H : Set G) :=
            Subgroup.inv_mem _ hxNormσH
          have hbackM : x⁻¹ * (x * u * x⁻¹) * x ∈ M := by
            exact M.mul_mem (M.mul_mem (M.inv_mem hx.1) (hUhall.1 hxu)) hx.1
          have hbackσH : x⁻¹ * (x * u * x⁻¹) * x ∈ section10Msigma H := by
            have hxuσH : x * u * x⁻¹ ∈ section10Msigma H := hUleσ hxu
            have hbackσH' :
                x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ ∈ section10Msigma H :=
              (Subgroup.mem_normalizer_iff.mp hxInvNormσH (x * u * x⁻¹)).1 hxuσH
            simpa using hbackσH'
          have huU : x⁻¹ * (x * u * x⁻¹) * x ∈ U := by
            have hbackMHσ : x⁻¹ * (x * u * x⁻¹) * x ∈ M ⊓ section10Msigma H :=
              ⟨hbackM, hbackσH⟩
            simpa [hMHσ_eq] using hbackMHσ
          simpa [mul_assoc] using huU
      have hKU_le_MH : K ⊔ U ≤ M ⊓ H := by
        apply sup_le
        · intro k hk
          exact ⟨hKM hk, hKH hk⟩
        · intro u hu
          exact ⟨hUhall.1 hu, hUH hu⟩
      have hMH_eq_norm : M ⊓ H = subgroupNormalizerIn M (U : Set G) := by
        apply le_antisymm hMH_le_NMU
        rw [hNMU]
        simpa [sup_comm] using hKU_le_MH
      calc
        ((M ⊓ H : Subgroup G) : Set G) = ↑(subgroupNormalizerIn M (U : Set G)) := by
          simp [hMH_eq_norm]
        _ = ↑(K ⊔ U) := by
          simp [hNMU]
        _ = ↑(U ⊔ K) := by
          simp [sup_comm]
        _ = (U : Set G) * (K : Set G) := by
          simpa using
            (Subgroup.coe_mul_of_right_le_normalizer_left U K hK_norm_U)
    · intro hNHM
      have hσH_nil : Group.IsNilpotent (section10Msigma H) := by
        let S : Sylow q.val H := Classical.choice (Sylow.nonempty (p := q.val) (G := H))
        have hqH : q ∈ subgroupPrimeSet H := by
          show q.val ∣ Nat.card H
          simpa [q] using (Subgroup.card_dvd_of_le hKH : Nat.card K ∣ Nat.card H)
        have hqD : q ∈ subgroupPrimeSet D := by
          show q.val ∣ Nat.card D
          simpa [q] using (Subgroup.card_dvd_of_le hKD : Nat.card K ∣ Nat.card D)
        have hq_not_sigmaH : q ∉ section10SigmaPrimes H :=
          section12_not_sigma_of_mem_complement (G := G) (M := H) (E := D) hHF.1 hDcomp hqD
        have hHnotP1 : H ∉ section14MFamilyP1 G := by
          intro hHP1
          have hHP : H ∈ section14MFamilyP G := hHP1.1
          simpa [hHF.2] using hHP.2
        exact
          (lemma_14_1 (G := G) (M := H) hHF.1 hHnotP1
            ⟨hqH, by
              intro hqbad
              rcases hqbad with hqσ | hqκ
              · exact hq_not_sigmaH hqσ
              · simp [hHF.2] at hqκ⟩ S).2.2
      by_cases hUtop : U = section10Msigma H
      · have hHnormU : H ≤ Subgroup.normalizer (U : Set G) := by
          subst hUtop
          simpa using section12_le_normalizer_msigma (M := H)
        have hNHH : H ≤ subgroupNormalizerIn H (U : Set G) := by
          intro x hxH
          exact mem_subgroupNormalizerIn.mpr ⟨hHnormU hxH, hxH⟩
        have hHleM : H ≤ M := hNHH.trans hNHM
        have hHM : H = M := by
          exact ((hH.1.le_iff_eq hM.1.1.1).mp hHleM).symm
        have hHP : H ∈ section14MFamilyP G := by
          simpa [hHM] using hM.1
        simpa [hHF.2] using hHP.2
      · let Uσ : Subgroup (section10Msigma H) := U.subgroupOf (section10Msigma H)
        have hUσ_ne_top : Uσ ≠ ⊤ := by
          intro htop
          apply hUtop
          ext x
          constructor
          · intro hxU
            exact hUleσ hxU
          · intro hxσ
            have hxTop : (⟨x, hxσ⟩ : section10Msigma H) ∈ (⊤ : Subgroup (section10Msigma H)) := by
              simp
            have hxUσ : (⟨x, hxσ⟩ : section10Msigma H) ∈ Uσ := by
              simp [htop]
            simpa [Uσ, Subgroup.mem_subgroupOf] using hxUσ
        have hUσ_lt_top : Uσ < ⊤ := lt_top_iff_ne_top.mpr hUσ_ne_top
        have hnc : NormalizerCondition (section10Msigma H) := by
          letI : Group.IsNilpotent (section10Msigma H) := hσH_nil
          exact Group.normalizerCondition_of_isNilpotent (G := section10Msigma H)
        let Nσ : Subgroup (section10Msigma H) :=
          Subgroup.normalizer ((U.subgroupOf (section10Msigma H) : Subgroup (section10Msigma H)) : Set (section10Msigma H))
        have hUσ_lt_Nσ : Uσ < Nσ := hnc Uσ hUσ_lt_top
        obtain ⟨z, hzN, hzU⟩ := SetLike.exists_of_lt hUσ_lt_Nσ
        have hzσH : (z : G) ∈ section10Msigma H := z.2
        have hzNormU : (z : G) ∈ Subgroup.normalizer (U : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro u
          constructor
          · intro hu
            have huUσ : (⟨u, hUleσ hu⟩ : section10Msigma H) ∈ Uσ := by
              simpa [Uσ, Subgroup.mem_subgroupOf] using hu
            have hconj :
                z * ⟨u, hUleσ hu⟩ * z⁻¹ ∈ Uσ :=
              (Subgroup.mem_normalizer_iff.mp hzN ⟨u, hUleσ hu⟩).1 huUσ
            change (z : G) * u * (z : G)⁻¹ ∈ U
            simpa [Uσ, Subgroup.mem_subgroupOf] using hconj
          · intro hu
            have hzInv : z⁻¹ ∈ Subgroup.normalizer (Uσ : Set (section10Msigma H)) :=
              Subgroup.inv_mem _ hzN
            have huUσ :
                (⟨(z : G) * u * (z : G)⁻¹, hUleσ hu⟩ : section10Msigma H) ∈ Uσ := by
              simpa [Uσ, Subgroup.mem_subgroupOf] using hu
            have hback' :
                z⁻¹ * ⟨(z : G) * u * (z : G)⁻¹, hUleσ hu⟩ * z⁻¹⁻¹ ∈ Uσ :=
              (Subgroup.mem_normalizer_iff.mp hzInv
                ⟨(z : G) * u * (z : G)⁻¹, hUleσ hu⟩).1 huUσ
            have hback :
                z⁻¹ * ⟨(z : G) * u * (z : G)⁻¹, hUleσ hu⟩ * z ∈ Uσ := by
              simpa using hback'
            change u ∈ U
            simpa [Uσ, Subgroup.mem_subgroupOf, mul_assoc] using hback
        have hzHU : (z : G) ∈ subgroupNormalizerIn H (U : Set G) := by
          exact mem_subgroupNormalizerIn.mpr ⟨hzNormU, hDcomp.1 hzσH⟩
        have hzM : (z : G) ∈ M := hNHM hzHU
        have hzU' : (z : G) ∉ U := by
          intro hzU'
          exact hzU (by simpa [Uσ, Subgroup.mem_subgroupOf] using hzU')
        have hzMHσ : (z : G) ∈ M ⊓ section10Msigma H := ⟨hzM, hzσH⟩
        have : (z : G) ∈ U := by simpa [hMHσ_eq] using hzMHσ
        exact hzU' this
    · simpa [hD_eq] using hKF
    · simpa [section12ComplementToMsigma, hD_eq] using hDcomp
  exact ⟨hHF, hTail⟩

end Section14
