module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.theorem_15_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 15 8 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_complementToMsigma_of_isComplement_subgroup
    {M : Subgroup G} {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E) :
    section12ComplementToMsigma M (E.map M.subtype) := by
  classical
  have hmap_top : (⊤ : Subgroup M).map M.subtype = M := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hsup :
      section10Msigma M ⊔ E.map M.subtype = M := by
    calc
      section10Msigma M ⊔ E.map M.subtype =
          (section10MsigmaSubgroup M).map M.subtype ⊔ E.map M.subtype := by
            simp [section10Msigma]
      _ = ((section10MsigmaSubgroup M) ⊔ E).map M.subtype := by
            rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup M).map M.subtype := by rw [hcomp.sup_eq_top]
      _ = M := hmap_top
  refine ⟨section15_msigma_le (M := M), ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le E
  · exact hsup.symm
  · rw [Subgroup.disjoint_def]
    intro x hxσ hxE
    rcases Subgroup.mem_map.mp hxE with ⟨y, hyE, hyx⟩
    have hx_eq : x = y := by simpa using hyx.symm
    have hyσ : y ∈ section10MsigmaSubgroup M := by
      have hyσG : (y : G) ∈ section10Msigma M := by simpa [hx_eq] using hxσ
      simpa [section10Msigma] using hyσG
    have hybot : y ∈ (⊥ : Subgroup M) :=
      Subgroup.disjoint_def.mp hcomp.disjoint hyσ hyE
    have hyone : y = 1 := by simpa using hybot
    simp [hx_eq, hyone]

private theorem CFSG.section15_hall_kappa_complementToMsigma_of_mem_P1
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP1 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section12ComplementToMsigma M K := by
  classical
  rcases hK with ⟨hKM, hHallK⟩
  have hKHall :
      section12HallSubgroupIn (section10SigmaPrimes M)ᶜ K M := by
    refine ⟨hKM, ?_⟩
    refine isHallSubgroup_of (G := M) (section10SigmaPrimes M)ᶜ (K.subgroupOf M) ?_ ?_
    · intro p hpKsub
      have hpκ : p ∈ section14KappaPrimes M :=
        hHallK.p_in_pi_of_p_dvd_card p hpKsub
      have hpκ' : p ∈ subgroupPrimeSet M \ section10SigmaPrimes M := by
        simpa [hM.2] using hpκ
      exact hpκ'.2
    · intro p hpσc hpidx
      have hpM : p ∈ subgroupPrimeSet M := by
        rw [subgroupPrimeSet]
        exact hpidx.trans (Subgroup.index_dvd_card (H := K.subgroupOf M))
      have hpκ : p ∈ section14KappaPrimes M := by
        rw [hM.2]
        exact ⟨hpM, hpσc⟩
      exact (hHallK.p_in_pi_of_p_dvd_index p hpidx) hpκ
  have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b (G := G) hM.1.1).2
  have hcomp :
      (section10MsigmaSubgroup M).IsComplement' (K.subgroupOf M) :=
    section11_isComplement_of_isHall_compl hσHall hKHall.2
  have hmap : (K.subgroupOf M).map M.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKM
  simpa [hmap] using
    section15_complementToMsigma_of_isComplement_subgroup
      (G := G) (M := M) (E := K.subgroupOf M) hcomp

/-- Theorem 15.8: in the situation of Corollary 14.12, if `τ₂(H)` is
nonempty and `q ∈ π(K)`, then `q = |K|`, `q` is the unique prime in
`τ₂(H)`, and `τ₂(M)` is empty. -/
private theorem CFSG.section15_theorem15_8_q_card_K
    {M H K Mstar U : Subgroup G} {q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hqK : q ∈ subgroupPrimeSet K) :
    q.val = Nat.card K := by
  rcases hSituation with ⟨hMP2, hK, _h14, _hU, _hr⟩
  have hKprime : Nat.Prime (Nat.card K) :=
    (proposition_14_2_g (G := G) (M := M) (K := K) hMP2 hK).2.1
  exact (Nat.prime_dvd_prime_iff_eq q.2 hKprime).mp
    (by simpa [subgroupPrimeSet] using hqK)

/-- The Corollary 14.12 package extracted from the bundled hypotheses used
throughout Theorem 15.8. -/
public theorem CFSG.section15_theorem15_8_corollary14_12_conclusions
    {M H K Mstar U : Subgroup G}
    (hSituation : section15Corollary14_12Situation M H K Mstar U) :
    H ∈ section14MFamilyF G ∧
      U ≤ section10Msigma H ∧
      ((M ⊓ H : Subgroup G) : Set G) = (U : Set G) * (K : Set G) ∧
      ¬ subgroupNormalizerIn H (U : Set G) ≤ M ∧
      K ≤ section8FittingSubgroup (H ⊓ Mstar) ∧
      section12ComplementIn H (section10Msigma H) (H ⊓ Mstar) := by
  rcases hSituation with ⟨hMP2, hK, h14, hU, r, R, hrU, hHmax⟩
  exact corollary_14_12
    (G := G) (M := M) (K := K) (Mstar := Mstar) (U := U)
    hMP2 hK h14 hU hrU R hHmax

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_le_fitting_of_le_msigma_and_centralizes_quotient_kstar
    {M K Q₀ X : Subgroup G}
    (hquot :
      section15QuotientCentralizerEquals
        (section8FittingSubgroup M) (section10Msigma M) K Q₀)
    (hXσ : X ≤ section10Msigma M)
    (hXcentK : X ≤ Subgroup.centralizer (K : Set G)) :
    X ≤ section8FittingSubgroup M := by
  classical
  let σ : Subgroup G := section10Msigma M
  rcases hquot with ⟨hQ₀σ, hKσ, hQ₀norm, hF_eq_Cbar⟩
  let qσ : σ →* σ ⧸ Q₀.subgroupOf σ := QuotientGroup.mk' (Q₀.subgroupOf σ)
  let Kbar : Subgroup (σ ⧸ Q₀.subgroupOf σ) := (K.subgroupOf σ).map qσ
  rw [hF_eq_Cbar]
  intro x hxX
  let xσ : σ := ⟨x, hXσ hxX⟩
  refine Subgroup.mem_map.mpr ⟨xσ, ?_, rfl⟩
  change qσ xσ ∈ Subgroup.centralizer (Kbar : Set (σ ⧸ Q₀.subgroupOf σ))
  rw [Subgroup.mem_centralizer_iff]
  intro y hyKbar
  rcases Subgroup.mem_map.mp hyKbar with ⟨kσ, hkKσ, rfl⟩
  have hkK : (kσ : G) ∈ K := by
    simpa [Subgroup.mem_subgroupOf] using hkKσ
  have hcommG : (kσ : G) * x = x * (kσ : G) :=
    Subgroup.mem_centralizer_iff.mp (hXcentK hxX) (kσ : G) hkK
  have hcommσ : kσ * xσ = xσ * kσ := by
    apply Subtype.ext
    simpa [xσ] using hcommG
  simpa [map_mul] using congrArg qσ hcommσ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_exists_msigma_sylow_eq_of_sylowSubgroupIn
    {M Q : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M)
    (hQσ : Q ≤ section10Msigma M) :
    ∃ S : Sylow q.val (section10Msigma M),
      section10AmbientSylowSubgroup (section10Msigma M) S = Q := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let σ : Subgroup G := section10Msigma M
  rcases hQ with ⟨P, hPamb⟩
  let Qσ : Subgroup σ := Q.subgroupOf σ
  have hQσ_p : IsPGroup q.val Qσ := by
    have hQp : IsPGroup q.val Q := by
      rw [← hPamb]
      change IsPGroup q.val ((P : Subgroup M).map M.subtype)
      exact IsPGroup.map (p := q.val) (H := (P : Subgroup M))
        P.isPGroup' M.subtype
    exact hQp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Q) (K := σ) hQσ).symm
  obtain ⟨S, hQσ_le_S⟩ := IsPGroup.exists_le_sylow (G := σ) (p := q.val) hQσ_p
  have hQ_le_amb :
      Q ≤ section10AmbientSylowSubgroup σ S := by
    intro x hxQ
    let xσ : σ := ⟨x, hQσ hxQ⟩
    have hxQσ : xσ ∈ Qσ := by
      simpa [Qσ, xσ, Subgroup.mem_subgroupOf] using hxQ
    exact Subgroup.mem_map.mpr ⟨xσ, hQσ_le_S hxQσ, rfl⟩
  have hAmb_le_M :
      section10AmbientSylowSubgroup σ S ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact section15_msigma_le y.property
  have hAmb_p : IsPGroup q.val (section10AmbientSylowSubgroup σ S) := by
    change IsPGroup q.val ((S : Subgroup σ).map σ.subtype)
    exact IsPGroup.map (p := q.val) (H := (S : Subgroup σ))
      S.isPGroup' σ.subtype
  let R : Subgroup M := (section10AmbientSylowSubgroup σ S).subgroupOf M
  have hR_p : IsPGroup q.val R :=
    hAmb_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (H := section10AmbientSylowSubgroup σ S) (K := M) hAmb_le_M).symm
  have hQsub_eq_P : Q.subgroupOf M = (P : Subgroup M) := by
    rw [← hPamb]
    simpa [section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := M) (P : Subgroup M))
  have hP_le_R : (P : Subgroup M) ≤ R := by
    intro x hxP
    have hxQ : ((x : M) : G) ∈ Q := by
      have hxQsub : x ∈ Q.subgroupOf M := by
        simpa [hQsub_eq_P] using hxP
      simpa [Subgroup.mem_subgroupOf] using hxQsub
    have hxAmb : ((x : M) : G) ∈ section10AmbientSylowSubgroup σ S :=
      hQ_le_amb hxQ
    simpa [R, Subgroup.mem_subgroupOf] using hxAmb
  have hR_eq_P : R = (P : Subgroup M) := P.is_maximal' hR_p hP_le_R
  refine ⟨S, le_antisymm ?_ hQ_le_amb⟩
  intro x hxAmb
  have hxM : x ∈ M := hAmb_le_M hxAmb
  let xM : M := ⟨x, hxM⟩
  have hxR : xM ∈ R := by
    simpa [R, xM, Subgroup.mem_subgroupOf] using hxAmb
  have hxP : xM ∈ (P : Subgroup M) := by
    simpa [hR_eq_P] using hxR
  have hxQsub : xM ∈ Q.subgroupOf M := by
    simpa [hQsub_eq_P] using hxP
  simpa [xM, Subgroup.mem_subgroupOf] using hxQsub

private theorem CFSG.section15_unique_of_sylowSubgroupIn_msigma_kstar
    {M K Q : Subgroup G} {q : Nat.Primes}
    (hMP : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hqKstar : q ∈ subgroupPrimeSet (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQσ : Q ≤ section10Msigma M) :
    Q ∈ section9UniqueSubgroups G := by
  classical
  rcases section15_exists_msigma_sylow_eq_of_sylowSubgroupIn
      (G := G) (M := M) (Q := Q) (q := q) hQ hQσ with
    ⟨S, hS⟩
  have hUnique :
      section9MaximalSubgroupsContaining Q = {M} := by
    simpa [hS] using
      (proposition_14_2_e (G := G) (M := M) (K := K) hMP hK
        q hqKstar S).1
  refine ⟨?_, M, hUnique⟩
  intro hQtop
  have htop_le_M : (⊤ : Subgroup G) ≤ M := by
    simpa [hQtop] using hQσ.trans (section15_msigma_le (M := M))
  exact hMP.1.1 (top_le_iff.mp htop_le_M)

private theorem CFSG.section15_theorem15_8_no_rankTwo_centralizes_K_core
    {M H K Mstar MFstar A : Subgroup G} {p q : Nat.Primes}
    (_hHF : H ∈ section14MFamilyF G)
    (hMstarP1 : Mstar ∈ section14MFamilyP1 G)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hKstarHall :
      section12HallSubgroupIn (section14KappaPrimes Mstar) (section14KStar M K) Mstar)
    (hKeq : K = section14KStar Mstar (section14KStar M K))
    (hAcentK : A ≤ Subgroup.centralizer (K : Set G))
    (hqcardK : q.val = Nat.card K)
    (_hqSigmaMstar : q ∈ section10SigmaPrimes Mstar)
    (hpSigmaMstar : p ∈ section10SigmaPrimes Mstar)
    (_hp_not_betaMstar : p ∉ section10BetaPrimes Mstar)
    (_hA_H : A ∈ section12RankTwoElementaryAbelianIn p H)
    (hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar)
    (hAnotUnique : A ∉ section9UniqueSubgroups G)
    (_hσHinfMstar_bot : section10Msigma H ⊓ Mstar = ⊥)
    (hAleσMstar : A ≤ section10Msigma Mstar)
    (hpq : p ≠ q) :
    False := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hσD : section10Msigma Mstar = ambientDerivedSubgroup Mstar :=
    section15_msigma_eq_ambientDerived_of_familyP1
      (G := G) (M := Mstar) (K := section14KStar M K)
      hMstarP1.1.1 hMstarP1 hKstarHall
  have hKleσMstar : K ≤ section10Msigma Mstar := by
    rw [hKeq]
    exact inf_le_left
  have hAp : IsPGroup p.val A := by
    rcases section15_rankTwo_elementary hA_Mstar with ⟨_hcard, hElem⟩
    haveI : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  have hAnoncyc : ¬ IsCyclic A :=
    section15_rankTwo_not_isCyclic (G := G) hA_Mstar
  have hNormA_le_Mstar : Subgroup.normalizer (A : Set G) ≤ Mstar :=
    corollary_12_10_d
      (G := G) (M := Mstar) (P := A) (p := p)
      hMstarP1.1.1 hpSigmaMstar hAp (section15_rankTwo_le hA_Mstar) hAnoncyc
  have hMstarNormA :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    ⟨hMstarP1.1.1, hNormA_le_Mstar⟩
  have hqKstar_card :
      q.val = Nat.card (section14KStar Mstar (section14KStar M K)) := by
    simpa [← hKeq] using hqcardK
  have hqKstarPrimeSet :
      q ∈ subgroupPrimeSet (section14KStar Mstar (section14KStar M K)) := by
    have hdiv :
        q.val ∣ Nat.card (section14KStar Mstar (section14KStar M K)) := by
      rw [← hqKstar_card]
    simpa [subgroupPrimeSet] using hdiv
  have hArank : 2 ≤ groupRank A :=
    section15_groupRank_at_least_two_of_rankTwo_elementary_le
      (G := G) (K := A) (A := A) (p := p) le_rfl
      (section15_rankTwo_elementary hA_Mstar)
  have hAπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) A :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) hAp
  have hdisj : Disjoint ({p} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro r hrp hrq
    have hrp_eq : r = p := by simpa using hrp
    have hrq_eq : r = q := by simpa using hrq
    exact hpq (hrp_eq.symm.trans hrq_eq)
  have hAunique_of :
      ∀ {Q : Subgroup G}, Q ∈ section9UniqueSubgroups G →
        Q ≤ section8FittingSubgroup Mstar →
          IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q →
            A ≤ section8FittingSubgroup Mstar →
            A ∈ section9UniqueSubgroups G := by
    intro Q hQunique hQleF hQπ hAleF
    have hAcentQ : A ≤ Subgroup.centralizer (Q : Set G) :=
      section10_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
        (G := G) (π := ({p} : Set Nat.Primes)) (ρ := ({q} : Set Nat.Primes))
        (L := section8FittingSubgroup Mstar) (A := A) (B := Q)
        hdisj (section8FittingSubgroup_isNilpotent Mstar)
        hAleF hQleF hAπ hQπ
    exact corollary_9_2 (G := G) (L := Q) (K := A) hQunique hAcentQ hArank
  by_cases hMF_eq : MFstar = section10Msigma Mstar
  ·
    let S : Sylow q.val (section10Msigma Mstar) :=
      Classical.choice (Sylow.nonempty (p := q.val) (G := section10Msigma Mstar))
    let Q : Subgroup G := section10AmbientSylowSubgroup (section10Msigma Mstar) S
    have hQσ : Q ≤ section10Msigma Mstar := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hσleF : section10Msigma Mstar ≤ section8FittingSubgroup Mstar := by
      rw [← hMF_eq]
      exact section15_MF_le_fitting (M := Mstar) (MF := MFstar) hMFstar
    have hQleF : Q ≤ section8FittingSubgroup Mstar :=
      hQσ.trans hσleF
    have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q := by
      have hQp : IsPGroup q.val Q := by
        change IsPGroup q.val
          ((S : Subgroup (section10Msigma Mstar)).map (section10Msigma Mstar).subtype)
        exact IsPGroup.map (p := q.val)
          (H := (S : Subgroup (section10Msigma Mstar))) S.isPGroup'
          (section10Msigma Mstar).subtype
      exact section8_isPiSubgroup_singleton_of_isPGroup (G := G) hQp
    have hQunique : Q ∈ section9UniqueSubgroups G := by
      have hUnique :
          section9MaximalSubgroupsContaining Q = {Mstar} := by
        simpa [Q] using
          (proposition_14_2_e
            (G := G) (M := Mstar) (K := section14KStar M K)
            hMstarP1.1 hKstarHall q hqKstarPrimeSet S).1
      refine ⟨?_, Mstar, hUnique⟩
      intro hQtop
      have htop_le_Mstar : (⊤ : Subgroup G) ≤ Mstar := by
        simpa [Q, hQtop] using hQσ.trans (section15_msigma_le (M := Mstar))
      exact hMstarP1.1.1.1 (top_le_iff.mp htop_le_Mstar)
    have hAleF : A ≤ section8FittingSubgroup Mstar :=
      hAleσMstar.trans hσleF
    exact hAnotUnique (hAunique_of hQunique hQleF hQπ hAleF)
  ·
    rcases theorem_15_2_c
        (G := G) (M := Mstar) (MF := MFstar) (K := section14KStar M K)
        hMstarP1.1.1 hMFstar hKstarHall hMF_eq with
      ⟨r, hr, Q, hQ, hQnormal, hQMF⟩
    have hrq : r = q := by
      apply Subtype.ext
      exact hr.trans hqKstar_card.symm
    have hQq : section12SylowSubgroupIn q Q Mstar := by
      simpa [hrq] using hQ
    rcases theorem_15_2_d
        (G := G) (M := Mstar) (MF := MFstar) (K := section14KStar M K)
        (Q := Q) (q := r)
        hMstarP1.1.1 hMFstar hKstarHall hMF_eq hr hQ hQnormal hQMF with
      ⟨D, hD⟩
    have hg := theorem_15_2_g
      (G := G) (M := Mstar) (MF := MFstar) (K := section14KStar M K)
      (Q := Q) (D := D) (q := r)
      hMstarP1.1.1 hMFstar hKstarHall hMF_eq hr hQ hQnormal hQMF hD
    have hquot_sigma :
        section15QuotientCentralizerEquals
          (section8FittingSubgroup Mstar) (section10Msigma Mstar)
            (section14KStar Mstar (section14KStar M K))
            (subgroupCentralizerIn Q D) :=
      hg.2.2.2.2.1
    have hAcentKstar :
        A ≤ Subgroup.centralizer
          (section14KStar Mstar (section14KStar M K) : Set G) := by
      simpa [← hKeq] using hAcentK
    have hAleF : A ≤ section8FittingSubgroup Mstar :=
      section15_le_fitting_of_le_msigma_and_centralizes_quotient_kstar
        (G := G) (M := Mstar)
        (K := section14KStar Mstar (section14KStar M K))
        (Q₀ := subgroupCentralizerIn Q D) (X := A)
        hquot_sigma hAleσMstar hAcentKstar
    have hQleF : Q ≤ section8FittingSubgroup Mstar :=
      hQMF.trans (section15_MF_le_fitting (M := Mstar) (MF := MFstar) hMFstar)
    have hQσ : Q ≤ section10Msigma Mstar :=
      hQMF.trans (section15_MF_le_msigma hMstarP1.1.1 hMFstar)
    have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q := by
      simpa [hrq] using
        (section15_sylowSubgroupIn_isPiSubgroup_singleton
          (G := G) (M := Mstar) (Q := Q) (q := r) hQ)
    have hQunique : Q ∈ section9UniqueSubgroups G :=
      section15_unique_of_sylowSubgroupIn_msigma_kstar
        (G := G) (M := Mstar) (K := section14KStar M K)
        (Q := Q) (q := q)
        hMstarP1.1 hKstarHall hqKstarPrimeSet hQq hQσ
    exact hAnotUnique (hAunique_of hQunique hQleF hQπ hAleF)

/-- Source core for Theorem 15.8: with `D = H ∩ M*`, every rank-two
elementary subgroup of the complement is a `q`-group.  This is the long
paragraph using Corollary 12.6, Theorem 15.2, the Uniqueness Theorem, and
Lemma 12.17. -/
private theorem CFSG.section15_theorem15_8_no_rankTwo_centralizes_K_of_ne_q
    {M H K Mstar U MFstar A : Subgroup G} {p q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hqK : q ∈ subgroupPrimeSet K)
    (hpτ2H : p ∈ section12Tau2Primes H)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (H ⊓ Mstar))
    (hpq : p ≠ q)
    (hAcentK : A ≤ Subgroup.centralizer (K : Set G)) :
    False := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hqcard : q.val = Nat.card K :=
    section15_theorem15_8_q_card_K
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituation hqK
  rcases section15_theorem15_8_corollary14_12_conclusions
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituation with
    ⟨hHF, _hUleσH, _hMHprod, _hNormU_notM, _hKleF, hDcomp⟩
  rcases hSituation with
    ⟨_hMP2, _hHallK, h14, _hUdata, _r, _R, _hrU, _hHmax⟩
  rcases h14 with
    ⟨hMstarP, _hMstar_not_conj, hPrimeOrderUnique, _hKstarHall,
      _hKsigmaHall, hKeq, _hKappaEq, _hZdp, _hZcyc, _hInterData,
      _hWidehatTI, _hWidehatNorm, _hWidehatDisj, _hWidehatCard,
      _hWidehatHalf, _hP2prime, _hPconj, _hDerCompl⟩
  have hKleσMstar : K ≤ section10Msigma Mstar := by
    rw [hKeq]
    exact inf_le_left
  have hqSigmaMstar : q ∈ section10SigmaPrimes Mstar := by
    have hqMsigma : q.val ∣ Nat.card (section10Msigma Mstar) := by
      simpa [hqcard] using
        (Subgroup.card_dvd_of_le hKleσMstar :
          Nat.card K ∣ Nat.card (section10Msigma Mstar))
    exact ((theorem_10_2_b (G := G) hMstarP.1).1).p_in_pi_of_p_dvd_card q hqMsigma
  have hKprimeSub : K ∈ section12PrimeOrderSubgroups K :=
    ⟨le_rfl, ⟨q, hqcard.symm⟩⟩
  have hCentK_le_Mstar : Subgroup.centralizer (K : Set G) ≤ Mstar := by
    have hUnique :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) =
          {Mstar} :=
      hPrimeOrderUnique K hKprimeSub
    have hMstarMem :
        Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) := by
      rw [hUnique]
      simp
    exact hMstarMem.2
  have hAleMstar_via_cent : A ≤ Mstar := hAcentK.trans hCentK_le_Mstar
  have hA_H : A ∈ section12RankTwoElementaryAbelianIn p H :=
    section12_rankTwo_mono hA inf_le_left
  let D : Subgroup G := H ⊓ Mstar
  have hDcompTo : section12ComplementToMsigma H D := by
    simpa [D, section12ComplementToMsigma] using hDcomp
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := H) (E := D) hHF.1 hDcompTo with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  have hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G :=
    (lemma_12_1_g
      (G := G) (M := H) (E := D) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hHF.1 hEdata hpτ2H hA_H).1
  have hp_not_betaG : p ∉ section12BetaPrimesOfGroup G :=
    (lemma_12_1_g
      (G := G) (M := H) (E := D) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hHF.1 hEdata hpτ2H hA_H).2
  have hMstarMemA : Mstar ∈ section9MaximalSubgroupsContaining A :=
    ⟨hMstarP.1, hAleMstar_via_cent⟩
  have hMstar_ne_H : Mstar ≠ H := by
    intro hEq
    have hκnonempty : (section14KappaPrimes H).Nonempty := by
      simpa [hEq] using hMstarP.2
    simp [hHF.2] at hκnonempty
  have hAnotUnique : A ∉ section9UniqueSubgroups G :=
    section15_not_unique_of_le_two_distinct_maximal
      (G := G) (L := A) (M := H) (N := Mstar)
      hHF.1 hMstarP.1 (section12_rankTwo_le hA_H) hAleMstar_via_cent hMstar_ne_H
  have hσHinfMstar_bot : section10Msigma H ⊓ Mstar = ⊥ :=
    theorem_12_5_e (G := G) (M := H) (A := A) (p := p)
      hHF.1 hpτ2H hA_H Mstar hMstarMemA hMstar_ne_H
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
    ⟨hAleMstar_via_cent, section12_rankTwo_elementary hA⟩
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hcardK : Nat.card K = 1 := by
      simp [hKbot]
    exact q.2.ne_one (hqcard.trans hcardK)
  have hKcentA : K ≤ Subgroup.centralizer (A : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hAcentK ha) k hk).symm
  have hAleσMstar : A ≤ section10Msigma Mstar := by
    by_contra hnot_le
    have hp_not_sigma : p ∉ section10SigmaPrimes Mstar := by
      intro hpσ
      exact hnot_le
        (section12_rankTwo_le_msigma_of_sigma
          (G := G) (M := Mstar) (A := A) (p := p) hMstarP.1 hpσ hA_Mstar)
    have hpτ2Mstar : p ∈ section12Tau2Primes Mstar := by
      have hrank_ge : 2 ≤ primeRank p.val Mstar :=
        section15_primeRank_at_least_two_of_rankTwo (G := G) hA_Mstar
      have hrank_le : primeRank p.val Mstar ≤ 2 := by
        by_contra hnot
        have hgt : 2 < primeRank p.val Mstar := by omega
        have hpMstar : p ∈ subgroupPrimeSet Mstar :=
          section12_rankTwo_prime_mem hA_Mstar
        exact hp_not_sigma
          (section12_sigmaPrimes_mem_of_alphaPrimes_mem
            (G := G) hMstarP.1 ⟨hpMstar, hgt⟩)
      have hrank_eq : primeRank p.val Mstar = 2 := le_antisymm hrank_le hrank_ge
      simpa [section12Tau2Primes] using ⟨hp_not_sigma, hrank_eq⟩
    have hCbot : subgroupCentralizerIn (section10Msigma Mstar) A = ⊥ :=
      theorem_12_5_d
        (G := G) (M := Mstar) (A := A) (p := p)
        hMstarP.1 hpτ2Mstar hA_Mstar
    have hKleBot : K ≤ ⊥ := by
      rw [← hCbot]
      intro k hk
      exact ⟨hKleσMstar hk, hKcentA hk⟩
    exact hKne (le_bot_iff.mp hKleBot)
  have hpSigmaMstar : p ∈ section10SigmaPrimes Mstar := by
    have hp_dvd_A : p.val ∣ Nat.card A := by
      rcases section12_rankTwo_elementary hA_Mstar with ⟨hAcard, _hAelem⟩
      rw [hAcard]
      simp [pow_two]
    have hp_dvd_Msigma : p.val ∣ Nat.card (section10Msigma Mstar) :=
      hp_dvd_A.trans (Subgroup.card_dvd_of_le hAleσMstar)
    exact ((theorem_10_2_b (G := G) hMstarP.1).1).p_in_pi_of_p_dvd_card
      p hp_dvd_Msigma
  have hp_not_betaMstar : p ∉ section10BetaPrimes Mstar := by
    intro hpβ
    have hpIdeal : section10IdealPrime p G := by
      rcases (by simpa [section10BetaPrimes] using hpβ) with ⟨_hpα, hpIdeal⟩
      exact hpIdeal
    exact hp_not_betaG (by simpa [section12BetaPrimesOfGroup] using hpIdeal)
  have hMstar_not_P2 : Mstar ∉ section14MFamilyP2 G := by
    intro hP2
    have hσeqβ : section10SigmaPrimes Mstar = section10BetaPrimes Mstar :=
      (proposition_14_2_g
        (G := G) (M := Mstar) (K := section14KStar M K) hP2 _hKstarHall).1
    exact hp_not_betaMstar (by simpa [hσeqβ] using hpSigmaMstar)
  have hMstarP1 : Mstar ∈ section14MFamilyP1 G := by
    refine ⟨hMstarP, ?_⟩
    by_contra hκne
    exact hMstar_not_P2 ⟨hMstarP, hκne⟩
  exact
    section15_theorem15_8_no_rankTwo_centralizes_K_core
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar)
      (MFstar := MFstar) (A := A) (p := p) (q := q)
      hHF hMstarP1 hMFstar _hKstarHall hKeq hAcentK hqcard
      hqSigmaMstar hpSigmaMstar hp_not_betaMstar
      hA_H hA_Mstar hAnotUnique hσHinfMstar_bot hAleσMstar hpq

private theorem CFSG.section15_theorem15_8_rankTwo_in_H_inter_Mstar_prime_eq
    {M H K Mstar U MFstar A : Subgroup G} {p q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hqK : q ∈ subgroupPrimeSet K)
    (hpτ2H : p ∈ section12Tau2Primes H)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (H ⊓ Mstar)) :
    p = q := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let D : Subgroup G := H ⊓ Mstar
  have hqcard : q.val = Nat.card K :=
    section15_theorem15_8_q_card_K
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituation hqK
  rcases section15_theorem15_8_corollary14_12_conclusions
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituation with
    ⟨hHF, _hUleσH, _hMHprod, _hNormU_notM, hKleF, hDcomp⟩
  have hDcompTo : section12ComplementToMsigma H D := by
    simpa [D, section12ComplementToMsigma] using hDcomp
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := H) (E := D) hHF.1 hDcompTo with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  have hA_D : A ∈ section12RankTwoElementaryAbelianIn p D := by
    simpa [D] using hA
  rcases section12_rankTwo_elementary hA_D with ⟨_hAcard, hAelem⟩
  haveI : IsElementaryAbelian p.val A := hAelem
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  have hAnil : Group.IsNilpotent A :=
    IsPGroup.isNilpotent (p := p.val) (G := A) (h := hAp)
  have hAnormD : section10NormalIn A D :=
    (corollary_12_6_a
      (G := G) (M := H) (E := D) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hHF.1 hEdata hpτ2H hA_D).1
  have hAleFD : A ≤ section8FittingSubgroup D :=
    section12_le_fittingSubgroupOf_of_normalIn_nilpotent
      (G := G) (H := D) (N := A) hAnormD.1 hAnormD.2 hAnil
  have hKleFD : K ≤ section8FittingSubgroup D := by
    simpa [D] using hKleF
  have hKq : IsPGroup q.val K := by
    refine IsPGroup.of_card (p := q.val) (G := K) (n := 1) ?_
    simpa [pow_one] using hqcard.symm
  by_cases hpq : p = q
  · exact hpq
  · have hAπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) A :=
      section8_isPiSubgroup_singleton_of_isPGroup (G := G) hAp
    have hKπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) K :=
      section8_isPiSubgroup_singleton_of_isPGroup (G := G) hKq
    have hdisj : Disjoint ({p} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
      rw [Set.disjoint_left]
      intro r hrp hrq
      have hrp_eq : r = p := by simpa using hrp
      have hrq_eq : r = q := by simpa using hrq
      exact hpq (hrp_eq.symm.trans hrq_eq)
    have hAcentK : A ≤ Subgroup.centralizer (K : Set G) :=
      section10_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
        (G := G) (π := ({p} : Set Nat.Primes)) (ρ := ({q} : Set Nat.Primes))
        (L := section8FittingSubgroup D) (A := A) (B := K)
        hdisj (section8FittingSubgroup_isNilpotent D) hAleFD hKleFD hAπ hKπ
    exact False.elim
      (section15_theorem15_8_no_rankTwo_centralizes_K_of_ne_q
        (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
        (MFstar := MFstar) (A := A) (p := p) (q := q)
        hSituation hMFstar hqK hpτ2H hA hpq hAcentK)

/-- Source core for Theorem 15.8, in the form used by the singleton proof:
rank-two elementary subgroups of `H ∩ M*` are `q`-groups. -/
private theorem CFSG.section15_theorem15_8_rankTwo_in_H_inter_Mstar_isPGroup
    {M H K Mstar U MFstar A : Subgroup G} {p q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hqK : q ∈ subgroupPrimeSet K)
    (hpτ2H : p ∈ section12Tau2Primes H)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (H ⊓ Mstar)) :
    IsPGroup q.val A := by
  have hpq : p = q :=
    section15_theorem15_8_rankTwo_in_H_inter_Mstar_prime_eq
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar)
      (U := U) (MFstar := MFstar) (A := A) (p := p) (q := q)
      hSituation hMFstar hqK hpτ2H hA
  rcases section12_rankTwo_elementary hA with ⟨_hAcard, hAelem⟩
  haveI : IsElementaryAbelian p.val A := hAelem
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  simpa [hpq] using hAp

/-- If the source core makes every `τ₂(H)` rank-two subgroup a `q`-group,
then every prime in `τ₂(H)` is `q`. -/
private theorem CFSG.section15_theorem15_8_tau2H_unique_prime
    {M H K Mstar U MFstar : Subgroup G} {q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hqK : q ∈ subgroupPrimeSet K) :
    ∀ p : Nat.Primes, p ∈ section12Tau2Primes H → p = q := by
  classical
  rcases section15_theorem15_8_corollary14_12_conclusions
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituation with
    ⟨hHF, _hUleσH, _hMHprod, _hNormU_notM, _hKleF, hDcomp⟩
  have hDcompTo :
      section12ComplementToMsigma H (H ⊓ Mstar) := by
    simpa [section12ComplementToMsigma] using hDcomp
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := H) (E := H ⊓ Mstar) hHF.1 hDcompTo with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  intro p hpτ2H
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := H) (E := H ⊓ Mstar) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hHF.1 hEdata hpτ2H
  have hAq : IsPGroup q.val A :=
    section15_theorem15_8_rankTwo_in_H_inter_Mstar_isPGroup
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar)
      (U := U) (MFstar := MFstar) (A := A) (p := p) (q := q)
      hSituation hMFstar hqK hpτ2H hA
  have hpA : p.val ∣ Nat.card A := by
    rcases section12_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
    rw [hAcard]
    exact dvd_pow_self p.val (by decide : 2 ≠ 0)
  have hpSingleton : p ∈ ({q} : Set Nat.Primes) :=
    section8_isPiSubgroup_singleton_of_isPGroup (G := G) hAq p hpA
  simpa using hpSingleton

omit [Finite G] [IsMinCE G] in
/-- A nonempty prime set with all elements equal to `q` is `{q}`. -/
private theorem CFSG.section15_tau2_singleton_of_nonempty_unique
    {H : Subgroup G} {q : Nat.Primes}
    (hτ2H : (section12Tau2Primes H).Nonempty)
    (hunique : ∀ p : Nat.Primes, p ∈ section12Tau2Primes H → p = q) :
    section12Tau2Primes H = {q} := by
  rcases hτ2H with ⟨p₀, hp₀⟩
  have hqτ2 : q ∈ section12Tau2Primes H := by
    simpa [hunique p₀ hp₀] using hp₀
  ext p
  constructor
  · intro hp
    have hpq : p = q := hunique p hp
    simp [hpq]
  · intro hp
    have hpq : p = q := by simpa using hp
    simpa [hpq] using hqτ2

/-- Theorem 15.8 source block with `D=H∩M*`: arbitrary rank-two elementary
subgroups of the complement are `q`-groups, so `τ₂(H)={q}`. -/
private theorem CFSG.section15_theorem15_8_tau2H_singleton
    {M H K Mstar U MFstar : Subgroup G} {q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hτ2H : (section12Tau2Primes H).Nonempty)
    (hqK : q ∈ subgroupPrimeSet K) :
    section12Tau2Primes H = {q} := by
  exact section15_tau2_singleton_of_nonempty_unique hτ2H
    (section15_theorem15_8_tau2H_unique_prime
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      (MFstar := MFstar) hSituation hMFstar hqK)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_tau2_not_mem_kappa
    {M : Subgroup G} {p : Nat.Primes}
    (hpτ2 : p ∈ section12Tau2Primes M) :
    p ∉ section14KappaPrimes M := by
  intro hpκ
  have hpκ' :
      (p ∈ section12Tau1Primes M ∧
        ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p M ∧
          subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) ∨
        (p ∈ section12Tau3Primes M ∧
          ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p M ∧
            subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) := by
    simpa [section14KappaPrimes] using hpκ
  rcases hpκ' with ⟨hpτ1, _P, _hPprime, _hcent⟩ |
      ⟨hpτ3, _P, _hPprime, _hcent⟩
  · exact (section15_tau2_disjoint_tau1_tau3 (M := M) (q := p) hpτ2)
      (Or.inl hpτ1)
  · exact (section15_tau2_disjoint_tau1_tau3 (M := M) (q := p) hpτ2)
      (Or.inr hpτ3)

public theorem CFSG.section15_tau2_mem_prop14_U_primeSet_of_complement
    {M N K U : Subgroup G} {r : Nat.Primes}
    (hN : N ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementIn N (section10Msigma N) (M ⊓ N))
    (hrτ2 : r ∈ section12Tau2Primes N)
    (hU : section14Proposition14_2AData N K U) :
    r ∈ subgroupPrimeSet U := by
  classical
  have hcompTo : section12ComplementToMsigma N (M ⊓ N) := by
    simpa [section12ComplementToMsigma] using hcomp
  have hrN : r ∈ subgroupPrimeSet N :=
    section15_tau2_mem_subgroupPrimeSet_of_complement
      (G := G) (M := N) (E := M ⊓ N) hN hcompTo hrτ2
  rcases hU with ⟨_hprime, _hcomm, hUHall, _hreg, _hnormComp⟩
  have hrπ :
      r ∈ ((section14KappaPrimes N ∪ section10SigmaPrimes N)ᶜ) := by
    intro hrκσ
    rcases hrκσ with hrκ | hrσ
    · exact section15_tau2_not_mem_kappa (G := G) (M := N) hrτ2 hrκ
    · exact hrτ2.1 hrσ
  exact
    section15_subgroupPrimeSet_of_hallSubgroupIn
      (G := G) (π := ((section14KappaPrimes N ∪ section10SigmaPrimes N)ᶜ))
      (K := U) (H := N) (p := r) hUHall hrπ hrN

private theorem CFSG.section15_tau2_empty_of_centralizer_U_not_le
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hCGU_not : ¬ Subgroup.centralizer (U : Set G) ≤ M) :
    section12Tau2Primes M = ∅ := by
  classical
  apply Set.eq_empty_iff_forall_notMem.2
  intro r hrτ2
  let E : Subgroup G := K ⊔ U
  have hEcomp : section12ComplementToMsigma M E := by
    change section12ComplementIn M (section10Msigma M) (K ⊔ U)
    exact hKU.2.2.1
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := M) (E := E) hM hEcomp with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  rcases section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hEdata hrτ2 with
    ⟨A, hA⟩
  have hrπ :
      r ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
    intro hrκσ
    rcases hrκσ with hrκ | hrσ
    · exact section15_tau2_not_mem_kappa (G := G) (M := M) hrτ2 hrκ
    · exact hrτ2.1 hrσ
  have hUHallE :
      section12HallSubgroupIn
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U E := by
    exact section15_hallSubgroupIn_of_le_overgroup
      (G := G) (M := M) (E := E) (U := U)
      (π := ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ))
      hKU.2.2.2.1 (by simp [E])
      (by simpa [E] using hKU.2.2.1.2.1)
  have hUnormE : section10NormalIn U E := by
    simpa [E] using hKU.2.2.2.2.2.2
  have hAleU : A ≤ U := by
    have hAE : A ≤ E := section15_rankTwo_le hA
    have hAsub_p : IsPGroup r.val (A.subgroupOf E) :=
      section15_rankTwo_subgroupOf_isPGroup (G := G) (M := E) hA
    haveI : (U.subgroupOf E).Normal := hUnormE.2
    have hAsub_le_Usub : A.subgroupOf E ≤ U.subgroupOf E :=
      section15_pSubgroup_le_normal_hall_of_prime_mem
        (R := E) (π := ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ))
        (H := U.subgroupOf E) (A := A.subgroupOf E)
        hUHallE.2 hrπ hAsub_p
    intro x hxA
    let xE : E := ⟨x, hAE hxA⟩
    have hxAsub : xE ∈ A.subgroupOf E := by
      simpa [xE, Subgroup.mem_subgroupOf] using hxA
    have hxUsub : xE ∈ U.subgroupOf E := hAsub_le_Usub hxAsub
    simpa [xE, Subgroup.mem_subgroupOf] using hxUsub
  have hCGU_le_CGA :
      Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    exact hx a (hAleU ha)
  have hCGA_le_M : Subgroup.centralizer (A : Set G) ≤ M := by
    have h126 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := r)
        hM hEdata hrτ2 hA
    intro x hx
    exact (h126.1 hx).2
  exact hCGU_not (hCGU_le_CGA.trans hCGA_le_M)

omit [IsMinCE G] in
private theorem CFSG.section15_isMulCommutative_of_surjective
    {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (hA : IsMulCommutative A) :
    IsMulCommutative B := by
  classical
  refine ⟨⟨fun x y => ?_⟩⟩
  rcases hf x with ⟨a, rfl⟩
  rcases hf y with ⟨b, rfl⟩
  letI : IsMulCommutative A := hA
  letI : CommGroup A := IsMulCommutative.instCommGroup
  simpa using congrArg f (mul_comm a b)

omit [IsMinCE G] in
private theorem CFSG.section15_ambientDerived_le_pPrimeCore_map_of_nilpotent_pCore_commutative
    {H : Subgroup G} {p : Nat.Primes}
    (hHnil : Group.IsNilpotent H)
    (hPcomm : IsMulCommutative (pCore p.val H)) :
    ambientDerivedSubgroup H ≤ (pPrimeCore p.val H).map H.subtype := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let P : Subgroup H := pCore p.val H
  let L : Subgroup H := pPrimeCore p.val H
  let qH : H →* H ⧸ L := QuotientGroup.mk' L
  letI : Group.IsNilpotent H := hHnil
  have hfit_top : fittingSubgroup H = ⊤ :=
    fitting_eq_top_of_nilpotent (G := H)
  have htop_le_PL : (⊤ : Subgroup H) ≤ P ⊔ L := by
    rw [← hfit_top]
    simpa [P, L] using
      section15_local_fitting_le_pCore_sup_pPrimeCore (H := H) (p := p.val)
  let φ : P →* H ⧸ L := qH.comp P.subtype
  have hφ_surj : Function.Surjective φ := by
    intro z
    rcases QuotientGroup.mk'_surjective (N := L) z with ⟨x, rfl⟩
    have hxPL : x ∈ P ⊔ L := htop_le_PL (Subgroup.mem_top x)
    rcases (Subgroup.mem_sup_of_normal_left (s := P) (t := L) (x := x)).1 hxPL with
      ⟨a, haP, b, hbL, habx⟩
    refine ⟨⟨a, haP⟩, ?_⟩
    change qH a = qH x
    rw [← habx]
    simp [qH, L, hbL]
  have hquot_comm : IsMulCommutative (H ⧸ L) :=
    section15_isMulCommutative_of_surjective φ hφ_surj
      (by simpa [P] using hPcomm)
  have hder_le_L : derivedSubgroup H ≤ L := by
    have hcomm_le : _root_.commutator H ≤ L :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := L)).1 hquot_comm
    simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def, L] using hcomm_le
  have hmap_le :
      (derivedSubgroup H).map H.subtype ≤ (pPrimeCore p.val H).map H.subtype :=
    Subgroup.map_mono hder_le_L
  simpa [ambientDerivedSubgroup, L] using hmap_le

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_hasNonabelianSylow_of_noncomm_pSubgroup
    {P : Subgroup G} {p : Nat.Primes}
    (hPp : IsPGroup p.val P) (hPnoncomm : ¬ IsMulCommutative P) :
    section12HasNonabelianSylowSubgroup p G := by
  classical
  obtain ⟨S, hP_le_S⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPp
  refine ⟨S, ?_⟩
  intro hScomm
  apply hPnoncomm
  refine ⟨⟨fun x y => ?_⟩⟩
  exact Subtype.ext <|
    setLike_mul_comm
      (s := (S : Subgroup G)) (hP_le_S x.property) (hP_le_S y.property)

private theorem CFSG.section15_theorem15_8_hasNonabelianSylow_q
    {M H K Mstar U MFstar : Subgroup G} {q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hτ2H : (section12Tau2Primes H).Nonempty)
    (hqK : q ∈ subgroupPrimeSet K) :
    section12HasNonabelianSylowSubgroup q G := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let σ : Subgroup G := section10Msigma Mstar
  let Kstar : Subgroup G := section14KStar M K
  have hSituationFull := hSituation
  have hqcard : q.val = Nat.card K :=
    section15_theorem15_8_q_card_K
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituationFull hqK
  rcases section15_theorem15_8_corollary14_12_conclusions
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituationFull with
    ⟨hHF, _hUleσH, _hMHprod, _hNormU_notM, _hKleF, hDcomp⟩
  rcases hSituation with
    ⟨_hMP2, _hHallK, h14, _hUdata, _r, _R, _hrU, _hHmax⟩
  rcases h14 with
    ⟨hMstarP, _hMstar_not_conj, _hPrimeOrderUnique, hKstarHall,
      _hKsigmaHall, hKeq, _hKappaEq, _hZdp, _hZcyc, _hInterData,
      _hWidehatTI, _hWidehatNorm, _hWidehatDisj, _hWidehatCard,
      _hWidehatHalf, _hP2prime, _hPconj, _hDerCompl⟩
  rcases hτ2H with ⟨p, hpτ2H⟩
  have hp_eq_q : p = q :=
    section15_theorem15_8_tau2H_unique_prime
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      (MFstar := MFstar) hSituationFull hMFstar hqK p hpτ2H
  let D : Subgroup G := H ⊓ Mstar
  have hDcompTo : section12ComplementToMsigma H D := by
    simpa [D, section12ComplementToMsigma] using hDcomp
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := H) (E := D) hHF.1 hDcompTo with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := H) (E := D) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hHF.1 hEdata hpτ2H
  have hA_H : A ∈ section12RankTwoElementaryAbelianIn p H :=
    section12_rankTwo_mono hA inf_le_left
  have hp_not_betaG : p ∉ section12BetaPrimesOfGroup G :=
    (lemma_12_1_g
      (G := G) (M := H) (E := D) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hHF.1 hEdata hpτ2H hA_H).2
  have hq_not_betaG : q ∉ section12BetaPrimesOfGroup G := by
    simpa [hp_eq_q] using hp_not_betaG
  have hKleσMstar : K ≤ section10Msigma Mstar := by
    rw [hKeq]
    exact inf_le_left
  have hqSigmaMstar : q ∈ section10SigmaPrimes Mstar := by
    have hqMsigma : q.val ∣ Nat.card (section10Msigma Mstar) := by
      simpa [hqcard] using
        (Subgroup.card_dvd_of_le hKleσMstar :
          Nat.card K ∣ Nat.card (section10Msigma Mstar))
    exact ((theorem_10_2_b (G := G) hMstarP.1).1).p_in_pi_of_p_dvd_card q hqMsigma
  have hMstar_not_P2 : Mstar ∉ section14MFamilyP2 G := by
    intro hP2
    have hσeqβ : section10SigmaPrimes Mstar = section10BetaPrimes Mstar :=
      (proposition_14_2_g
        (G := G) (M := Mstar) (K := Kstar) hP2 hKstarHall).1
    have hqβ : q ∈ section10BetaPrimes Mstar := by
      simpa [Kstar, hσeqβ] using hqSigmaMstar
    exact hq_not_betaG (by
      have hqIdeal : section10IdealPrime q G := hqβ.2
      simpa [section12BetaPrimesOfGroup] using hqIdeal)
  have hMstarP1 : Mstar ∈ section14MFamilyP1 G := by
    refine ⟨hMstarP, ?_⟩
    by_contra hκne
    exact hMstar_not_P2 (by
      simpa [section14MFamilyP2] using (⟨hMstarP, hκne⟩ :
        Mstar ∈ section14MFamilyP G ∧
          section14KappaPrimes Mstar ≠
            subgroupPrimeSet Mstar \ section10SigmaPrimes Mstar))
  have hqKstar_card :
      q.val = Nat.card (section14KStar Mstar Kstar) := by
    simpa [Kstar, ← hKeq] using hqcard
  have hMF_eq : MFstar = section10Msigma Mstar := by
    by_contra hMF_ne
    rcases theorem_15_2_b
        (G := G) (M := Mstar) (MF := MFstar) (K := Kstar)
        hMstarP.1 hMFstar hKstarHall hMF_ne with
      ⟨_p0, q0, _hp0, hq0, hq0MFβ⟩
    have hq0_eq_q : q0 = q := by
      apply Subtype.ext
      exact hq0.trans hqKstar_card.symm
    have hqβ : q ∈ section10BetaPrimes Mstar := by
      simpa [hq0_eq_q] using hq0MFβ.2
    exact hq_not_betaG (by
      have hqIdeal : section10IdealPrime q G := hqβ.2
      simpa [section12BetaPrimesOfGroup] using hqIdeal)
  have hσnil : Group.IsNilpotent σ := by
    rcases hMFstar.1 with ⟨_hMFle, _hMFnorm, hMFnil, _hMFHall⟩
    change Group.IsNilpotent (section10Msigma Mstar)
    rw [← hMF_eq]
    exact hMFnil
  have hKstarComp : section12ComplementToMsigma Mstar Kstar :=
    section15_hall_kappa_complementToMsigma_of_mem_P1
      (G := G) (M := Mstar) (K := Kstar) hMstarP1 hKstarHall
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := Mstar) (E := Kstar) hMstarP.1 hKstarComp with
    ⟨Estar₁₂, Estar₁, Estar₂, Estar₃, hEstarData⟩
  have hCentKstar_le_der :
      subgroupCentralizerIn (section10Msigma Mstar) Kstar ≤
        ambientDerivedSubgroup (section10Msigma Mstar) :=
    (lemma_12_17
      (G := G) (M := Mstar) (E := Kstar) (E₁₂ := Estar₁₂)
      (E₁ := Estar₁) (E₂ := Estar₂) (E₃ := Estar₃)
      hMstarP.1 hEstarData).1
  have hKleDerived : K ≤ ambientDerivedSubgroup σ := by
    rw [hKeq]
    simpa [Kstar, σ, section14KStar] using hCentKstar_le_der
  let S : Sylow q.val σ := Classical.choice (Sylow.nonempty (p := q.val) (G := σ))
  have hSnoncomm : ¬ IsMulCommutative (S : Subgroup σ) := by
    intro hScomm
    let Pcore : Subgroup σ := pCore q.val σ
    have hPcore_le_S : Pcore ≤ (S : Subgroup σ) := by
      simpa [Pcore] using section15_pCore_le_sylow S
    have hPcore_comm : IsMulCommutative Pcore := by
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      exact
        setLike_mul_comm
          (s := (S : Subgroup σ)) (hPcore_le_S x.property) (hPcore_le_S y.property)
    have hder_le_pprime :
        ambientDerivedSubgroup σ ≤ (pPrimeCore q.val σ).map σ.subtype :=
      section15_ambientDerived_le_pPrimeCore_map_of_nilpotent_pCore_commutative
        (G := G) (H := σ) (p := q) hσnil (by simpa [Pcore] using hPcore_comm)
    have hKlePprime : K ≤ (pPrimeCore q.val σ).map σ.subtype :=
      hKleDerived.trans hder_le_pprime
    have hq_dvd_map : q.val ∣ Nat.card ((pPrimeCore q.val σ).map σ.subtype) := by
      have hcard_dvd :
          Nat.card K ∣ Nat.card ((pPrimeCore q.val σ).map σ.subtype) :=
        Subgroup.card_dvd_of_le hKlePprime
      simpa only [← hqcard] using hcard_dvd
    have hq_dvd_core : q.val ∣ Nat.card (pPrimeCore q.val σ) :=
      hq_dvd_map.trans (Subgroup.card_map_dvd (H := pPrimeCore q.val σ) σ.subtype)
    exact
      (q.property.coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (G := σ) (p := q.val))) hq_dvd_core
  let Qamb : Subgroup G := section10AmbientSylowSubgroup σ S
  have hQamb_p : IsPGroup q.val Qamb := by
    change IsPGroup q.val ((S : Subgroup σ).map σ.subtype)
    exact IsPGroup.map (p := q.val) (H := (S : Subgroup σ))
      S.isPGroup' σ.subtype
  have hQamb_noncomm : ¬ IsMulCommutative Qamb := by
    intro hQamb_comm
    let e : (S : Subgroup σ) ≃* (S : Subgroup σ).map σ.subtype :=
      Subgroup.equivMapOfInjective (f := σ.subtype) (S : Subgroup σ)
        σ.subtype_injective
    have hScomm : IsMulCommutative (S : Subgroup σ) :=
      section15_isMulCommutative_of_mulEquiv e
        (by
          change IsMulCommutative ((S : Subgroup σ).map σ.subtype) at hQamb_comm
          exact hQamb_comm)
    exact hSnoncomm hScomm
  exact
    section15_hasNonabelianSylow_of_noncomm_pSubgroup
      (G := G) (P := Qamb) (p := q) hQamb_p hQamb_noncomm

private theorem CFSG.section15_theorem15_8_primeOrder_le_K_of_le_inter
    {M K Mstar X : Subgroup G} {q : Nat.Primes}
    (hMP : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (h14 : section14Theorem14_7Data M K Mstar)
    (hqK : q ∈ subgroupPrimeSet K)
    (hXcard : Nat.card X = q.val)
    (hXM : X ≤ M)
    (hXMstar : X ≤ Mstar) :
    X ≤ K := by
  classical
  rcases h14 with
    ⟨_hMstarP, _hMstar_not_conj, _hPrimeOrderUnique, _hKstarHall,
      _hKsigmaHall, _hKeq, _hKappaEq, _hZdp, _hZcyc, hInterData,
      _hWidehatTI, _hWidehatNorm, _hWidehatDisj, _hWidehatCard,
      _hWidehatHalf, _hP2prime, _hPconj, _hDerCompl⟩
  have hqKdvd : q.val ∣ Nat.card K := by
    simpa [subgroupPrimeSet] using hqK
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hq_dvd_one : q.val ∣ 1 := by
      simpa [hKbot] using hqKdvd
    exact q.property.not_dvd_one hq_dvd_one
  have hKstarne : section14KStar M K ≠ ⊥ :=
    (proposition_14_2_c (G := G) (M := M) (K := K) hMP hK).1
  obtain ⟨x0, hx0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  obtain ⟨y0, hy0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKstarne
  have hInter : M ⊓ Mstar = section14Z M K :=
    (hInterData x0 y0 x0.2 (by simpa using hx0ne) y0.2
      (by simpa using hy0ne)).1
  have hXleInf : X ≤ M ⊓ Mstar := by
    intro x hx
    exact ⟨hXM hx, hXMstar hx⟩
  have hXZ : X ≤ section14Z M K := by
    simpa [← hInter] using hXleInf
  have hXprime : X ∈ section12PrimeOrderSubgroups (section14Z M K) :=
    ⟨hXZ, ⟨q, hXcard⟩⟩
  rcases
      section14_7_primeOrder_le_k_or_kstar_of_z
        (G := G) (M := M) (K := K) (X := X) hMP hK hXprime with
    hXK | hXKstar
  · exact hXK
  · have hqKsub : q.val ∣ Nat.card (K.subgroupOf M) := by
      simpa [section12_card_subgroupOf_eq hK.1] using hqKdvd
    have hqκ : q ∈ section14KappaPrimes M :=
      hK.2.p_in_pi_of_p_dvd_card q hqKsub
    have hq_dvd_X : q.val ∣ Nat.card X := by
      rw [hXcard]
    have hqKstar : q.val ∣ Nat.card (section14KStar M K) :=
      hq_dvd_X.trans (Subgroup.card_dvd_of_le hXKstar)
    have hqMsigma : q.val ∣ Nat.card (section10Msigma M) :=
      hqKstar.trans
        (Subgroup.card_dvd_of_le
          (show section14KStar M K ≤ section10Msigma M from inf_le_left))
    have hqMsigmaSub : q.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      have hcardMsigma :
          Nat.card (section10MsigmaSubgroup M) = Nat.card (section10Msigma M) := by
        simpa [section15_msigma_subgroupOf_eq (M := M)] using
          (section12_card_subgroupOf_eq (section15_msigma_le (M := M)))
      rw [hcardMsigma]
      exact hqMsigma
    have hqσ : q ∈ section10SigmaPrimes M :=
      ((theorem_10_2_b (G := G) hMP.1).2).p_in_pi_of_p_dvd_card q hqMsigmaSub
    exact False.elim ((section15_kappa_subset_primeSet_diff_sigma
      (G := G) (M := M) hqκ).2 hqσ)

omit [IsMinCE G] in
private theorem CFSG.section15_eq_of_le_prime_card
    {K X : Subgroup G} {q : Nat.Primes}
    (hXK : X ≤ K)
    (hXcard : Nat.card X = q.val)
    (hKcard : q.val = Nat.card K) :
    X = K := by
  apply Subgroup.eq_of_le_of_card_ge hXK
  rw [← hKcard, hXcard]

/-- The source step after choosing the prime-order subgroup `X ≤ A` from
Theorem 12.7(b): `U ≤ H_σ` centralizes `X`, while `X` is not contained in
`M`, so `C_G(U) ⊄ M`. -/
private theorem CFSG.section15_theorem15_8_centralizer_U_not_le_M
    {M H K Mstar U MFstar : Subgroup G} {q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hτ2H : (section12Tau2Primes H).Nonempty)
    (hqK : q ∈ subgroupPrimeSet K) :
    ¬ Subgroup.centralizer (U : Set G) ≤ M := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let D : Subgroup G := H ⊓ Mstar
  have hSituationFull := hSituation
  have hqcard : q.val = Nat.card K :=
    section15_theorem15_8_q_card_K
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituation hqK
  rcases section15_theorem15_8_corollary14_12_conclusions
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      hSituation with
    ⟨hHF, hUleσH, _hMHprod, _hNormU_notM, _hKleF, hDcomp⟩
  rcases hSituation with
    ⟨hMP2, hKHall, h14, _hUdata, _r, _R, _hrU, _hHmax⟩
  have h14full := h14
  rcases h14 with
    ⟨hMstarP, _hMstar_not_conj, hPrimeOrderUnique, _hKstarHall,
      _hKsigmaHall, _hKeq, _hKappaEq, _hZdp, _hZcyc, _hInterData,
      _hWidehatTI, _hWidehatNorm, _hWidehatDisj, _hWidehatCard,
      _hWidehatHalf, _hP2prime, _hPconj, _hDerCompl⟩
  have hDcompTo : section12ComplementToMsigma H D := by
    simpa [D, section12ComplementToMsigma] using hDcomp
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := H) (E := D) hHF.1 hDcompTo with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  have hτ2eq : section12Tau2Primes H = {q} :=
    section15_theorem15_8_tau2H_singleton
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      (MFstar := MFstar) hSituationFull hMFstar hτ2H hqK
  have hqτ2H : q ∈ section12Tau2Primes H := by
    rw [hτ2eq]
    simp
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := H) (E := D) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hHF.1 hEdata hqτ2H
  have hSylow : section12HasNonabelianSylowSubgroup q G :=
    section15_theorem15_8_hasNonabelianSylow_q
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar)
      (U := U) (MFstar := MFstar) hSituationFull hMFstar hτ2H hqK
  let X : Subgroup G := subgroupCentralizerIn A (section10Msigma H)
  have h127 :=
    theorem_12_7_b
      (G := G) (M := H) (E := D) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
      hHF.1 hEdata hqτ2H hA hSylow
  have hXcard : Nat.card X = q.val := by
    simpa [X] using h127.1
  have hXleA : X ≤ A := by
    intro x hx
    exact hx.1
  have hAleD : A ≤ D := section12_rankTwo_le hA
  have hXleD : X ≤ D := hXleA.trans hAleD
  have hXleMstar : X ≤ Mstar := hXleD.trans inf_le_right
  have hσH_le_CX : section10Msigma H ≤ Subgroup.centralizer (X : Set G) := by
    simpa [X] using h127.2.2.2.2.2
  have hKprimeSub : K ∈ section12PrimeOrderSubgroups K :=
    ⟨le_rfl, ⟨q, hqcard.symm⟩⟩
  have hCentK_le_Mstar : Subgroup.centralizer (K : Set G) ≤ Mstar := by
    have hUnique :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) =
          {Mstar} :=
      hPrimeOrderUnique K hKprimeSub
    have hMstarMem :
        Mstar ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer (K : Set G)) := by
      rw [hUnique]
      simp
    exact hMstarMem.2
  have hMstar_ne_H : Mstar ≠ H := by
    intro hEq
    have hκnonempty : (section14KappaPrimes H).Nonempty := by
      simpa [hEq] using hMstarP.2
    simp [hHF.2] at hκnonempty
  have hX_ne_K : X ≠ K := by
    intro hXeqK
    have hσH_le_CK : section10Msigma H ≤ Subgroup.centralizer (K : Set G) := by
      simpa [hXeqK] using hσH_le_CX
    have hσH_le_Mstar : section10Msigma H ≤ Mstar :=
      hσH_le_CK.trans hCentK_le_Mstar
    have hD_le_Mstar : D ≤ Mstar := by
      intro x hx
      exact hx.2
    have hH_le_Mstar : H ≤ Mstar := by
      rw [hDcomp.2.2.1]
      exact sup_le hσH_le_Mstar hD_le_Mstar
    have hH_lt_Mstar : H < Mstar :=
      lt_of_le_of_ne hH_le_Mstar hMstar_ne_H.symm
    exact hMstarP.1.1 (hHF.1.2 Mstar hH_lt_Mstar)
  have hX_not_le_M : ¬ X ≤ M := by
    intro hXM
    have hXleK : X ≤ K :=
      section15_theorem15_8_primeOrder_le_K_of_le_inter
        (G := G) (M := M) (K := K) (Mstar := Mstar) (X := X) (q := q)
        hMP2.1 hKHall h14full hqK hXcard hXM hXleMstar
    have hXeqK : X = K :=
      section15_eq_of_le_prime_card
        (G := G) (K := K) (X := X) (q := q) hXleK hXcard hqcard
    exact hX_ne_K hXeqK
  have hXleCGU : X ≤ Subgroup.centralizer (U : Set G) := by
    intro x hxX
    rw [Subgroup.mem_centralizer_iff]
    intro u huU
    have huσ : u ∈ section10Msigma H := hUleσH huU
    exact (Subgroup.mem_centralizer_iff.mp (hσH_le_CX huσ) x hxX).symm
  intro hCGUleM
  exact hX_not_le_M (hXleCGU.trans hCGUleM)

/-- Theorem 15.8 final source block: an order-`q` subgroup centralizing
`H_σ` forces `C_G(U) ⊄ M`, contradicting any prime in `τ₂(M)`. -/
private theorem CFSG.section15_theorem15_8_tau2M_empty
    {M H K Mstar U MFstar : Subgroup G} {q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hτ2H : (section12Tau2Primes H).Nonempty)
    (hqK : q ∈ subgroupPrimeSet K) :
    section12Tau2Primes M = ∅ := by
  have hSituationFull := hSituation
  rcases hSituation with ⟨hMP2, hK, _h14, hUdata, _r, _R, _hrU, _hHmax⟩
  have hKU : section15KUData M K U :=
    section15_KUData_of_proposition14_2AData
      (G := G) (M := M) (K := K) (U := U) hMP2.1.1 hK hUdata
  exact section15_tau2_empty_of_centralizer_U_not_le
    (G := G) (M := M) (K := K) (U := U) hMP2.1.1 hKU
    (section15_theorem15_8_centralizer_U_not_le_M
      (G := G) (M := M) (H := H) (K := K) (Mstar := Mstar) (U := U)
      (MFstar := MFstar) hSituationFull hMFstar hτ2H hqK)

/-- Theorem 15.8: in the situation of Corollary 14.12, if `τ₂(H)` is
nonempty and `q ∈ π(K)`, then `q = |K|`, `q` is the unique prime in
`τ₂(H)`, and `τ₂(M)` is empty. -/
public theorem CFSG.theorem_15_8
    {M H K Mstar U MFstar : Subgroup G} {q : Nat.Primes}
    (hSituation : section15Corollary14_12Situation M H K Mstar U)
    (hMFstar : section15MFSubgroup Mstar MFstar)
    (hτ2H : (section12Tau2Primes H).Nonempty)
    (hqK : q ∈ subgroupPrimeSet K) :
    q.val = Nat.card K ∧ section12Tau2Primes H = {q} ∧
      section12Tau2Primes M = ∅ := by
  exact
    ⟨section15_theorem15_8_q_card_K hSituation hqK,
      section15_theorem15_8_tau2H_singleton hSituation hMFstar hτ2H hqK,
      section15_theorem15_8_tau2M_empty hSituation hMFstar hτ2H hqK⟩

end Section15
