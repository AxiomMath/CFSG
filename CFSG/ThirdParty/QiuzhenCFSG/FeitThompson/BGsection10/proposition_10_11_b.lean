module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_11_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_exists_rank_two_elementary_subgroup_of_rank_ge_two
    {R : Subgroup G} (hRrank : 2 ≤ groupRank R) :
    ∃ p : Nat.Primes, ∃ A : Subgroup G,
      A ≤ R ∧ Nat.card A = p.val ^ 2 ∧ IsElementaryAbelian p.val A := by
  classical
  obtain ⟨p, B, hBp, _hBcomm, hBgen⟩ :=
    section10_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank_pre
      (R := R) hRrank
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hBnoncyc : ¬ IsCyclic B := by
    intro hcyc
    have hle : generatorRank B ≤ 1 := generatorRank_le_one_of_isCyclic (G := B) hcyc
    omega
  have hp_dvd_G : p.val ∣ Nat.card G :=
    (section10_prime_dvd_card_of_pSubgroup_two_le_generatorRank_pre
      (p := p.val) (R := R) (B := B) hBp hBgen).trans
      (Subgroup.card_subgroup_dvd_card R)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  haveI : Fact (IsPGroup p.val B) := ⟨hBp⟩
  obtain ⟨E0, _hE0norm, hE0card, hE0elem⟩ :=
    lemma_4_5_a (R := B) (p := p.val) hpodd hBnoncyc
  let E : Subgroup R := E0.map B.subtype
  let A : Subgroup G := E.map R.subtype
  have hEcard : Nat.card E = p.val ^ 2 := by
    calc
      Nat.card E = Nat.card E0 := by
        exact Subgroup.card_map_of_injective
          (K := E0) (f := B.subtype) B.subtype_injective
      _ = p.val ^ 2 := hE0card
  have hEelem : IsElementaryAbelian p.val E := by
    letI : IsElementaryAbelian p.val E0 := hE0elem
    simpa [E] using
      section10_isElementaryAbelian_map_early
        (G := B) (p := p.val) (A := E0) (G' := R) B.subtype
  have hAleR : A ≤ R := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hAcard : Nat.card A = p.val ^ 2 := by
    calc
      Nat.card A = Nat.card E := by
        exact Subgroup.card_map_of_injective
          (K := E) (f := R.subtype) R.subtype_injective
      _ = p.val ^ 2 := hEcard
  have hAelem : IsElementaryAbelian p.val A := by
    letI : IsElementaryAbelian p.val E := hEelem
    simpa [A] using
      section10_isElementaryAbelian_map_early
        (G := R) (p := p.val) (A := E) (G' := G) R.subtype
  exact ⟨p, A, hAleR, hAcard, hAelem⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section10_ambientDerivedSubgroup_le_of_le
    {H K : Subgroup G} (hHK : H ≤ K) :
    ambientDerivedSubgroup H ≤ ambientDerivedSubgroup K := by
  simp only [ambientDerivedSubgroup, derivedSubgroup, derivedSeries_one]
  rw [Subgroup.map_subtype_commutator H, Subgroup.map_subtype_commutator K]
  exact Subgroup.commutator_mono hHK hHK

private theorem CFSG.section10_ambientDerived_nilpotent_of_malpha_bot
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hMalpha_bot : section10MalphaSubgroup M = ⊥) :
    Group.IsNilpotent (ambientDerivedSubgroup M) := by
  classical
  let D : Subgroup M := derivedSubgroup M
  let K : Subgroup M := section10MalphaSubgroup M
  rcases (theorem_10_2_d (G := G) hM).2 with ⟨hKD, hKnormalD, hquot_nil⟩
  let KsubD : Subgroup D := K.subgroupOf D
  have hKsubD_bot : KsubD = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxK : (x : M) ∈ K := Subgroup.mem_subgroupOf.mp hx
      have hxbot : (x : M) ∈ (⊥ : Subgroup M) := by
        simpa [K, hMalpha_bot] using hxK
      have hx_eq : x = 1 := by
        apply Subtype.ext
        simpa using hxbot
      simpa using hx_eq
    · intro hx
      have hx_eq : x = 1 := by
        simpa using hx
      rw [hx_eq]
      exact KsubD.one_mem
  have hDnil : Group.IsNilpotent D := by
    let e : D ⧸ KsubD ≃* D :=
      (QuotientGroup.quotientMulEquivOfEq hKsubD_bot).trans QuotientGroup.quotientBot
    have hquot_nil' : Group.IsNilpotent (D ⧸ KsubD) := by
      simpa [D, K, KsubD] using hquot_nil
    letI : Group.IsNilpotent (D ⧸ KsubD) := hquot_nil'
    exact Group.nilpotent_of_mulEquiv (G := D ⧸ KsubD) (G' := D) e
  let eD : D ≃* ambientDerivedSubgroup M :=
    Subgroup.equivMapOfInjective (f := M.subtype) D M.subtype_injective
  letI : Group.IsNilpotent D := hDnil
  exact Group.nilpotent_of_mulEquiv (G := D) (G' := ambientDerivedSubgroup M) eD

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section10_ambientDerivedSubgroup_le_base
    {H : Subgroup G} :
    ambientDerivedSubgroup H ≤ H := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

omit [IsMinCE G] in
private theorem CFSG.section10_mem_section7HStarFamily_top_of_sylow_le_normalizer
    {A : Subgroup G} {q : Nat.Primes} (Q : Sylow q.val G)
    (hAQ : A ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G)) :
    (Q : Subgroup G) ∈ section7HStarFamily (⊤ : Subgroup G) A {q} := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  refine ⟨⟨le_top, ?_, hAQ⟩, ?_⟩
  · exact section8_isPiSubgroup_singleton_of_isPGroup Q.isPGroup'
  · intro R hQR hRfam
    have hRq : IsPGroup q.val R :=
      section8_isPGroup_of_isPiSubgroup_singleton hRfam.2.1
    exact Q.is_maximal' hRq hQR

private theorem CFSG.section10_sigma_of_global_sylow_le_nilpotent_ambientDerived
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (P : Sylow p.val G)
    (hDnil : Group.IsNilpotent (ambientDerivedSubgroup M))
    (hPD : (P : Subgroup G) ≤ ambientDerivedSubgroup M)
    (hPne : (P : Subgroup G) ≠ ⊥) :
    p ∈ section10SigmaPrimes M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hP_le_M : (P : Subgroup G) ≤ M :=
    hPD.trans section10_ambientDerivedSubgroup_le_base
  let PM : Sylow p.val M := P.subtype hP_le_M
  have hPMmap :
      (PM : Subgroup M).map M.subtype = (P : Subgroup G) := by
    calc
      (PM : Subgroup M).map M.subtype =
          ((P : Subgroup G).subgroupOf M).map M.subtype := by
            simp [PM, Sylow.coe_subtype]
      _ = (P : Subgroup G) ⊓ M := by
            exact Subgroup.subgroupOf_map_subtype (P : Subgroup G) M
      _ = (P : Subgroup G) := inf_eq_left.mpr hP_le_M
  have hPnontr : Nontrivial (P : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot (P : Subgroup G)).2 hPne
  have hp_dvd_P : p.val ∣ Nat.card (P : Subgroup G) := by
    obtain ⟨n, hnpos, hcard⟩ := P.isPGroup'.nontrivial_iff_card.mp hPnontr
    rw [hcard]
    exact dvd_pow_self p.val (Nat.ne_zero_of_lt hnpos)
  have hp_dvd_M : p.val ∣ Nat.card M :=
    hp_dvd_P.trans (Subgroup.card_dvd_of_le hP_le_M)
  let D : Subgroup M := derivedSubgroup M
  have hDnil_local : Group.IsNilpotent D := by
    let eD : D ≃* ambientDerivedSubgroup M :=
      Subgroup.equivMapOfInjective (f := M.subtype) D M.subtype_injective
    letI : Group.IsNilpotent (ambientDerivedSubgroup M) := hDnil
    exact Group.nilpotent_of_mulEquiv (G := ambientDerivedSubgroup M) (G' := D) eD.symm
  have hPM_le_D : (PM : Subgroup M) ≤ D := by
    intro x hx
    have hxP : ((x : M) : G) ∈ (P : Subgroup G) := by
      have hxmap : ((x : M) : G) ∈ (PM : Subgroup M).map M.subtype :=
        Subgroup.mem_map_of_mem M.subtype hx
      simpa [hPMmap] using hxmap
    have hxDg : ((x : M) : G) ∈ ambientDerivedSubgroup M := hPD hxP
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxDg
    rcases hxDg with ⟨y, hyD, hyx⟩
    have hyxM : y = x := Subtype.ext hyx
    simpa [D, hyxM] using hyD
  let PD : Sylow p.val D := PM.subtype hPM_le_D
  have hPDmap :
      (PD : Subgroup D).map D.subtype = (PM : Subgroup M) := by
    calc
      (PD : Subgroup D).map D.subtype =
          ((PM : Subgroup M).subgroupOf D).map D.subtype := by
            simp [PD, Sylow.coe_subtype]
      _ = (PM : Subgroup M) ⊓ D := by
            exact Subgroup.subgroupOf_map_subtype (PM : Subgroup M) D
      _ = (PM : Subgroup M) := inf_eq_left.mpr hPM_le_D
  have hPM_le_core : (PM : Subgroup M) ≤ pCore p.val M := by
    have hPD_le_core :
        (PD : Subgroup D).map D.subtype ≤ pCore p.val M :=
      section10_sylow_map_le_pCore_of_nilpotent_normal
        (H := M) (N := D) (by infer_instance) hDnil_local p.val PD
    simpa [hPDmap] using hPD_le_core
  have hcore_eq : pCore p.val M = (PM : Subgroup M) :=
    PM.is_maximal' (pCore_isPGroup (G := M) (p := p.val)) hPM_le_core
  have hPMnormal : (PM : Subgroup M).Normal := by
    rw [← hcore_eq]
    infer_instance
  letI : (PM : Subgroup M).Normal := hPMnormal
  have hPMne : (PM : Subgroup M) ≠ ⊥ := by
    intro hbot
    apply hPne
    rw [← hPMmap, hbot]
    simp
  have hnorm_eq :
      Subgroup.normalizer (((PM : Subgroup M).map M.subtype : Subgroup G) : Set G) = M :=
    section10_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
      hM (PM : Subgroup M) hPMne
  refine ⟨hp_dvd_M, PM, ?_⟩
  intro x hx
  have hx' :
      x ∈ Subgroup.normalizer (((PM : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
    simpa [section10AmbientSylowSubgroup, hPMmap] using hx
  rw [hnorm_eq] at hx'
  exact hx'

/-- Proposition 10.11(b). -/
public theorem CFSG.proposition_10_11_b
    {M K : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) (hKle : K ≤ M)
    (hKσ : IsPiSubgroup (section10SigmaPrimes M)ᶜ K) :
    groupRank (subgroupCentralizerIn K (section10Msigma M)) ≤ 1 := by
  classical
  let C : Subgroup G := subgroupCentralizerIn K (section10Msigma M)
  by_contra hnot
  have hnotC : ¬ groupRank C ≤ 1 := by
    simpa [C] using hnot
  have hCrank : 2 ≤ groupRank C := by
    omega
  obtain ⟨p, A, hA_le_C, hAcard, hAelem⟩ :=
    section10_exists_rank_two_elementary_subgroup_of_rank_ge_two
      (G := G) (R := C) hCrank
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hA_le_K : A ≤ K := hA_le_C.trans inf_le_left
  have hA_le_M : A ≤ M := hA_le_K.trans hKle
  have hAp : IsPGroup p.val A := by
    letI : IsElementaryAbelian p.val A := hAelem
    exact IsElementaryAbelian.isPGroup p.val A
  have hp_not_sigma : p ∉ section10SigmaPrimes M := by
    have hp_dvd_A : p.val ∣ Nat.card A := by
      rw [hAcard, pow_two]
      exact dvd_mul_right p.val p.val
    have hp_dvd_K : p.val ∣ Nat.card K :=
      hp_dvd_A.trans (Subgroup.card_dvd_of_le hA_le_K)
    exact hKσ p hp_dvd_K
  have hAσ : IsPiSubgroup (section10SigmaPrimes M)ᶜ A :=
    section10_isPiSubgroup_compl_of_isPGroup_not_mem hp_not_sigma hAp
  have hAnot_unique : A ∉ section9UniqueSubgroups G :=
    proposition_10_11_a (G := G) hM hA_le_M hAσ
  have hArankTwo : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := by
    exact ⟨hAcard, hAelem⟩
  have hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G := by
    by_contra hAnonmax
    exact hAnot_unique <|
      theorem_9_6_in_particular (G := G)
        ⟨p.val, p.property, hArankTwo, hAnonmax⟩
  have hAstar : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G :=
    ⟨hArankTwo, hAmax⟩
  have hAproper : A ≠ ⊤ := by
    intro hAtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hAtop] using hA_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hAgroupRank : 2 ≤ groupRank A :=
    section10_groupRank_at_least_two_of_elementaryAbelian_subgroup_card_p_sq_early
      (p := p.val) (A := A) (K := A) le_rfl hAcard hAelem
  have hCentA_rank_le_two :
      groupRank (Subgroup.centralizer (A : Set G)) ≤ 2 := by
    by_contra hle
    have hlarge : 3 ≤ groupRank (Subgroup.centralizer (A : Set G)) := by
      omega
    exact hAnot_unique <|
      theorem_9_6 (K := A) hAproper hAgroupRank (Or.inr hlarge)
  have hA_le_cent_msigma : A ≤ Subgroup.centralizer (section10Msigma M : Set G) := by
    intro a ha
    exact (hA_le_C ha).2
  have hMsigma_le_centA :
      section10Msigma M ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hA_le_cent_msigma ha)) x hx).symm
  have hMalpha_le_centA :
      section10Malpha M ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyα, rfl⟩
    exact hMsigma_le_centA <|
      Subgroup.mem_map.mpr
        ⟨y, section10_malphaSubgroup_le_msigmaSubgroup hM hyα, rfl⟩
  have hMalpha_bot : section10Malpha M = ⊥ := by
    by_contra hMalpha_ne
    let Kα : Subgroup M := section10MalphaSubgroup M
    have hKαne : Kα ≠ ⊥ := by
      intro hKαbot
      apply hMalpha_ne
      simp [section10Malpha, Kα, hKαbot]
    letI : Nontrivial Kα := (Subgroup.nontrivial_iff_ne_bot Kα).2 hKαne
    obtain ⟨q, hqLargest⟩ := section10_exists_largest_prime_divisor_of_nontrivial Kα
    have hqα : q ∈ section10AlphaPrimes M :=
      (section10_malphaSubgroup_isHall hM).p_in_pi_of_p_dvd_card q hqLargest.2.1
    haveI : Fact q.val.Prime := ⟨q.property⟩
    let Pα : Sylow q.val (section10Malpha M) :=
      Classical.choice (Sylow.nonempty (p := q.val) (G := section10Malpha M))
    have hPαrank : 3 ≤ groupRank (Pα : Subgroup (section10Malpha M)) :=
      section10_malpha_sylow_groupRank_ge_three_of_mem_alpha_early hM hqα Pα
    let PGα : Subgroup G := (Pα : Subgroup (section10Malpha M)).map (section10Malpha M).subtype
    have hPGαrank : 3 ≤ groupRank PGα := by
      let ePG : (Pα : Subgroup (section10Malpha M)) ≃* PGα :=
        Subgroup.equivMapOfInjective
          (Pα : Subgroup (section10Malpha M)) (section10Malpha M).subtype
          (section10Malpha M).subtype_injective
      exact hPαrank.trans
        (section10_groupRank_le_of_equiv_pre
          (R := PGα) (S := (Pα : Subgroup (section10Malpha M))) ePG.symm)
    have hPGα_le_centA : PGα ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact hMalpha_le_centA y.property
    have hCentA_large : 3 ≤ groupRank (Subgroup.centralizer (A : Set G)) :=
      hPGαrank.trans (section10_groupRank_le_of_le hPGα_le_centA)
    exact (not_le_of_gt hCentA_large) hCentA_rank_le_two
  have hMalphaSubgroup_bot : section10MalphaSubgroup M = ⊥ := by
    apply Subgroup.map_injective M.subtype_injective
    simpa [section10Malpha] using hMalpha_bot
  obtain ⟨q, hqσ, hqM⟩ :=
    section10_exists_sigma_prime_of_malpha_eq_bot hM hMalphaSubgroup_bot
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let QM : Sylow q.val M := Classical.choice (Sylow.nonempty (p := q.val) (G := M))
  let QG : Subgroup G := section10AmbientSylowSubgroup M QM
  have hQM_le_Msigma :
      (QM : Subgroup M) ≤ section10MsigmaSubgroup M :=
    section10_sylow_le_normal_hall_of_mem
      (section10_msigmaSubgroup_isHall hM) hqσ QM
  have hQG_le_Msigma : QG ≤ section10Msigma M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQM, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, hQM_le_Msigma hyQM, rfl⟩
  have hQGp : IsPGroup q.val QG := by
    change IsPGroup q.val ((QM : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := q.val) (H := (QM : Subgroup M)) QM.isPGroup' M.subtype
  obtain ⟨Q, hQGQ⟩ := IsPGroup.exists_le_sylow (G := G) (p := q.val) hQGp
  have hQ_eq_QG : (Q : Subgroup G) = QG :=
    section10_sigma_ambient_sylow_eq_of_le_sylow hqσ QM Q hQGQ
  have hQ_le_Msigma : (Q : Subgroup G) ≤ section10Msigma M := by
    intro x hx
    exact hQG_le_Msigma (by simpa [hQ_eq_QG] using hx)
  have hA_le_normQ : A ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    intro a ha
    have haσ : a ∈ Subgroup.centralizer (section10Msigma M : Set G) :=
      hA_le_cent_msigma ha
    have haQ : a ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxQ
      exact Subgroup.mem_centralizer_iff.mp haσ x (hQ_le_Msigma hxQ)
    exact centralizer_le_normalizer (Q : Subgroup G) haQ
  have hQstar :
      (Q : Subgroup G) ∈ section7HStarFamily (⊤ : Subgroup G) A {q} :=
    section10_mem_section7HStarFamily_top_of_sylow_le_normalizer Q hA_le_normQ
  have hQ_le_centA : (Q : Subgroup G) ≤ Subgroup.centralizer (A : Set G) :=
    hQ_le_Msigma.trans hMsigma_le_centA
  have hq_dvd_Q : q.val ∣ Nat.card (Q : Subgroup G) := by
    have hqQM : q.val ∣ Nat.card (QM : Subgroup M) :=
      Sylow.dvd_card_of_dvd_card QM hqM
    have hcardQG : Nat.card QG = Nat.card (QM : Subgroup M) := by
      simpa [QG] using section10AmbientSylowSubgroup_card (G := G) QM
    have hcardQ : Nat.card (Q : Subgroup G) = Nat.card QG := by
      rw [hQ_eq_QG]
    simpa [hcardQ, hcardQG] using hqQM
  have hqC : q ∈ subgroupPrimeSet (Subgroup.centralizer (A : Set G)) := by
    exact hq_dvd_Q.trans (Subgroup.card_dvd_of_le hQ_le_centA)
  have hpq : p ≠ q := by
    intro hpq
    exact hp_not_sigma (by simpa [hpq] using hqσ)
  obtain ⟨P, hAP, hPderNQ⟩ :=
    proposition_10_10_b (G := G) hpq hAstar hQstar hqC
  have hNQ_le_M : Subgroup.normalizer ((Q : Subgroup G) : Set G) ≤ M := by
    intro x hx
    exact (section10_sigma_sylow_normalizer_le hqσ QM) (by
      simpa [QG, hQ_eq_QG] using hx)
  have hP_le_D :
      (P : Subgroup G) ≤ ambientDerivedSubgroup M :=
    hPderNQ.trans (section10_ambientDerivedSubgroup_le_of_le hNQ_le_M)
  have hPne : (P : Subgroup G) ≠ ⊥ := by
    intro hPbot
    have hA_bot : A = ⊥ :=
      le_bot_iff.mp (hAP.trans (le_of_eq hPbot))
    have hp_dvd_A : p.val ∣ Nat.card A := by
      rw [hAcard, pow_two]
      exact dvd_mul_right p.val p.val
    have hp_dvd_one : p.val ∣ 1 := by
      have hcardA : Nat.card A = 1 := by
        simp [hA_bot]
      simpa [hcardA] using hp_dvd_A
    exact p.property.not_dvd_one hp_dvd_one
  have hDnil : Group.IsNilpotent (ambientDerivedSubgroup M) :=
    section10_ambientDerived_nilpotent_of_malpha_bot hM hMalphaSubgroup_bot
  have hpσ : p ∈ section10SigmaPrimes M :=
    section10_sigma_of_global_sylow_le_nilpotent_ambientDerived hM P hDnil hP_le_D hPne
  exact hp_not_sigma hpσ


end Section10
