module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection14.lemma_14_1

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

set_option maxHeartbeats 800000

/-! # Proposition 14 2 from BG Section 14 -/

section Section14

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_kappa_subset_not_sigma
    {M : Subgroup G} :
    section14KappaPrimes M ⊆ (section10SigmaPrimes M)ᶜ := by
  intro p hpκ hpσ
  exact section12_tau13_not_sigma hpκ.1 hpσ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_hall_kappa_is_sigma_compl_pi_subgroup
    {M K : Subgroup G}
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ K := by
  intro p hpK
  rcases hK with ⟨hKM, hHallK⟩
  have hcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    section12_card_subgroupOf_eq hKM
  exact section14_kappa_subset_not_sigma
    (hHallK.p_in_pi_of_p_dvd_card p (by simpa [hcard] using hpK))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_complement_to_msigma_of_isComplement'
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
  refine ⟨section14_msigma_le M, ?_, ?_, ?_⟩
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

public theorem CFSG.section14_exists_sigma_complement_containing
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKM : K ≤ M)
    (hKπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ K) :
    ∃ E : Subgroup G, section12ComplementToMsigma M E ∧ K ≤ E := by
  classical
  letI : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let Ksub : Subgroup M := K.subgroupOf M
  have hKsubπ : IsPiSubgroup (G := M) (section10SigmaPrimes M)ᶜ Ksub := by
    intro p hpKsub
    have hcard : Nat.card Ksub = Nat.card K := section12_card_subgroupOf_eq hKM
    exact hKπ p (by simpa [Ksub, hcard] using hpKsub)
  have hKsubInv : IsInvariant Unit M Ksub := by
    refine ⟨?_⟩
    intro _ x
    simp [Ksub]
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨Esub, hEHall, _hEInv, hKsubE⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcop (section10SigmaPrimes M)ᶜ
      Ksub hKsubπ hKsubInv
  have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b hM).2
  have hcompSub : (section10MsigmaSubgroup M).IsComplement' Esub :=
    section11_isComplement_of_isHall_compl hσHall hEHall
  refine ⟨Esub.map M.subtype, section14_complement_to_msigma_of_isComplement' hcompSub, ?_⟩
  intro x hxK
  exact Subgroup.mem_map.mpr
    ⟨⟨x, hKM hxK⟩, hKsubE (show (⟨x, hKM hxK⟩ : M) ∈ Ksub from hxK), rfl⟩

private theorem CFSG.section14_exists_sigma_complement_containing_hall_kappa
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∃ E : Subgroup G, section12ComplementToMsigma M E ∧ K ≤ E := by
  rcases hK with ⟨hKM, hHallK⟩
  exact section14_exists_sigma_complement_containing
    (G := G) (M := M) (K := K) hM.1 hKM
    (section14_hall_kappa_is_sigma_compl_pi_subgroup
      (M := M) (K := K) ⟨hKM, hHallK⟩)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_msigma_subgroupOf_eq {M : Subgroup G} :
    (section10Msigma M).subgroupOf M = section10MsigmaSubgroup M := by
  change (piCoreIn (section10SigmaPrimes M) M).subgroupOf M =
    piCore (section10SigmaPrimes M) M
  exact piCore_map_subtype_subgroupOf (G := G) (section10SigmaPrimes M) M

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_complement_to_msigma_isComplement'
    {M E : Subgroup G}
    (hcomp : section12ComplementToMsigma M E) :
    (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) := by
  classical
  rcases hcomp with ⟨hσM, hEM, hM, hdisj⟩
  have hσsub_eq : (section10Msigma M).subgroupOf M = section10MsigmaSubgroup M :=
    section14_msigma_subgroupOf_eq (M := M)
  have hsup_local : E.subgroupOf M ⊔ section10MsigmaSubgroup M = ⊤ := by
    have hsup1 : (section10Msigma M).subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
      calc
        (section10Msigma M).subgroupOf M ⊔ E.subgroupOf M =
            (section10Msigma M ⊔ E).subgroupOf M := by
          symm
          exact
            Subgroup.subgroupOf_sup (A := section10Msigma M) (A' := E) (B := M)
              hσM hEM
        _ = ⊤ := by
          rw [← hM]
          simp
    simpa [hσsub_eq, sup_comm] using hsup1
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxE hxσ
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp hdisj
    · have hxσ' : x ∈ (section10Msigma M).subgroupOf M := by
        simpa [hσsub_eq] using hxσ
      simpa [Subgroup.mem_subgroupOf] using hxσ'
    · simpa [Subgroup.mem_subgroupOf] using hxE
  · simpa [hsup_local] using
      (Subgroup.mul_normal (E.subgroupOf M) (section10MsigmaSubgroup M)).symm

omit [IsMinCE G] in
private theorem CFSG.section14_hall_kappa_isHall_sigma_compl_of_mem_P1
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP1 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section12HallSubgroupIn (section10SigmaPrimes M)ᶜ K M := by
  rcases hK with ⟨hKM, hHallK⟩
  refine ⟨hKM, ?_⟩
  refine isHallSubgroup_of (G := M) (section10SigmaPrimes M)ᶜ (K.subgroupOf M) ?_ ?_
  · intro p hpKsub
    have hpK : p.val ∣ Nat.card K := by
      simpa [section12_card_subgroupOf_eq hKM] using hpKsub
    exact section14_hall_kappa_is_sigma_compl_pi_subgroup
      (G := G) (M := M) (K := K) ⟨hKM, hHallK⟩ p hpK
  · intro p hpσc hpidx
    have hpM : p ∈ subgroupPrimeSet M := by
      rw [subgroupPrimeSet]
      exact hpidx.trans (Subgroup.index_dvd_card (H := K.subgroupOf M))
    have hpκ : p ∈ section14KappaPrimes M := by
      rw [hM.2]
      exact ⟨hpM, hpσc⟩
    exact (hHallK.p_in_pi_of_p_dvd_index p hpidx) hpκ

public theorem CFSG.section14_hall_kappa_complementToMsigma_of_mem_P1
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP1 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section12ComplementToMsigma M K := by
  have hKHall :
      section12HallSubgroupIn (section10SigmaPrimes M)ᶜ K M :=
    section14_hall_kappa_isHall_sigma_compl_of_mem_P1
      (G := G) (M := M) (K := K) hM hK
  have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b hM.1.1).2
  have hcomp :
      (section10MsigmaSubgroup M).IsComplement' (K.subgroupOf M) :=
    section11_isComplement_of_isHall_compl hσHall hKHall.2
  simpa [Subgroup.map_subgroupOf_eq_of_le hK.1] using
    section14_complement_to_msigma_of_isComplement' hcomp

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_hallSubgroupIn_map_subtype
    {H : Subgroup G} {π : Set Nat.Primes} {L : Subgroup H}
    (hL : IsHallSubgroup π L) :
    section12HallSubgroupIn π (L.map H.subtype) H := by
  classical
  refine ⟨Subgroup.map_subtype_le L, ?_⟩
  have hsub_eq : (L.map H.subtype).subgroupOf H = L := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le L)]
  simpa [hsub_eq] using hL

omit [IsMinCE G] in
public theorem CFSG.section14_exists_hallSubgroupIn
    {H : Subgroup G} (hsolvH : IsSolvable H) (π : Set Nat.Primes) :
    ∃ L : Subgroup G, section12HallSubgroupIn π L H := by
  classical
  letI : MulDistribMulAction Unit H := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card H) := by simp
  obtain ⟨L, hLHall, _hLInv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := H) (A := Unit) hsolvH hcop π
  exact ⟨L.map H.subtype, section14_hallSubgroupIn_map_subtype hLHall⟩

public theorem CFSG.section14_solvable_of_le_maximal
    {M H : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) (hHM : H ≤ M) :
    IsSolvable H := by
  have hHne : H ≠ ⊤ := by
    intro hHtop
    have hMtop : M = ⊤ := top_le_iff.mp (by simpa [hHtop] using hHM)
    exact hM.1 hMtop
  exact IsMinCE.proper_subgroups_solvable H (lt_top_iff_ne_top.mpr hHne)

public theorem CFSG.section14_exists_EData_of_complement
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    ∃ E₁₂ E₁ E₂ E₃ : Subgroup G, section12EData M E E₁₂ E₁ E₂ E₃ := by
  classical
  have hsolvE : IsSolvable E :=
    section14_solvable_of_le_maximal hM hcomp.2.1
  obtain ⟨E₁₂, hE₁₂⟩ :=
    section14_exists_hallSubgroupIn
      (G := G) hsolvE (section12Tau1Primes M ∪ section12Tau2Primes M)
  have hE₁₂M : E₁₂ ≤ M := hE₁₂.1.trans hcomp.2.1
  have hsolvE₁₂ : IsSolvable E₁₂ :=
    section14_solvable_of_le_maximal hM hE₁₂M
  obtain ⟨E₁, hE₁⟩ :=
    section14_exists_hallSubgroupIn
      (G := G) hsolvE₁₂ (section12Tau1Primes M)
  obtain ⟨E₂, hE₂⟩ :=
    section14_exists_hallSubgroupIn
      (G := G) hsolvE₁₂ (section12Tau2Primes M)
  obtain ⟨E₃, hE₃⟩ :=
    section14_exists_hallSubgroupIn
      (G := G) hsolvE (section12Tau3Primes M)
  exact ⟨E₁₂, E₁, E₂, E₃, hcomp, hE₁₂, hE₁, hE₂, hE₃⟩

public theorem CFSG.section14_exists_EData_containing
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKM : K ≤ M)
    (hKπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ K) :
    ∃ E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ ∧ K ≤ E := by
  rcases section14_exists_sigma_complement_containing
      (G := G) (M := M) (K := K) hM hKM hKπ with
    ⟨E, hEcomp, hKE⟩
  rcases section14_exists_EData_of_complement
      (G := G) (M := M) (E := E) hM hEcomp with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  exact ⟨E, E₁₂, E₁, E₂, E₃, hEdata, hKE⟩

private theorem CFSG.section14_exists_EData_containing_hall_kappa
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∃ E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ ∧ K ≤ E := by
  classical
  obtain ⟨E, hEcomp, hKE⟩ :=
    section14_exists_sigma_complement_containing_hall_kappa
      (G := G) (M := M) (K := K) hM hK
  obtain ⟨E₁₂, E₁, E₂, E₃, hEData⟩ :=
    section14_exists_EData_of_complement (G := G) hM.1 hEcomp
  exact ⟨E, E₁₂, E₁, E₂, E₃, hEData, hKE⟩

private theorem CFSG.section14_exists_EData_with_kappa_in_E1_of_tau1
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    ∃ E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ ∧ K ≤ E ∧ K ≤ E₁ := by
  classical
  obtain ⟨E, hEcomp, hKE⟩ :=
    section14_exists_sigma_complement_containing_hall_kappa
      (G := G) (M := M) (K := K) hM hK
  rcases hK with ⟨hKM, hKHallM⟩
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
      hKHallM.p_in_pi_of_p_dvd_card p (by simpa [KsubE, hcardE, hcardM] using hpKsubE)
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
  exact ⟨E, E₁₂, E₁, E₂, E₃, ⟨hEcomp, hE₁₂, hE₁, hE₂, hE₃⟩, hKE, hKE₁⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_actsInPrimeManner_of_section13
    {A R : Subgroup G}
    (h : section13ActsPrimeManner A R) :
    section14ActsInPrimeManner A R := by
  simpa [section14ActsInPrimeManner, section13ActsPrimeManner] using h

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_actsRegularlyOn_of_section13
    {A R : Subgroup G}
    (h : section13ActsRegularlyOn A R) :
    section14ActsRegularlyOn A R := by
  simpa [section14ActsRegularlyOn, section13ActsRegularlyOn] using h

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_actsInPrimeManner_of_le
    {A B R : Subgroup G}
    (hAB : A ≤ B)
    (hB : section14ActsInPrimeManner B R) :
    section14ActsInPrimeManner A R := by
  classical
  rcases hB with ⟨hBnorm, hprime⟩
  refine ⟨hAB.trans hBnorm, ?_⟩
  intro P hPA
  have hPB : P ∈ section12PrimeOrderSubgroups B := by
    rcases hPA with ⟨hPA_le, hp⟩
    exact ⟨hPA_le.trans hAB, hp⟩
  have hCPB : subgroupCentralizerIn R P ≤ subgroupCentralizerIn R B :=
    hprime P hPB
  have hCBA : subgroupCentralizerIn R B ≤ subgroupCentralizerIn R A := by
    intro x hx
    refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a haA
    exact Subgroup.mem_centralizer_iff.mp hx.2 a (hAB haA)
  exact hCPB.trans hCBA

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_actsRegularlyOn_of_le
    {A B R : Subgroup G}
    (hAB : A ≤ B)
    (hB : section14ActsRegularlyOn B R) :
    section14ActsRegularlyOn A R := by
  rcases hB with ⟨hBnorm, hreg⟩
  exact ⟨hAB.trans hBnorm, fun x hxA hxne => hreg x (hAB hxA) hxne⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_actsRegularlyOn_bot
    (A : Subgroup G) :
    section14ActsRegularlyOn A (⊥ : Subgroup G) := by
  refine ⟨?_, ?_⟩
  · intro x _hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      simpa using hy
    · intro hy
      simpa using hy
  · intro x _hx _hxne
    exact le_bot_iff.mp (fun y hy => hy.1)

omit [IsMinCE G] in
public theorem CFSG.section14_hall_kappa_ne_bot
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

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_msigma_normalIn
    {M : Subgroup G} :
    section10NormalIn (section10Msigma M) M := by
  refine ⟨section14_msigma_le M, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (section14_msigma_le M)).2
    (section12_le_normalizer_msigma (M := M))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_isMulCommutative_of_le
    {H K : Subgroup G} (hH : IsMulCommutative H) (hKH : K ≤ H) :
    IsMulCommutative K := by
  classical
  letI : IsMulCommutative H := hH
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Subtype.ext
  exact setLike_mul_comm (s := H) (hKH x.property) (hKH y.property)

public theorem CFSG.section14_isPiSubgroup_map
    {R S : Type*} [Group R] [Group S] {π : Set Nat.Primes} {H : Subgroup R}
    (hH : IsPiSubgroup (G := R) π H) (f : R →* S) :
    IsPiSubgroup (G := S) π (H.map f) := by
  intro p hp
  exact hH p (hp.trans (Subgroup.card_map_dvd (H := H) f))


omit [IsMinCE G] in
public theorem CFSG.section14_exists_primeOrderSubgroupIn_of_dvd_card
    {A : Subgroup G} {p : Nat.Primes}
    (hpA : p.val ∣ Nat.card A) :
    ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p A := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) p.val hpA
  refine ⟨Subgroup.zpowers (a : G), ?_⟩
  refine ⟨?_, ?_⟩
  · exact Subgroup.zpowers_le.2 a.property
  · rw [Nat.card_zpowers]
    simpa [Subgroup.orderOf_coe] using ha

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_kappa_subset_tau13
    {M : Subgroup G} :
    section14KappaPrimes M ⊆
      section12Tau1Primes M ∪ section12Tau3Primes M := by
  intro p hpκ
  exact hpκ.1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_kappa_subset_tau1_of_not_inter_tau3
    {M : Subgroup G}
    (hκτ3 : ¬ (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty) :
    section14KappaPrimes M ⊆ section12Tau1Primes M := by
  intro p hpκ
  rcases hpκ.1 with hpτ1 | hpτ3
  · exact hpτ1
  · exact False.elim (hκτ3 ⟨p, hpκ, hpτ3⟩)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_subgroupCentralizerIn_antitone_ne_bot
    {R A B : Subgroup G}
    (hAB : A ≤ B)
    (hCB : subgroupCentralizerIn R B ≠ ⊥) :
    subgroupCentralizerIn R A ≠ ⊥ := by
  intro hCA
  have hle : subgroupCentralizerIn R B ≤ subgroupCentralizerIn R A := by
    intro x hx
    rcases (by simpa [subgroupCentralizerIn] using hx) with ⟨hxR, hxCentB⟩
    have hxCentA : x ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hxCentB ⊢
      intro a haA
      exact hxCentB a (hAB haA)
    exact by simpa [subgroupCentralizerIn] using ⟨hxR, hxCentA⟩
  exact hCB (le_bot_iff.mp (by simpa [hCA] using hle))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_primeOrderSubgroups_of_primeOrderSubgroupsIn
    {A X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    X ∈ section12PrimeOrderSubgroups A := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXA, hXcard⟩
  exact ⟨hXA, ⟨p, hXcard⟩⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_prime_manner_centralizer_ne_bot
    {A R P : Subgroup G}
    (hA : section14ActsInPrimeManner A R)
    (hP : P ∈ section12PrimeOrderSubgroups A)
    (hCP : subgroupCentralizerIn R P ≠ ⊥) :
    subgroupCentralizerIn R A ≠ ⊥ := by
  intro hCA
  exact hCP (le_bot_iff.mp (by simpa [hCA] using hA.2 P hP))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_prime_manner_centralizer_ne_bot_of_exists
    {A R P Q : Subgroup G}
    (hA : section14ActsInPrimeManner A R)
    (hP : P ∈ section12PrimeOrderSubgroups A)
    (hCP : subgroupCentralizerIn R P ≠ ⊥)
    (hQ : Q ∈ section12PrimeOrderSubgroups A) :
    subgroupCentralizerIn R Q ≠ ⊥ := by
  have hCA : subgroupCentralizerIn R A ≠ ⊥ :=
    section14_prime_manner_centralizer_ne_bot hA hP hCP
  exact section14_subgroupCentralizerIn_antitone_ne_bot hQ.1 hCA


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_not_regular_of_primeOrder_centralizer_ne_bot
    {A R P : Subgroup G} {p : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p A)
    (hCP : subgroupCentralizerIn R P ≠ ⊥) :
    ¬ section14ActsRegularlyOn A R := by
  classical
  intro hreg
  have hPne : P ≠ ⊥ := section12_primeOrder_ne_bot hP
  haveI : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  obtain ⟨xP, hxPne⟩ := exists_ne (1 : P)
  let x : G := xP
  have hxP : x ∈ P := xP.property
  have hxA : x ∈ A := (by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPA, _hPcard⟩
    exact hPA hxP)
  have hxne : x ≠ 1 := by
    intro hx
    exact hxPne (Subtype.ext hx)
  have hCne : subgroupCentralizerIn R P ≠ ⊥ := hCP
  haveI : Nontrivial (subgroupCentralizerIn R P) :=
    (Subgroup.nontrivial_iff_ne_bot (H := subgroupCentralizerIn R P)).2 hCne
  obtain ⟨yC, hyCne⟩ := exists_ne (1 : subgroupCentralizerIn R P)
  let y : G := yC
  have hyR : y ∈ R := yC.property.1
  have hycentP : y ∈ Subgroup.centralizer (P : Set G) := yC.property.2
  have hyElemCent : y ∈ elementCentralizerIn R x := by
    refine ⟨hyR, ?_⟩
    simpa [Subgroup.mem_centralizer_iff] using
      (Subgroup.mem_centralizer_iff.mp hycentP x hxP)
  have hybot : y ∈ (⊥ : Subgroup G) := by
    simpa [hreg.2 x hxA hxne] using hyElemCent
  have hyone : y = 1 := by simpa using hybot
  exact hyCne (Subtype.ext hyone)

omit [IsMinCE G] in
private theorem CFSG.section14_hallSubgroupIn_eq_of_le
    {π : Set Nat.Primes} {A B H : Subgroup G}
    (hA : section12HallSubgroupIn π A H)
    (hB : section12HallSubgroupIn π B H)
    (hAB : A ≤ B) :
    A = B := by
  classical
  rcases hA with ⟨hAH, hHallA⟩
  rcases hB with ⟨hBH, hHallB⟩
  have hsub :
      A.subgroupOf H ≤ B.subgroupOf H := by
    intro x hx
    exact hAB hx
  have hsubeq : A.subgroupOf H = B.subgroupOf H :=
    hHallA.eq_of_le hHallB hsub
  ext x
  constructor
  · intro hxA
    exact hAB hxA
  · intro hxB
    have hxH : x ∈ H := hBH hxB
    let xH : H := ⟨x, hxH⟩
    have hxBsub : xH ∈ B.subgroupOf H := hxB
    have hxAsub : xH ∈ A.subgroupOf H := by
      simpa [hsubeq] using hxBsub
    exact hxAsub

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_card_conjBy (H : Subgroup G) (g : G) :
    Nat.card (H.conjBy g) = Nat.card H := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := H) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_conjBy_le_of_subgroupOf_conjBy_le
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
    have hconjM : g * y * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM hyM) (M.inv_mem hgM)
    have hx_eq : x = g * y * g⁻¹ := by
      simpa [MulAut.conj_apply] using hyx.symm
    simpa [hx_eq] using hconjM
  let xM : M := ⟨x, hxM⟩
  let yM : M := ⟨y, hHM hyH⟩
  have hyM_sub : yM ∈ H.subgroupOf M := hyH
  have hxM_conj :
      xM ∈ (H.subgroupOf M).map (MulAut.conj (⟨g, hgM⟩ : M)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨yM, hyM_sub, ?_⟩
    apply Subtype.ext
    simpa [xM, yM, MulAut.conj_apply] using hyx
  exact (hsub hxM_conj : x ∈ K)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_conjBy_inv_le_of_le_conjBy
    {H K : Subgroup G} {g : G}
    (hHK : H ≤ K.conjBy g) :
    H.conjBy g⁻¹ ≤ K := by
  intro x hx
  rw [Subgroup.conjBy, Subgroup.mem_map] at hx
  rcases hx with ⟨y, hyH, rfl⟩
  have hyKg : y ∈ K.conjBy g := hHK hyH
  rw [Subgroup.conjBy, Subgroup.mem_map] at hyKg
  rcases hyKg with ⟨z, hzK, hzy⟩
  rw [← hzy]
  simpa [MulAut.conj_apply, mul_assoc] using hzK

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_subgroupOf_conjBy_map_subtype
    {M H : Subgroup G} (hHM : H ≤ M) (m : M) :
    ((H.subgroupOf M).conjBy m).map M.subtype = H.conjBy (m : G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ (H.subgroupOf M).map (MulAut.conj m).toMonoidHom at hy
    rw [Subgroup.mem_map] at hy
    rcases hy with ⟨z, hz, hzy⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(z : G), hz, ?_⟩
    exact congrArg Subtype.val hzy
  · intro hx
    change x ∈ H.map (MulAut.conj (m : G)).toMonoidHom at hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨z, hz, hzx⟩
    let zM : M := ⟨z, hHM hz⟩
    refine ⟨m * zM * m⁻¹, ?_, ?_⟩
    · change m * zM * m⁻¹ ∈ (H.subgroupOf M).map (MulAut.conj m).toMonoidHom
      rw [Subgroup.mem_map]
      refine ⟨zM, hz, ?_⟩
      ext
      simp [zM, MulAut.conj_apply, mul_assoc]
    · change (m : G) * z * (m : G)⁻¹ = x
      simpa [MulAut.conj_apply, mul_assoc] using hzx

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_mem_normalizer_of_conjBy_eq
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
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by simpa [hg] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by
          rw [show g * x * g⁻¹ = g * y * g⁻¹ by
            simpa [MulAut.conj_apply] using hyx.symm]
        _ = y := by group
    simpa [hxy] using hy

private theorem CFSG.section14_unique_subgroup_of_prime_order_in_cyclic
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {p : ℕ} [Fact p.Prime] (A B : Subgroup H)
    (hA : Nat.card A = p) (hB : Nat.card B = p) : A = B := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := Nat.Prime.pos hp_prime
  have hp_dvd_cardH : p ∣ Nat.card H := by
    rw [← hA]
    exact Subgroup.card_subgroup_dvd_card A
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := H)
  have hg_order : orderOf g = Nat.card H := by
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    have hx := hg x
    rcases (Submonoid.mem_powers_iff _ _).mp hx with ⟨k, hk⟩
    rw [← hk]
    exact ⟨(k : ℤ), by simp⟩
  set d := Nat.card H / p with hd_def
  have hd_mul : d * p = Nat.card H := Nat.div_mul_cancel hp_dvd_cardH
  have hd_dvd : d ∣ Nat.card H := by rw [← hd_mul]; exact ⟨p, rfl⟩
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd0' : d = 0 := Nat.eq_zero_of_not_pos hd0
    rw [hd0', zero_mul] at hd_mul
    have hcard_pos : 0 < Nat.card H := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
    omega
  set g0 := g ^ d with hg0_def
  have hg0_order : orderOf g0 = p := by
    rw [hg0_def, orderOf_pow, hg_order]
    have h_gcd : Nat.gcd (Nat.card H) d = d := Nat.gcd_eq_right hd_dvd
    rw [h_gcd]
    exact Nat.div_eq_of_eq_mul_right hd_pos hd_mul.symm
  let H0 : Subgroup H := Subgroup.zpowers g0
  have hH0_card : Nat.card H0 = p := by rw [Nat.card_zpowers, hg0_order]
  have h_eq_H0 (L : Subgroup H) (hL : Nat.card L = p) : L = H0 := by
    have hL_ne_bot : L ≠ ⊥ := by
      intro hbot
      have hcard1 : Nat.card L = 1 := by
        simp [hbot]
      rw [hL] at hcard1
      exact hp_prime.ne_one hcard1
    haveI : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL_ne_bot
    obtain ⟨h, hh⟩ := IsCyclic.exists_monoid_generator (α := L)
    have hh_order_L : orderOf (h : L) = p := by
      have h_eq : orderOf (h : L) = Nat.card L :=
        orderOf_eq_card_of_forall_mem_zpowers (by
          intro x
          have hx := hh x
          rcases (Submonoid.mem_powers_iff _ _).mp hx with ⟨n, hn⟩
          rw [← hn]
          exact ⟨(n : ℤ), by simp⟩)
      rw [hL] at h_eq
      exact h_eq
    have hh_order_H : orderOf (h : H) = p := by
      rw [Subgroup.orderOf_coe (h : L), hh_order_L]
    have hh_mem : (h : H) ∈ Submonoid.powers g := hg (h : H)
    rcases (Submonoid.mem_powers_iff _ _).mp hh_mem with ⟨k, hk⟩
    rw [← hk] at hh_order_H
    rw [orderOf_pow, hg_order] at hh_order_H
    set gk := Nat.gcd (Nat.card H) k with hgk_def
    have hgk_dvd_N : gk ∣ Nat.card H := Nat.gcd_dvd_left _ _
    have hN_eq_gk_mul_p : Nat.card H = gk * p := by
      calc
        Nat.card H = gk * (Nat.card H / gk) := (Nat.mul_div_cancel' hgk_dvd_N).symm
        _ = gk * p := by rw [hh_order_H]
    have hgk_eq_d : gk = d := by
      have h_eq : gk * p = d * p := by rw [← hN_eq_gk_mul_p, hd_mul]
      apply Nat.eq_of_mul_eq_mul_right hp_pos
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq
    have hd_dvd_k : d ∣ k := by rw [← hgk_eq_d]; exact Nat.gcd_dvd_right _ _
    rcases hd_dvd_k with ⟨m, hm⟩
    have h_mem_H0 : (h : H) ∈ H0 := by
      rw [← hk, hm, pow_mul, ← hg0_def]
      exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by simp⟩
    have hL_le_H0 : L ≤ H0 := by
      intro x hx
      have hx_mem : (⟨x, hx⟩ : L) ∈ Submonoid.powers (h : L) := hh ⟨x, hx⟩
      rcases (Submonoid.mem_powers_iff _ _).mp hx_mem with ⟨n, hn⟩
      have hx_eq : x = (h : H) ^ n := by simpa using congrArg Subtype.val hn.symm
      rw [hx_eq]
      exact Subgroup.pow_mem H0 h_mem_H0 n
    apply Subgroup.eq_of_le_of_card_ge hL_le_H0
    rw [hH0_card, hL]
  exact (h_eq_H0 A hA).trans (h_eq_H0 B hB).symm

omit [IsMinCE G] in
public theorem CFSG.section14_primeRank_at_least_two_of_rankTwo
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    2 ≤ primeRank p.val M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hAM : A ≤ M := section12_rankTwo_le hA
  rcases section12_rankTwo_elementary hA with ⟨hcard, hElem⟩
  haveI : IsElementaryAbelian p.val A := hElem
  have hAcomm : IsMulCommutative A := inferInstance
  let A' : Subgroup M := A.subgroupOf M
  have hA'p : IsPGroup p.val A' :=
    (IsElementaryAbelian.isPGroup p.val A).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM).symm
  have hA'comm : IsMulCommutative A' := by
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := M)
  have hgenA : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hcard
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM)
  have hgenA' : 2 ≤ generatorRank A' := by
    simpa [hgen_eq] using hgenA
  exact hgenA'.trans
    (section12_generatorRank_le_primeRank_of_subgroup (R := M) (q := p.val)
      (A := A') hA'p hA'comm)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_elementCentralizerIn_subgroupOf_eq
    {S A : Subgroup G} {x : S} :
    elementCentralizerIn (A.subgroupOf S) x =
      (elementCentralizerIn A (x : G)).subgroupOf S := by
  ext y
  constructor
  · intro hy
    change (y : G) ∈ A ∧ (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G)
    rcases hy with ⟨hyA, hyC⟩
    refine ⟨hyA, ?_⟩
    change y ∈ Subgroup.centralizer ({x} : Set S) at hyC
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro z hz
    have hyx : x * y = y * x :=
      (Subgroup.mem_centralizer_iff.mp hyC) x (by simp)
    have hz_eq : z = (x : G) := by simpa using hz
    simpa [hz_eq] using congrArg Subtype.val hyx
  · intro hy
    change (y : G) ∈ A ∧ (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) at hy
    rcases hy with ⟨hyA, hyC⟩
    refine ⟨hyA, ?_⟩
    change y ∈ Subgroup.centralizer ({x} : Set S)
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro z hz
    have hyx : (x : G) * (y : G) = (y : G) * x :=
      hyC x (by simp)
    have hz_eq : z = x := by simpa using hz
    apply Subtype.ext
    simpa [hz_eq] using hyx

public theorem CFSG.section14_conjBy_exists_of_primeOrderIn_primeRank_eq_one
    {M P Q : Subgroup G} {p : Nat.Primes}
    (hprank : primeRank p.val M = 1)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p M)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn p M) :
    ∃ m : M, P.conjBy (m : G) = Q := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  let Psub : Subgroup M := P.subgroupOf M
  let Qsub : Subgroup M := Q.subgroupOf M
  have hPsub_card : Nat.card Psub = p.val := by
    calc
      Nat.card Psub = Nat.card P := by
        simpa [Psub] using section12_card_subgroupOf_eq (H := P) (K := M) hP.1
      _ = p.val := hP.2
  have hQsub_card : Nat.card Qsub = p.val := by
    calc
      Nat.card Qsub = Nat.card Q := by
        simpa [Qsub] using section12_card_subgroupOf_eq (H := Q) (K := M) hQ.1
      _ = p.val := hQ.2
  have hPsub_p : IsPGroup p.val Psub := by
    refine IsPGroup.of_card (p := p.val) (G := Psub) (n := 1) ?_
    simp [hPsub_card]
  have hQsub_p : IsPGroup p.val Qsub := by
    refine IsPGroup.of_card (p := p.val) (G := Qsub) (n := 1) ?_
    simp [hQsub_card]
  have hpM : p.val ∣ Nat.card M := by
    simpa [hP.2] using (Subgroup.card_dvd_of_le hP.1)
  have hpG : p.val ∣ Nat.card G :=
    hpM.trans (Subgroup.card_subgroup_dvd_card M)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  have hSylowCyclic : ∀ S : Sylow p.val M, IsCyclic (S : Subgroup M) :=
    section12_sylow_cyclic_of_primeRank_le_one hpodd
      (le_of_eq hprank)
  obtain ⟨SP, hPsub_le_SP⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := p.val) hPsub_p
  obtain ⟨SQ, hQsub_le_SQ⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := p.val) hQsub_p
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M SP SQ
  have hPsub_m_le_SQ : (MulAut.conj (m : M)) • Psub ≤ (SQ : Subgroup M) := by
    calc
      (MulAut.conj (m : M)) • Psub ≤ (MulAut.conj (m : M)) • (SP : Subgroup M) := by
        intro x hx
        rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
        exact Set.mem_smul_set.mpr ⟨y, hPsub_le_SP hy, rfl⟩
      _ = ((m • SP : Sylow p.val M) : Subgroup M) := by
        rw [← Sylow.coe_subgroup_smul (g := m) (P := SP)]
      _ = (SQ : Subgroup M) := by
        rw [hm]
  let Psub_m : Subgroup M := (MulAut.conj (m : M)) • Psub
  have hPsub_m_card : Nat.card Psub_m = p.val := by
    have hcard_eq : Nat.card Psub_m = Nat.card Psub := by
      dsimp [Psub_m]
      let e : Psub ≃* ((MulAut.conj (m : M)) • Psub : Subgroup M) :=
        Subgroup.equivSMul (a := MulAut.conj (m : M)) (H := Psub)
      exact Nat.card_congr e.symm.toEquiv
    rw [hcard_eq, hPsub_card]
  have hPsub_m_le_SQ : Psub_m ≤ (SQ : Subgroup M) := hPsub_m_le_SQ
  have h_eq_in_SQ :
      Psub_m.subgroupOf (SQ : Subgroup M) =
        Qsub.subgroupOf (SQ : Subgroup M) := by
    letI : IsCyclic (SQ : Subgroup M) := hSylowCyclic SQ
    exact
      section14_unique_subgroup_of_prime_order_in_cyclic
        (A := Psub_m.subgroupOf (SQ : Subgroup M))
        (B := Qsub.subgroupOf (SQ : Subgroup M))
        (hA := by
          have e : Psub_m.subgroupOf (SQ : Subgroup M) ≃* Psub_m :=
            Subgroup.subgroupOfEquivOfLe (H := Psub_m) (K := (SQ : Subgroup M)) hPsub_m_le_SQ
          exact (Nat.card_congr e.toEquiv).trans hPsub_m_card)
        (hB := by
          have e : Qsub.subgroupOf (SQ : Subgroup M) ≃* Qsub :=
            Subgroup.subgroupOfEquivOfLe (H := Qsub) (K := (SQ : Subgroup M)) hQsub_le_SQ
          exact (Nat.card_congr e.toEquiv).trans hQsub_card)
  have hPsub_m_eq_Qsub : Psub_m = Qsub := by
    calc
      Psub_m = (Psub_m.subgroupOf (SQ : Subgroup M)).map (SQ : Subgroup M).subtype := by
        rw [Subgroup.subgroupOf_map_subtype Psub_m (SQ : Subgroup M)]
        exact (inf_eq_left.mpr hPsub_m_le_SQ).symm
      _ = (Qsub.subgroupOf (SQ : Subgroup M)).map (SQ : Subgroup M).subtype := by
        rw [h_eq_in_SQ]
      _ = Qsub := by
        rw [Subgroup.subgroupOf_map_subtype Qsub (SQ : Subgroup M)]
        exact inf_eq_left.mpr hQsub_le_SQ
  have h_map_Psub_m : Psub_m.map M.subtype = P.conjBy (m : G) := by
    have hPsub_map : Psub.map M.subtype = P := by
      calc
        Psub.map M.subtype = (P.subgroupOf M).map M.subtype := rfl
        _ = P := by
          apply le_antisymm
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            exact Subgroup.mem_subgroupOf.mp hy
          · intro x hx
            exact Subgroup.mem_map.mpr ⟨⟨x, hP.1 hx⟩, hx, rfl⟩
    calc
      Psub_m.map M.subtype = ((MulAut.conj (m : M)) • Psub).map M.subtype := rfl
      _ = (MulAut.conj (m : G)) • (Psub.map M.subtype) := by
        apply le_antisymm
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases Set.mem_smul_set.mp hy with ⟨z, hz, rfl⟩
          refine Set.mem_smul_set.mpr
            ⟨M.subtype z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
          simp [MulAut.conj_apply, mul_assoc]
        · intro x hx
          rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
          rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
          refine Subgroup.mem_map.mpr
            ⟨(MulAut.conj (m : M)) z, Set.mem_smul_set.mpr ⟨z, hz, rfl⟩, ?_⟩
          simp [MulAut.conj_apply, mul_assoc]
      _ = P.conjBy (m : G) := by
        rw [hPsub_map]
        rfl
  have h_map_Qsub : Qsub.map M.subtype = Q := by
    calc
      Qsub.map M.subtype = (Q.subgroupOf M).map M.subtype := rfl
      _ = Q := by
        apply le_antisymm
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          exact Subgroup.mem_subgroupOf.mp hy
        · intro x hx
          exact Subgroup.mem_map.mpr ⟨⟨x, hQ.1 hx⟩, hx, rfl⟩
  refine ⟨m, ?_⟩
  calc
    P.conjBy (m : G) = Psub_m.map M.subtype := by
      rw [h_map_Psub_m]
    _ = Qsub.map M.subtype := by
      rw [hPsub_m_eq_Qsub]
    _ = Q := h_map_Qsub

public theorem CFSG.section14_primeRank_le_of_equiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (q : ℕ) (e : R ≃* S) :
    primeRank q S ≤ primeRank q R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAq, hAcomm, hsSup_le⟩
    let A' : Subgroup R := A.map e.symm.toMonoidHom
    have hA'q : IsPGroup q A' :=
      IsPGroup.map (p := q) (H := A) hAq e.symm.toMonoidHom
    have hA'comm : IsMulCommutative A' := by
      letI : IsMulCommutative A := hAcomm
      infer_instance
    have hgen_le : generatorRank A ≤ generatorRank A' := by
      let eA : A ≃* A' :=
        Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact le_of_eq (Group.rank_congr eA)
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
          n ≤ generatorRank B} :=
      ⟨A', hA'q, hA'comm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank q R := by
      simpa [primeRank] using le_csSup
        (show BddAbove
            {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
              n ≤ generatorRank B} from
          ⟨Nat.card R, by
            intro n hn
            rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
            exact hnB.trans <|
              (section8_generatorRank_le_natCard B).trans
                (Subgroup.card_le_card_group B)⟩)
        hmem
    rw [primeRank]
    exact hsSup_le.trans hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} = ∅ := by
      simpa [T] using hTempty
    rw [primeRank, hSet]
    simp

public theorem CFSG.section14_hall_kappa_isZGroup
    {M K : Subgroup G}
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    IsZGroup K := by
  classical
  rcases hK with ⟨hKM, hHallK⟩
  refine ⟨fun q hq Q => ?_⟩
  let p : Nat.Primes := ⟨q, hq⟩
  haveI : Fact p.val.Prime := ⟨p.2⟩
  by_cases hpK : p.val ∣ Nat.card K
  · have hpκ : p ∈ section14KappaPrimes M := by
      exact hHallK.p_in_pi_of_p_dvd_card p
        (by simpa [section12_card_subgroupOf_eq hKM] using hpK)
    have hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
      section14_kappa_subset_tau13 hpκ
    have hpG : p.val ∣ Nat.card G := hpK.trans (Subgroup.card_subgroup_dvd_card K)
    have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
    let f : K →* M := K.subtype.codRestrict M (fun x => hKM x.property)
    let Qmap : Subgroup M := (Q : Subgroup K).map f
    have hQmap_p : IsPGroup p.val Qmap :=
      IsPGroup.map (p := p.val) (H := (Q : Subgroup K)) Q.isPGroup' f
    obtain ⟨S, hQmap_le_S⟩ := IsPGroup.exists_le_sylow (G := M) (p := p.val) hQmap_p
    have hrankM : primeRank p.val M ≤ 1 := by
      have h := section12_tau13_primeRank_eq_one hpτ13
      omega
    have hS_cyc : IsCyclic (S : Subgroup M) :=
      section12_sylow_cyclic_of_primeRank_le_one hpodd hrankM S
    have hQmap_cyc : IsCyclic Qmap := by
      letI : IsCyclic (S : Subgroup M) := hS_cyc
      exact Subgroup.isCyclic_of_le hQmap_le_S
    have hf_inj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      simpa [f] using congrArg Subtype.val hxy
    let e : (Q : Subgroup K) ≃* Qmap :=
      Subgroup.equivMapOfInjective (f := f) (Q : Subgroup K) hf_inj
    exact e.isCyclic.2 hQmap_cyc
  · have hQbot : (Q : Subgroup K) = ⊥ := by
      by_contra hQne
      haveI : Nontrivial (Q : Subgroup K) :=
        (Subgroup.nontrivial_iff_ne_bot (H := (Q : Subgroup K))).2 hQne
      have hpQ : p.val ∣ Nat.card (Q : Subgroup K) :=
        section12_prime_dvd_card_of_nontrivial_pSubgroup
          (p := p) (B := (Q : Subgroup K)) Q.isPGroup' inferInstance
      exact hpK (hpQ.trans (Subgroup.card_subgroup_dvd_card (Q : Subgroup K)))
    haveI : Subsingleton (Q : Subgroup K) := by
      rw [hQbot]
      infer_instance
    exact isCyclic_of_subsingleton (α := (Q : Subgroup K))

public theorem CFSG.section14_conjugate_kappa_witness_into_hall
    {M K : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hpκ : p ∈ section14KappaPrimes M) :
    ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p K ∧
      subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ := by
  classical
  have hpκ_mem : p ∈ section14KappaPrimes M := hpκ
  rcases hpκ with ⟨_hpτ13, P₀, hP₀prime, hCP₀⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP₀prime) with
    ⟨hP₀M, hP₀card⟩
  rcases hK with ⟨hKM, hKHall⟩
  letI : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let P₀sub : Subgroup M := P₀.subgroupOf M
  have hP₀sub_pi :
      IsPiSubgroup (G := M) (section14KappaPrimes M) P₀sub := by
    intro q hqP
    have hqdiv : q.val ∣ p.val := by
      have hcard : Nat.card P₀sub = Nat.card P₀ :=
        section12_card_subgroupOf_eq hP₀M
      simpa [P₀sub, hcard, hP₀card] using hqP
    have hq_eq : q = p := by
      exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hqdiv)
    simpa [hq_eq] using hpκ_mem
  have hP₀sub_inv : IsInvariant Unit M P₀sub := by
    refine ⟨?_⟩
    intro _ x
    simp [P₀sub]
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1.1)
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨L, hLHall, _hLInv, hP₀L⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcop (section14KappaPrimes M)
      P₀sub hP₀sub_pi hP₀sub_inv
  obtain ⟨m, hm⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := M) hsolvM hLHall hKHall
  let P : Subgroup G := P₀.conjBy (m : G)
  have hP_le_K : P ≤ K := by
    have hPsub_conj_le :
        P₀sub.map (MulAut.conj m).toMonoidHom ≤ K.subgroupOf M := by
      have hPsub_conj_le_L :
          P₀sub.map (MulAut.conj m).toMonoidHom ≤ L.map (MulAut.conj m).toMonoidHom :=
        Subgroup.map_mono hP₀L
      simpa [hm] using hPsub_conj_le_L
    simpa [P] using
      section14_conjBy_le_of_subgroupOf_conjBy_le
        (G := G) (H := P₀) (K := K) (M := M) (g := (m : G))
        m.property hP₀M hPsub_conj_le
  have hPcard : Nat.card P = p.val := by
    simpa [P, hP₀card] using section14_card_conjBy (G := G) P₀ (m : G)
  have hPprime : P ∈ section10PrimeOrderSubgroupsIn p K := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hP_le_K, hPcard⟩
  have hm_norm : (m : G) ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section12_le_normalizer_msigma (M := M) m.property
  have hCP : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ := by
    simpa [P] using
      section11_subgroupCentralizerIn_conjBy_self_ne_bot_of_mem_normalizer
        (G := G) (R := section10Msigma M) (X := P₀) (g := (m : G)) hm_norm hCP₀
  exact ⟨P, hPprime, hCP⟩

omit [IsMinCE G] in
private theorem CFSG.section14_conjugate_prime_witness_into_hall
    {R A H P : Subgroup G} {π : Set Nat.Primes} {p : Nat.Primes}
    (hsolvA : IsSolvable A)
    (hA_norm : A ≤ Subgroup.normalizer (R : Set G))
    (hH : section12HallSubgroupIn π H A)
    (hpπ : p ∈ π)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p A)
    (hCP : subgroupCentralizerIn R P ≠ ⊥) :
    ∃ Q : Subgroup G, Q ∈ section10PrimeOrderSubgroupsIn p H ∧
      subgroupCentralizerIn R Q ≠ ⊥ := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPA, hPcard⟩
  rcases hH with ⟨hHA, hHHall⟩
  letI : MulDistribMulAction Unit A := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let Psub : Subgroup A := P.subgroupOf A
  have hPsub_pi : IsPiSubgroup (G := A) π Psub := by
    intro q hqP
    have hqdiv : q.val ∣ p.val := by
      have hcard : Nat.card Psub = Nat.card P :=
        section12_card_subgroupOf_eq hPA
      simpa [Psub, hcard, hPcard] using hqP
    have hq_eq : q = p := by
      exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hqdiv)
    simpa [hq_eq] using hpπ
  have hPsub_inv : IsInvariant Unit A Psub := by
    refine ⟨?_⟩
    intro _ x
    simp [Psub]
  have hcop : Nat.Coprime (Nat.card Unit) (Nat.card A) := by simp
  obtain ⟨L, hLHall, _hLInv, hPsubL⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := A) (A := Unit) hsolvA hcop π Psub hPsub_pi hPsub_inv
  obtain ⟨a, ha⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := A) hsolvA hLHall hHHall
  let Q : Subgroup G := P.conjBy (a : G)
  have hQ_le_H : Q ≤ H := by
    have hPsub_conj_le :
        Psub.map (MulAut.conj a).toMonoidHom ≤ H.subgroupOf A := by
      have hPsub_conj_le_L :
          Psub.map (MulAut.conj a).toMonoidHom ≤
            L.map (MulAut.conj a).toMonoidHom :=
        Subgroup.map_mono hPsubL
      simpa [ha] using hPsub_conj_le_L
    simpa [Q] using
      section14_conjBy_le_of_subgroupOf_conjBy_le
        (G := G) (H := P) (K := H) (M := A) (g := (a : G))
        a.property hPA hPsub_conj_le
  have hQcard : Nat.card Q = p.val := by
    simpa [Q, hPcard] using section14_card_conjBy (G := G) P (a : G)
  have hQprime : Q ∈ section10PrimeOrderSubgroupsIn p H := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hQ_le_H, hQcard⟩
  have ha_norm : (a : G) ∈ Subgroup.normalizer (R : Set G) := hA_norm a.property
  have hCQ : subgroupCentralizerIn R Q ≠ ⊥ := by
    simpa [Q] using
      section11_subgroupCentralizerIn_conjBy_self_ne_bot_of_mem_normalizer
        (G := G) (R := R) (X := P) (g := (a : G)) ha_norm hCP
  exact ⟨Q, hQprime, hCQ⟩

private theorem CFSG.section14_tau3_witness_in_E3
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hpκ : p ∈ section14KappaPrimes M)
    (hpτ3 : p ∈ section12Tau3Primes M) :
    ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p E₃ ∧
      subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ := by
  classical
  obtain ⟨P, hPK, hCP⟩ :=
    section14_conjugate_kappa_witness_into_hall
      (G := G) (M := M) (K := K) hM hK hpκ
  have hPE : P ∈ section10PrimeOrderSubgroupsIn p E := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hPK) with ⟨hPK_le, hPcard⟩
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hPK_le.trans hKE, hPcard⟩
  rcases hE with ⟨hcomp, _hE12, _hE1, _hE2, hE3⟩
  have hsolvE : IsSolvable E :=
    section14_solvable_of_le_maximal hM.1 hcomp.2.1
  have hE_norm : E ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    hcomp.2.1.trans (section12_le_normalizer_msigma (M := M))
  exact
    section14_conjugate_prime_witness_into_hall
      (G := G) (R := section10Msigma M) (A := E) (H := E₃) (P := P)
      (π := section12Tau3Primes M) hsolvE hE_norm hE3 hpτ3 hPE hCP

private theorem CFSG.section14_tau3_case_preconditions
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty) :
    E₃ ≠ ⊥ ∧ ¬ section14ActsRegularlyOn E₃ (section10Msigma M) := by
  classical
  rcases hκτ3 with ⟨p, hpκ, hpτ3⟩
  obtain ⟨P, hPE3, hCP⟩ :=
    section14_tau3_witness_in_E3
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hpκ hpτ3
  have hPne : P ≠ ⊥ := section12_primeOrder_ne_bot hPE3
  have hE3ne : E₃ ≠ ⊥ := by
    intro hE3bot
    have hP_le_bot : P ≤ ⊥ := by
      intro x hxP
      have hxE3 : x ∈ E₃ := hPE3.1 hxP
      simpa [hE3bot] using hxE3
    exact hPne (le_bot_iff.mp hP_le_bot)
  exact ⟨hE3ne, section14_not_regular_of_primeOrder_centralizer_ne_bot hPE3 hCP⟩

private theorem CFSG.section14_tau3_case_prime_manner_and_centralizer
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty) :
    section14ActsInPrimeManner E (section10Msigma M) ∧
      subgroupCentralizerIn (section10Msigma M) E ≠ ⊥ := by
  classical
  rcases section14_tau3_case_preconditions
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3 with
    ⟨hE₃ne, hnotRegular14⟩
  have hnotRegular13 :
      ¬ section13ActsRegularlyOn E₃ (section10Msigma M) := by
    intro hreg
    exact hnotRegular14 (section14_actsRegularlyOn_of_section13 hreg)
  have hEprime : section14ActsInPrimeManner E (section10Msigma M) :=
    section14_actsInPrimeManner_of_section13
      (corollary_13_11_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hE₃ne hnotRegular13)
  rcases hκτ3 with ⟨p, hpκ, hpτ3⟩
  obtain ⟨P, hPE₃, hCP⟩ :=
    section14_tau3_witness_in_E3
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hpκ hpτ3
  have hPE : P ∈ section12PrimeOrderSubgroups E := by
    rcases hE with ⟨_hcomp, _hE₁₂, _hE₁, _hE₂, hE₃Hall⟩
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hPE₃) with
      ⟨hPE₃le, hPcard⟩
    exact ⟨hPE₃le.trans hE₃Hall.1, ⟨p, hPcard⟩⟩
  exact ⟨hEprime, section14_prime_manner_centralizer_ne_bot hEprime hPE hCP⟩

private theorem CFSG.section14_tau3_case_not_tau2
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty) :
    p ∉ section12Tau2Primes M := by
  classical
  intro hpτ2
  obtain ⟨_hEprime, hCE⟩ :=
    section14_tau3_case_prime_manner_and_centralizer
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM.1 hE hpτ2
  have hCAne : subgroupCentralizerIn (section10Msigma M) A ≠ ⊥ :=
    section14_subgroupCentralizerIn_antitone_ne_bot (section12_rankTwo_le hA) hCE
  have hAM : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  exact hCAne (theorem_12_5_d (G := G) (M := M) (A := A) (p := p) hM.1 hpτ2 hAM)

private theorem CFSG.section14_tau3_case_mem_kappa_of_dvd_card_E
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty)
    (hpE : p.val ∣ Nat.card E) :
    p ∈ section14KappaPrimes M := by
  classical
  obtain ⟨_hEprime, hCE⟩ :=
    section14_tau3_case_prime_manner_and_centralizer
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
  have hpTau :
      p ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M :=
    section12_prime_mem_tau_union_of_mem_E hM.1 hE.1 (by
      simpa [subgroupPrimeSet] using hpE)
  have hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
    rcases hpTau with hpτ12 | hpτ3
    · rcases hpτ12 with hpτ1 | hpτ2
      · exact Or.inl hpτ1
      · exact False.elim
          (section14_tau3_case_not_tau2
            (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
            (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3 hpτ2)
    · exact Or.inr hpτ3
  obtain ⟨P, hPE⟩ :=
    section14_exists_primeOrderSubgroupIn_of_dvd_card (G := G) (A := E) (p := p) hpE
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hPE) with ⟨hPEle, hPcard⟩
  have hPM : P ∈ section10PrimeOrderSubgroupsIn p M := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hPEle.trans hE.1.2.1, hPcard⟩
  have hCP : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ :=
    section14_subgroupCentralizerIn_antitone_ne_bot hPEle hCE
  exact ⟨hpτ13, ⟨P, hPM, hCP⟩⟩

private theorem CFSG.section14_tau3_case_E_hall_kappa
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty) :
    section12HallSubgroupIn (section14KappaPrimes M) E M := by
  classical
  have hEM : E ≤ M := hE.1.2.1
  refine ⟨hEM, ?_⟩
  refine isHallSubgroup_of (G := M) (section14KappaPrimes M) (E.subgroupOf M) ?_ ?_
  · intro p hpEsub
    have hpE : p.val ∣ Nat.card E := by
      simpa [section12_card_subgroupOf_eq hEM] using hpEsub
    exact
      section14_tau3_case_mem_kappa_of_dvd_card_E
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3 hpE
  · intro p hpκ hpidx
    have hcomp : (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
      section14_complement_to_msigma_isComplement' hE.1
    have hpMσ : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      simpa [hcomp.symm.index_eq_card] using hpidx
    have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
      (theorem_10_2_b hM.1).2
    exact (section14_kappa_subset_not_sigma (M := M) hpκ)
      (hσHall.p_in_pi_of_p_dvd_card p hpMσ)

private theorem CFSG.section14_tau3_case_K_eq_E
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty) :
    K = E := by
  exact section14_hallSubgroupIn_eq_of_le hK
    (section14_tau3_case_E_hall_kappa
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3)
    hKE

private theorem CFSG.section14_tau3_case_bot_hall
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty) :
    section12HallSubgroupIn
      ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) (⊥ : Subgroup G) M := by
  classical
  let π : Set Nat.Primes := (section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ
  refine ⟨bot_le, ?_⟩
  refine isHallSubgroup_of (G := M) π ((⊥ : Subgroup G).subgroupOf M) ?_ ?_
  · intro p hpbot
    exact False.elim (p.2.not_dvd_one (by
      simpa [Subgroup.bot_subgroupOf] using hpbot))
  · intro p hpπ hpidx
    have hpM : p.val ∣ Nat.card M := by
      simpa [Subgroup.bot_subgroupOf, Subgroup.index_bot] using hpidx
    have hEM : E ≤ M := hE.1.2.1
    have hcomp : (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
      section14_complement_to_msigma_isComplement' hE.1
    have hpProd : p.val ∣ Nat.card (section10MsigmaSubgroup M) * Nat.card E := by
      have hmul :
          (E.subgroupOf M).index * Nat.card (E.subgroupOf M) = Nat.card M :=
        Subgroup.index_mul_card (H := E.subgroupOf M)
      rw [← hmul] at hpM
      simpa [hcomp.symm.index_eq_card, section12_card_subgroupOf_eq hEM] using hpM
    have hp_not_union : p ∉ section14KappaPrimes M ∪ section10SigmaPrimes M := by
      simpa [π] using hpπ
    rcases p.2.dvd_mul.mp hpProd with hpMσ | hpE
    · have hpσ : p ∈ section10SigmaPrimes M :=
        ((theorem_10_2_b hM.1).2).p_in_pi_of_p_dvd_card p hpMσ
      exact hp_not_union (Or.inr hpσ)
    · have hpκ : p ∈ section14KappaPrimes M :=
        section14_tau3_case_mem_kappa_of_dvd_card_E
          (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3 hpE
      exact hp_not_union (Or.inl hpκ)

private theorem CFSG.section14_tau3_case_data
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty) :
    section14Proposition14_2AData M K (⊥ : Subgroup G) := by
  classical
  have hKEq : K = E :=
    section14_tau3_case_K_eq_E
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
  obtain ⟨hEprime, _hCE⟩ :=
    section14_tau3_case_prime_manner_and_centralizer
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hKEq] using hEprime
  · infer_instance
  · exact
      section14_tau3_case_bot_hall
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
  · exact section14_actsRegularlyOn_bot K
  · refine ⟨?_, ?_⟩
    · rcases hE.1 with ⟨hσM, hEM, hMsup, hdisj⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hKEq] using hEM
      · simpa using hσM
      · simpa [hKEq, sup_comm, sup_left_comm, sup_assoc] using hMsup
      · simpa [hKEq, disjoint_comm] using hdisj
    · simpa using section14_msigma_normalIn (G := G) (M := M)

private theorem CFSG.section14_tau1_case_prime_manner
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hKne : K ≠ ⊥) :
    section14ActsInPrimeManner K (section10Msigma M) := by
  classical
  have hE₁ne : E₁ ≠ ⊥ := by
    intro hE₁bot
    exact hKne (le_bot_iff.mp (by simpa [hE₁bot] using hKE₁))
  exact
    section14_actsInPrimeManner_of_le hKE₁
      (section14_actsInPrimeManner_of_section13
        (theorem_13_5 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hE₁ne))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_E1_hall_in_E
    {M E E₁₂ E₁ : Subgroup G}
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE1 : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂) :
    section12HallSubgroupIn (section12Tau1Primes M) E₁ E := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  refine ⟨hE1E12.trans hE12E, ?_⟩
  refine isHallSubgroup_of (G := E) (section12Tau1Primes M) (E₁.subgroupOf E) ?_ ?_
  · intro p hp
    have hcardE : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      section12_card_subgroupOf_eq (hE1E12.trans hE12E)
    have hcardE12 : Nat.card (E₁.subgroupOf E₁₂) = Nat.card E₁ :=
      section12_card_subgroupOf_eq hE1E12
    exact hHallE1.p_in_pi_of_p_dvd_card p (by simpa [hcardE, hcardE12] using hp)
  · intro p hpτ1 hpidx
    change p.val ∣ E₁.relIndex E at hpidx
    have hmul :
        E₁.relIndex E₁₂ * E₁₂.relIndex E = E₁.relIndex E :=
      Subgroup.relIndex_mul_relIndex E₁ E₁₂ E hE1E12 hE12E
    have hprod : p.val ∣ E₁.relIndex E₁₂ * E₁₂.relIndex E := by
      simpa [hmul] using hpidx
    rcases p.2.dvd_mul.mp hprod with hpidx1 | hpidx12
    · exact (hHallE1.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidx1)) hpτ1
    · exact (hHallE12.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidx12)) (Or.inl hpτ1)

private theorem CFSG.section14_tau1_case_E1_hall_in_M
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    section12HallSubgroupIn (section12Tau1Primes M) E₁ M := by
  classical
  have hE1HallE : section12HallSubgroupIn (section12Tau1Primes M) E₁ E :=
    section14_E1_hall_in_E
      (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      hE.2.1 hE.2.2.1
  rcases hE1HallE with ⟨hE1E, hHallE1E⟩
  refine ⟨hE1E.trans hE.1.2.1, ?_⟩
  refine isHallSubgroup_of (G := M) (section12Tau1Primes M) (E₁.subgroupOf M) ?_ ?_
  · intro p hpE1M
    have hcardM : Nat.card (E₁.subgroupOf M) = Nat.card E₁ :=
      section12_card_subgroupOf_eq (hE1E.trans hE.1.2.1)
    have hcardE : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      section12_card_subgroupOf_eq hE1E
    exact hHallE1E.p_in_pi_of_p_dvd_card p
      (by simpa [hcardM, hcardE] using hpE1M)
  · intro p hpτ1 hpidxM
    have hcomp : (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
      section14_complement_to_msigma_isComplement' hE.1
    change p.val ∣ E₁.relIndex M at hpidxM
    have hmul :
        E₁.relIndex E * E.relIndex M = E₁.relIndex M :=
      Subgroup.relIndex_mul_relIndex E₁ E M hE1E hE.1.2.1
    have hprod : p.val ∣ E₁.relIndex E * E.relIndex M := by
      simpa [hmul] using hpidxM
    rcases p.2.dvd_mul.mp hprod with hpidxE | hpidxEM
    · exact (hHallE1E.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidxE)) hpτ1
    · have hpMσ : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
        simpa [Subgroup.relIndex, hcomp.symm.index_eq_card] using hpidxEM
      have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
        (theorem_10_2_b hM.1).2
      have hpσ : p ∈ section10SigmaPrimes M :=
        hσHall.p_in_pi_of_p_dvd_card p hpMσ
      exact hpτ1.1 hpσ

omit [IsMinCE G] in
public theorem CFSG.section14_prime_dvd_card_of_primeRank_pos
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes}
    (hpos : 1 ≤ primeRank p.val R) :
    p.val ∣ Nat.card R := by
  classical
  have hTnonempty :
      {n : ℕ | ∃ A : Subgroup R, IsPGroup p.val A ∧ IsMulCommutative A ∧
        n ≤ generatorRank A}.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨⊥, IsPGroup.of_bot (p := p.val) (G := R), inferInstance, Nat.zero_le _⟩
  have hTbdd :
      BddAbove
        {n : ℕ | ∃ A : Subgroup R, IsPGroup p.val A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hsSup_mem :
      sSup {n : ℕ | ∃ A : Subgroup R, IsPGroup p.val A ∧ IsMulCommutative A ∧
        n ≤ generatorRank A} ∈
        {n : ℕ | ∃ A : Subgroup R, IsPGroup p.val A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} :=
    Nat.sSup_mem hTnonempty hTbdd
  rcases (by simpa [primeRank] using hsSup_mem) with ⟨A, hAp, _hAcomm, hgen⟩
  have hAne : A ≠ ⊥ := by
    intro hAbot
    have hAle0 : generatorRank A ≤ 0 := by
      rw [generatorRank_eq_group_rank]
      haveI : Subsingleton A := by
        rw [hAbot]
        infer_instance
      have hclosure_empty : Subgroup.closure (∅ : Set A) = ⊤ := by
        rw [Subgroup.closure_empty]
        ext x
        constructor
        · intro _hx
          simp
        · intro _hx
          change x = 1
          exact Subsingleton.elim x 1
      exact_mod_cast
        (Group.rank_le (G := A) (S := (∅ : Finset A)) (by
          simpa using hclosure_empty))
    have hAgen_pos : 1 ≤ generatorRank A := hpos.trans hgen
    omega
  haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot (H := A)).2 hAne
  have hpA : p.val ∣ Nat.card A :=
    section12_prime_dvd_card_of_nontrivial_pSubgroup
      (p := p) (B := A) hAp inferInstance
  exact hpA.trans (Subgroup.card_subgroup_dvd_card A)

private theorem CFSG.section14_tau1_case_exists_primeOrder_in_E1
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M) :
    ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p E₁ := by
  classical
  have hpM : p ∈ subgroupPrimeSet M := by
    exact section14_prime_dvd_card_of_primeRank_pos
      (R := M) (p := p) (le_of_eq hpτ1.2.2.symm)
  have hE1HallM : section12HallSubgroupIn (section12Tau1Primes M) E₁ M :=
    section14_tau1_case_E1_hall_in_M
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE
  rcases hE1HallM with ⟨hE1M, hHallE1M⟩
  have hp_not_idx : ¬ p.val ∣ (E₁.subgroupOf M).index :=
    fun hpidx => (hHallE1M.p_in_pi_of_p_dvd_index p hpidx) hpτ1
  have hmul : (E₁.subgroupOf M).index * Nat.card (E₁.subgroupOf M) = Nat.card M :=
    Subgroup.index_mul_card (H := E₁.subgroupOf M)
  have hp_prod : p.val ∣ (E₁.subgroupOf M).index * Nat.card (E₁.subgroupOf M) := by
    simpa [subgroupPrimeSet, hmul] using hpM
  have hpE1sub : p.val ∣ Nat.card (E₁.subgroupOf M) := by
    rcases p.2.dvd_mul.mp hp_prod with hpidx | hpcard
    · exact False.elim (hp_not_idx hpidx)
    · exact hpcard
  have hpE1 : p.val ∣ Nat.card E₁ := by
    simpa [section12_card_subgroupOf_eq hE1M] using hpE1sub
  exact section14_exists_primeOrderSubgroupIn_of_dvd_card (G := G) (A := E₁) (p := p) hpE1

private theorem CFSG.section14_tau1_case_tau1_subset_kappa
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁) :
    section12Tau1Primes M ⊆ section14KappaPrimes M := by
  classical
  have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM hK
  have hE₁ne : E₁ ≠ ⊥ := by
    intro hE₁bot
    exact hKne (le_bot_iff.mp (by simpa [hE₁bot] using hKE₁))
  have hE₁prime : section14ActsInPrimeManner E₁ (section10Msigma M) :=
    section14_actsInPrimeManner_of_section13
      (theorem_13_5 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hE₁ne)
  rcases hM.2 with ⟨r, hrκ⟩
  obtain ⟨Q, hQK, hCQ⟩ :=
    section14_conjugate_kappa_witness_into_hall
      (G := G) (M := M) (K := K) hM hK hrκ
  have hQE₁ : Q ∈ section12PrimeOrderSubgroups E₁ := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hQK) with
      ⟨hQKle, hQcard⟩
    exact ⟨hQKle.trans hKE₁, ⟨r, hQcard⟩⟩
  intro p hpτ1
  obtain ⟨P, hPE₁⟩ :=
    section14_tau1_case_exists_primeOrder_in_E1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hpτ1
  have hPM : P ∈ section10PrimeOrderSubgroupsIn p M := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hPE₁) with
      ⟨hPE₁le, hPcard⟩
    exact ⟨hPE₁le.trans (hE.2.2.1.1.trans (hE.2.1.1.trans hE.1.2.1)), hPcard⟩
  have hPE₁prime : P ∈ section12PrimeOrderSubgroups E₁ :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hPE₁
  have hCP : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ :=
    section14_prime_manner_centralizer_ne_bot_of_exists hE₁prime hQE₁ hCQ hPE₁prime
  exact ⟨Or.inl hpτ1, ⟨P, hPM, hCP⟩⟩

private theorem CFSG.section14_tau1_case_kappa_eq_tau1
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    section14KappaPrimes M = section12Tau1Primes M := by
  exact Set.Subset.antisymm hκτ1
    (section14_tau1_case_tau1_subset_kappa
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁)

private theorem CFSG.section14_tau1_case_K_eq_E1
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    K = E₁ := by
  classical
  have hκeqτ1 : section14KappaPrimes M = section12Tau1Primes M :=
    section14_tau1_case_kappa_eq_tau1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have hKτ1 : section12HallSubgroupIn (section12Tau1Primes M) K M := by
    simpa [hκeqτ1] using hK
  exact
    section14_hallSubgroupIn_eq_of_le hKτ1
      (section14_tau1_case_E1_hall_in_M
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hE)
      hKE₁

private theorem CFSG.section14_tau1_case_U_hall
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    section12HallSubgroupIn
      ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) (E₂ ⊔ E₃) M := by
  classical
  let π : Set Nat.Primes := (section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ
  have hκeqτ1 : section14KappaPrimes M = section12Tau1Primes M :=
    section14_tau1_case_kappa_eq_tau1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have hE3norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE).2
  have hUHallE :
      section12HallSubgroupIn
        (section12Tau2Primes M ∪ section12Tau3Primes M) (E₂ ⊔ E₃) E :=
    section12_E2_sup_E3_hall_in_E
      (M := M) (E := E) (E₁₂ := E₁₂) (E₂ := E₂) (E₃ := E₃)
      hE.2.1 hE.2.2.2.1 hE.2.2.2.2 hE3norm
  rcases hUHallE with ⟨hUE, hHallU_E⟩
  have hUM : E₂ ⊔ E₃ ≤ M := hUE.trans hE.1.2.1
  refine ⟨hUM, ?_⟩
  refine isHallSubgroup_of (G := M) π ((E₂ ⊔ E₃).subgroupOf M) ?_ ?_
  · intro p hpUsub
    have hpU : p.val ∣ Nat.card (E₂ ⊔ E₃ : Subgroup G) := by
      simpa [section12_card_subgroupOf_eq hUM] using hpUsub
    have hpτ23 : p ∈ section12Tau2Primes M ∪ section12Tau3Primes M :=
      hHallU_E.p_in_pi_of_p_dvd_card p
        (by simpa [section12_card_subgroupOf_eq hUE] using hpU)
    have hp_not_σ : p ∉ section10SigmaPrimes M := by
      rcases hpτ23 with hpτ2 | hpτ3
      · exact hpτ2.1
      · exact hpτ3.1
    have hp_not_τ1 : p ∉ section12Tau1Primes M := by
      intro hpτ1
      rcases hpτ23 with hpτ2 | hpτ3
      · have h1 : primeRank p.val M = 1 := hpτ1.2.2
        have h2 : primeRank p.val M = 2 := hpτ2.2
        omega
      · exact hpτ1.2.1 hpτ3.2.1
    have hp_not_κ : p ∉ section14KappaPrimes M := by
      simpa [hκeqτ1] using hp_not_τ1
    exact (by
      rw [show π = (section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ by rfl,
        Set.mem_compl_iff, Set.mem_union]
      exact fun hp => hp.elim hp_not_κ hp_not_σ)
  · intro p hpπ hpidx
    change p.val ∣ (E₂ ⊔ E₃).relIndex M at hpidx
    have hmul :
        (E₂ ⊔ E₃).relIndex E * E.relIndex M = (E₂ ⊔ E₃).relIndex M :=
      Subgroup.relIndex_mul_relIndex (E₂ ⊔ E₃) E M hUE hE.1.2.1
    have hpProd : p.val ∣ (E₂ ⊔ E₃).relIndex E * E.relIndex M := by
      simpa [hmul] using hpidx
    have hp_not_union : p ∉ section14KappaPrimes M ∪ section10SigmaPrimes M := by
      simpa [π] using hpπ
    rcases p.2.dvd_mul.mp hpProd with hpidxE | hpidxEM
    · have hp_not_τ23 : p ∉ section12Tau2Primes M ∪ section12Tau3Primes M :=
        hHallU_E.p_in_pi_of_p_dvd_index p
          (by simpa [Subgroup.relIndex] using hpidxE)
      have hpE : p ∈ subgroupPrimeSet E := by
        have hcardE :
            (E₂ ⊔ E₃).relIndex E * Nat.card ((E₂ ⊔ E₃).subgroupOf E) =
              Nat.card E := by
          simpa [Subgroup.relIndex] using
            (Subgroup.index_mul_card (H := (E₂ ⊔ E₃).subgroupOf E))
        have hpMul :
            p.val ∣ (E₂ ⊔ E₃).relIndex E *
              Nat.card ((E₂ ⊔ E₃).subgroupOf E) :=
          dvd_mul_of_dvd_left hpidxE _
        simpa [subgroupPrimeSet, hcardE] using hpMul
      have hpτ :
          p ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M :=
        section12_prime_mem_tau_union_of_mem_E hM.1 hE.1 hpE
      have hpτ1 : p ∈ section12Tau1Primes M := by
        rcases hpτ with hpτ12 | hpτ3
        · rcases hpτ12 with hpτ1 | hpτ2
          · exact hpτ1
          · exact False.elim (hp_not_τ23 (Or.inl hpτ2))
        · exact False.elim (hp_not_τ23 (Or.inr hpτ3))
      exact hp_not_union (Or.inl (by simpa [hκeqτ1] using hpτ1))
    · have hcomp : (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
        section14_complement_to_msigma_isComplement' hE.1
      have hpMσ : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
        simpa [Subgroup.relIndex, hcomp.symm.index_eq_card] using hpidxEM
      have hpσ : p ∈ section10SigmaPrimes M :=
        ((theorem_10_2_b hM.1).2).p_in_pi_of_p_dvd_card p hpMσ
      exact hp_not_union (Or.inr hpσ)

omit [IsMinCE G] in
public theorem CFSG.section14_exists_primeOrder_zpowers_in
    {B : Subgroup G} {x : G} (hxB : x ∈ B) (hxne : x ≠ 1) :
    ∃ q : Nat.Primes, ∃ z : G, z ∈ Subgroup.zpowers x ∧ z ∈ B ∧ z ≠ 1 ∧
      Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q B := by
  classical
  have hcard_ne_one : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    intro hcard
    have hzbot : Subgroup.zpowers x = ⊥ :=
      (Subgroup.card_eq_one (H := Subgroup.zpowers x)).1 hcard
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hzbot] using (Subgroup.mem_zpowers x)
    exact hxne (by simpa using hxbot)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨q, hqprime, hqdiv⟩
  let q' : Nat.Primes := ⟨q, hqprime⟩
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨z₀, hz₀_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers x) q hqdiv
  let z : G := z₀
  have hz_zpowx : z ∈ Subgroup.zpowers x := z₀.property
  have hzB : z ∈ B := (Subgroup.zpowers_le.2 hxB) hz_zpowx
  have hz_order : orderOf z = q := by
    simpa [z, Subgroup.orderOf_coe] using hz₀_order
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hq_one : q = 1 := by
      rw [← hz_order, hz1, orderOf_one]
    exact hqprime.ne_one hq_one
  have hX_card : Nat.card (Subgroup.zpowers z) = q'.val := by
    rw [Nat.card_zpowers]
    exact hz_order
  exact ⟨q', z, hz_zpowx, hzB, hz_ne,
    by
      simpa [section10PrimeOrderSubgroupsIn] using
        (⟨Subgroup.zpowers_le.2 hzB, hX_card⟩ :
          Subgroup.zpowers z ≤ B ∧ Nat.card (Subgroup.zpowers z) = q'.val)⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_zpowers_commute
    {x y a b : G} (hxy : Commute x y)
    (ha : a ∈ Subgroup.zpowers x) (hb : b ∈ Subgroup.zpowers y) :
    a * b = b * a := by
  rcases Subgroup.mem_zpowers_iff.mp ha with ⟨m, rfl⟩
  rcases Subgroup.mem_zpowers_iff.mp hb with ⟨n, rfl⟩
  exact ((hxy.zpow_left m).zpow_right n).eq

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_subgroupCentralizerIn_ne_bot_of_primeOrder_le
    {A R P : Subgroup G} {p : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p A)
    (hPA : P ≤ subgroupCentralizerIn A R) :
    subgroupCentralizerIn A R ≠ ⊥ := by
  intro hbot
  have hPne : P ≠ ⊥ := section12_primeOrder_ne_bot hP
  exact hPne (le_bot_iff.mp (by simpa [hbot] using hPA))

private theorem CFSG.section14_tau1_case_primeOrder_zpowers_msigma_ne_bot
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G} {x : G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M)
    (hxE₁ : x ∈ E₁) (hxne : x ≠ 1) :
    ∃ p : Nat.Primes, ∃ P : Subgroup G,
      P ∈ section10PrimeOrderSubgroupsIn p E₁ ∧ P ≤ Subgroup.zpowers x ∧
        p ∈ section12Tau1Primes M ∧
          subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ := by
  classical
  obtain ⟨p, z, hz_zpowx, hzE₁, _hzne, hP_E₁⟩ :=
    section14_exists_primeOrder_zpowers_in (B := E₁) hxE₁ hxne
  let P : Subgroup G := Subgroup.zpowers z
  have hP_zpowx : P ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hz_zpowx
  rcases hE.2.2.1 with ⟨hE₁E₁₂, hHallE₁⟩
  have hpE₁ : p.val ∣ Nat.card E₁ := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP_E₁) with
      ⟨hPE₁, hPcard⟩
    have hPcardP : Nat.card P = p.val := by simpa [P] using hPcard
    have hPE₁P : P ≤ E₁ := by simpa [P] using hPE₁
    have hpP : p.val ∣ Nat.card P := by rw [hPcardP]
    exact hpP.trans (Subgroup.card_dvd_of_le hPE₁P)
  have hpτ1 : p ∈ section12Tau1Primes M :=
    hHallE₁.p_in_pi_of_p_dvd_card p
      (by simpa [section12_card_subgroupOf_eq hE₁E₁₂] using hpE₁)
  have hE₁ne : E₁ ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : Subgroup G) := by simpa [hbot] using hxE₁
    exact hxne (by simpa using hxbot)
  have hE₁prime : section14ActsInPrimeManner E₁ (section10Msigma M) :=
    section14_actsInPrimeManner_of_section13
      (theorem_13_5 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hE₁ne)
  have hκeqτ1 : section14KappaPrimes M = section12Tau1Primes M :=
    section14_tau1_case_kappa_eq_tau1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have hpκ : p ∈ section14KappaPrimes M := by
    simpa [hκeqτ1] using hpτ1
  obtain ⟨Q, hQK, hCQ⟩ :=
    section14_conjugate_kappa_witness_into_hall
      (G := G) (M := M) (K := K) hM hK hpκ
  have hQE₁ : Q ∈ section12PrimeOrderSubgroups E₁ := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hQK) with ⟨hQKle, hQcard⟩
    exact ⟨hQKle.trans hKE₁, ⟨p, hQcard⟩⟩
  have hPE₁ : P ∈ section12PrimeOrderSubgroups E₁ :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn (by simpa [P] using hP_E₁)
  have hCP : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ :=
    section14_prime_manner_centralizer_ne_bot_of_exists hE₁prime hQE₁ hCQ hPE₁
  exact ⟨p, P, by simpa [P] using hP_E₁, hP_zpowx, hpτ1, hCP⟩

private theorem CFSG.section14_tau1_case_E1_regular_on_E3
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    section14ActsRegularlyOn E₁ E₃ := by
  classical
  have hE3norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE).2
  have hE₁E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
  have hnorm : E₁ ≤ Subgroup.normalizer (E₃ : Set G) :=
    hE₁E.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hE3norm.1).1 hE3norm.2)
  by_contra hnotRegular
  have hnotRegular13 : ¬ section13ActsRegularlyOn E₁ E₃ := by
    intro hreg13
    exact hnotRegular (section14_actsRegularlyOn_of_section13 hreg13)
  have hE₁ne : E₁ ≠ ⊥ := by
    intro hE₁bot
    exact (section14_hall_kappa_ne_bot (G := G) hM hK)
      (le_bot_iff.mp (by simpa [hE₁bot] using hKE₁))
  have hE3ne : E₃ ≠ ⊥ := by
    intro hE3bot
    apply hnotRegular
    refine ⟨hnorm, ?_⟩
    intro x _hx _hxne
    apply le_bot_iff.mp
    intro y hy
    have hyE3 : y ∈ E₃ := by simpa [elementCentralizerIn] using hy.1
    simpa [hE3bot] using hyE3
  have hprime13 :
      section13ActsPrimeManner (E₁ ⊔ E₃) (section10Msigma M) :=
    lemma_13_7 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hE₁ne hnotRegular13
  have hprime14 : section14ActsInPrimeManner (E₁ ⊔ E₃) (section10Msigma M) :=
    section14_actsInPrimeManner_of_section13 hprime13
  have hcardE3_ne_one : Nat.card E₃ ≠ 1 := by
    intro hcard
    exact hE3ne ((Subgroup.card_eq_one (H := E₃)).1 hcard)
  rcases Nat.exists_prime_and_dvd hcardE3_ne_one with ⟨q, hqprime, hqE3⟩
  let q' : Nat.Primes := ⟨q, hqprime⟩
  obtain ⟨P, hPE3⟩ :=
    section14_exists_primeOrderSubgroupIn_of_dvd_card (G := G) (A := E₃) (p := q') hqE3
  rcases hE.2.2.2.2 with ⟨hE3E, hHallE3⟩
  have hqτ3 : q' ∈ section12Tau3Primes M :=
    hHallE3.p_in_pi_of_p_dvd_card q'
      (by simpa [section12_card_subgroupOf_eq hE3E, q'] using hqE3)
  rcases hM.2 with ⟨r, hrκ⟩
  obtain ⟨Q, hQK, hCQ⟩ :=
    section14_conjugate_kappa_witness_into_hall
      (G := G) (M := M) (K := K) hM hK hrκ
  have hQsup : Q ∈ section12PrimeOrderSubgroups (E₁ ⊔ E₃) := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hQK) with ⟨hQKle, hQcard⟩
    exact ⟨hQKle.trans (hKE₁.trans le_sup_left), ⟨r, hQcard⟩⟩
  have hPsup : P ∈ section12PrimeOrderSubgroups (E₁ ⊔ E₃) := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hPE3) with ⟨hPE3le, hPcard⟩
    exact ⟨hPE3le.trans le_sup_right, ⟨q', hPcard⟩⟩
  have hCP : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ :=
    section14_prime_manner_centralizer_ne_bot_of_exists hprime14 hQsup hCQ hPsup
  have hPM : P ∈ section10PrimeOrderSubgroupsIn q' M := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hPE3) with ⟨hPE3le, hPcard⟩
    exact ⟨hPE3le.trans (hE3E.trans hE.1.2.1), hPcard⟩
  have hqκ : q' ∈ section14KappaPrimes M :=
    ⟨Or.inr hqτ3, ⟨P, hPM, hCP⟩⟩
  have hqτ1 : q' ∈ section12Tau1Primes M := hκτ1 hqκ
  exact hqτ1.2.1 hqτ3.2.1

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_subgroupCentralizerIn_eq_bot_of_regular
    {X R : Subgroup G}
    (hXne : X ≠ ⊥)
    (hreg : section14ActsRegularlyOn X R) :
    subgroupCentralizerIn R X = ⊥ := by
  classical
  apply le_bot_iff.mp
  intro y hy
  haveI : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot (H := X)).2 hXne
  obtain ⟨xX, hxXne⟩ := exists_ne (1 : X)
  let x : G := xX
  have hxX : x ∈ X := xX.property
  have hxne : x ≠ 1 := by
    intro hx
    exact hxXne (Subtype.ext hx)
  have hyElem : y ∈ elementCentralizerIn R x := by
    refine ⟨hy.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr <| by
      exact (Subgroup.mem_centralizer_iff.mp hy.2 x hxX).symm
  simpa [hreg.2 x hxX hxne] using hyElem

private theorem CFSG.section14_tau1_case_U_regular
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    section14ActsRegularlyOn K (E₂ ⊔ E₃) := by
  classical
  let U : Subgroup G := E₂ ⊔ E₃
  have hK_eq_E₁ : K = E₁ :=
    section14_tau1_case_K_eq_E1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE
  have hUnormE : section10NormalIn U E := by
    simpa [U] using h12.2.2.1
  have hE₁E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
  have hnormE₁U : E₁ ≤ Subgroup.normalizer (U : Set G) :=
    hE₁E.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hUnormE.1).1 hUnormE.2)
  refine ⟨by simpa [hK_eq_E₁, U] using hnormE₁U, ?_⟩
  intro x hxK hxne
  have hxE₁ : x ∈ E₁ := by simpa [hK_eq_E₁] using hxK
  by_contra hCne
  let C : Subgroup G := elementCentralizerIn U x
  have hCne' : C ≠ ⊥ := by simpa [C] using hCne
  haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot (H := C)).2 hCne'
  obtain ⟨yC, hyCne⟩ := exists_ne (1 : C)
  let y : G := yC
  have hyC : y ∈ C := yC.property
  have hyne : y ≠ 1 := by
    intro hy
    exact hyCne (Subtype.ext hy)
  obtain ⟨q, z, _hz_zpowy, _hzC, _hzne, hQ_C⟩ :=
    section14_exists_primeOrder_zpowers_in (B := C) hyC hyne
  let Q : Subgroup G := Subgroup.zpowers z
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hQ_C) with
    ⟨hQC_raw, hQcard_raw⟩
  have hQC : Q ≤ C := by simpa [Q] using hQC_raw
  have hQcard : Nat.card Q = q.val := by simpa [Q] using hQcard_raw
  have hQU : Q ≤ U := hQC.trans inf_le_left
  have hQcentx : Q ≤ Subgroup.centralizer ({x} : Set G) := hQC.trans inf_le_right
  have hqU : q.val ∣ Nat.card U := by
    have hqQ : q.val ∣ Nat.card Q := by rw [hQcard]
    exact hqQ.trans (Subgroup.card_dvd_of_le hQU)
  have hE3norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE).2
  have hUHallE :
      section12HallSubgroupIn
        (section12Tau2Primes M ∪ section12Tau3Primes M) U E := by
    simpa [U] using
      section12_E2_sup_E3_hall_in_E
        (M := M) (E := E) (E₁₂ := E₁₂) (E₂ := E₂) (E₃ := E₃)
        hE.2.1 hE.2.2.2.1 hE.2.2.2.2 hE3norm
  rcases hUHallE with ⟨hUE, hHallU_E⟩
  have hqτ23 : q ∈ section12Tau2Primes M ∪ section12Tau3Primes M :=
    hHallU_E.p_in_pi_of_p_dvd_card q
      (by simpa [U, section12_card_subgroupOf_eq hUE] using hqU)
  obtain ⟨p, P, hP_E₁, hP_zpowx, hpτ1, hCP⟩ :=
    section14_tau1_case_primeOrder_zpowers_msigma_ne_bot
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1 hxE₁ hxne
  have hP_E : P ∈ section10PrimeOrderSubgroupsIn p E := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP_E₁) with ⟨hPE₁, hPcard⟩
    exact ⟨hPE₁.trans hE₁E, hPcard⟩
  rcases hqτ23 with hqτ2 | hqτ3
  · obtain ⟨A, hA⟩ :=
      section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM.1 hE hqτ2
    have hQ_E : Q ∈ section10PrimeOrderSubgroupsIn q E := by
      exact ⟨hQU.trans hUE, hQcard⟩
    have hQ_A : Q ∈ section10PrimeOrderSubgroupsIn q A := by
      have hEq :=
        (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
          hM.1 hE hqτ2 hA).2
      simpa [hEq] using hQ_E
    have hQ_le_CAP : Q ≤ subgroupCentralizerIn A P := by
      intro w hwQ
      refine ⟨hQ_A.1 hwQ, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro a haP
      have hxw : Commute x w :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hQcentx hwQ)).symm
      exact section14_zpowers_commute hxw (hP_zpowx haP) (Subgroup.mem_zpowers w)
    have hCAP : subgroupCentralizerIn A P ≠ ⊥ :=
      section14_subgroupCentralizerIn_ne_bot_of_primeOrder_le hQ_A hQ_le_CAP
    exact hCP
      (lemma_13_12 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (A := A)
        (p := p) (q := q) hM.1 hE hpτ1 hP_E hqτ2 hA hCAP)
  · have hQ_E : Q ≤ E := hQU.trans hUE
    have hQ_E_sub_p : IsPGroup q.val (Q.subgroupOf E) := by
      refine IsPGroup.of_card (p := q.val) (G := Q.subgroupOf E) (n := 1) ?_
      have hcard : Nat.card (Q.subgroupOf E) = Nat.card Q :=
        section12_card_subgroupOf_eq hQ_E
      simp [hcard, hQcard, pow_one]
    haveI : (E₃.subgroupOf E).Normal := hE3norm.2
    have hQsub_le_E3sub : Q.subgroupOf E ≤ E₃.subgroupOf E :=
      section12_pSubgroup_le_normal_hall_of_prime_mem
        (R := E) (π := section12Tau3Primes M) (H := E₃.subgroupOf E)
        (A := Q.subgroupOf E) hE.2.2.2.2.2 hqτ3 hQ_E_sub_p
    have hQ_E3 : Q ≤ E₃ := by
      intro w hwQ
      let wE : E := ⟨w, hQ_E hwQ⟩
      have hwSub : wE ∈ Q.subgroupOf E := by
        simpa [wE, Subgroup.mem_subgroupOf] using hwQ
      have hwE3sub : wE ∈ E₃.subgroupOf E := hQsub_le_E3sub hwSub
      simpa [wE, Subgroup.mem_subgroupOf] using hwE3sub
    have hregE3 :=
      section14_tau1_case_E1_regular_on_E3
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
    have hQ_le_CE3 : Q ≤ elementCentralizerIn E₃ x := by
      intro w hwQ
      exact ⟨hQ_E3 hwQ, hQcentx hwQ⟩
    have hQ_E3_prime : Q ∈ section10PrimeOrderSubgroupsIn q E₃ := by
      exact ⟨hQ_E3, hQcard⟩
    have hQne : Q ≠ ⊥ := section12_primeOrder_ne_bot hQ_E3_prime
    exact hQne (le_bot_iff.mp (by
      simpa [hregE3.2 x hxE₁ hxne] using hQ_le_CE3))


private theorem CFSG.section14_tau1_case_U_abelian
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    IsMulCommutative (E₂ ⊔ E₃ : Subgroup G) := by
  classical
  let U : Subgroup G := E₂ ⊔ E₃
  have hK_eq_E₁ : K = E₁ :=
    section14_tau1_case_K_eq_E1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have hUreg : section14ActsRegularlyOn K U := by
    simpa [U] using
      section14_tau1_case_U_regular
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have hCbot : subgroupCentralizerIn U K = ⊥ :=
    section14_subgroupCentralizerIn_eq_bot_of_regular
      (section14_hall_kappa_ne_bot (G := G) hM hK) hUreg
  have hUHallM :
      section12HallSubgroupIn
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M := by
    simpa [U] using
      section14_tau1_case_U_hall
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  rcases hK with ⟨hKM, hHallK⟩
  rcases hUHallM with ⟨hUM, hHallU⟩
  have hcop : Nat.Coprime (Nat.card K) (Nat.card U) := by
    refine Nat.coprime_of_dvd ?_
    intro q hqprime hqK hqU
    let q' : Nat.Primes := ⟨q, hqprime⟩
    have hqκ : q' ∈ section14KappaPrimes M :=
      hHallK.p_in_pi_of_p_dvd_card q'
        (by simpa [section12_card_subgroupOf_eq hKM, q'] using hqK)
    have hqπ : q' ∈ (section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ :=
      hHallU.p_in_pi_of_p_dvd_card q'
        (by simpa [section12_card_subgroupOf_eq hUM, q'] using hqU)
    exact hqπ (Or.inl hqκ)
  have hsolvU : IsSolvable U :=
    section14_solvable_of_le_maximal hM.1 hUM
  have hU_le_comm : U ≤ ⁅U, K⁆ :=
    section8_le_commutator_of_subgroupCentralizerIn_eq_bot
      (Y := U) (R := K) hsolvU hUreg.1 hcop hCbot
  have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE
  have hUE : U ≤ E := by simpa [U] using h12.2.2.1.1
  have hKE : K ≤ E := by
    have hE₁E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
    simpa [hK_eq_E₁] using hE₁E
  have hcomm_le_der : ⁅U, K⁆ ≤ ambientDerivedSubgroup E := by
    have hcomm_le : ⁅U, K⁆ ≤ ⁅E, E⁆ :=
      Subgroup.commutator_mono hUE hKE
    simpa [section12_ambientDerivedSubgroup_eq_commutator] using hcomm_le
  have hU_le_der : U ≤ ambientDerivedSubgroup E :=
    hU_le_comm.trans hcomm_le_der
  have hDer_comm : IsMulCommutative (ambientDerivedSubgroup E) :=
    (corollary_12_10_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE).2
  exact section14_isMulCommutative_of_le hDer_comm (by simpa [U] using hU_le_der)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_msigma_sup_normalIn_of_complement_normal
    {M E U : Subgroup G}
    (hcomp : section12ComplementToMsigma M E)
    (hUnorm : section10NormalIn U E) :
    section10NormalIn (section10Msigma M ⊔ U) M := by
  classical
  let S : Subgroup M := section10MsigmaSubgroup M
  let Ec : Subgroup M := E.subgroupOf M
  let Uc : Subgroup M := U.subgroupOf M
  let N : Subgroup M := S ⊔ Uc
  have hUM : U ≤ M := hUnorm.1.trans hcomp.2.1
  have hcomp' : Ec.IsComplement' S :=
    section14_complement_to_msigma_isComplement' hcomp
  have hE_norm_U : E ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUnorm.1).1 hUnorm.2
  haveI : S.Normal := by
    simpa [S, section14_msigma_subgroupOf_eq] using
      (section14_msigma_normalIn (G := G) (M := M)).2
  have hEc_norm_S : Ec ≤ Subgroup.normalizer (S : Set M) := by
    simpa [S] using (Subgroup.le_normalizer_of_normal (H := S))
  have hEc_norm_Uc : Ec ≤ Subgroup.normalizer (Uc : Set M) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      have heE : (e : G) ∈ E := by
        simpa [Ec, Subgroup.mem_subgroupOf] using he
      have huU : (u : G) ∈ U := by
        simpa [Uc, Subgroup.mem_subgroupOf] using hu
      have hconj : (e : G) * (u : G) * (e : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hE_norm_U heE) (u : G)).1 huU
      simpa [Uc, Subgroup.mem_subgroupOf] using hconj
    · intro hu
      have heE : (e : G) ∈ E := by
        simpa [Ec, Subgroup.mem_subgroupOf] using he
      have hconj : (e : G) * (u : G) * (e : G)⁻¹ ∈ U := by
        simpa [Uc, Subgroup.mem_subgroupOf] using hu
      have huU : (u : G) ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hE_norm_U heE) (u : G)).2 hconj
      simpa [Uc, Subgroup.mem_subgroupOf] using huU
  have hS_norm_N : S ≤ Subgroup.normalizer (N : Set M) :=
    le_sup_left.trans (Subgroup.le_normalizer (H := N))
  have hEc_norm_N : Ec ≤ Subgroup.normalizer (N : Set M) := by
    refine subgroup_le_normalizer_of_conj_mem N Ec ?_
    intro e x hxN
    haveI : S.Normal := by
      simpa [S, section14_msigma_subgroupOf_eq] using
        (section14_msigma_normalIn (G := G) (M := M)).2
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := S) (t := Uc)).1 hxN with
      ⟨s, hsS, u, huUc, hsu⟩
    have hesS : e * s * e⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hEc_norm_S e.property) s).1 hsS
    have heuU : e * u * e⁻¹ ∈ Uc :=
      (Subgroup.mem_normalizer_iff.mp (hEc_norm_Uc e.property) u).1 huUc
    change e * x * e⁻¹ ∈ N
    rw [← hsu]
    have he_inv : (↑(e⁻¹) : M) = (e : M)⁻¹ := by
      simp
    have hmul : e * (s * u) * e⁻¹ = (e * s * e⁻¹) * (e * u * e⁻¹) := by
      rw [he_inv]
      group
    rw [hmul]
    exact N.mul_mem ((show S ≤ N from le_sup_left) hesS)
      ((show Uc ≤ N from le_sup_right) heuU)
  have htop_norm : (⊤ : Subgroup M) ≤ Subgroup.normalizer (N : Set M) := by
    rw [← hcomp'.symm.sup_eq_top]
    exact sup_le hS_norm_N hEc_norm_N
  have hN_normal : N.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop_norm)
  refine ⟨sup_le (section14_msigma_le M) hUM, ?_⟩
  have hsig_sub_eq : (section10Msigma M).subgroupOf M = S := by
    simpa [S] using section14_msigma_subgroupOf_eq (G := G) (M := M)
  have hsub_eq : (section10Msigma M ⊔ U).subgroupOf M = N := by
    calc
      (section10Msigma M ⊔ U).subgroupOf M =
          (section10Msigma M).subgroupOf M ⊔ U.subgroupOf M := by
        exact
          Subgroup.subgroupOf_sup (A := section10Msigma M) (A' := U) (B := M)
            (section14_msigma_le M) hUM
      _ = N := by
        simp [N, S, Uc, hsig_sub_eq]
  simpa [hsub_eq] using hN_normal

private theorem CFSG.section14_E1_disjoint_E2_sup_E3
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    Disjoint E₁ (E₂ ⊔ E₃) := by
  classical
  let U : Subgroup G := E₂ ⊔ E₃
  have hE1HallE : section12HallSubgroupIn (section12Tau1Primes M) E₁ E :=
    section14_E1_hall_in_E
      (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) hE.2.1 hE.2.2.1
  have hE3norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
  have hUHallE :
      section12HallSubgroupIn
        (section12Tau2Primes M ∪ section12Tau3Primes M) U E := by
    simpa [U] using
      section12_E2_sup_E3_hall_in_E
        (M := M) (E := E) (E₁₂ := E₁₂) (E₂ := E₂) (E₃ := E₃)
        hE.2.1 hE.2.2.2.1 hE.2.2.2.2 hE3norm
  rcases hE1HallE with ⟨hE1E, hHallE1⟩
  rcases hUHallE with ⟨hUE, hHallU⟩
  have hInf_bot : E₁ ⊓ U = ⊥ := by
    apply Subgroup.card_eq_one.mp
    apply section12_card_eq_one_of_no_prime_dvd
    intro p hpdiv
    have hpE1 : p.val ∣ Nat.card E₁ :=
      hpdiv.trans (Subgroup.card_dvd_of_le inf_le_left)
    have hpE1sub : p.val ∣ Nat.card (E₁.subgroupOf E) := by
      simpa [section12_card_subgroupOf_eq hE1E] using hpE1
    have hpτ1 : p ∈ section12Tau1Primes M :=
      hHallE1.p_in_pi_of_p_dvd_card p hpE1sub
    have hpU : p.val ∣ Nat.card U :=
      hpdiv.trans (Subgroup.card_dvd_of_le inf_le_right)
    have hpUsub : p.val ∣ Nat.card (U.subgroupOf E) := by
      simpa [section12_card_subgroupOf_eq hUE] using hpU
    have hpτ23 : p ∈ section12Tau2Primes M ∪ section12Tau3Primes M :=
      hHallU.p_in_pi_of_p_dvd_card p hpUsub
    rcases hpτ23 with hpτ2 | hpτ3
    · have h1 : primeRank p.val M = 1 := hpτ1.2.2
      have h2 : primeRank p.val M = 2 := hpτ2.2
      omega
    · exact hpτ1.2.1 hpτ3.2.1
  rw [Subgroup.disjoint_def]
  intro x hxE1 hxU
  have hxInf : x ∈ E₁ ⊓ U := ⟨hxE1, hxU⟩
  have hxBot : x ∈ (⊥ : Subgroup G) := by
    simpa [hInf_bot] using hxInf
  simpa using hxBot

private theorem CFSG.section14_tau1_case_normal_complement
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    section14NormalComplementIn M K ((E₂ ⊔ E₃) ⊔ section10Msigma M) := by
  classical
  let U : Subgroup G := E₂ ⊔ E₃
  let N : Subgroup G := U ⊔ section10Msigma M
  have hK_eq_E₁ : K = E₁ :=
    section14_tau1_case_K_eq_E1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE
  have hUnormE : section10NormalIn U E := by
    simpa [U] using h12.2.2.1
  have hUE : U ≤ E := hUnormE.1
  have hUM : U ≤ M := hUE.trans hE.1.2.1
  have hNM : N ≤ M := by
    simpa [N] using sup_le hUM (section14_msigma_le M)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have hE1M : E₁ ≤ M := hE.2.2.1.1.trans (hE.2.1.1.trans hE.1.2.1)
      simpa [hK_eq_E₁] using hE1M
    · exact hNM
    · calc
        M = section10Msigma M ⊔ E := hE.1.2.2.1
        _ = section10Msigma M ⊔ (E₁ ⊔ U) := by
          have hE_eq : E = E₁ ⊔ U := by
            simpa [U, sup_assoc] using h12.1
          rw [hE_eq]
        _ = K ⊔ N := by
          simp [N, U, hK_eq_E₁, sup_left_comm, sup_comm]
    · rw [Subgroup.disjoint_def]
      intro x hxK hxN
      have hxE₁ : x ∈ E₁ := by
        simpa [hK_eq_E₁] using hxK
      have hxE : x ∈ E := hE.2.2.1.1.trans hE.2.1.1 hxE₁
      have hxN' : x ∈ N := by
        simpa [N] using hxN
      have hσN : section10Msigma M ≤ N := by
        simp [N]
      have hUN : U ≤ N := by
        simp [N]
      have hN_norm_σ : N ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
        hNM.trans (section12_le_normalizer_msigma (M := M))
      haveI : ((section10Msigma M).subgroupOf N).Normal := by
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer hσN).2 hN_norm_σ
      let xN : N := ⟨x, hxN'⟩
      have htop : U.subgroupOf N ⊔ (section10Msigma M).subgroupOf N = ⊤ := by
        calc
          U.subgroupOf N ⊔ (section10Msigma M).subgroupOf N =
              (U ⊔ section10Msigma M).subgroupOf N := by
            symm
            exact Subgroup.subgroupOf_sup
              (A := U) (A' := section10Msigma M) (B := N) hUN hσN
          _ = ⊤ := by
            exact Subgroup.subgroupOf_eq_top.mpr (by simp [N])
      have hxTop : xN ∈ U.subgroupOf N ⊔ (section10Msigma M).subgroupOf N := by
        simp [htop]
      rcases (Subgroup.mem_sup_of_normal_right
          (s := U.subgroupOf N) (t := (section10Msigma M).subgroupOf N)
          (x := xN)).1 hxTop with
        ⟨uN, huU, sN, hsσ, hus⟩
      let u : G := uN
      let s : G := sN
      have huU' : u ∈ U := by
        simpa [u, Subgroup.mem_subgroupOf] using huU
      have hsσ' : s ∈ section10Msigma M := by
        simpa [s, Subgroup.mem_subgroupOf] using hsσ
      have hus_eq : u * s = x := by
        simpa [u, s, xN] using congrArg (fun y : N => (y : G)) hus
      have hsE : s ∈ E := by
        have hs_eq : s = u⁻¹ * x := by
          rw [← hus_eq]
          simp
        rw [hs_eq]
        exact E.mul_mem (E.inv_mem (hUE huU')) hxE
      have hsBot : s ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hE.1.2.2.2 hsσ' hsE
      have hs_one : s = 1 := by
        simpa using hsBot
      have hxU : x ∈ U := by
        have hx_eq : x = u := by
          rw [← hus_eq, hs_one, mul_one]
        simpa [hx_eq] using huU'
      have hE1U_disj : Disjoint E₁ U := by
        simpa [U] using
          section14_E1_disjoint_E2_sup_E3
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
            (E₂ := E₂) (E₃ := E₃) hM.1 hE
      exact Subgroup.disjoint_def.mp hE1U_disj hxE₁ hxU
  · have hnormal : section10NormalIn (section10Msigma M ⊔ U) M :=
      section14_msigma_sup_normalIn_of_complement_normal
        (G := G) (M := M) (E := E) (U := U) hE.1 hUnormE
    simpa [N, U, sup_comm] using hnormal

public theorem CFSG.section14_tau1_case_data
    {M K E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    section14Proposition14_2AData M K (E₂ ⊔ E₃) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      section14_tau1_case_prime_manner
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hE hKE₁
        (section14_hall_kappa_ne_bot (G := G) hM hK)
  · exact
      section14_tau1_case_U_abelian
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  · exact
      section14_tau1_case_U_hall
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  · exact
      section14_tau1_case_U_regular
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  · exact
      section14_tau1_case_normal_complement
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1

private theorem CFSG.section14_tau1_case
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M) :
    ∃ U : Subgroup G, section14Proposition14_2AData M K U := by
  obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, _hKE, hKE₁⟩ :=
    section14_exists_EData_with_kappa_in_E1_of_tau1
      (G := G) (M := M) (K := K) hM hK hκτ1
  exact ⟨E₂ ⊔ E₃,
    section14_tau1_case_data
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1⟩

/-- Proposition 14.2(a): a Hall `κ(M)`-subgroup has prime action on `M_σ`
and a regular abelian Hall complement `U`. -/
public theorem CFSG.proposition_14_2_a
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∃ U : Subgroup G, section14Proposition14_2AData M K U := by
  classical
  by_cases hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty
  · obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, hKE⟩ :=
      section14_exists_EData_containing_hall_kappa
        (G := G) (M := M) (K := K) hM hK
    exact ⟨⊥,
      section14_tau3_case_data
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3⟩
  · have hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M :=
      section14_kappa_subset_tau1_of_not_inter_tau3 hκτ3
    exact section14_tau1_case (G := G) (M := M) (K := K) hM hK hκτ1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_b1_kstar_le_centralizer
    {M K X : Subgroup G}
    (hXK : X ≤ K) :
    section14KStar M K ≤ subgroupCentralizerIn (section10Msigma M) X := by
  intro y hy
  refine ⟨hy.1, ?_⟩
  change y ∈ Subgroup.centralizer (X : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hxX
  exact Subgroup.mem_centralizer_iff.mp hy.2 x (hXK hxX)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_b1_centralizer_eq_kstar_of_prime_manner
    {M K X : Subgroup G}
    (hprime : section14ActsInPrimeManner K (section10Msigma M))
    (hX : X ∈ section12PrimeOrderSubgroups K) :
    subgroupCentralizerIn (section10Msigma M) X = section14KStar M K := by
  apply le_antisymm
  · exact hprime.2 X hX
  · exact section14_b1_kstar_le_centralizer (M := M) (K := K) (X := X) hX.1

private theorem CFSG.section14_b1_tau3_case_normalIn
    {M K E E₁₂ E₁ E₂ E₃ X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty)
    (hX : X ∈ section12PrimeOrderSubgroups K) :
    section10NormalIn X K := by
  classical
  have hKEq : K = E :=
    section14_tau3_case_K_eq_E
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
  rcases section14_tau3_case_preconditions
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3 with
    ⟨hE₃ne, hnotRegular14⟩
  have hnotRegular13 :
      ¬ section13ActsRegularlyOn E₃ (section10Msigma M) := by
    intro hreg
    exact hnotRegular14 (section14_actsRegularlyOn_of_section13 hreg)
  have hXE : X ∈ section12PrimeOrderSubgroups E := by
    simpa [hKEq] using hX
  have hnormE : section10NormalIn X E :=
    corollary_13_11_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hE₃ne hnotRegular13
      X hXE
  simpa [hKEq] using hnormE

private theorem CFSG.section14_b1_tau1_case_normalIn
    {M K E E₁₂ E₁ E₂ E₃ X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M)
    (hX : X ∈ section12PrimeOrderSubgroups K) :
    section10NormalIn X K := by
  classical
  have hKEq : K = E₁ :=
    section14_tau1_case_K_eq_E1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have hE₁cyc : IsCyclic E₁ :=
    (lemma_12_1_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE).1
  let Xsub : Subgroup E₁ := X.subgroupOf E₁
  have hXchar : Xsub.Characteristic := by
    letI : IsCyclic E₁ := hE₁cyc
    exact section12_subgroup_characteristic_of_cyclic Xsub
  have hXnormE₁ : E₁ ≤ Subgroup.normalizer (X : Set G) := by
    letI : Xsub.Characteristic := hXchar
    have hmap : Xsub.map E₁.subtype = X := by
      exact Subgroup.map_subgroupOf_eq_of_le (by simpa [hKEq] using hX.1)
    exact
      (E₁).le_normalizer.trans <| by
        simpa [hmap] using
          (section8_normalizer_map_subtype_le_of_characteristic
            (G := G) (H := E₁) (K := Xsub))
  have hXK : X ≤ K := hX.1
  refine ⟨hXK, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).2
    (by simpa [hKEq] using hXnormE₁)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_b1_primeOrder_ne_bot
    {K X : Subgroup G}
    (hX : X ∈ section12PrimeOrderSubgroups K) :
    X ≠ ⊥ := by
  rcases hX with ⟨_hXK, p, hXcard⟩
  intro hXbot
  have hcard_one : Nat.card X = 1 := by
    simp [hXbot]
  have hp_one : p.val = 1 := by
    rw [← hXcard, hcard_one]
  have hp_gt_one : 1 < p.val := p.2.one_lt
  omega

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_b1_left_eq_of_mul_eq_of_disjoint
    {U S : Subgroup G} (hdisj : Disjoint U S)
    {a₁ b₁ a₂ b₂ : G}
    (ha₁ : a₁ ∈ U) (hb₁ : b₁ ∈ S) (ha₂ : a₂ ∈ U) (hb₂ : b₂ ∈ S)
    (hmul : a₁ * b₁ = a₂ * b₂) :
    a₁ = a₂ := by
  have hquot : a₂⁻¹ * a₁ = b₂ * b₁⁻¹ := by
    calc
      a₂⁻¹ * a₁ = (a₂⁻¹ * a₁ * b₁) * b₁⁻¹ := by group
      _ = (a₂⁻¹ * (a₁ * b₁)) * b₁⁻¹ := by group
      _ = (a₂⁻¹ * (a₂ * b₂)) * b₁⁻¹ := by rw [hmul]
      _ = b₂ * b₁⁻¹ := by group
  have hU : a₂⁻¹ * a₁ ∈ U := U.mul_mem (U.inv_mem ha₂) ha₁
  have hS : a₂⁻¹ * a₁ ∈ S := by
    rw [hquot]
    exact S.mul_mem hb₂ (S.inv_mem hb₁)
  have hbot : a₂⁻¹ * a₁ ∈ (⊥ : Subgroup G) :=
    Subgroup.disjoint_def.mp hdisj hU hS
  have hone : a₂⁻¹ * a₁ = 1 := Subgroup.mem_bot.mp hbot
  calc
    a₁ = a₂ * (a₂⁻¹ * a₁) := by group
    _ = a₂ := by rw [hone]; simp

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section14_b1_subgroupCentralizerIn_sup_eq_of_regular
    {X U S : Subgroup G}
    (hXne : X ≠ ⊥)
    (hreg : section14ActsRegularlyOn X U)
    (hXnormS : X ≤ Subgroup.normalizer (S : Set G))
    (hUnormS : U ≤ Subgroup.normalizer (S : Set G))
    (hdisj : Disjoint U S) :
    subgroupCentralizerIn (U ⊔ S) X = subgroupCentralizerIn S X := by
  classical
  apply le_antisymm
  · intro y hy
    let T : Subgroup G := U ⊔ S
    let Usub : Subgroup T := U.subgroupOf T
    let Ssub : Subgroup T := S.subgroupOf T
    haveI : Ssub.Normal := by
      simpa [T, Ssub] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := U) (N := S) hUnormS)
    let yT : T := ⟨y, hy.1⟩
    have htop : Usub ⊔ Ssub = ⊤ := by
      calc
        Usub ⊔ Ssub = (U ⊔ S).subgroupOf T := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := U) (A' := S) (B := T) le_sup_left le_sup_right
        _ = ⊤ := by
          simp [T]
    have hyTop : yT ∈ Usub ⊔ Ssub := by
      simp [htop]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := Usub) (t := Ssub) (x := yT)).1 hyTop with
      ⟨uT, huUsub, sT, hsSsub, hus⟩
    let u : G := uT
    let s : G := sT
    have huU : u ∈ U := by
      simpa [u, Usub, Subgroup.mem_subgroupOf] using huUsub
    have hsS : s ∈ S := by
      simpa [s, Ssub, Subgroup.mem_subgroupOf] using hsSsub
    have husG : u * s = y := by
      simpa [u, s, yT] using congrArg (fun z : T => (z : G)) hus
    have huC : u ∈ subgroupCentralizerIn U X := by
      refine ⟨huU, ?_⟩
      change u ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hxX
      have hxyx : x * y * x⁻¹ = y := by
        have hcomm := Subgroup.mem_centralizer_iff.mp hy.2 x hxX
        calc
          x * y * x⁻¹ = (x * y) * x⁻¹ := by group
          _ = (y * x) * x⁻¹ := by rw [hcomm]
          _ = y := by group
      have hxuU : x * u * x⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hreg.1 hxX) u).1 huU
      have hxsS : x * s * x⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hXnormS hxX) s).1 hsS
      have hdecomp : (x * u * x⁻¹) * (x * s * x⁻¹) = u * s := by
        calc
          (x * u * x⁻¹) * (x * s * x⁻¹) = x * (u * s) * x⁻¹ := by group
          _ = x * y * x⁻¹ := by rw [husG]
          _ = y := hxyx
          _ = u * s := husG.symm
      have hleft :
          x * u * x⁻¹ = u :=
        section14_b1_left_eq_of_mul_eq_of_disjoint
          (G := G) hdisj hxuU hxsS huU hsS hdecomp
      calc
        x * u = (x * u * x⁻¹) * x := by group
        _ = u * x := by rw [hleft]
    have hCUbot : subgroupCentralizerIn U X = ⊥ :=
      section14_subgroupCentralizerIn_eq_bot_of_regular hXne hreg
    have huBot : u ∈ (⊥ : Subgroup G) := by
      simpa [hCUbot] using huC
    have hu_one : u = 1 := Subgroup.mem_bot.mp huBot
    have hy_eq_s : y = s := by
      rw [← husG, hu_one, one_mul]
    exact ⟨by simpa [hy_eq_s] using hsS, by simpa [hy_eq_s] using hy.2⟩
  · intro y hy
    exact ⟨Subgroup.mem_sup_right hy.1, hy.2⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_b1_normalizer_eq_sup_centralizer_of_normal_complement
    {M K N X : Subgroup G}
    (hcomp : section14NormalComplementIn M K N)
    (hXnorm : section10NormalIn X K) :
    subgroupNormalizerIn M (X : Set G) = K ⊔ subgroupCentralizerIn N X := by
  classical
  rcases hcomp with ⟨hcompl, hNnormIn⟩
  rcases hcompl with ⟨hKM, hNM, hM_eq, hdisj⟩
  rcases hNnormIn with ⟨_hNM', hNnormal⟩
  rcases hXnorm with ⟨hXK, hXnormal⟩
  have hK_norm_X : K ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).1 hXnormal
  have hN_norm_M : M ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).1 hNnormal
  apply le_antisymm
  · intro x hx
    rcases mem_subgroupNormalizerIn.mp hx with ⟨hxNorm, hxM⟩
    let Ksub : Subgroup M := K.subgroupOf M
    let Nsub : Subgroup M := N.subgroupOf M
    haveI : Nsub.Normal := by
      simpa [Nsub] using hNnormal
    let xM : M := ⟨x, hxM⟩
    have htop : Ksub ⊔ Nsub = ⊤ := by
      calc
        Ksub ⊔ Nsub = (K ⊔ N).subgroupOf M := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := K) (A' := N) (B := M) hKM hNM
        _ = ⊤ := by
          rw [← hM_eq]
          simp
    have hxTop : xM ∈ Ksub ⊔ Nsub := by
      simp [htop]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := Ksub) (t := Nsub) (x := xM)).1 hxTop with
      ⟨kM, hkKsub, nM, hnNsub, hkn⟩
    let k : G := kM
    let n : G := nM
    have hkK : k ∈ K := by
      simpa [k, Ksub, Subgroup.mem_subgroupOf] using hkKsub
    have hnN : n ∈ N := by
      simpa [n, Nsub, Subgroup.mem_subgroupOf] using hnNsub
    have hknG : k * n = x := by
      simpa [k, n, xM] using congrArg (fun z : M => (z : G)) hkn
    have hnC : n ∈ subgroupCentralizerIn N X := by
      refine ⟨hnN, ?_⟩
      change n ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyX
      have hxyx : x * y * x⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp hxNorm y).1 hyX
      have hkInvNorm : k⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
        hK_norm_X (K.inv_mem hkK)
      have hnynX : n * y * n⁻¹ ∈ X := by
        have hconj :
            k⁻¹ * (x * y * x⁻¹) * (k⁻¹)⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp hkInvNorm (x * y * x⁻¹)).1 hxyx
        have heq : k⁻¹ * (x * y * x⁻¹) * k = n * y * n⁻¹ := by
          rw [← hknG]
          group
        simpa [heq] using hconj
      have hcommK : n * y * n⁻¹ * y⁻¹ ∈ K :=
        K.mul_mem (hXK hnynX) (K.inv_mem (hXK hyX))
      have hcommN : n * y * n⁻¹ * y⁻¹ ∈ N := by
        have hyM : y ∈ M := hKM (hXK hyX)
        have hynInvN : y * n⁻¹ * y⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp (hN_norm_M hyM) n⁻¹).1
            (N.inv_mem hnN)
        have hmem : n * (y * n⁻¹ * y⁻¹) ∈ N :=
          N.mul_mem hnN hynInvN
        simpa [mul_assoc] using hmem
      have hbot : n * y * n⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hdisj hcommK hcommN
      have hone : n * y * n⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.mp hbot
      have hcomm : n * y = y * n := by
        calc
          n * y = (n * y * n⁻¹ * y⁻¹) * y * n := by group
          _ = y * n := by rw [hone]; simp
      exact hcomm.symm
    change x ∈ K ⊔ subgroupCentralizerIn N X
    rw [← hknG]
    exact Subgroup.mul_mem_sup hkK hnC
  · apply sup_le
    · intro k hk
      exact mem_subgroupNormalizerIn.mpr ⟨hK_norm_X hk, hKM hk⟩
    · intro c hc
      exact mem_subgroupNormalizerIn.mpr
        ⟨centralizer_le_normalizer X hc.2, hNM hc.1⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section14_b1_zInternalDirectProduct_of_normal_complement
    {M K N : Subgroup G}
    (hcomp : section14NormalComplementIn M K N)
    (hσN : section10Msigma M ≤ N) :
    section14ZInternalDirectProduct M K := by
  classical
  rcases hcomp with ⟨hcompl, _hNnorm⟩
  rcases hcompl with ⟨_hKM, _hNM, _hM_eq, hdisj⟩
  have hKstarN : section14KStar M K ≤ N :=
    (inf_le_left : section14KStar M K ≤ section10Msigma M).trans hσN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_sup_left
  · exact le_sup_right
  · rfl
  · rw [Subgroup.disjoint_def]
    intro x hxK hxKstar
    exact Subgroup.disjoint_def.mp hdisj hxK (hKstarN hxKstar)
  · intro x hxK
    rw [Subgroup.mem_centralizer_iff]
    intro y hyKstar
    exact (Subgroup.mem_centralizer_iff.mp hyKstar.2 x hxK).symm

private theorem CFSG.section14_b2_le_msigma_of_prime_mem_sigma
    {Mstar X : Subgroup G} {p : Nat.Primes}
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hpσ : p ∈ section10SigmaPrimes Mstar)
    (hXMstar : X ≤ Mstar)
    (hXp : IsPGroup p.val X) :
    X ≤ section10Msigma Mstar := by
  classical
  have hXsub_p : IsPGroup p.val (X.subgroupOf Mstar) :=
    hXp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := X) (K := Mstar) hXMstar).symm
  have hXsub_le_sigma :
      X.subgroupOf Mstar ≤ section10MsigmaSubgroup Mstar :=
    section12_pSubgroup_le_normal_hall_of_prime_mem
      (R := Mstar) (π := section10SigmaPrimes Mstar)
      (H := section10MsigmaSubgroup Mstar) (A := X.subgroupOf Mstar)
      (p := p) (theorem_10_2_b (G := G) hMstar).2 hpσ hXsub_p
  intro x hx
  exact Subgroup.mem_map.mpr
    ⟨⟨x, hXMstar hx⟩,
      hXsub_le_sigma (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩

public theorem CFSG.section14_b2_prime_mem_sigma_of_primeOrder
    {M K X Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p K)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    p ∈ section10SigmaPrimes Mstar := by
  classical
  have hpκ : p ∈ section14KappaPrimes M := by
    have hpX : p.val ∣ Nat.card X := by rw [hX.2]
    have hXM : X ≤ M := hX.1.trans hK.1
    have hXsub_le_Ksub : X.subgroupOf M ≤ K.subgroupOf M := by
      intro x hx
      exact hX.1 (by simpa [Subgroup.mem_subgroupOf] using hx)
    have hcardXsub : Nat.card (X.subgroupOf M) = Nat.card X :=
      section12_card_subgroupOf_eq hXM
    have hpXsub : p.val ∣ Nat.card (X.subgroupOf M) := by
      simpa [hcardXsub] using hpX
    exact hK.2.p_in_pi_of_p_dvd_card p
      (hpXsub.trans (Subgroup.card_dvd_of_le hXsub_le_Ksub))
  have hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
    hpκ.1
  have hXsection : X ∈ section12PrimeOrderSubgroups K := by
    simpa [section12PrimeOrderSubgroups, section10PrimeOrderSubgroupsIn] using
      ⟨hX.1, ⟨p, hX.2⟩⟩
  by_cases hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty
  · obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, hKE⟩ :=
      section14_exists_EData_containing_hall_kappa
        (G := G) (M := M) (K := K) hM hK
    have hdata :
        section14Proposition14_2AData M K (⊥ : Subgroup G) :=
      section14_tau3_case_data
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
    have hXE : X ∈ section10PrimeOrderSubgroupsIn p E := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hX.1.trans hKE, hX.2⟩
    obtain ⟨Q, hQK, hCQ⟩ :=
      section14_conjugate_kappa_witness_into_hall
        (G := G) (M := M) (K := K) hM hK hpκ
    have hQsection : Q ∈ section12PrimeOrderSubgroups K :=
      section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hQK
    have hCne : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
      exact section14_prime_manner_centralizer_ne_bot_of_exists
        hdata.1 hQsection hCQ hXsection
    exact
      lemma_13_13
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := X) (p := p)
        hM.1 hE hpτ13 hXE hCne Mstar hMstar
  · have hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M :=
      section14_kappa_subset_tau1_of_not_inter_tau3 hκτ3
    obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, _hKE, hKE₁⟩ :=
      section14_exists_EData_with_kappa_in_E1_of_tau1
        (G := G) (M := M) (K := K) hM hK hκτ1
    have hdata :
        section14Proposition14_2AData M K (E₂ ⊔ E₃) :=
      section14_tau1_case_data
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
    have hXE : X ∈ section10PrimeOrderSubgroupsIn p E := by
      have hE₁E : E₁ ≤ E :=
        hE.2.2.1.1.trans hE.2.1.1
      simpa [section10PrimeOrderSubgroupsIn] using
        ⟨hX.1.trans (hKE₁.trans hE₁E), hX.2⟩
    obtain ⟨Q, hQK, hCQ⟩ :=
      section14_conjugate_kappa_witness_into_hall
        (G := G) (M := M) (K := K) hM hK hpκ
    have hQsection : Q ∈ section12PrimeOrderSubgroups K :=
      section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hQK
    have hCne : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
      exact section14_prime_manner_centralizer_ne_bot_of_exists
        hdata.1 hQsection hCQ hXsection
    exact
      lemma_13_13
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := X) (p := p)
        hM.1 hE hpτ13 hXE hCne Mstar hMstar

/-- Proposition 14.2(b1): prime-order subgroups of `K` have normalizer
`N_M(X)=N_M(K)=K×K*`. -/
public theorem CFSG.proposition_14_2_b1
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups K →
      subgroupNormalizerIn M (X : Set G) = subgroupNormalizerIn M (K : Set G) ∧
        subgroupNormalizerIn M (K : Set G) = section14Z M K ∧
          section14ZInternalDirectProduct M K := by
  classical
  intro X hX
  have hXne : X ≠ ⊥ := section14_b1_primeOrder_ne_bot (G := G) hX
  by_cases hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty
  · obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, hKE⟩ :=
      section14_exists_EData_containing_hall_kappa
        (G := G) (M := M) (K := K) hM hK
    let N : Subgroup G := section10Msigma M
    have hdata :
        section14Proposition14_2AData M K (⊥ : Subgroup G) :=
      section14_tau3_case_data
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
    have hcomp : section14NormalComplementIn M K N := by
      simpa [N] using hdata.2.2.2.2
    have hXnorm : section10NormalIn X K :=
      section14_b1_tau3_case_normalIn
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (X := X) hM hK hE hKE hκτ3 hX
    have hKnorm : section10NormalIn K K := by
      exact
        ⟨le_rfl,
          (Subgroup.normal_subgroupOf_iff_le_normalizer (le_rfl : K ≤ K)).2
            Subgroup.le_normalizer⟩
    have hNX :
        subgroupNormalizerIn M (X : Set G) = K ⊔ subgroupCentralizerIn N X :=
      section14_b1_normalizer_eq_sup_centralizer_of_normal_complement
        (G := G) (M := M) (K := K) (N := N) (X := X) hcomp hXnorm
    have hNK :
        subgroupNormalizerIn M (K : Set G) = K ⊔ subgroupCentralizerIn N K :=
      section14_b1_normalizer_eq_sup_centralizer_of_normal_complement
        (G := G) (M := M) (K := K) (N := N) (X := K) hcomp hKnorm
    have hCX :
        subgroupCentralizerIn N X = section14KStar M K := by
      simpa [N] using
        section14_b1_centralizer_eq_kstar_of_prime_manner
          (G := G) (M := M) (K := K) (X := X) hdata.1 hX
    have hCK :
        subgroupCentralizerIn N K = section14KStar M K := by
      simp [N, section14KStar]
    have hNXeqNK : subgroupNormalizerIn M (X : Set G) = subgroupNormalizerIn M (K : Set G) := by
      rw [hNX, hNK, hCX, hCK]
    have hNKZ : subgroupNormalizerIn M (K : Set G) = section14Z M K := by
      rw [hNK, hCK, section14Z]
    have hZdp : section14ZInternalDirectProduct M K :=
      section14_b1_zInternalDirectProduct_of_normal_complement
        (G := G) (M := M) (K := K) (N := N) hcomp (by simp [N])
    exact ⟨hNXeqNK, hNKZ, hZdp⟩
  · have hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M :=
      section14_kappa_subset_tau1_of_not_inter_tau3 hκτ3
    obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, _hKE, hKE₁⟩ :=
      section14_exists_EData_with_kappa_in_E1_of_tau1
        (G := G) (M := M) (K := K) hM hK hκτ1
    let U : Subgroup G := E₂ ⊔ E₃
    let N : Subgroup G := U ⊔ section10Msigma M
    have hdata :
        section14Proposition14_2AData M K U :=
      section14_tau1_case_data
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
    have hcomp : section14NormalComplementIn M K N := by
      simpa [N, U] using hdata.2.2.2.2
    have hXnorm : section10NormalIn X K :=
      section14_b1_tau1_case_normalIn
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (X := X) hM hK hE hKE₁ hκτ1 hX
    have hKnorm : section10NormalIn K K := by
      exact
        ⟨le_rfl,
          (Subgroup.normal_subgroupOf_iff_le_normalizer (le_rfl : K ≤ K)).2
            Subgroup.le_normalizer⟩
    have hNX :
        subgroupNormalizerIn M (X : Set G) = K ⊔ subgroupCentralizerIn N X :=
      section14_b1_normalizer_eq_sup_centralizer_of_normal_complement
        (G := G) (M := M) (K := K) (N := N) (X := X) hcomp hXnorm
    have hNK :
        subgroupNormalizerIn M (K : Set G) = K ⊔ subgroupCentralizerIn N K :=
      section14_b1_normalizer_eq_sup_centralizer_of_normal_complement
        (G := G) (M := M) (K := K) (N := N) (X := K) hcomp hKnorm
    have hX_norm_σ : X ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
      hX.1.trans hdata.1.1
    have hU_norm_σ : U ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
      rcases hdata.2.2.2.2 with ⟨_hcomp, hNnorm⟩
      have hUM : U ≤ M := hdata.2.2.1.1
      exact hUM.trans (section12_le_normalizer_msigma (M := M))
    have hdisjUσ : Disjoint U (section10Msigma M) := by
      rcases hdata.2.2.2.2 with ⟨hcomp', _hNnorm⟩
      rcases hcomp' with ⟨_hKM, hNM, hM_eq, hdisjKN⟩
      have hKUdisj : Disjoint K U := by
        rw [Subgroup.disjoint_def]
        intro x hxK hxU
        have hxN : x ∈ N := by
          exact Subgroup.mem_sup_left hxU
        exact Subgroup.disjoint_def.mp hdisjKN hxK hxN
      have hK_eq_E₁ : K = E₁ :=
        section14_tau1_case_K_eq_E1
          (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
      rw [Subgroup.disjoint_def]
      intro x hxU hxσ
      have hxE : x ∈ E := by
        exact (show U ≤ E from by
          have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE
          simpa [U] using h12.2.2.1.1) hxU
      have hxbot : x ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hE.1.2.2.2 hxσ hxE
      simpa using hxbot
    have hCNX :
        subgroupCentralizerIn N X =
          subgroupCentralizerIn (section10Msigma M) X := by
      have hXreg : section14ActsRegularlyOn X U :=
        section14_actsRegularlyOn_of_le hX.1 hdata.2.2.2.1
      simpa [N] using
        section14_b1_subgroupCentralizerIn_sup_eq_of_regular
          (G := G) (X := X) (U := U) (S := section10Msigma M)
          hXne hXreg hX_norm_σ hU_norm_σ hdisjUσ
    have hCNK :
        subgroupCentralizerIn N K =
          subgroupCentralizerIn (section10Msigma M) K := by
      have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM hK
      simpa [N] using
        section14_b1_subgroupCentralizerIn_sup_eq_of_regular
          (G := G) (X := K) (U := U) (S := section10Msigma M)
          hKne hdata.2.2.2.1 hdata.1.1 hU_norm_σ hdisjUσ
    have hCX :
        subgroupCentralizerIn (section10Msigma M) X = section14KStar M K :=
      section14_b1_centralizer_eq_kstar_of_prime_manner
        (G := G) (M := M) (K := K) (X := X) hdata.1 hX
    have hCK :
        subgroupCentralizerIn (section10Msigma M) K = section14KStar M K := by
      simp [section14KStar]
    have hNXeqNK : subgroupNormalizerIn M (X : Set G) = subgroupNormalizerIn M (K : Set G) := by
      rw [hNX, hNK, hCNX, hCNK, hCX, hCK]
    have hNKZ : subgroupNormalizerIn M (K : Set G) = section14Z M K := by
      rw [hNK, hCNK, hCK, section14Z]
    have hσN : section10Msigma M ≤ N := by
      intro x hx
      exact Subgroup.mem_sup_right hx
    have hZdp : section14ZInternalDirectProduct M K :=
      section14_b1_zInternalDirectProduct_of_normal_complement
        (G := G) (M := M) (K := K) (N := N) hcomp hσN
    exact ⟨hNXeqNK, hNKZ, hZdp⟩

/-- Proposition 14.2(b2): every `X ∈ 𝓔¹(K)` lies in `(M*)_σ` for
each `M* ∈ 𝓜(N_G(X))`. -/
public theorem CFSG.proposition_14_2_b2
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups K →
      ∀ Mstar : Subgroup G,
        Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) →
          X ≤ section10Msigma Mstar := by
  classical
  intro X hX Mstar hMstar
  rcases hX with ⟨hXK, p, hXcard⟩
  have hXprime : X ∈ section10PrimeOrderSubgroupsIn p K := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXK, hXcard⟩
  have hpσstar : p ∈ section10SigmaPrimes Mstar :=
    section14_b2_prime_mem_sigma_of_primeOrder
      (G := G) (M := M) (K := K) (X := X) (Mstar := Mstar) (p := p)
      hM hK hXprime hMstar
  have hXMstar : X ≤ Mstar :=
    Subgroup.le_normalizer.trans hMstar.2
  have hXp : IsPGroup p.val X := by
    refine IsPGroup.of_card (p := p.val) (G := X) (n := 1) ?_
    simpa [pow_one] using hXcard
  exact
    section14_b2_le_msigma_of_prime_mem_sigma
      (G := G) (Mstar := Mstar) (X := X) (p := p)
      hMstar.1 hpσstar hXMstar hXp

public theorem CFSG.section14_c_kstar_ne_bot
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14KStar M K ≠ ⊥ := by
  classical
  obtain ⟨U, hdata⟩ := proposition_14_2_a (G := G) (M := M) (K := K) hM hK
  rcases hM.2 with ⟨p, hpκ⟩
  obtain ⟨P, hPK, hCP⟩ :=
    section14_conjugate_kappa_witness_into_hall
      (G := G) (M := M) (K := K) hM hK hpκ
  have hPsection : P ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hPK
  simpa [section14KStar] using
    section14_prime_manner_centralizer_ne_bot hdata.1 hPsection hCP

public theorem CFSG.section14_c_sigma_of_primeOrder_le_kstar
    {M K X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p (section14KStar M K)) :
    p ∈ section10SigmaPrimes M := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXKstar, hXcard⟩
  have hpX : p.val ∣ Nat.card X := by rw [hXcard]
  have hpMsigma : p.val ∣ Nat.card (section10Msigma M) :=
    hpX.trans (Subgroup.card_dvd_of_le (hXKstar.trans inf_le_left))
  exact ((theorem_10_2_b hM.1).1).p_in_pi_of_p_dvd_card p hpMsigma

omit [IsMinCE G] in
public theorem CFSG.section14_c_exists_primeOrderSubgroupIn_of_ne_bot
    {A : Subgroup G} (hAne : A ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p A := by
  classical
  have hcard_ne_one : Nat.card A ≠ 1 := by
    intro hcard
    exact hAne ((Subgroup.eq_bot_iff_card (H := A)).2 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdiv⟩
  obtain ⟨P, hP⟩ :=
    section14_exists_primeOrderSubgroupIn_of_dvd_card
      (G := G) (A := A) (p := ⟨p, hpprime⟩) hpdiv
  exact ⟨⟨p, hpprime⟩, P, hP⟩

private theorem CFSG.section14_c_unique_overgroups_of_primeOrder_tau1
    {M K E E₁₂ E₁ E₂ E₃ X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M)
    (hX : X ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  classical
  rcases hX with ⟨hXKstar, q, hXcard⟩
  have hK_eq_E₁ : K = E₁ :=
    section14_tau1_case_K_eq_E1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM hK
  have hqσ : q ∈ section10SigmaPrimes M :=
    section14_c_sigma_of_primeOrder_le_kstar
      (G := G) (M := M) (K := K) (X := X) (p := q) hM
      (by simpa [section10PrimeOrderSubgroupsIn] using ⟨hXKstar, hXcard⟩)
  have hXprime :
      X ∈ section10PrimeOrderSubgroupsIn q
        (subgroupCentralizerIn (section10Msigma M) K) := by
    simpa [section10PrimeOrderSubgroupsIn, section14KStar] using ⟨hXKstar, hXcard⟩
  let S : Sylow q.val (section10Msigma M) :=
    Classical.choice (Sylow.nonempty (p := q.val) (G := section10Msigma M))
  exact
      (lemma_13_6
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := K) (X := X) (q := q) S
      hM.1 hE hKne (by simp [hK_eq_E₁]) hqσ hXprime).1

private theorem CFSG.section14_c_unique_overgroups_of_primeOrder_tau3
    {M K E E₁₂ E₁ E₂ E₃ X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty)
    (hX : X ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  classical
  rcases hX with ⟨hXKstar, q, hXcard⟩
  have hK_eq_E : K = E :=
    section14_tau3_case_K_eq_E
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
  rcases section14_tau3_case_preconditions
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3 with
    ⟨hE₃ne, hnotRegular14⟩
  have hnotRegular13 :
      ¬ section13ActsRegularlyOn E₃ (section10Msigma M) := by
    intro hreg
    exact hnotRegular14 (section14_actsRegularlyOn_of_section13 hreg)
  have hE₁ne : E₁ ≠ ⊥ :=
    corollary_13_11_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hE₃ne hnotRegular13
  obtain ⟨p, P, hP_E₁⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot (G := G) (A := E₁) hE₁ne
  have hPne : P ≠ ⊥ := section12_primeOrder_ne_bot hP_E₁
  have hqσ : q ∈ section10SigmaPrimes M :=
    section14_c_sigma_of_primeOrder_le_kstar
      (G := G) (M := M) (K := K) (X := X) (p := q) hM
      (by simpa [section10PrimeOrderSubgroupsIn] using ⟨hXKstar, hXcard⟩)
  have hX_le_CMP :
      X ≤ subgroupCentralizerIn (section10Msigma M) P := by
    intro x hx
    have hxCME : x ∈ subgroupCentralizerIn (section10Msigma M) E := by
      simpa [section14KStar, hK_eq_E] using hXKstar hx
    refine ⟨hxCME.1, ?_⟩
    change x ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    exact Subgroup.mem_centralizer_iff.mp hxCME.2 y
      (hP_E₁.1.trans (hE.2.2.1.1.trans hE.2.1.1) hyP)
  have hXprime :
      X ∈ section10PrimeOrderSubgroupsIn q
        (subgroupCentralizerIn (section10Msigma M) P) := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hX_le_CMP, hXcard⟩
  let S : Sylow q.val (section10Msigma M) :=
    Classical.choice (Sylow.nonempty (p := q.val) (G := section10Msigma M))
  exact
    (lemma_13_6
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (X := X) (q := q) S
      hM.1 hE hPne hP_E₁.1 hqσ hXprime).1

private theorem CFSG.section14_c_unique_overgroups_of_primeOrder
    {M K X : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hX : X ∈ section12PrimeOrderSubgroups (section14KStar M K)) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  classical
  by_cases hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty
  · obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, hKE⟩ :=
      section14_exists_EData_containing_hall_kappa
        (G := G) (M := M) (K := K) hM hK
    exact
      section14_c_unique_overgroups_of_primeOrder_tau3
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (X := X)
        hM hK hE hKE hκτ3 hX
  · have hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M :=
      section14_kappa_subset_tau1_of_not_inter_tau3 hκτ3
    obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, _hKE, hKE₁⟩ :=
      section14_exists_EData_with_kappa_in_E1_of_tau1
        (G := G) (M := M) (K := K) hM hK hκτ1
    exact
      section14_c_unique_overgroups_of_primeOrder_tau1
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (X := X)
        hM hK hE hKE₁ hκτ1 hX

/-- Proposition 14.2(c): `K*` is nontrivial and prime-order subgroups of
`K*` have unique maximal overgroup of their centralizer. -/
public theorem CFSG.proposition_14_2_c
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section14KStar M K ≠ ⊥ ∧
      ∀ X : Subgroup G, X ∈ section12PrimeOrderSubgroups (section14KStar M K) →
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  exact
    ⟨section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM hK,
      fun X hX =>
        section14_c_unique_overgroups_of_primeOrder
          (G := G) (M := M) (K := K) (X := X) hM hK hX⟩

/-- Proposition 14.2(d): intersections with conjugates outside the stated
normalizers are trivial. -/
public theorem CFSG.proposition_14_2_d
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    (∀ g : G, g ∉ M → section14KStar M K ⊓ M.conjBy g = ⊥) ∧
      ∀ g : G, g ∈ M → g ∉ section14Z M K → K ⊓ K.conjBy g = ⊥ := by
  classical
  refine ⟨?_, ?_⟩
  · intro g hgM
    by_contra hne
    obtain ⟨p, X, hX⟩ :=
      section14_c_exists_primeOrderSubgroupIn_of_ne_bot
        (G := G) (A := section14KStar M K ⊓ M.conjBy g) hne
    have hXle : X ≤ section14KStar M K ⊓ M.conjBy g := by
      exact hX.1
    have hXcard : Nat.card X = p.val := by
      exact hX.2
    have hXleKstar : X ≤ section14KStar M K := hXle.trans inf_le_left
    have hXleMg : X ≤ M.conjBy g := hXle.trans inf_le_right
    have hXprime : X ∈ section12PrimeOrderSubgroups (section14KStar M K) := by
      exact ⟨hXleKstar, ⟨p, hXcard⟩⟩
    have hCeq :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} :=
      (proposition_14_2_c (G := G) (M := M) (K := K) hM hK).2 X hXprime
    have hpσ : p ∈ section10SigmaPrimes M :=
      section14_c_sigma_of_primeOrder_le_kstar
        (G := G) (M := M) (K := K) (X := X) (p := p) hM
        ⟨hXleKstar, hXcard⟩
    have hXp : IsPGroup p.val X := by
      refine IsPGroup.of_card (p := p.val) (G := X) (n := 1) ?_
      simpa [pow_one] using hXcard
    have hXne : X ≠ ⊥ :=
      section12_primeOrder_ne_bot ⟨hXleKstar, hXcard⟩
    have hXM : X ≤ M := hXleKstar.trans inf_le_left |>.trans (section14_msigma_le M)
    have hg_mem : g ∈ M := by
      have hCXM : Subgroup.centralizer (X : Set G) ≤ M := by
        have hMmem : M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
          rw [hCeq]
          simp
        exact hMmem.2
      have hXgInvM : X.conjBy g⁻¹ ≤ M := by
        exact section14_conjBy_inv_le_of_le_conjBy (H := X) (K := M) (g := g) hXleMg
      have hginv_mem : g⁻¹ ∈ M := by
        exact theorem_10_1_e (G := G) (M := M) (X := X) (p := p)
          hM.1 hpσ hXne hXp hXM hCXM hXgInvM
      simpa using M.inv_mem hginv_mem
    exact hgM hg_mem
  · intro g hgM hgZ
    rcases hK with ⟨hKM, hHallK⟩
    have hKfull : section12HallSubgroupIn (section14KappaPrimes M) K M := ⟨hKM, hHallK⟩
    by_contra hne
    obtain ⟨p, X, hX⟩ :=
      section14_c_exists_primeOrderSubgroupIn_of_ne_bot
        (G := G) (A := K ⊓ K.conjBy g) hne
    let _ : Fact p.val.Prime := ⟨p.2⟩
    have hXle : X ≤ K ⊓ K.conjBy g := hX.1
    have hXcard : Nat.card X = p.val := hX.2
    have hXleK : X ≤ K := hXle.trans inf_le_left
    have hXleKg : X ≤ K.conjBy g := hXle.trans inf_le_right
    have hXp : IsPGroup p.val X := by
      refine IsPGroup.of_card (p := p.val) (G := X) (n := 1) ?_
      simpa [pow_one] using hXcard
    have hXprime : X ∈ section12PrimeOrderSubgroups K := by
      exact ⟨hXleK, ⟨p, hXcard⟩⟩
    have hXinv_leK : X.conjBy g⁻¹ ≤ K :=
      section14_conjBy_inv_le_of_le_conjBy (H := X) (K := K) (g := g) hXleKg
    have hXinv_card : Nat.card (X.conjBy g⁻¹) = p.val := by
      rw [section14_card_conjBy]
      exact hXcard
    have hXinvp : IsPGroup p.val (X.conjBy g⁻¹) := by
      refine IsPGroup.of_card (p := p.val) (G := X.conjBy g⁻¹) (n := 1) ?_
      simpa [pow_one] using hXinv_card
    have hXinv_prime : X.conjBy g⁻¹ ∈ section12PrimeOrderSubgroups K := by
      exact ⟨hXinv_leK, ⟨p, hXinv_card⟩⟩
    have hKZ : IsZGroup K := section14_hall_kappa_isZGroup (M := M) (K := K) hKfull
    let Xsub : Subgroup K := X.subgroupOf K
    let Xinvsub : Subgroup K := (X.conjBy g⁻¹).subgroupOf K
    have hXsub_card : Nat.card Xsub = p.val := by
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := X) (K := K) hXleK).toEquiv).trans
        hXcard
    have hXinvsub_card : Nat.card Xinvsub = p.val := by
      exact
        (Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := X.conjBy g⁻¹) (K := K) hXinv_leK).toEquiv).trans
          hXinv_card
    have hXsub_p : IsPGroup p.val Xsub :=
      hXp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := K) hXleK).symm
    have hXinvsub_p : IsPGroup p.val Xinvsub :=
      hXinvp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X.conjBy g⁻¹) (K := K) hXinv_leK).symm
    obtain ⟨S, hXsub_le_S⟩ := IsPGroup.exists_le_sylow (G := K) (p := p.val) hXsub_p
    obtain ⟨Sinv, hXinvsub_le_Sinv⟩ :=
      IsPGroup.exists_le_sylow (G := K) (p := p.val) hXinvsub_p
    haveI : IsZGroup K := hKZ
    have hS_cyc : IsCyclic (S : Subgroup K) :=
      IsPGroup.isCyclic_of_isZGroup (G := K) (P := (S : Subgroup K)) S.isPGroup'
    have hSinv_cyc : IsCyclic (Sinv : Subgroup K) :=
      IsPGroup.isCyclic_of_isZGroup (G := K) (P := (Sinv : Subgroup K)) Sinv.isPGroup'
    obtain ⟨k, hkS⟩ := MulAction.exists_smul_eq K Sinv S
    have h_Xinvsub_k_le_S : (MulAut.conj (k : K)) • Xinvsub ≤ (S : Subgroup K) := by
      calc
        (MulAut.conj (k : K)) • Xinvsub ≤ (MulAut.conj (k : K)) • (Sinv : Subgroup K) := by
          intro x hx
          rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
          exact Set.mem_smul_set.mpr ⟨y, hXinvsub_le_Sinv hy, rfl⟩
        _ = ((k • Sinv : Sylow p.val K) : Subgroup K) := by
          rw [← Sylow.coe_subgroup_smul (g := k) (P := Sinv)]
        _ = (S : Subgroup K) := by
          simp [hkS]
    let Xinvsub_k : Subgroup K := (MulAut.conj (k : K)) • Xinvsub
    have hXinvsub_k_card : Nat.card Xinvsub_k = p.val := by
      have h_card_eq : Nat.card Xinvsub_k = Nat.card Xinvsub := by
        dsimp [Xinvsub_k]
        let e : Xinvsub ≃* ((MulAut.conj (k : K)) • Xinvsub : Subgroup K) :=
          Subgroup.equivSMul (a := MulAut.conj (k : K)) (H := Xinvsub)
        exact Nat.card_congr e.symm.toEquiv
      rw [h_card_eq, hXinvsub_card]
    have hXinvsub_k_le_S : Xinvsub_k ≤ (S : Subgroup K) := h_Xinvsub_k_le_S
    have h_eq_in_S :
        Xinvsub_k.subgroupOf (S : Subgroup K) = Xsub.subgroupOf (S : Subgroup K) := by
      letI : IsCyclic (S : Subgroup K) := hS_cyc
      have huniq :=
        section14_unique_subgroup_of_prime_order_in_cyclic
          (A := Xinvsub_k.subgroupOf (S : Subgroup K))
          (B := Xsub.subgroupOf (S : Subgroup K))
          (hA := by
            have e : Xinvsub_k.subgroupOf (S : Subgroup K) ≃* Xinvsub_k :=
              Subgroup.subgroupOfEquivOfLe (H := Xinvsub_k) (K := (S : Subgroup K)) hXinvsub_k_le_S
            exact (Nat.card_congr e.toEquiv).trans hXinvsub_k_card)
          (hB := by
            have e : Xsub.subgroupOf (S : Subgroup K) ≃* Xsub :=
              Subgroup.subgroupOfEquivOfLe (H := Xsub) (K := (S : Subgroup K)) hXsub_le_S
            exact (Nat.card_congr e.toEquiv).trans hXsub_card)
      exact huniq
    have hXinvsub_k_eq_Xsub : Xinvsub_k = Xsub := by
      calc
        Xinvsub_k = (Xinvsub_k.subgroupOf (S : Subgroup K)).map (S : Subgroup K).subtype := by
          rw [Subgroup.subgroupOf_map_subtype Xinvsub_k (S : Subgroup K)]
          exact (inf_eq_left.mpr hXinvsub_k_le_S).symm
        _ = (Xsub.subgroupOf (S : Subgroup K)).map (S : Subgroup K).subtype := by
          rw [h_eq_in_S]
        _ = Xsub := by
          rw [Subgroup.subgroupOf_map_subtype Xsub (S : Subgroup K)]
          exact inf_eq_left.mpr hXsub_le_S
    have hmap_Xsub : Xsub.map K.subtype = X := by
      calc
        Xsub.map K.subtype = (X.subgroupOf K).map K.subtype := rfl
        _ = X := by
          apply le_antisymm
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            exact Subgroup.mem_subgroupOf.mp hy
          · intro x hx
            exact Subgroup.mem_map.mpr ⟨⟨x, hXleK hx⟩, hx, rfl⟩
    have hmap_Xinvsub : Xinvsub.map K.subtype = X.conjBy g⁻¹ := by
      calc
        Xinvsub.map K.subtype = ((X.conjBy g⁻¹).subgroupOf K).map K.subtype := rfl
        _ = X.conjBy g⁻¹ := by
          apply le_antisymm
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            exact Subgroup.mem_subgroupOf.mp hy
          · intro x hx
            exact Subgroup.mem_map.mpr ⟨⟨x, hXinv_leK hx⟩, hx, rfl⟩
    have hmap_Xinvsub_k :
        Xinvsub_k.map K.subtype = (X.conjBy g⁻¹).conjBy (k : G) := by
      calc
        Xinvsub_k.map K.subtype = ((MulAut.conj (k : K)) • Xinvsub).map K.subtype := rfl
        _ = (MulAut.conj (k : G)) • (Xinvsub.map K.subtype) := by
          refine le_antisymm ?_ ?_
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            rcases Set.mem_smul_set.mp hy with ⟨z, hz, rfl⟩
            refine Set.mem_smul_set.mpr
              ⟨K.subtype z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
            simp [MulAut.conj_apply, mul_assoc]
          · intro x hx
            rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
            rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
            refine Subgroup.mem_map.mpr
              ⟨(MulAut.conj (k : K)) z, Set.mem_smul_set.mpr ⟨z, hz, rfl⟩, ?_⟩
            simp [MulAut.conj_apply, mul_assoc]
        _ = (X.conjBy g⁻¹).conjBy (k : G) := by
          rw [hmap_Xinvsub]
          rfl
    have hkg_normX : k * g⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
      apply section14_mem_normalizer_of_conjBy_eq
      calc
        X.conjBy (k * g⁻¹) = (X.conjBy g⁻¹).conjBy (k : G) := by
          rw [section11_conjBy_conjBy]
        _ = X := by
          have hEqMap : Xinvsub_k.map K.subtype = X := by
            rw [hXinvsub_k_eq_Xsub, hmap_Xsub]
          have hEqConj : (X.conjBy g⁻¹).conjBy (k : G) = Xinvsub_k.map K.subtype := by
            exact hmap_Xinvsub_k.symm
          exact hEqConj.trans hEqMap
    have hkg_memM : k * g⁻¹ ∈ M := by
      exact M.mul_mem (hKM (k : K).property) (M.inv_mem hgM)
    have hkg_memZ : k * g⁻¹ ∈ section14Z M K := by
      have hNXZ := (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hKfull X hXprime).1
      have hkg_memNX : k * g⁻¹ ∈ subgroupNormalizerIn M (X : Set G) :=
        mem_subgroupNormalizerIn.mpr ⟨hkg_normX, hkg_memM⟩
      rw [hNXZ,
        (proposition_14_2_b1 (G := G) (M := M) (K := K) hM hKfull X hXprime).2.1] at hkg_memNX
      exact hkg_memNX
    have hk_memZ : (k : G) ∈ section14Z M K := by
      exact Subgroup.mem_sup_left (k : K).property
    have hg_inv_memZ : g⁻¹ ∈ section14Z M K := by
      have hk_inv_memZ : (k : G)⁻¹ ∈ section14Z M K :=
        Subgroup.inv_mem (section14Z M K) hk_memZ
      have hmul : (k : G)⁻¹ * (k * g⁻¹) ∈ section14Z M K :=
        (section14Z M K).mul_mem hk_inv_memZ hkg_memZ
      simpa [mul_assoc] using hmul
    have hg_memZ : g ∈ section14Z M K := by
      simpa using Subgroup.inv_mem (section14Z M K) hg_inv_memZ
    exact hgZ hg_memZ

/-- Proposition 14.2(e): Sylow subgroups of `M_σ` for primes in `π(K*)`
have unique maximal overgroup and are not contained in `K*`. -/
private theorem CFSG.section14_e_unique_overgroups_of_primeOrder_tau1
    {M K E E₁₂ E₁ E₂ E₃ X : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE₁ : K ≤ E₁)
    (hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M)
    (S : Sylow q.val (section10Msigma M))
    (hX : X ∈ section10PrimeOrderSubgroupsIn q (section14KStar M K)) :
    section9MaximalSubgroupsContaining
        (section10AmbientSylowSubgroup (section10Msigma M) S) = {M} := by
  have hK_eq_E₁ : K = E₁ :=
    section14_tau1_case_K_eq_E1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE₁ hκτ1
  have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM hK
  have hqσ : q ∈ section10SigmaPrimes M :=
    section14_c_sigma_of_primeOrder_le_kstar
      (G := G) (M := M) (K := K) (X := X) (p := q) hM hX
  have hXprime :
      X ∈ section10PrimeOrderSubgroupsIn q
        (subgroupCentralizerIn (section10Msigma M) K) := by
    simpa [section10PrimeOrderSubgroupsIn, section14KStar] using hX
  exact
    (lemma_13_6
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := K) (X := X) (q := q) S
      hM.1 hE hKne (by simp [hK_eq_E₁]) hqσ hXprime).2

private theorem CFSG.section14_e_unique_overgroups_of_primeOrder_tau3
    {M K E E₁₂ E₁ E₂ E₃ X : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hKE : K ≤ E)
    (hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty)
    (S : Sylow q.val (section10Msigma M))
    (hX : X ∈ section10PrimeOrderSubgroupsIn q (section14KStar M K)) :
    section9MaximalSubgroupsContaining
        (section10AmbientSylowSubgroup (section10Msigma M) S) = {M} := by
  rcases hX with ⟨hXKstar, hXcard⟩
  have hK_eq_E : K = E :=
    section14_tau3_case_K_eq_E
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3
  rcases section14_tau3_case_preconditions
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hK hE hKE hκτ3 with
    ⟨hE₃ne, hnotRegular14⟩
  have hnotRegular13 :
      ¬ section13ActsRegularlyOn E₃ (section10Msigma M) := by
    intro hreg
    exact hnotRegular14 (section14_actsRegularlyOn_of_section13 hreg)
  have hE₁ne : E₁ ≠ ⊥ :=
    corollary_13_11_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hE₃ne hnotRegular13
  obtain ⟨p, P, hP_E₁⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot (G := G) (A := E₁) hE₁ne
  have hPne : P ≠ ⊥ := section12_primeOrder_ne_bot hP_E₁
  have hqσ : q ∈ section10SigmaPrimes M :=
    section14_c_sigma_of_primeOrder_le_kstar
      (G := G) (M := M) (K := K) (X := X) (p := q)
      hM (by simpa [section10PrimeOrderSubgroupsIn] using ⟨hXKstar, hXcard⟩)
  have hX_le_CMP :
      X ≤ subgroupCentralizerIn (section10Msigma M) P := by
    intro x hx
    have hxCME : x ∈ subgroupCentralizerIn (section10Msigma M) E := by
      simpa [section14KStar, hK_eq_E] using hXKstar hx
    refine ⟨hxCME.1, ?_⟩
    change x ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    exact Subgroup.mem_centralizer_iff.mp hxCME.2 y
      (hP_E₁.1.trans (hE.2.2.1.1.trans hE.2.1.1) hyP)
  have hXprime :
      X ∈ section10PrimeOrderSubgroupsIn q
        (subgroupCentralizerIn (section10Msigma M) P) := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hX_le_CMP, hXcard⟩
  exact
    (lemma_13_6
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (X := X) (q := q) S
      hM.1 hE hPne hP_E₁.1 hqσ hXprime).2

private theorem CFSG.section14_e_unique_overgroup_of_ambientSylow
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    {p : Nat.Primes}
    (hpKstar : p ∈ subgroupPrimeSet (section14KStar M K))
    (S : Sylow p.val (section10Msigma M)) :
    section9MaximalSubgroupsContaining
        (section10AmbientSylowSubgroup (section10Msigma M) S) = {M} := by
  classical
  obtain ⟨X, hX⟩ :=
    section14_exists_primeOrderSubgroupIn_of_dvd_card
      (G := G) (A := section14KStar M K) (p := p) hpKstar
  by_cases hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty
  · obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, hKE⟩ :=
      section14_exists_EData_containing_hall_kappa
        (G := G) (M := M) (K := K) hM hK
    exact
      section14_e_unique_overgroups_of_primeOrder_tau3
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (X := X)
        hM hK hE hKE hκτ3 S hX
  · have hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M :=
      section14_kappa_subset_tau1_of_not_inter_tau3 hκτ3
    obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, _hKE, hKE₁⟩ :=
      section14_exists_EData_with_kappa_in_E1_of_tau1
        (G := G) (M := M) (K := K) hM hK hκτ1
    exact
      section14_e_unique_overgroups_of_primeOrder_tau1
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (X := X)
        hM hK hE hKE₁ hκτ1 S hX

private theorem CFSG.section14_e_exists_maximal_overgroup_kstar_ne
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ section9MaximalSubgroupsContaining (section14KStar M K) ∧ Mstar ≠ M := by
  classical
  obtain ⟨p, X, hX⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := K) (section14_hall_kappa_ne_bot (G := G) hM hK)
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXK, hXcard⟩
  have hXprime : X ∈ section12PrimeOrderSubgroups K :=
    section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hX
  have hNXZ := proposition_14_2_b1 (G := G) (M := M) (K := K) hM hK X hXprime
  have hNXeqZ : subgroupNormalizerIn M (X : Set G) = section14Z M K :=
    hNXZ.1.trans hNXZ.2.1
  have hKstar_le_subNX :
      section14KStar M K ≤ subgroupNormalizerIn M (X : Set G) := by
    rw [hNXeqZ]
    exact le_sup_right
  have hKstar_le_NX :
      section14KStar M K ≤ Subgroup.normalizer (X : Set G) :=
    hKstar_le_subNX.trans (subgroupNormalizerIn_le_normalizer M (X : Set G))
  have hNX_not_le_M : ¬ Subgroup.normalizer (X : Set G) ≤ M := by
    intro hNXM
    have hMcontNX : M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
      ⟨hM.1, hNXM⟩
    have hXleMsigma : X ≤ section10Msigma M :=
      proposition_14_2_b2 (G := G) (M := M) (K := K) hM hK X hXprime M hMcontNX
    have hXM : X ≤ M := hXK.trans hK.1
    have hXleMsigmaSub : X.subgroupOf M ≤ section10MsigmaSubgroup M := by
      intro x hx
      have hx_sigma : (x : G) ∈ section10Msigma M :=
        hXleMsigma (by simpa [Subgroup.mem_subgroupOf] using hx)
      have hx_sigma_sub : x ∈ (section10Msigma M).subgroupOf M := by
        simpa [Subgroup.mem_subgroupOf] using hx_sigma
      simpa [section14_msigma_subgroupOf_eq (M := M)] using hx_sigma_sub
    have hpMsigma : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      have hcardXsub : Nat.card (X.subgroupOf M) = Nat.card X :=
        section12_card_subgroupOf_eq hXM
      have hpXsub : p.val ∣ Nat.card (X.subgroupOf M) := by
        simpa [hcardXsub] using (show p.val ∣ Nat.card X by rw [hXcard])
      exact hpXsub.trans (Subgroup.card_dvd_of_le hXleMsigmaSub)
    have hpσ : p ∈ section10SigmaPrimes M :=
      ((theorem_10_2_b hM.1).2).p_in_pi_of_p_dvd_card p hpMsigma
    have hpKc : p ∈ (section10SigmaPrimes M)ᶜ := by
      have hpK : p.val ∣ Nat.card K := by
        rw [← hXcard]
        exact Subgroup.card_dvd_of_le hXK
      exact
        section14_hall_kappa_is_sigma_compl_pi_subgroup
          (G := G) (M := M) (K := K) hK p hpK
    exact hpKc hpσ
  have hXne : X ≠ ⊥ := section12_primeOrder_ne_bot hX
  have hXne_top : X ≠ ⊤ := by
    intro hXtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hXK.trans hK.1
    exact hM.1.1 (top_le_iff.mp htop_le_M)
  have hNXne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro hNtop
    have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    let _ : IsSimpleGroup G := IsMinCE.simple
    rcases hXnormal.eq_bot_or_eq_top with hXbot | hXtop
    · exact hXne hXbot
    · exact hXne_top hXtop
  obtain ⟨Mstar, hMstar⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) (H := Subgroup.normalizer (X : Set G)) hNXne_top
  refine ⟨Mstar, ⟨hMstar.1, hKstar_le_NX.trans hMstar.2⟩, ?_⟩
  intro hMstar_eq_M
  exact hNX_not_le_M (hMstar_eq_M ▸ hMstar.2)

public theorem CFSG.proposition_14_2_e
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∀ p : Nat.Primes, p ∈ subgroupPrimeSet (section14KStar M K) →
      ∀ S : Sylow p.val (section10Msigma M),
        section9MaximalSubgroupsContaining
            (section10AmbientSylowSubgroup (section10Msigma M) S) = {M} ∧
          ¬ section10AmbientSylowSubgroup (section10Msigma M) S ≤ section14KStar M K := by
  intro p hpKstar S
  constructor
  · exact
      section14_e_unique_overgroup_of_ambientSylow
        (G := G) (M := M) (K := K) hM hK hpKstar S
  · intro hSleKstar
    obtain ⟨Mstar, hMstar, hMstar_ne_M⟩ :=
      section14_e_exists_maximal_overgroup_kstar_ne
        (G := G) (M := M) (K := K) hM hK
    have hMstar_cont :
        Mstar ∈ section9MaximalSubgroupsContaining
          (section10AmbientSylowSubgroup (section10Msigma M) S) := by
      exact ⟨hMstar.1, hSleKstar.trans hMstar.2⟩
    have hMstar_eq_M : Mstar = M := by
      have hMstar_single : Mstar ∈ ({M} : Set (Subgroup G)) := by
        simpa [section14_e_unique_overgroup_of_ambientSylow
          (G := G) (M := M) (K := K) hM hK hpKstar S] using hMstar_cont
      simpa using hMstar_single
    exact hMstar_ne_M hMstar_eq_M

/-- Proposition 14.2(f): every `σ(M)`-subgroup meeting `K*` nontrivially
lies in `M_σ`. -/
public theorem CFSG.section14_exists_conjugating_element_of_sigmaSubgroup
    {M Y : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hYσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Y)
    (hYne : Y ≠ ⊥)
    (hYne_top : Y ≠ ⊤) :
    ∃ g : G, Y.conjBy g ≤ section10Msigma M := by
  classical
  have hinside :
      ∀ {Z : Subgroup G}, Z ≤ M →
        IsPiSubgroup (G := G) (section10SigmaPrimes M) Z →
          ∃ g : M, Z.conjBy (g : G) ≤ section10Msigma M := by
    intro Z hZM hZσ
    let _ : MulDistribMulAction Unit M := {
      smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
    let Zsub : Subgroup M := Z.subgroupOf M
    have hZsubσ : IsPiSubgroup (G := M) (section10SigmaPrimes M) Zsub := by
      intro p hpZsub
      have hpZ : p ∈ subgroupPrimeSet Z := by
        simpa [Zsub, subgroupPrimeSet, section12_card_subgroupOf_eq hZM] using hpZsub
      exact hZσ p hpZ
    have hZsub_inv : IsInvariant Unit M Zsub := by
      refine ⟨?_⟩
      intro _ x
      simp [Zsub]
    have hMsolv : Group.IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
    have hcop : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
    obtain ⟨L, hLHall, _hLInv, hZsubL⟩ :=
      exists_isHallSubgroup_isInvariant_of_isPiSubgroup
        (G := M) (A := Unit) hMsolv hcop (section10SigmaPrimes M)
        Zsub hZsubσ hZsub_inv
    obtain ⟨a, ha⟩ :=
      exists_conj_eq_of_isHallSubgroup_of_solvable
        (G := M) hMsolv hLHall ((theorem_10_2_b (G := G) hM).2)
    refine ⟨a, ?_⟩
    exact section14_conjBy_le_of_subgroupOf_conjBy_le
      (G := G) (H := Z) (K := section10Msigma M) (M := M) (g := (a : G))
      a.property hZM (by
        simpa [section14_msigma_subgroupOf_eq (G := G) (M := M), ha] using
          Subgroup.map_mono hZsubL)
  by_cases hYM : Y ≤ M
  · rcases hinside hYM hYσ with ⟨a, ha⟩
    exact ⟨a, ha⟩
  obtain ⟨H, hHmax, hYleH⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top (G := G) (H := Y) hYne_top
  have hHcontY : H ∈ section9MaximalSubgroupsContaining Y := ⟨hHmax, hYleH⟩
  by_cases hconj : section14ConjugateSubgroups H M
  · rcases hconj with ⟨g, hHg⟩
    let Yg : Subgroup G := Y.conjBy g⁻¹
    have hYg_le_M : Yg ≤ M := by
      have hYleHg : Y ≤ M.conjBy g := by simpa [hHg] using hYleH
      have hmap : Y.conjBy g⁻¹ ≤ (M.conjBy g).conjBy g⁻¹ := Subgroup.map_mono hYleHg
      simpa [Yg, section11_conjBy_inv] using hmap
    have hYgσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Yg := by
      intro p hpYg
      have hpY : p ∈ subgroupPrimeSet Y := by
        simpa [Yg, subgroupPrimeSet, section14_card_conjBy (G := G) Y g⁻¹] using hpYg
      exact hYσ p hpY
    let _ : MulDistribMulAction Unit M := {
      smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
    rcases hinside hYg_le_M hYgσ with ⟨a, hYga_le_sigma⟩
    refine ⟨(a : G) * g⁻¹, ?_⟩
    simpa [Yg, section11_conjBy_conjBy, mul_assoc] using hYga_le_sigma
  · have hHnot : section12NotConjugate H M := by
      intro g hHg
      exact hconj ⟨g⁻¹, by simpa [section11_conjBy_inv] using congrArg (fun K => K.conjBy g⁻¹) hHg⟩
    have hYsolv : Group.IsSolvable Y :=
      IsMinCE.proper_subgroups_solvable Y (lt_top_iff_ne_top.mpr hYne_top)
    let _ : Group.IsSolvable Y := hYsolv
    let F : Subgroup Y := fittingSubgroup Y
    have hFne : F ≠ ⊥ := by
      intro hFbot
      have hYcard : Nat.card Y = 1 :=
        (fitting_eq_bot_iff_card_eq_one_of_solvable Y).mp (by simpa [F] using hFbot)
      exact hYne ((Subgroup.card_eq_one (H := Y)).1 hYcard)
    have hFcard_ne_one : Nat.card F ≠ 1 := by
      intro hcard
      have hFbot : F = ⊥ := (Subgroup.card_eq_one (H := F)).1 hcard
      exact hFne hFbot
    obtain ⟨q0, hq0prime, hq0dvdF⟩ := Nat.exists_prime_and_dvd hFcard_ne_one
    let q : Nat.Primes := ⟨q0, hq0prime⟩
    let _ : Fact q.val.Prime := ⟨q.property⟩
    let P : Sylow q.val F := Classical.choice (Sylow.nonempty (p := q.val) (G := F))
    have hPneF : (P : Subgroup F) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := F) P (by simpa [q] using hq0dvdF)
    have hPcharF : ((P : Subgroup F)).Characteristic :=
      Sylow.characteristic_of_normal P
        (Group.IsNilpotent.sylow_normal (inferInstance : Group.IsNilpotent F) q.val P)
    let PF : Subgroup Y := (P : Subgroup F).map F.subtype
    have hPFchar : PF.Characteristic := by
      let _ : ((P : Subgroup F)).Characteristic := hPcharF
      simpa [PF, F] using
        characteristic_map_subtype_of_characteristic (G := Y) F (P : Subgroup F)
    let X : Subgroup G := PF.map Y.subtype
    have hXne : X ≠ ⊥ := by
      intro hXbot
      have hPFbot : PF = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective
          (H := PF) (f := Y.subtype) Y.subtype_injective).mp
          (by simpa [X, PF] using hXbot)
      have hPbot : (P : Subgroup F) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective
          (H := (P : Subgroup F)) (f := F.subtype) F.subtype_injective).mp
          (by simpa [PF] using hPFbot)
      exact hPneF hPbot
    have hXleY : X ≤ Y := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.property
    have hXq : IsPGroup q.val X := by
      simpa [X, PF] using
        IsPGroup.map (p := q.val) (H := PF)
          (IsPGroup.map (p := q.val) (H := (P : Subgroup F)) P.isPGroup' F.subtype)
          Y.subtype
    have hNormY_le_NormX :
        Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (X : Set G) := by
      let _ : PF.Characteristic := hPFchar
      simpa [X, PF] using
        section8_normalizer_map_subtype_le_of_characteristic
          (G := G) (H := Y) (K := PF)
    have hqY : q ∈ subgroupPrimeSet Y := by
      have hXnontrivial : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hXne
      exact
        section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
          (A := Y) (B := X.subgroupOf Y)
          (hBp := hXq.of_equiv
            (Subgroup.subgroupOfEquivOfLe (H := X) (K := Y) hXleY).symm)
          (hB_ne_bot := by
            intro hbot
            exact hXne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hXleY))
    have hqσ : q ∈ section10SigmaPrimes M := hYσ q hqY
    obtain ⟨a, hX_le_Ma⟩ :=
      section10_exists_conjBy_le_of_isPGroup_of_sigma
        (G := G) (M := M) (Y := X) (p := q) hqσ hXq
    let Yg : Subgroup G := Y.conjBy a⁻¹
    let Xg : Subgroup G := X.conjBy a⁻¹
    have hXg_le_M : Xg ≤ M := by
      have hmap : X.conjBy a⁻¹ ≤ (M.conjBy a).conjBy a⁻¹ := Subgroup.map_mono hX_le_Ma
      simpa [Xg, section11_conjBy_inv] using hmap
    have hXg_le_Yg : Xg ≤ Yg := by
      change X.map ((MulAut.conj a⁻¹).toMonoidHom) ≤
        Y.map ((MulAut.conj a⁻¹).toMonoidHom)
      exact Subgroup.map_mono hXleY
    have hYgσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Yg := by
      intro p hpYg
      have hpY : p ∈ subgroupPrimeSet Y := by
        simpa [Yg, subgroupPrimeSet, section14_card_conjBy (G := G) Y a⁻¹] using hpYg
      exact hYσ p hpY
    have hXgne : Xg ≠ ⊥ := by
      intro hXgbot
      have hXeq : X = Xg.conjBy a := by
        simpa [Xg] using (section11_conjBy_inv' (G := G) X a).symm
      have hXbot : X = ⊥ := by
        calc
          X = Xg.conjBy a := hXeq
          _ = (⊥ : Subgroup G).conjBy a := by rw [hXgbot]
          _ = ⊥ := by simp [Subgroup.conjBy]
      exact hXne hXbot
    have hXgq : IsPGroup q.val Xg := by
      change IsPGroup q.val (X.map ((MulAut.conj a⁻¹).toMonoidHom))
      exact IsPGroup.map (p := q.val) (H := X) hXq
        ((MulAut.conj a⁻¹).toMonoidHom)
    have hNormYg_le_NormXg :
        Subgroup.normalizer (Yg : Set G) ≤ Subgroup.normalizer (Xg : Set G) := by
      intro n hnYg
      have hYfix : Yg.conjBy n = Yg :=
        section11_conjBy_eq_of_mem_normalizer (H := Yg) hnYg
      have hconj_n_normY : a * n * a⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
        apply section14_mem_normalizer_of_conjBy_eq (G := G) (H := Y)
        calc
          Y.conjBy (a * n * a⁻¹) = (Yg.conjBy n).conjBy a := by
            calc
              Y.conjBy (a * n * a⁻¹) = (Y.conjBy a⁻¹).conjBy (a * n) := by
                simpa [mul_assoc] using
                  (section11_conjBy_conjBy (G := G) Y a⁻¹ (a * n)).symm
              _ = (Yg.conjBy n).conjBy a := by
                change (Y.conjBy a⁻¹).conjBy (a * n) = ((Y.conjBy a⁻¹).conjBy n).conjBy a
                simpa [mul_assoc] using
                  (section11_conjBy_conjBy (G := G) (Y.conjBy a⁻¹) n a).symm
          _ = Yg.conjBy a := by rw [hYfix]
          _ = Y := by
            simpa [Yg] using (section11_conjBy_inv' (G := G) Y a)
      have hconj_n_normX : a * n * a⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
        hNormY_le_NormX hconj_n_normY
      have hXfix : X.conjBy (a * n * a⁻¹) = X :=
        section11_conjBy_eq_of_mem_normalizer (H := X) hconj_n_normX
      apply section14_mem_normalizer_of_conjBy_eq (G := G) (H := Xg)
      calc
        Xg.conjBy n = (X.conjBy (a * n * a⁻¹)).conjBy a⁻¹ := by
          calc
            Xg.conjBy n = X.conjBy (n * a⁻¹) := by
              simpa [Xg, mul_assoc] using
                (section11_conjBy_conjBy (G := G) X a⁻¹ n)
            _ = X.conjBy (a⁻¹ * (a * n * a⁻¹)) := by
              simp [mul_assoc]
            _ = (X.conjBy (a * n * a⁻¹)).conjBy a⁻¹ := by
              simpa [mul_assoc] using
                (section11_conjBy_conjBy (G := G) X (a * n * a⁻¹) a⁻¹).symm
        _ = X.conjBy a⁻¹ := by rw [hXfix]
        _ = Xg := by rfl
    by_cases hNXgM : Subgroup.normalizer (Xg : Set G) ≤ M
    · have hNormYg_M : Subgroup.normalizer (Yg : Set G) ≤ M := hNormYg_le_NormXg.trans hNXgM
      have hYg_le_M : Yg ≤ M := Subgroup.le_normalizer.trans hNormYg_M
      rcases hinside hYg_le_M hYgσ with ⟨g, hg⟩
      refine ⟨(g : G) * a⁻¹, ?_⟩
      simpa [Yg, section11_conjBy_conjBy, mul_assoc] using hg
    · have hNXgne_top : Subgroup.normalizer (Xg : Set G) ≠ ⊤ := by
        intro hNtop
        have hXgnormal : Xg.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
        let _ : IsSimpleGroup G := IsMinCE.simple
        rcases hXgnormal.eq_bot_or_eq_top with hXgbot | hXgtop
        · exact hXgne hXgbot
        · have hYgne_top : Yg ≠ ⊤ := by
            intro hYgtop
            apply hYne_top
            calc
              Y = Yg.conjBy a := by
                simpa [Yg] using (section11_conjBy_inv' (G := G) Y a).symm
              _ = (⊤ : Subgroup G).conjBy a := by rw [hYgtop]
              _ = ⊤ := by
                ext x
                simp [Subgroup.conjBy]
          have htop_le_Yg : (⊤ : Subgroup G) ≤ Yg := by
            simpa [hXgtop] using hXg_le_Yg
          exact hYgne_top (top_le_iff.mp htop_le_Yg)
      obtain ⟨Mstar, hMstar⟩ :=
        section9_exists_maximalSubgroupsContaining_of_ne_top
          (G := G) (H := Subgroup.normalizer (Xg : Set G)) hNXgne_top
      have hMstar_ne_M : Mstar ≠ M := by
        intro hEq
        exact hNXgM (hEq ▸ hMstar.2)
      have hXg_le_Mstar : Xg ≤ Mstar := Subgroup.le_normalizer.trans hMstar.2
      have hXginf : Xg ≤ M ⊓ Mstar := le_inf hXg_le_M hXg_le_Mstar
      obtain ⟨S, hXgS⟩ :=
        IsPGroup.exists_le_sylow (G := (M ⊓ Mstar : Subgroup G)) (p := q.val)
          (hXgq.of_equiv
            (Subgroup.subgroupOfEquivOfLe (H := Xg) (K := M ⊓ Mstar) hXginf).symm)
      have hXg_leS :
          Xg ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S := by
        intro x hx
        exact Subgroup.mem_map.mpr
          ⟨⟨x, hXginf hx⟩, hXgS (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
      have hnotconj_star : section12NotConjugate Mstar M :=
        proposition_12_15_a
          (G := G) (M := M) (Mstar := Mstar) (X := Xg) (q := q) (S := S)
          hM hqσ hXg_le_M hXgne hXgq hMstar hMstar_ne_M hXg_leS
      have hσdis :
          Disjoint (section10SigmaPrimes M) (section10SigmaPrimes Mstar) :=
        theorem_13_9 (G := G) hM hMstar.1 hnotconj_star
      have hq_not_sigma_star : q ∉ section10SigmaPrimes Mstar := by
        rw [Set.disjoint_left] at hσdis
        exact fun hqσstar => hσdis hqσ hqσstar
      rcases proposition_12_15_e
          (G := G) (M := M) (Mstar := Mstar) (X := Xg) (q := q) (S := S)
          hM hqσ hXg_le_M hXgne hXgq hMstar hMstar_ne_M hXg_leS
          hq_not_sigma_star with
        ⟨_hqτ2star, _hbeta, hcomp⟩
      have hNormYg_Mstar : Subgroup.normalizer (Yg : Set G) ≤ Mstar :=
        hNormYg_le_NormXg.trans hMstar.2
      have hYg_le_Mstar : Yg ≤ Mstar := Subgroup.le_normalizer.trans hNormYg_Mstar
      let Ygsub : Subgroup Mstar := Yg.subgroupOf Mstar
      have hYgsub_sigma_compl :
          IsPiSubgroup (G := Mstar) (section10SigmaPrimes Mstar)ᶜ Ygsub := by
        intro p hpYgsub
        have hpYg : p ∈ subgroupPrimeSet Yg := by
          have hcard : Nat.card Ygsub = Nat.card Yg :=
            section12_card_subgroupOf_eq hYg_le_Mstar
          simpa [Ygsub, subgroupPrimeSet, hcard] using hpYgsub
        have hpσM : p ∈ section10SigmaPrimes M := hYgσ p hpYg
        rw [Set.mem_compl_iff]
        rw [Set.disjoint_left] at hσdis
        exact fun hpσstar => hσdis hpσM hpσstar
      let _ : MulDistribMulAction Unit Mstar := {
        smul := fun _ x => x
        one_smul := fun _ => rfl
        mul_smul := fun _ _ _ => rfl
        smul_mul := fun _ _ _ => rfl
        smul_one := fun _ => rfl }
      have hYgsub_inv : IsInvariant Unit Mstar Ygsub := by
        refine ⟨?_⟩
        intro _ x
        simp [Ygsub]
      have hsolvMstar : Group.IsSolvable Mstar :=
        IsMinCE.proper_subgroups_solvable Mstar (lt_top_iff_ne_top.mpr hMstar.1.1)
      have hcopMstar : Nat.Coprime (Nat.card Unit) (Nat.card Mstar) := by simp
      obtain ⟨L, hLHall, _hLInv, hYgsubL⟩ :=
        exists_isHallSubgroup_isInvariant_of_isPiSubgroup
          (G := Mstar) (A := Unit) hsolvMstar hcopMstar
          (section10SigmaPrimes Mstar)ᶜ Ygsub hYgsub_sigma_compl hYgsub_inv
      have hcompHall :
          IsHallSubgroup (section10SigmaPrimes Mstar)ᶜ
            ((M ⊓ Mstar).subgroupOf Mstar) :=
        section12_msigma_complement_isHall_sigma_compl
          (G := G) (M := Mstar) (E := M ⊓ Mstar) hMstar.1 hcomp
      obtain ⟨m, hm⟩ :=
        exists_conj_eq_of_isHallSubgroup_of_solvable
          (G := Mstar) hsolvMstar hLHall hcompHall
      have hYgsub_conj_le :
          Ygsub.map (MulAut.conj m).toMonoidHom ≤ (M ⊓ Mstar).subgroupOf Mstar := by
        have htmp :
            Ygsub.map (MulAut.conj m).toMonoidHom ≤
              L.map (MulAut.conj m).toMonoidHom :=
          Subgroup.map_mono hYgsubL
        simpa [hm] using htmp
      have hYgm_le_inf : Yg.conjBy (m : G) ≤ M ⊓ Mstar := by
        simpa [Ygsub] using
          section14_conjBy_le_of_subgroupOf_conjBy_le
            (G := G) (H := Yg) (K := M ⊓ Mstar) (M := Mstar) (g := (m : G))
            m.property hYg_le_Mstar hYgsub_conj_le
      have hYgmσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) (Yg.conjBy (m : G)) := by
        intro p hpYgm
        have hpYg : p ∈ subgroupPrimeSet Yg := by
          simpa [subgroupPrimeSet, section14_card_conjBy (G := G) Yg (m : G)] using hpYgm
        exact hYgσ p hpYg
      rcases hinside (hYgm_le_inf.trans inf_le_left) hYgmσ with ⟨b, hb⟩
      refine ⟨(b : G) * (m : G) * a⁻¹, ?_⟩
      simpa [Yg, section11_conjBy_conjBy, mul_assoc] using hb

private theorem CFSG.section14_f_exists_conjugating_element
    {M K Y : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hYσ : IsPiSubgroup (G := G) (section10SigmaPrimes M) Y)
    (hYKstar : Y ⊓ section14KStar M K ≠ ⊥) :
    ∃ g : G, Y.conjBy g ≤ section10Msigma M := by
  classical
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    apply hYKstar
    rw [hYbot]
    simp
  have hYne_top : Y ≠ ⊤ := by
    intro hYtop
    rcases hM.2 with ⟨p, hpκ⟩
    rcases hpκ.2 with ⟨P, hPM, hCP⟩
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hPM) with ⟨hPleM, hPcard⟩
    have hpM' : p ∈ subgroupPrimeSet M := by
      have hpP : p.val ∣ Nat.card P := by rw [hPcard]
      exact hpP.trans (Subgroup.card_dvd_of_le hPleM)
    have hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G) := by
      have hpG' : p.val ∣ Nat.card G := by
        simpa [subgroupPrimeSet] using hpM'.trans (Subgroup.card_subgroup_dvd_card M)
      simpa [subgroupPrimeSet, Subgroup.card_top] using hpG'
    have hpY : p ∈ subgroupPrimeSet Y := by
      simpa [hYtop] using hpG
    have hpσ : p ∈ section10SigmaPrimes M := hYσ p hpY
    exact section14_kappa_subset_not_sigma (M := M) hpκ hpσ
  exact
    section14_exists_conjugating_element_of_sigmaSubgroup
      (G := G) (M := M) (Y := Y) hM.1 hYσ hYne hYne_top

public theorem CFSG.proposition_14_2_f
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∀ Y : Subgroup G, IsPiSubgroup (G := G) (section10SigmaPrimes M) Y →
      Y ⊓ section14KStar M K ≠ ⊥ → Y ≤ section10Msigma M := by
  classical
  intro Y hYσ hYKstar
  obtain ⟨g, hYgσ⟩ :=
    section14_f_exists_conjugating_element
      (G := G) (M := M) (K := K) (Y := Y) hM hK hYσ hYKstar
  obtain ⟨p, X, hX⟩ :=
    section14_c_exists_primeOrderSubgroupIn_of_ne_bot
      (G := G) (A := Y ⊓ section14KStar M K) hYKstar
  have hXle : X ≤ Y ⊓ section14KStar M K := hX.1
  have hXcard : Nat.card X = p.val := hX.2
  have hXleY : X ≤ Y := hXle.trans inf_le_left
  have hXleKstar : X ≤ section14KStar M K := hXle.trans inf_le_right
  have hXg_le_Msigma : X.conjBy g ≤ section10Msigma M :=
    (Subgroup.map_mono hXleY).trans hYgσ
  have hX_le_Mg : X ≤ M.conjBy g⁻¹ := by
    have hXg_le_M : X.conjBy g ≤ M := hXg_le_Msigma.trans (section14_msigma_le M)
    have hXginv_le_Mginv : (X.conjBy g).conjBy g⁻¹ ≤ M.conjBy g⁻¹ :=
      Subgroup.map_mono hXg_le_M
    simpa [section11_conjBy_inv] using hXginv_le_Mginv
  have hgM : g ∈ M := by
    by_contra hgM
    have hbot :
        section14KStar M K ⊓ M.conjBy g⁻¹ = ⊥ :=
      (proposition_14_2_d (G := G) (M := M) (K := K) hM hK).1 g⁻¹
        (by simpa using hgM)
    have hX_le_bot : X ≤ ⊥ := by
      rw [← hbot]
      exact le_inf hXleKstar hX_le_Mg
    exact section12_primeOrder_ne_bot ⟨hXleY, hXcard⟩
      ((le_bot_iff.mp hX_le_bot))
  have hg_norm_sigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section12_le_normalizer_msigma (M := M) hgM
  have hginv_norm_sigma : g⁻¹ ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    Subgroup.inv_mem _ hg_norm_sigma
  have hYginvσ : (Y.conjBy g).conjBy g⁻¹ ≤ (section10Msigma M).conjBy g⁻¹ :=
    Subgroup.map_mono hYgσ
  calc
    Y = (Y.conjBy g).conjBy g⁻¹ := (section11_conjBy_inv (G := G) Y g).symm
    _ ≤ (section10Msigma M).conjBy g⁻¹ := hYginvσ
    _ = section10Msigma M :=
      section11_conjBy_eq_of_mem_normalizer hginv_norm_sigma

/-- Proposition 14.2(g): in type `𝓟₂`, `σ(M)=β(M)`, `K` has prime order,
and `M_σ` is nilpotent TI. -/
public theorem CFSG.proposition_14_2_g
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP2 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    section10SigmaPrimes M = section10BetaPrimes M ∧
      Nat.Prime (Nat.card K) ∧
      Group.IsNilpotent (section10Msigma M) ∧
      section14TISubgroup (section10Msigma M) := by
  classical
  have hMnotP1 : M ∉ section14MFamilyP1 G := by
    intro hM1
    exact hM.2 (by simpa [section14MFamilyP1] using hM1.2)
  have hτ3_implies_P1 :
      ∀ hκτ3 : (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty,
        M ∈ section14MFamilyP1 G := by
    intro hκτ3
    obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, hKE⟩ :=
      section14_exists_EData_containing_hall_kappa
        (G := G) (M := M) (K := K) hM.1 hK
    have hEHall : section12HallSubgroupIn (section14KappaPrimes M) E M :=
      section14_tau3_case_E_hall_kappa
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM.1 hK hE hKE hκτ3
    have hKEq : K = E :=
      section14_tau3_case_K_eq_E
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM.1 hK hE hKE hκτ3
    refine ⟨hM.1, ?_⟩
    ext p
    constructor
    · intro hpκ
      refine ⟨?_, section14_kappa_subset_not_sigma (M := M) hpκ⟩
      rcases hpκ.2 with ⟨P, hP, _⟩
      have hpP : p.val ∣ Nat.card P := by rw [hP.2]
      exact hpP.trans (Subgroup.card_dvd_of_le hP.1)
    · intro hp
      have hcomp : (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
        section14_complement_to_msigma_isComplement' hE.1
      have hEM : E ≤ M := hE.1.2.1
      have hpM : p.val ∣ Nat.card M := by
        simpa [subgroupPrimeSet] using hp.1
      have hpProd : p.val ∣ Nat.card E * Nat.card (section10MsigmaSubgroup M) := by
        have hmul :
            Nat.card (E.subgroupOf M) * Nat.card (section10MsigmaSubgroup M) = Nat.card M := by
          simpa [mul_comm] using hcomp.card_mul_card
        have hpProd' :
            p.val ∣ Nat.card (E.subgroupOf M) * Nat.card (section10MsigmaSubgroup M) := by
          rw [hmul]
          exact hpM
        simpa [section12_card_subgroupOf_eq hEM] using hpProd'
      have hp_not_sigma : p ∉ section10SigmaPrimes M := hp.2
      have hp_not_Msigma : ¬ p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
        intro hpMsigma
        exact hp_not_sigma (((theorem_10_2_b hM.1.1).2).p_in_pi_of_p_dvd_card p hpMsigma)
      have hpE : p.val ∣ Nat.card E := by
        rcases p.2.dvd_mul.mp hpProd with hpE | hpMsigma
        · exact hpE
        · exact False.elim (hp_not_Msigma hpMsigma)
      have hpκE : p ∈ section14KappaPrimes M :=
        hEHall.2.p_in_pi_of_p_dvd_card p (by
          simpa [section12_card_subgroupOf_eq hEM] using hpE)
      simpa [hKEq] using hpκE
  have hκτ3_empty : ¬ (section14KappaPrimes M ∩ section12Tau3Primes M).Nonempty := by
    intro hκτ3
    exact hMnotP1 (hτ3_implies_P1 hκτ3)
  have hκτ1 : section14KappaPrimes M ⊆ section12Tau1Primes M :=
    section14_kappa_subset_tau1_of_not_inter_tau3 hκτ3_empty
  obtain ⟨E, E₁₂, E₁, E₂, E₃, hE, hKE, hKE₁⟩ :=
    section14_exists_EData_with_kappa_in_E1_of_tau1
      (G := G) (M := M) (K := K) hM.1 hK hκτ1
  let U : Subgroup G := E₂ ⊔ E₃
  have hK_eq_E₁ : K = E₁ :=
    section14_tau1_case_K_eq_E1
      (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM.1 hK hE hKE₁ hκτ1
  have hUeq : U = E₂ ⊔ E₃ := rfl
  have hUcomm : IsMulCommutative U := by
    simpa [U] using
      section14_tau1_case_U_abelian
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM.1 hK hE hKE₁ hκτ1
  have hUhall :
      section12HallSubgroupIn
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M := by
    simpa [U] using
      section14_tau1_case_U_hall
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM.1 hK hE hKE₁ hκτ1
  have hUreg : section14ActsRegularlyOn K U := by
    simpa [U] using
      section14_tau1_case_U_regular
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM.1 hK hE hKE₁ hκτ1
  have hUcomp : section14NormalComplementIn M K (U ⊔ section10Msigma M) := by
    simpa [U] using
      section14_tau1_case_normal_complement
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM.1 hK hE hKE₁ hκτ1
  have hUne : U ≠ ⊥ := by
    intro hUbot
    have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1.1 hE
    have hEeq : E = E₁ ⊔ E₂ ⊔ E₃ := h12.1
    have hEE₁ : E = E₁ := by
      calc
        E = E₁ ⊔ E₂ ⊔ E₃ := hEeq
        _ = E₁ ⊔ U := by rw [hUeq, sup_assoc]
        _ = E₁ := by simp [hUbot]
    have hEHall : section12HallSubgroupIn (section14KappaPrimes M) E M := by
      simpa [hEE₁, hK_eq_E₁] using hK
    have hUP1 : M ∈ section14MFamilyP1 G := by
      refine ⟨hM.1, ?_⟩
      ext p
      constructor
      · intro hpκ
        refine ⟨?_, section14_kappa_subset_not_sigma (M := M) hpκ⟩
        rcases hpκ.2 with ⟨P, hP, _⟩
        have hpP : p.val ∣ Nat.card P := by rw [hP.2]
        exact hpP.trans (Subgroup.card_dvd_of_le hP.1)
      · intro hp
        have hcomp : (E.subgroupOf M).IsComplement' (section10MsigmaSubgroup M) :=
          section14_complement_to_msigma_isComplement' hE.1
        have hEM : E ≤ M := hE.1.2.1
        have hpM : p.val ∣ Nat.card M := by
          simpa [subgroupPrimeSet] using hp.1
        have hpProd : p.val ∣ Nat.card E * Nat.card (section10MsigmaSubgroup M) := by
          have hmul :
              Nat.card (E.subgroupOf M) * Nat.card (section10MsigmaSubgroup M) = Nat.card M := by
            simpa [mul_comm] using hcomp.card_mul_card
          have hpProd' :
              p.val ∣ Nat.card (E.subgroupOf M) * Nat.card (section10MsigmaSubgroup M) := by
            rw [hmul]
            exact hpM
          simpa [section12_card_subgroupOf_eq hEM] using hpProd'
        have hp_not_sigma : p ∉ section10SigmaPrimes M := hp.2
        have hp_not_Msigma : ¬ p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
          intro hpMsigma
          exact hp_not_sigma (((theorem_10_2_b hM.1.1).2).p_in_pi_of_p_dvd_card p hpMsigma)
        have hpE : p.val ∣ Nat.card E := by
          rcases p.2.dvd_mul.mp hpProd with hpE | hpMsigma
          · exact hpE
          · exact False.elim (hp_not_Msigma hpMsigma)
        exact hEHall.2.p_in_pi_of_p_dvd_card p (by
          simpa [section12_card_subgroupOf_eq hEM] using hpE)
    exact hMnotP1 hUP1
  have hnilCbotU :
      Group.IsNilpotent (section10Msigma M) ∧
        subgroupCentralizerIn (section10Msigma M) U = ⊥ := by
    obtain ⟨p, P, hP⟩ :=
      section14_c_exists_primeOrderSubgroupIn_of_ne_bot (G := G) (A := U) hUne
    haveI : Fact p.val.Prime := ⟨p.2⟩
    have hpU : p.val ∣ Nat.card U := by
      rw [← hP.2]
      exact Subgroup.card_dvd_of_le hP.1
    have hpπc : p ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
      exact hUhall.2.p_in_pi_of_p_dvd_card p (by
        simpa [section12_card_subgroupOf_eq hUhall.1] using hpU)
    have hp_not_sigma : p ∉ section10SigmaPrimes M := by
      exact fun hpσ => hpπc (Or.inr hpσ)
    have hp_not_kappa : p ∉ section14KappaPrimes M := by
      exact fun hpκ => hpπc (Or.inl hpκ)
    have hpM : p ∈ subgroupPrimeSet M := by
      simpa [subgroupPrimeSet] using hpU.trans (Subgroup.card_dvd_of_le hUhall.1)
    let Usub : Subgroup M := U.subgroupOf M
    let T : Sylow p.val Usub := Classical.choice (Sylow.nonempty (p := p.val) (G := Usub))
    let Tmap : Subgroup M := (T : Subgroup Usub).map Usub.subtype
    have hTmap_p : IsPGroup p.val Tmap := by
      simpa [Tmap] using
        IsPGroup.map (p := p.val) (H := (T : Subgroup Usub)) T.isPGroup' Usub.subtype
    have hUsub_not_index : ¬ p.val ∣ Usub.index := by
      intro hpUidx
      exact (hUhall.2.p_in_pi_of_p_dvd_index p hpUidx) hpπc
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
    have h14 :=
      lemma_14_1 (G := G) hM.1.1 hMnotP1 ⟨hpM, by
        intro hp
        rcases hp with hpσ | hpκ
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
    refine ⟨h14.2.2, ?_⟩
    exact le_bot_iff.mp (by simpa [h14.2.1] using hle)
  have hnil : Group.IsNilpotent (section10Msigma M) := hnilCbotU.1
  have hCbotU : subgroupCentralizerIn (section10Msigma M) U = ⊥ := hnilCbotU.2
  have hU_le_der : U ≤ ambientDerivedSubgroup E := by
    have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM.1 hK
    have hCbot : subgroupCentralizerIn U K = ⊥ :=
      section14_subgroupCentralizerIn_eq_bot_of_regular hKne hUreg
    rcases hK with ⟨hKM, hHallK⟩
    rcases hUhall with ⟨hUM, hHallU⟩
    have hcop : Nat.Coprime (Nat.card K) (Nat.card U) := by
      refine Nat.coprime_of_dvd ?_
      intro q hqprime hqK hqU
      let q' : Nat.Primes := ⟨q, hqprime⟩
      have hqκ : q' ∈ section14KappaPrimes M :=
        hHallK.p_in_pi_of_p_dvd_card q'
          (by simpa [section12_card_subgroupOf_eq hKM, q'] using hqK)
      have hqπ : q' ∈ (section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ :=
        hHallU.p_in_pi_of_p_dvd_card q'
          (by simpa [section12_card_subgroupOf_eq hUM, q'] using hqU)
      exact hqπ (Or.inl hqκ)
    have hsolvU : IsSolvable U :=
      section14_solvable_of_le_maximal hM.1.1 hUM
    have hU_le_comm : U ≤ ⁅U, K⁆ :=
      section8_le_commutator_of_subgroupCentralizerIn_eq_bot
        (Y := U) (R := K) hsolvU hUreg.1 hcop hCbot
    have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1.1 hE
    have hUE : U ≤ E := by simpa [U] using h12.2.2.1.1
    have hKE : K ≤ E := by
      have hE₁E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
      simpa [hK_eq_E₁] using hE₁E
    have hcomm_le_der : ⁅U, K⁆ ≤ ambientDerivedSubgroup E := by
      have hcomm_le : ⁅U, K⁆ ≤ ⁅E, E⁆ :=
        Subgroup.commutator_mono hUE hKE
      simpa [section12_ambientDerivedSubgroup_eq_commutator] using hcomm_le
    exact hU_le_comm.trans hcomm_le_der
  have hσeqβ : section10SigmaPrimes M = section10BetaPrimes M := by
    apply Set.Subset.antisymm
    · intro q hqσ
      by_contra hqβ
      rcases lemma_12_19
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1.1 hE with
        ⟨H, hHHallIn, hHcentD⟩
      rcases hHHallIn with ⟨hHσ, hHHall⟩
      let Kσ : Subgroup G := section10Msigma M
      let Hsub : Subgroup Kσ := H.subgroupOf Kσ
      have hHHallKσ : IsHallSubgroup (section10BetaPrimes M)ᶜ Hsub := by
        simpa [Hsub, Kσ] using hHHall
      have hH_le_CU : H ≤ subgroupCentralizerIn (section10Msigma M) U := by
        intro x hxH
        have hxσ : x ∈ section10Msigma M := hHσ hxH
        have hxcentU : x ∈ Subgroup.centralizer (U : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro u huU
          exact hHcentD hxH _ (hU_le_der huU)
        exact ⟨hxσ, hxcentU⟩
      have hHbot : H = ⊥ := by
        apply le_bot_iff.mp
        intro x hxH
        exact by simpa [hCbotU] using hH_le_CU hxH
      have hHsub_bot : Hsub = ⊥ := by
        ext x
        change ((x : G) ∈ H) ↔ x ∈ (⊥ : Subgroup Kσ)
        simp [hHbot]
      have hqπc : q ∈ (section10BetaPrimes M)ᶜ := by
        simpa using hqβ
      have hq_not_Hsub_index : ¬ q.val ∣ Hsub.index := by
        intro hqidx
        exact (hHHallKσ.p_in_pi_of_p_dvd_index q hqidx) hqπc
      have hq_dvd_Kσsub : q.val ∣ Nat.card ((section10Msigma M).subgroupOf M) := by
        have hHallσsub :
            IsHallSubgroup (section10SigmaPrimes M) ((section10Msigma M).subgroupOf M) := by
          simpa [section14_msigma_subgroupOf_eq] using (theorem_10_2_b (G := G) hM.1.1).2
        have hq_not_Kσsub_index : ¬ q.val ∣ ((section10Msigma M).subgroupOf M).index := by
          intro hqidx
          exact (hHallσsub.p_in_pi_of_p_dvd_index q hqidx) hqσ
        have hq_dvd_M : q.val ∣ Nat.card M := by
          simpa [subgroupPrimeSet] using hqσ.1
        have hcard :
            Nat.card ((section10Msigma M).subgroupOf M) *
                ((section10Msigma M).subgroupOf M).index =
              Nat.card M := by
          exact Subgroup.card_mul_index (H := (section10Msigma M).subgroupOf M)
        have hqmul :
            q.val ∣
              Nat.card ((section10Msigma M).subgroupOf M) *
                ((section10Msigma M).subgroupOf M).index := by
          rw [hcard]
          exact hq_dvd_M
        rcases q.2.dvd_mul.mp hqmul with hqKσ | hqidx
        · exact hqKσ
        · exact False.elim (hq_not_Kσsub_index hqidx)
      have hq_dvd_Kσ : q.val ∣ Nat.card Kσ := by
        have hcardKσ :
            Nat.card ((section10Msigma M).subgroupOf M) = Nat.card Kσ :=
          section12_card_subgroupOf_eq (section14_msigma_le M)
        simpa [hcardKσ] using hq_dvd_Kσsub
      have hq_dvd_Hsub : q.val ∣ Nat.card Hsub := by
        have hcard : Nat.card Hsub * Hsub.index = Nat.card Kσ := by
          exact Subgroup.card_mul_index (H := Hsub)
        have hqmul : q.val ∣ Nat.card Hsub * Hsub.index := by
          rw [hcard]
          exact hq_dvd_Kσ
        rcases q.2.dvd_mul.mp hqmul with hqH | hqidx
        · exact hqH
        · exact False.elim (hq_not_Hsub_index hqidx)
      have hq_not_Hsub_card : ¬ q.val ∣ Nat.card Hsub := by
        rw [hHsub_bot]
        simp [q.2.ne_one]
      exact hq_not_Hsub_card hq_dvd_Hsub
    · intro q hqβ
      exact section12_sigmaPrimes_mem_of_alphaPrimes_mem hM.1.1 hqβ.1
  have hβeqσ : section10BetaPrimes M = section10SigmaPrimes M := hσeqβ.symm
  have hTI : section14TISubgroup (section10Msigma M) := by
    refine ⟨?_, ?_, ?_⟩
    · intro hbot
      rcases hM.1.2 with ⟨p, hpκ⟩
      rcases hpκ.2 with ⟨P, hP, hCP⟩
      have hCPbot : subgroupCentralizerIn (section10Msigma M) P = ⊥ := by
        simp [hbot, subgroupCentralizerIn]
      exact hCP hCPbot
    · have hσleM : section10Msigma M ≤ M := section14_msigma_le M
      intro htop
      exact hM.1.1.1 (top_le_iff.mp (htop ▸ hσleM))
    · refine ⟨⟨1, by simp⟩, ?_⟩
      intro g hgNorm x hx
      have hg_not_M : g ∉ M := by
        intro hgM
        exact hgNorm (section12_le_normalizer_msigma (M := M) hgM)
      have hginv_not_M : g⁻¹ ∉ M := by
        intro hginvM
        have hgM : g ∈ M := by simpa using M.inv_mem hginvM
        exact hg_not_M hgM
      have h12_17 :=
        lemma_12_17
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1.1 hE
      have hinterβc :
          IsPiSubgroup (G := G) (section10BetaPrimes M)ᶜ
            (section10Msigma M ⊓ M.conjBy g⁻¹) :=
        (h12_17.2.2 g⁻¹ hginv_not_M).2.1
      have hinterσ :
          IsPiSubgroup (G := G) (section10SigmaPrimes M)
            (section10Msigma M ⊓ M.conjBy g⁻¹) := by
        have hhallσ : IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) :=
          (theorem_10_2_b (G := G) hM.1.1).1
        intro p hpinf
        exact hhallσ.p_in_pi_of_p_dvd_card p
          (hpinf.trans (Subgroup.card_dvd_of_le inf_le_left))
      have hinterβ :
          IsPiSubgroup (G := G) (section10BetaPrimes M)
            (section10Msigma M ⊓ M.conjBy g⁻¹) := by
        simpa [hβeqσ] using hinterσ
      have hinterbot :
          section10Msigma M ⊓ M.conjBy g⁻¹ = ⊥ :=
        section8_eq_bot_of_le_isPiSubgroup_and_le_isPiSubgroup_compl
          (H := section10Msigma M ⊓ M.conjBy g⁻¹)
          (Y := section10Msigma M ⊓ M.conjBy g⁻¹)
          (C := section10Msigma M ⊓ M.conjBy g⁻¹)
          le_rfl le_rfl hinterβc hinterβ
      rcases hx with ⟨hxσ, hxconj⟩
      rcases hxconj with ⟨y, hyσ, rfl⟩
      have hxinf : g⁻¹ * y * g ∈ section10Msigma M ⊓ M.conjBy g⁻¹ := by
        refine ⟨hxσ, ?_⟩
        exact Subgroup.mem_map.mpr ⟨y, section14_msigma_le M hyσ, by simp⟩
      have hxbot : g⁻¹ * y * g ∈ (⊥ : Subgroup G) := by
        simpa [hinterbot] using hxinf
      simpa using hxbot
  have hKprime : Nat.Prime (Nat.card K) := by
    let S : Subgroup G := K ⊔ U
    have hprime :
        section14ActsInPrimeManner K (section10Msigma M) :=
      section14_tau1_case_prime_manner
        (G := G) (M := M) (K := K) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1 hE hKE₁
        (section14_hall_kappa_ne_bot (G := G) hM.1 hK)
    have hS_norm_sigma : S ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
      refine sup_le ?_ ?_
      · exact hprime.1
      · exact hUhall.1.trans (section12_le_normalizer_msigma (M := M))
    let _ : Subgroup.Normalizes S (section10Msigma M) := ⟨hS_norm_sigma⟩
    have hfix_subgroupOf_eq {A : Subgroup G} (hA_le : A ≤ S) :
        letI : Subgroup.Normalizes A (section10Msigma M) := ⟨hA_le.trans hS_norm_sigma⟩
        letI : MulDistribMulAction ↥(A.subgroupOf S) ↥(section10Msigma M) :=
          MulDistribMulAction.compHom ↥(section10Msigma M) (A.subgroupOf S).subtype
        fixedPointSubgroup (↥(A.subgroupOf S)) (↥(section10Msigma M)) =
          fixedPointSubgroup (↥A) (↥(section10Msigma M)) := by
      let _ : Subgroup.Normalizes A (section10Msigma M) := ⟨hA_le.trans hS_norm_sigma⟩
      let _ : MulDistribMulAction ↥(A.subgroupOf S) ↥(section10Msigma M) :=
        MulDistribMulAction.compHom ↥(section10Msigma M) (A.subgroupOf S).subtype
      ext x
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      constructor
      · intro hx a
        have ha :
            (⟨⟨(a : G), hA_le a.2⟩, by
              show ((⟨(a : G), hA_le a.2⟩ : S) : G) ∈ A
              exact a.2⟩ : A.subgroupOf S) • x = x :=
          hx ⟨⟨(a : G), hA_le a.2⟩, by
            show ((⟨(a : G), hA_le a.2⟩ : S) : G) ∈ A
            exact a.2⟩
        apply Subtype.ext
        simpa [MulAction.compHom_smul_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val ha
      · intro hx a
        have hx' : (⟨(a : S), by
          show ((a : S) : G) ∈ A
          exact a.2⟩ : A) • x = x := by
          exact hx ⟨(a : S), by
            show ((a : S) : G) ∈ A
            exact a.2⟩
        apply Subtype.ext
        simpa [MulAction.compHom_smul_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val hx'
    have hzpowers_subgroupOf_eq (x : S) :
        (Subgroup.zpowers (x : G)).subgroupOf S = Subgroup.zpowers x := by
      ext y
      constructor
      · intro hy
        have hyz : ((y : S) : G) ∈ Subgroup.zpowers (x : G) := by
          simpa [Subgroup.mem_subgroupOf] using hy
        rcases Subgroup.mem_zpowers_iff.mp hyz with ⟨n, hn⟩
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
          apply Subtype.ext
          simpa using hn⟩
      · intro hy
        rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, hn⟩
        have hyz : ((y : S) : G) ∈ Subgroup.zpowers (x : G) := by
          exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
            simpa using congrArg Subtype.val hn⟩
        simpa [Subgroup.mem_subgroupOf] using hyz
    have hcent_subgroupOf_eq {A : Subgroup G} {x : S} :
        elementCentralizerIn (A.subgroupOf S) x =
          (elementCentralizerIn A (x : G)).subgroupOf S := by
      ext y
      constructor
      · intro hy
        change (y : G) ∈ A ∧ (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G)
        rcases hy with ⟨hyA, hyC⟩
        refine ⟨hyA, ?_⟩
        change y ∈ Subgroup.centralizer ({x} : Set S) at hyC
        rw [Subgroup.mem_centralizer_iff] at hyC ⊢
        intro z hz
        have hyx : x * y = y * x :=
          (Subgroup.mem_centralizer_iff.mp hyC) x (by simp)
        have hz_eq : z = (x : G) := by simpa using hz
        simpa [hz_eq] using congrArg Subtype.val hyx
      · intro hy
        change (y : G) ∈ A ∧ (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) at hy
        rcases hy with ⟨hyA, hyC⟩
        refine ⟨hyA, ?_⟩
        change y ∈ Subgroup.centralizer ({x} : Set S)
        rw [Subgroup.mem_centralizer_iff] at hyC ⊢
        intro z hz
        have hyx : (x : G) * (y : G) = (y : G) * x := hyC x (by simp)
        have hz_eq : z = x := by simpa using hz
        apply Subtype.ext
        simpa [hz_eq] using hyx
    have hKne : K ≠ ⊥ := section14_hall_kappa_ne_bot (G := G) hM.1 hK
    have hKE : K ≤ E := by
      have hE₁E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
      simpa [hK_eq_E₁] using hE₁E
    have hUE : U ≤ E := by
      have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1.1 hE
      simpa [U] using h12.2.2.1.1
    have hKUdisj : Disjoint U K := by
      rw [Subgroup.disjoint_def]
      intro x hxU hxK
      have hKE1 : x ∈ E₁ := by simpa [← hK_eq_E₁] using hxK
      exact
        Subgroup.disjoint_def.mp
          (section14_E1_disjoint_E2_sup_E3
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1.1 hE)
          hKE1 hxU
    have hinf : U ⊓ K = ⊥ := by
      exact hKUdisj.eq_bot
    have hEeq : E = K ⊔ U := by
      have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1.1 hE
      calc
        E = E₁ ⊔ E₂ ⊔ E₃ := h12.1
        _ = E₁ ⊔ (E₂ ⊔ E₃) := by rw [sup_assoc]
        _ = K ⊔ U := by simp [U, hK_eq_E₁]
    have hUnormE : section10NormalIn U E := by
      simpa [U] using
        (lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM.1.1 hE).2.2.1
    have hK_norm_U : K ≤ Subgroup.normalizer (U : Set G) := by
      exact hKE.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hUnormE.1).1 hUnormE.2)
    have hUnormS : (U.subgroupOf S).Normal := by
      simpa [S] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := K) (N := U) hK_norm_U)
    have hcompS : (U.subgroupOf S).IsComplement' (K.subgroupOf S) := by
      simpa [S] using
        section14_isComplement'_subgroupOf_sup_of_inf_eq_bot_of_le_normalizer
          (G := G) (H := U) (R := K) hK_norm_U hinf
    have hUneS : U.subgroupOf S ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card U = 1 := by
        calc
          Nat.card U = Nat.card (U.subgroupOf S) := by
            symm
            exact natCard_subgroupOf_eq U S le_sup_right
          _ = 1 := by simp [hbot]
      exact hUne ((Subgroup.eq_bot_iff_card (H := U)).2 hcard)
    have hKneS : K.subgroupOf S ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card K = 1 := by
        calc
          Nat.card K = Nat.card (K.subgroupOf S) := by
            symm
            exact natCard_subgroupOf_eq K S le_sup_left
          _ = 1 := by simp [hbot]
      exact hKne ((Subgroup.eq_bot_iff_card (H := K)).2 hcard)
    have hfrobS :
        IsFrobeniusGroupWithKernelComplement (U.subgroupOf S) (K.subgroupOf S) := by
      refine (lemma_3_1 (K := U.subgroupOf S) (R := K.subgroupOf S) hUneS hKneS hUnormS hcompS).2 ?_
      intro x hxne
      apply (Subgroup.eq_bot_iff_card (H := elementCentralizerIn (U.subgroupOf S) (x : S))).2
      have hxK : ((x : S) : G) ∈ K := x.2
      have hxneG : (x : G) ≠ 1 := by
        intro hx1
        apply hxne
        ext
        simpa using hx1
      have hcentU : elementCentralizerIn U (x : G) = ⊥ := hUreg.2 (x : G) hxK hxneG
      have hcent_sub :
          elementCentralizerIn (U.subgroupOf S) (x : S) =
            (elementCentralizerIn U (x : G)).subgroupOf S := by
        exact hcent_subgroupOf_eq (A := U) (x := x)
      have : Nat.card ((elementCentralizerIn U (x : G)).subgroupOf S) = 1 := by
        simp [hcentU]
      simpa [hcent_sub] using this
    have hsolvS : Group.IsSolvable S :=
      section14_solvable_of_le_maximal hM.1.1 (by
        have hEM : E ≤ M := hE.1.2.1
        have hSE : S = E := by simpa [S] using hEeq.symm
        exact hSE ▸ hEM)
    have hcopSσ : Nat.Coprime (Nat.card S) (Nat.card (section10Msigma M)) := by
      have hhallσ : IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) :=
        (theorem_10_2_b (G := G) hM.1.1).1
      have hSsigmaCompl : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ S := by
        intro p hpS
        by_cases hpK : p.val ∣ Nat.card K
        · exact section14_hall_kappa_is_sigma_compl_pi_subgroup (G := G) (M := M) (K := K) hK p hpK
        · have hpU : p.val ∣ Nat.card U := by
            have hcardS : Nat.card U * Nat.card K = Nat.card S := by
              simpa [S, natCard_subgroupOf_eq U S le_sup_right,
                natCard_subgroupOf_eq K S le_sup_left, Nat.mul_comm] using hcompS.card_mul
            have hpProd : p.val ∣ Nat.card U * Nat.card K := by
              exact hcardS ▸ hpS
            rcases p.2.dvd_mul.mp hpProd with hpU | hpK'
            · exact hpU
            · exact False.elim (hpK hpK')
          have hpπc : p ∈ (section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ :=
            hUhall.2.p_in_pi_of_p_dvd_card p (by
              simpa [section12_card_subgroupOf_eq hUhall.1] using hpU)
          exact fun hpσ => hpπc (Or.inr hpσ)
      refine Nat.coprime_of_dvd ?_
      intro q hqprime hqS hqσ
      let q' : Nat.Primes := ⟨q, hqprime⟩
      have hq_not_sigma : q' ∉ section10SigmaPrimes M := by
        exact hSsigmaCompl q' hqS
      have hq_sigma : q' ∈ section10SigmaPrimes M := by
        exact hhallσ.p_in_pi_of_p_dvd_card q' hqσ
      exact hq_not_sigma hq_sigma
    have hfixU :
        fixedPointSubgroup (↥(U.subgroupOf S)) (↥(section10Msigma M)) = ⊥ := by
      have hUnormσ : U ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
        hUhall.1.trans (section12_le_normalizer_msigma (M := M))
      let _ : Subgroup.Normalizes U (section10Msigma M) := ⟨hUnormσ⟩
      calc
        fixedPointSubgroup (↥(U.subgroupOf S)) (↥(section10Msigma M)) =
            fixedPointSubgroup (↥U) (↥(section10Msigma M)) :=
          hfix_subgroupOf_eq (A := U) le_sup_right
        _ = ⊥ := by
          have hfix_eq :
              fixedPointSubgroup (↥U) (section10Msigma M) =
                (subgroupCentralizerIn (section10Msigma M) U).subgroupOf (section10Msigma M) := by
            simpa using
              fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
                (section10Msigma M) U hUnormσ
          have hcard :
              Nat.card ((subgroupCentralizerIn (section10Msigma M) U).subgroupOf (section10Msigma M)) = 1 := by
            simp [hCbotU]
          apply (Subgroup.eq_bot_iff_card (H := fixedPointSubgroup (↥U) (section10Msigma M))).2
          simpa [hfix_eq] using hcard
    have hfixKsub :
        ∀ x : K.subgroupOf S, x ≠ 1 →
          fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) (↥(section10Msigma M)) =
            fixedPointSubgroup (↥(K.subgroupOf S)) (↥(section10Msigma M)) := by
      intro x hxne
      let _ : MulDistribMulAction ↥(K.subgroupOf S) ↥(section10Msigma M) :=
        MulDistribMulAction.compHom ↥(section10Msigma M) (K.subgroupOf S).subtype
      let _ : MulDistribMulAction ↥(Subgroup.zpowers (x : S)) ↥(section10Msigma M) :=
        MulDistribMulAction.compHom ↥(section10Msigma M) (Subgroup.zpowers (x : S)).subtype
      have hxK : (x : G) ∈ K := x.2
      have hxneG : (x : G) ≠ 1 := by
        intro hx1
        apply hxne
        ext
        simpa using hx1
      rcases section14_exists_primeOrder_zpowers_in (G := G) (B := K) hxK hxneG with
        ⟨q, z, hz_zpowx, hzK, hz_ne, hQ⟩
      have hQsection : Subgroup.zpowers z ∈ section12PrimeOrderSubgroups K :=
        section14_primeOrderSubgroups_of_primeOrderSubgroupsIn hQ
      have hCQ :
          subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) ≠ ⊥ := by
        have hCK : subgroupCentralizerIn (section10Msigma M) K ≠ ⊥ := by
          simpa [section14KStar] using
            section14_c_kstar_ne_bot (G := G) (M := M) (K := K) hM.1 hK
        exact section14_subgroupCentralizerIn_antitone_ne_bot hQsection.1 hCK
      have hCA :
          subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) =
            subgroupCentralizerIn (section10Msigma M) K := by
        apply le_antisymm
        · exact hprime.2 _ hQsection
        · exact section14_b1_kstar_le_centralizer (G := G) (M := M) (K := K) (X := Subgroup.zpowers z) hQsection.1
      have hKnormσ : K ≤ Subgroup.normalizer (section10Msigma M : Set G) := hprime.1
      let _ : Subgroup.Normalizes K (section10Msigma M) := ⟨hKnormσ⟩
      have hzpow_le_Ksub : Subgroup.zpowers z ≤ K := Subgroup.zpowers_le.2 hzK
      have hzp_norm_sigma :
          Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
        (Subgroup.zpowers_le.2 hxK).trans hKnormσ
      let _ : Subgroup.Normalizes (Subgroup.zpowers (x : G)) (section10Msigma M) := ⟨hzp_norm_sigma⟩
      have hfix_zpowS_eq :
          letI : MulDistribMulAction ↥((Subgroup.zpowers (x : G)).subgroupOf S) ↥(section10Msigma M) :=
            MulDistribMulAction.compHom ↥(section10Msigma M) ((Subgroup.zpowers (x : G)).subgroupOf S).subtype
          fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) (↥(section10Msigma M)) =
            fixedPointSubgroup (↥((Subgroup.zpowers (x : G)).subgroupOf S)) (↥(section10Msigma M)) := by
        let _ : MulDistribMulAction ↥((Subgroup.zpowers (x : G)).subgroupOf S) ↥(section10Msigma M) :=
          MulDistribMulAction.compHom ↥(section10Msigma M) ((Subgroup.zpowers (x : G)).subgroupOf S).subtype
        ext y
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
        constructor
        · intro hy a
          have ha_mem : (a : S) ∈ Subgroup.zpowers (x : S) := by
            rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨n, hn⟩
            exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
              apply Subtype.ext
              simpa using hn⟩
          have ha :
              (⟨(a : S), ha_mem⟩ : Subgroup.zpowers (x : S)) • y = y := by
            exact hy ⟨(a : S), ha_mem⟩
          apply Subtype.ext
          simpa [MulAction.compHom_smul_def,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            congrArg Subtype.val ha
        · intro hy a
          have ha_mem : ((a : S) : G) ∈ Subgroup.zpowers (x : G) := by
            rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨n, hn⟩
            exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
              simpa using congrArg Subtype.val hn⟩
          have ha :
              (⟨(a : S), ha_mem⟩ :
                (Subgroup.zpowers (x : G)).subgroupOf S) • y = y := by
            exact hy ⟨(a : S), ha_mem⟩
          change (a : S) • y = y at ha
          change (a : S) • y = y
          exact ha
      have hzx_eq :
          subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers (x : G)) =
            elementCentralizerIn (section10Msigma M) (x : G) := by
        ext g
        constructor
        · intro hg
          refine ⟨hg.1, ?_⟩
          exact Subgroup.mem_centralizer_singleton_iff.mpr <| by
            have hgcent : g ∈ Subgroup.centralizer (Subgroup.zpowers (x : G) : Set G) := hg.2
            have hxg : (x : G) * g = g * x :=
              (Subgroup.mem_centralizer_iff.mp hgcent) (x : G) (Subgroup.mem_zpowers (x : G))
            exact hxg.symm
        · intro hg
          refine ⟨hg.1, ?_⟩
          change g ∈ Subgroup.centralizer (Subgroup.zpowers (x : G) : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
          have hxg : Commute (x : G) g :=
            (Subgroup.mem_centralizer_singleton_iff.mp hg.2).symm
          exact (hxg.zpow_left n).eq
      have hfixK_eq :
          fixedPointSubgroup (↥(K.subgroupOf S)) (↥(section10Msigma M)) =
            fixedPointSubgroup (↥K) (↥(section10Msigma M)) :=
        hfix_subgroupOf_eq (A := K) le_sup_left
      calc
        fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) (section10Msigma M)
            = fixedPointSubgroup (↥((Subgroup.zpowers (x : G)).subgroupOf S)) (section10Msigma M) :=
              hfix_zpowS_eq
        _ = fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) (section10Msigma M) :=
              hfix_subgroupOf_eq (A := Subgroup.zpowers (x : G)) ((Subgroup.zpowers_le.2 hxK).trans le_sup_left)
        _ = (subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers (x : G))).subgroupOf
              (section10Msigma M) := by
              simpa using
                (fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
                  (section10Msigma M) (Subgroup.zpowers (x : G)) hzp_norm_sigma)
        _ = (elementCentralizerIn (section10Msigma M) (x : G)).subgroupOf (section10Msigma M) := by
              rw [hzx_eq]
        _ = (subgroupCentralizerIn (section10Msigma M) K).subgroupOf (section10Msigma M) := by
              have hCx :
                  elementCentralizerIn (section10Msigma M) (x : G) =
                    subgroupCentralizerIn (section10Msigma M) K := by
                apply le_antisymm
                · intro y hy
                  have hyQ : y ∈ subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) := by
                    refine ⟨hy.1, ?_⟩
                    change y ∈ Subgroup.centralizer (Subgroup.zpowers z : Set G)
                    rw [Subgroup.mem_centralizer_iff]
                    intro w hwQ
                    have hyx : Commute (x : G) y :=
                      (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
                    have hwx : w ∈ Subgroup.zpowers (x : G) :=
                      (Subgroup.zpowers_le.2 hz_zpowx) hwQ
                    rcases Subgroup.mem_zpowers_iff.mp hwx with ⟨n, rfl⟩
                    simpa using (hyx.zpow_left n).eq
                  simpa [hCA] using hyQ
                · intro y hy
                  refine ⟨hy.1, ?_⟩
                  exact Subgroup.mem_centralizer_singleton_iff.mpr <| by
                    exact (Subgroup.mem_centralizer_iff.mp hy.2 (x : G) hxK).symm
              rw [hCx]
        _ = fixedPointSubgroup (↥K) (section10Msigma M) := by
              rw [fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
                (section10Msigma M) K hKnormσ]
        _ = fixedPointSubgroup (↥(K.subgroupOf S)) (section10Msigma M) := hfixK_eq.symm
    let _ : Nontrivial ↥(section10Msigma M) :=
      (section10Msigma M).nontrivial_iff_ne_bot.mpr hTI.1
    have hmain :=
      theorem_3_10_a (G := S) (K := U.subgroupOf S) (R := K.subgroupOf S)
        (M := ↥(section10Msigma M)) hfrobS hsolvS hnil hcopSσ hfixU hfixKsub
    simpa [natCard_subgroupOf_eq K S le_sup_left] using hmain.2
  exact ⟨hσeqβ, hKprime, hnil, hTI⟩

end Section14
