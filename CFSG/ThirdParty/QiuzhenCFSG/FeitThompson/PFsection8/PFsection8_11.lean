module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_8

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u


/-- Peterfalvi `(8.12)`. -/


private theorem theorem_8_11_hall_subgroupPrimeSet_of_hall
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {H : Subgroup G}
    (hHall : IsHallSubgroup π H) :
    IsHallSubgroup (subgroupPrimeSet H) H := by
  refine isHallSubgroup_of (G := G) (π := subgroupPrimeSet H) (H := H) ?_ ?_
  · intro p hp
    simpa [subgroupPrimeSet] using hp
  · intro p hpH hpidx
    have hpπ : p ∈ π := hHall.p_in_pi_of_p_dvd_card p (by
      simpa [subgroupPrimeSet] using hpH)
    exact (hHall.p_in_pi_of_p_dvd_index p hpidx) hpπ

private theorem theorem_8_11_ambientSylow_prime_dvd_card
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {p : Nat.Primes} (P : Sylow p.val H)
    (hPne : section10AmbientSylowSubgroup H P ≠ ⊥) :
    p.val ∣ Nat.card H := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hPgroup : IsPGroup p.val (section10AmbientSylowSubgroup H P) :=
    section11_ambientSylow_isPGroup H P
  rcases hPgroup.card_eq_or_dvd with hcard | hp
  · exact False.elim (hPne ((Subgroup.card_eq_one).1 hcard))
  · exact hp.trans (Subgroup.card_dvd_of_le (section11_ambientSylow_le H P))

private theorem theorem_8_11_normalizer_le_of_eq_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMs : Ms = section10Msigma M) :
    ∀ p : Nat.Primes, ∀ P : Sylow p.val Ms,
      section10AmbientSylowSubgroup Ms P ≠ ⊥ →
        Subgroup.normalizer (section10AmbientSylowSubgroup Ms P : Set G) ≤ M := by
  subst Ms
  intro p P hPne
  have hSigmaHall : IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) :=
    (theorem_10_2_b (G := G) hM).1
  have hpCard : p.val ∣ Nat.card (section10Msigma M) :=
    theorem_8_11_ambientSylow_prime_dvd_card (G := G) P hPne
  have hpσ : p ∈ section10SigmaPrimes M :=
    hSigmaHall.p_in_pi_of_p_dvd_card p hpCard
  rcases section11_ambientSylow_isSylow_of_hall
      (G := G) (H := M) (K := section10Msigma M)
      hSigmaHall hpσ (section11_msigma_le M) P with
    ⟨PM, hPM⟩
  intro g hg
  have hgPM :
      g ∈ Subgroup.normalizer (section10AmbientSylowSubgroup M PM : Set G) := by
    simpa [hPM] using hg
  exact section10_sigma_sylow_normalizer_le (G := G) hpσ PM hgPM

private theorem theorem_8_11_section15MFSubgroup
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF) :
    section15MFSubgroup M MF := by
  simpa [section16MFSubgroup, section15MFSubgroup,
    section16NilpotentNormalHallIn, section15NilpotentNormalHallIn] using hMF

private theorem theorem_8_11_mf_hall_in_ambientDerived
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF) :
    IsHallSubgroup (subgroupPrimeSet MF)
      (MF.subgroupOf (ambientDerivedSubgroup M)) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hMF15 : section15MFSubgroup M MF :=
    theorem_8_11_section15MFSubgroup (G := G) hMF
  have hMFleD : MF ≤ D := by
    simpa [D] using (corollary_15_5_c (G := G) hM hMF15).1
  rcases hMF.1 with ⟨hMFM, _hMFnormM, _hMFnil, hMFHallM⟩
  let Dsub : Subgroup M := D.subgroupOf M
  have hMFcardM : Nat.card (MF.subgroupOf M) = Nat.card MF :=
    natCard_subgroupOf_eq MF M hMFM
  have hMFcardD : Nat.card (MF.subgroupOf D) = Nat.card MF :=
    natCard_subgroupOf_eq MF D hMFleD
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hMFsub_le_Dsub : MF.subgroupOf M ≤ Dsub := by
    intro x hx
    exact hMFleD hx
  refine isHallSubgroup_of (G := D) (π := subgroupPrimeSet MF)
    (H := MF.subgroupOf D) ?_ ?_
  · intro p hp
    exact hMFHallM.p_in_pi_of_p_dvd_card p
      (by simpa [hMFcardM, hMFcardD] using hp)
  · intro p hpπ hpidx
    have hrel_eq :
        (MF.subgroupOf D).index = (MF.subgroupOf M).relIndex Dsub := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := MF) (K := D) (L := M) hDleM
      simpa [Dsub, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (MF.subgroupOf D).index ∣ (MF.subgroupOf M).index := by
      have hrel_dvd :
          (MF.subgroupOf M).relIndex Dsub ∣ (MF.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hMFsub_le_Dsub
      simpa [hrel_eq] using hrel_dvd
    exact (hMFHallM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

private theorem theorem_8_11_hall_trans
    {G : Type u} [Group G] [Finite G]
    {H D : Subgroup G}
    (hHD : H ≤ D)
    (hHallHD : IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf D))
    (hHallD : IsHallSubgroup (subgroupPrimeSet D) D) :
    IsHallSubgroup (subgroupPrimeSet H) H := by
  classical
  refine isHallSubgroup_of (G := G) (π := subgroupPrimeSet H) (H := H) ?_ ?_
  · intro p hp
    simpa [subgroupPrimeSet] using hp
  · intro p hpH hpidx
    have hidx_eq : H.index = (H.subgroupOf D).index * D.index := by
      simpa [Subgroup.relIndex] using
        (Subgroup.relIndex_mul_index hHD : H.relIndex D * D.index = H.index).symm
    have hpProd : p.val ∣ (H.subgroupOf D).index * D.index := by
      simpa [hidx_eq] using hpidx
    rcases p.property.dvd_mul.mp hpProd with hpHD | hpDidx
    · exact (hHallHD.p_in_pi_of_p_dvd_index p hpHD) hpH
    · have hpHcard : p.val ∣ Nat.card H := by
        simpa [subgroupPrimeSet] using hpH
      have hpD : p ∈ subgroupPrimeSet D := by
        simpa [subgroupPrimeSet] using hpHcard.trans (Subgroup.card_dvd_of_le hHD)
      exact (hHallD.p_in_pi_of_p_dvd_index p hpDidx) hpD

private theorem theorem_8_11_conclusion_of_MF_eq_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF_eq : MF = section10Msigma M)
    (hMs : Ms = MF) :
    (∀ p : Nat.Primes, ∀ P : Sylow p.val Ms,
        section10AmbientSylowSubgroup Ms P ≠ ⊥ →
          Subgroup.normalizer (section10AmbientSylowSubgroup Ms P : Set G) ≤ M) ∧
      IsHallSubgroup (subgroupPrimeSet MF) MF ∧
        IsHallSubgroup (subgroupPrimeSet Ms) Ms := by
  have hMs_eq_sigma : Ms = section10Msigma M := by
    rw [hMs, hMF_eq]
  have hSigmaHall : IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) :=
    (theorem_10_2_b (G := G) hM).1
  refine ⟨theorem_8_11_normalizer_le_of_eq_msigma (G := G) hM hMs_eq_sigma,
    ?_, ?_⟩
  · rw [hMF_eq]
    exact theorem_8_11_hall_subgroupPrimeSet_of_hall (G := G) hSigmaHall
  · rw [hMs_eq_sigma]
    exact theorem_8_11_hall_subgroupPrimeSet_of_hall (G := G) hSigmaHall

private theorem theorem_8_11_conclusion_of_derived_eq_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hD_eq : ambientDerivedSubgroup M = section10Msigma M)
    (hMs : Ms = ambientDerivedSubgroup M) :
    (∀ p : Nat.Primes, ∀ P : Sylow p.val Ms,
        section10AmbientSylowSubgroup Ms P ≠ ⊥ →
          Subgroup.normalizer (section10AmbientSylowSubgroup Ms P : Set G) ≤ M) ∧
      IsHallSubgroup (subgroupPrimeSet MF) MF ∧
        IsHallSubgroup (subgroupPrimeSet Ms) Ms := by
  have hMs_eq_sigma : Ms = section10Msigma M := by
    rw [hMs, hD_eq]
  have hSigmaHall : IsHallSubgroup (section10SigmaPrimes M) (section10Msigma M) :=
    (theorem_10_2_b (G := G) hM).1
  have hDHall : IsHallSubgroup (subgroupPrimeSet (ambientDerivedSubgroup M))
      (ambientDerivedSubgroup M) := by
    rw [hD_eq]
    exact theorem_8_11_hall_subgroupPrimeSet_of_hall (G := G) hSigmaHall
  have hMF15 : section15MFSubgroup M MF :=
    theorem_8_11_section15MFSubgroup (G := G) hMF
  have hMFleD : MF ≤ ambientDerivedSubgroup M :=
    (corollary_15_5_c (G := G) hM hMF15).1
  have hMFHallD : IsHallSubgroup (subgroupPrimeSet MF)
      (MF.subgroupOf (ambientDerivedSubgroup M)) :=
    theorem_8_11_mf_hall_in_ambientDerived (G := G) hM hMF
  refine ⟨theorem_8_11_normalizer_le_of_eq_msigma (G := G) hM hMs_eq_sigma,
    ?_, ?_⟩
  · exact theorem_8_11_hall_trans (G := G) hMFleD hMFHallD hDHall
  · rw [hMs_eq_sigma]
    exact theorem_8_11_hall_subgroupPrimeSet_of_hall (G := G) hSigmaHall

public theorem theorem_8_11_msChoice_eq_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoice M MF Ms) :
    Ms = section10Msigma M := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U := by
    simpa [section16KUData] using hKU15
  rcases proposition_16_1 (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU with
    ⟨hIiff, _hIIiff, hIIIIViff, _hViff, hDeriff, hMFiff⟩
  rcases hMs with hEarly | hLate
  · rcases hEarly with ⟨hType, hMs_eq⟩
    have hMF_eq : MF = section10Msigma M := hMFiff.mpr hType
    rw [hMs_eq, hMF_eq]
  · rcases hLate with ⟨hType, hMs_eq⟩
    have hCase : section16CaseP1 K U ∧ MF ≠ section10Msigma M :=
      hIIIIViff.mp hType
    have hnotTypeI : ¬ section16TypeI M MF := by
      intro hTypeI
      have hCaseF : section16CaseF K U := hIiff.mp hTypeI
      exact hCase.1.1 hCaseF.1
    have hD_eq_U_sigma : ambientDerivedSubgroup M = U ⊔ section10Msigma M :=
      hDeriff.mpr hnotTypeI
    have hD_eq_sigma : ambientDerivedSubgroup M = section10Msigma M := by
      calc
        ambientDerivedSubgroup M = U ⊔ section10Msigma M := hD_eq_U_sigma
        _ = section10Msigma M := by simp [hCase.1.2]
    rw [hMs_eq, hD_eq_sigma]

public theorem theorem_8_11_of_msChoice
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoice M MF Ms) :
    (∀ p : Nat.Primes, ∀ P : Sylow p.val Ms,
        section10AmbientSylowSubgroup Ms P ≠ ⊥ →
          Subgroup.normalizer (section10AmbientSylowSubgroup Ms P : Set G) ≤ M) ∧
      IsHallSubgroup (subgroupPrimeSet MF) MF ∧
        IsHallSubgroup (subgroupPrimeSet Ms) Ms := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U := by
    simpa [section16KUData] using hKU15
  rcases proposition_16_1 (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU with
    ⟨hIiff, _hIIiff, hIIIIViff, _hViff, hDeriff, hMFiff⟩
  rcases hMs with hEarly | hLate
  · rcases hEarly with ⟨hType, hMs_eq⟩
    have hMF_eq : MF = section10Msigma M := hMFiff.mpr hType
    exact theorem_8_11_conclusion_of_MF_eq_msigma (G := G) hM hMF_eq hMs_eq
  · rcases hLate with ⟨hType, hMs_eq⟩
    have hCase : section16CaseP1 K U ∧ MF ≠ section10Msigma M :=
      hIIIIViff.mp hType
    have hnotTypeI : ¬ section16TypeI M MF := by
      intro hTypeI
      have hCaseF : section16CaseF K U := hIiff.mp hTypeI
      exact hCase.1.1 hCaseF.1
    have hD_eq_U_sigma : ambientDerivedSubgroup M = U ⊔ section10Msigma M :=
      hDeriff.mpr hnotTypeI
    have hD_eq_sigma : ambientDerivedSubgroup M = section10Msigma M := by
      calc
        ambientDerivedSubgroup M = U ⊔ section10Msigma M := hD_eq_U_sigma
        _ = section10Msigma M := by simp [hCase.1.2]
    exact theorem_8_11_conclusion_of_derived_eq_msigma
      (G := G) hM hMF hD_eq_sigma hMs_eq

public theorem theorem_8_11_msChoice_of_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms) :
    msChoice M MF Ms := by
  classical
  have hBG :
      section16TypeI M MF ∨ section16TypeII M MF ∨
        section16TypeIII M MF ∨ section16TypeIV M MF ∨
          section16TypeV M MF :=
    section16_type_exhaustive_of_maximal (G := G) hM hMF
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hSrcI, hnotII, hnotIII, hnotIV, hnotV, hMs_eq⟩
    rcases hBG with hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
    · exact Or.inl ⟨Or.inl hTypeI, hMs_eq⟩
    · exact False.elim
        (hnotII (theorem_8_8_typeII_to_source_public (G := G) hM hMF hTypeII))
    · exact False.elim
        (hnotIII (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
    · exact False.elim
        (hnotIV (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
    · exact False.elim
        (hnotV (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))
  · rcases hII with ⟨hnotI, _hSrcII, hnotIII, hnotIV, hnotV, hMs_eq⟩
    rcases hBG with hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
    · exact False.elim
        (hnotI (theorem_8_8_typeI_to_source_public (G := G) hM hMF hTypeI))
    · exact Or.inl ⟨Or.inr (Or.inl hTypeII), hMs_eq⟩
    · exact False.elim
        (hnotIII (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
    · exact False.elim
        (hnotIV (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
    · exact False.elim
        (hnotV (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))
  · rcases hIII with ⟨hnotI, hnotII, _hSrcIII, hnotIV, hnotV, hMs_eq⟩
    rcases hBG with hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
    · exact False.elim
        (hnotI (theorem_8_8_typeI_to_source_public (G := G) hM hMF hTypeI))
    · exact False.elim
        (hnotII (theorem_8_8_typeII_to_source_public (G := G) hM hMF hTypeII))
    · exact Or.inr ⟨Or.inl hTypeIII, hMs_eq⟩
    · exact False.elim
        (hnotIV (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
    · exact False.elim
        (hnotV (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))
  · rcases hIV with ⟨hnotI, hnotII, hnotIII, _hSrcIV, hnotV, hMs_eq⟩
    rcases hBG with hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
    · exact False.elim
        (hnotI (theorem_8_8_typeI_to_source_public (G := G) hM hMF hTypeI))
    · exact False.elim
        (hnotII (theorem_8_8_typeII_to_source_public (G := G) hM hMF hTypeII))
    · exact False.elim
        (hnotIII (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
    · exact Or.inr ⟨Or.inr hTypeIV, hMs_eq⟩
    · exact False.elim
        (hnotV (theorem_8_8_typeV_to_source_public (G := G) hM hMF hTypeV))
  · rcases hV with ⟨hnotI, hnotII, hnotIII, hnotIV, _hSrcV, hMs_eq⟩
    rcases hBG with hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
    · exact False.elim
        (hnotI (theorem_8_8_typeI_to_source_public (G := G) hM hMF hTypeI))
    · exact False.elim
        (hnotII (theorem_8_8_typeII_to_source_public (G := G) hM hMF hTypeII))
    · exact False.elim
        (hnotIII (theorem_8_8_typeIII_to_source_public (G := G) hM hMF hTypeIII))
    · exact False.elim
        (hnotIV (theorem_8_8_typeIV_to_source_public (G := G) hM hMF hTypeIV))
    · exact Or.inl ⟨Or.inr (Or.inr hTypeV), hMs_eq⟩

public theorem theorem_8_11_msChoiceSource_eq_msigma
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : msChoiceSource M MF Ms) :
    Ms = section10Msigma M := by
  exact theorem_8_11_msChoice_eq_msigma (G := G) hM hMF
    (theorem_8_11_msChoice_of_source (G := G) hM hMF hMs)


end CFSG.Section8
