module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u


/-- Peterfalvi `(8.18)`. -/


private theorem theorem_8_17_subgroupPrimeSet_section10Msigma_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    subgroupPrimeSet (section10Msigma M) = section10SigmaPrimes M := by
  classical
  ext p
  constructor
  · intro hp
    exact (section10_msigma_isHall (G := G) hM).p_in_pi_of_p_dvd_card p (by
      simpa [subgroupPrimeSet] using hp)
  · intro hpσ
    have hpMset : p ∈ subgroupPrimeSet M := by
      exact (show p ∈ subgroupPrimeSet M ∧
        ∃ P : Sylow p.val M,
          Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤ M from by
          simpa [section10SigmaPrimes] using hpσ).1
    have hpM : p.val ∣ Nat.card M := by
      simpa [subgroupPrimeSet] using hpMset
    have hKHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
      section10_msigmaSubgroup_isHall (G := G) hM
    have hprod :
        p.val ∣ (section10MsigmaSubgroup M).index *
          Nat.card (section10MsigmaSubgroup M) := by
      simpa [Subgroup.index_mul_card (H := section10MsigmaSubgroup M)] using hpM
    rcases p.property.dvd_or_dvd hprod with hpidx | hpcard
    · exact False.elim ((hKHall.p_in_pi_of_p_dvd_index p hpidx) hpσ)
    · have hcard_eq : Nat.card (section10Msigma M) =
          Nat.card (section10MsigmaSubgroup M) := by
        simpa [section10Msigma] using
          (Subgroup.card_map_of_injective
            (K := section10MsigmaSubgroup M) (f := M.subtype) M.subtype_injective)
      exact by
        simpa [subgroupPrimeSet, hcard_eq] using hpcard

/-- In PF `(8.10)` source notation, the prime support of `M_s` is the BG
`sigma(M)` prime set. -/
public theorem theorem_8_17_subgroupPrimeSet_msigma_eq
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : notation_8_10_source_data M MF Ms A A0 A1) :
    subgroupPrimeSet Ms = section10SigmaPrimes M := by
  rcases hNotation with ⟨hM, hMF, hMs, _hA1, _hCases⟩
  rw [theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs]
  exact theorem_8_17_subgroupPrimeSet_section10Msigma_eq (G := G) hM


private theorem theorem_8_17_tildeA1_eq_conjugates_tildeM_sourceR
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    tildeA1 = section16ConjugatesOfSetBySet (section16TildeM M R) Set.univ := by
  classical
  rcases hRep with ⟨h10, h14⟩
  rcases h10 with ⟨hM, hMF, hMs, hA1, _hCases⟩
  rcases h14 with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hUnique, _hReq, _htildeA, _htildeA0, htildeA1⟩
  have hMs_eq : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  ext y
  constructor
  · intro hy
    rw [htildeA1] at hy
    rcases hy with ⟨a, haA1, x, hxLeft, g, hg, rfl⟩
    rcases hxLeft with ⟨r, hr, rfl⟩
    have haMs_ne : a ∈ Ms ∧ a ≠ 1 := by
      simpa [hA1, a1Set, section16NonidentityElements] using haA1
    have haSigma : a ∈ section10Msigma M := by
      simpa [hMs_eq] using haMs_ne.1
    refine ⟨a * r, ?_, g, hg, rfl⟩
    exact ⟨a, haSigma, haMs_ne.2, r, hr, rfl⟩
  · intro hy
    rcases hy with ⟨x, hxTilde, g, hg, rfl⟩
    rcases hxTilde with ⟨a, haSigma, hane, r, hr, rfl⟩
    rw [htildeA1]
    have haMs : a ∈ Ms := by
      simpa [hMs_eq] using haSigma
    have haA1 : a ∈ A1 := by
      simpa [hA1, a1Set, section16NonidentityElements] using And.intro haMs hane
    refine ⟨a, haA1, a * r, ?_, g, hg, rfl⟩
    exact ⟨r, hr, rfl⟩

private theorem theorem_8_17_representativeR_eq_section14R_on_A1
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    ∀ a : G, a ∈ A1 → R a = section14R a := by
  classical
  rcases hRep with ⟨h10, h14⟩
  rcases h10 with ⟨hM, hMF, hMs, hA1, _hCases⟩
  rcases h14 with
    ⟨hA1A, hAA0, hD, hRbot, hUnique, hReq, _htildeA, _htildeA0, _htildeA1⟩
  have hMs_eq : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  intro a haA1
  have haMs_ne : a ∈ Ms ∧ a ≠ 1 := by
    simpa [hA1, a1Set, section16NonidentityElements] using haA1
  have haSigma : a ∈ section10Msigma M := by
    simpa [hMs_eq] using haMs_ne.1
  have haA0 : a ∈ A0 := hAA0 (hA1A haA1)
  by_cases hCGM : Subgroup.centralizer ({a} : Set G) ≤ M
  · have haA0diff : a ∈ A0 \ D := by
      refine ⟨haA0, ?_⟩
      intro haD
      have haD' : a ∈ section8DSet M A0 := by
        simpa [hD] using haD
      exact haD'.2 hCGM
    have hRbot_a : R a = (⊥ : Subgroup G) := hRbot a haA0diff
    have h14bot : section14R a = (⊥ : Subgroup G) :=
      section16_section14R_eq_bot_of_centralizer_le_public
        (G := G) hM haSigma haMs_ne.2 hCGM
    exact hRbot_a.trans h14bot.symm
  · have haD : a ∈ D := by
      rw [hD]
      exact ⟨haA0, hCGM⟩
    rcases hUnique a haD with ⟨L, hLmem, hLuniq⟩
    have hNpack :=
      section16_section14N_data_of_not_centralizer_le
        (G := G) hM haSigma haMs_ne.2 hCGM
    have hN_eq_L : section14N a = L := hLuniq (section14N a) hNpack.1
    have hSet :
        section9MaximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)) = {L} := by
      ext N
      constructor
      · intro hNmem
        have hNL : N = L := hLuniq N hNmem
        simp [hNL]
      · intro hNmem
        have hNL : N = L := by
          simpa using hNmem
        simpa [hNL] using hLmem
    have hLF : section16MFSubgroup L (section10Msigma L) := by
      simpa [hN_eq_L] using hNpack.2.2
    have hR_eq : R a = elementCentralizerIn (section10Msigma L) a :=
      hReq a haD L (section10Msigma L) hSet hLF
    have h14_eq : section14R a = elementCentralizerIn (section10Msigma L) a := by
      simpa [hN_eq_L] using hNpack.2.1
    exact hR_eq.trans h14_eq.symm

private theorem theorem_8_17_tildeM_representativeR_eq_section14R
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R)
    (hR : ∀ a : G, a ∈ A1 → R a = section14R a) :
    section16TildeM M R =
      section16TildeM M (fun x : G => section14R x) := by
  classical
  rcases hRep with ⟨h10, _h14⟩
  rcases h10 with ⟨hM, hMF, hMs, hA1, _hCases⟩
  have hMs_eq : Ms = section10Msigma M :=
    theorem_8_11_msChoiceSource_eq_msigma (G := G) hM hMF hMs
  ext y
  constructor
  · intro hy
    rcases hy with ⟨a, haSigma, hane, r, hr, rfl⟩
    have haMs : a ∈ Ms := by
      simpa [hMs_eq] using haSigma
    have haA1 : a ∈ A1 := by
      simpa [hA1, a1Set, section16NonidentityElements] using And.intro haMs hane
    refine ⟨a, haSigma, hane, r, ?_, rfl⟩
    simpa [hR a haA1] using hr
  · intro hy
    rcases hy with ⟨a, haSigma, hane, r, hr, rfl⟩
    have haMs : a ∈ Ms := by
      simpa [hMs_eq] using haSigma
    have haA1 : a ∈ A1 := by
      simpa [hA1, a1Set, section16NonidentityElements] using And.intro haMs hane
    refine ⟨a, haSigma, hane, r, ?_, rfl⟩
    simpa [hR a haA1] using hr

private theorem theorem_8_17_tildeA1_eq_conjugates_tildeM_section14R
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    tildeA1 =
      section16ConjugatesOfSetBySet
        (section16TildeM M (fun x : G => section14R x)) Set.univ := by
  have hR : ∀ a : G, a ∈ A1 → R a = section14R a :=
    theorem_8_17_representativeR_eq_section14R_on_A1 (G := G) hRep
  calc
    tildeA1 = section16ConjugatesOfSetBySet (section16TildeM M R) Set.univ := by
      exact theorem_8_17_tildeA1_eq_conjugates_tildeM_sourceR (G := G) hRep
    _ = section16ConjugatesOfSetBySet
          (section16TildeM M (fun x : G => section14R x)) Set.univ := by
      rw [theorem_8_17_tildeM_representativeR_eq_section14R (G := G) hRep hR]

public theorem theorem_8_17_tildeA1_eq_conjugates_tildeM_section14R_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hRep : theorem_8_17_representative_source_data M MF Ms A A0 A1 D
      tildeA tildeA0 tildeA1 R) :
    tildeA1 =
      section16ConjugatesOfSetBySet
        (section16TildeM M (fun x : G => section14R x)) Set.univ :=
  theorem_8_17_tildeA1_eq_conjugates_tildeM_section14R (G := G) hRep


end CFSG.Section8
