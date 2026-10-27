module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_12_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 10.12(b) from BG Section 10

This file contains Lemma 10.12(b) from BG Section 10.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_maximal_le_normalizer_sigma_sylow_of_msigma_nilpotent
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {p : Nat.Primes} (hpσ : p ∈ section10SigmaPrimes M)
    (hMσnil : Group.IsNilpotent (section10Msigma M))
    (P : Sylow p.val M) :
    M ≤ Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hP_le_S :
      (P : Subgroup M) ≤ section10MsigmaSubgroup M := by
    exact section10_sylow_le_normal_hall_of_mem
      (H := M) (π := section10SigmaPrimes M)
      (S := section10MsigmaSubgroup M)
      (section10_msigmaSubgroup_isHall hM) hpσ P
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  have hPG_le_Sg : PG ≤ section10Msigma M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyP, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, hP_le_S hyP, rfl⟩
  obtain ⟨T, hPGT⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPGp
  have hT_eq_PG : (T : Subgroup G) = PG :=
    section10_sigma_ambient_sylow_eq_of_le_sylow hpσ P T (by simpa [PG] using hPGT)
  have hT_le_Sg : (T : Subgroup G) ≤ section10Msigma M := by
    intro x hx
    exact hPG_le_Sg (by simpa [hT_eq_PG] using hx)
  let Pσ : Sylow p.val (section10Msigma M) := T.subtype hT_le_Sg
  have hPσmap : (Pσ : Subgroup (section10Msigma M)).map (section10Msigma M).subtype = PG := by
    calc
      (Pσ : Subgroup (section10Msigma M)).map (section10Msigma M).subtype =
          (T : Subgroup G) := by
            change ((T : Subgroup G).subgroupOf (section10Msigma M)).map
              (section10Msigma M).subtype = (T : Subgroup G)
            exact Subgroup.map_subgroupOf_eq_of_le
              (G := G) (H := (T : Subgroup G)) (K := section10Msigma M) hT_le_Sg
      _ = PG := hT_eq_PG
  let : Group.IsNilpotent (section10Msigma M) := hMσnil
  have hPσnormal : (Pσ : Subgroup (section10Msigma M)).Normal :=
    Group.IsNilpotent.sylow_normal (p := p.val) inferInstance Pσ
  have hPσchar : (Pσ : Subgroup (section10Msigma M)).Characteristic :=
    Sylow.characteristic_of_normal Pσ hPσnormal
  let : (Pσ : Subgroup (section10Msigma M)).Characteristic := hPσchar
  have hnormSg_le_normPG :
      Subgroup.normalizer (section10Msigma M : Set G) ≤ Subgroup.normalizer (PG : Set G) := by
    have hnorm :=
      section10_normalizer_le_normalizer_map_subtype_of_characteristic_pre
        (G := G) (section10Msigma M) (Pσ : Subgroup (section10Msigma M))
    simpa [hPσmap] using hnorm
  simpa [PG] using (section10_le_normalizer_msigma (G := G) (M := M)).trans hnormSg_le_normPG

private theorem CFSG.section10_sigma_primes_disjoint_of_nonconj_nilpotent
    {M H : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hH : H ∈ section9MaximalSubgroups G) (hconj : ∀ g : G, H.conjBy g ≠ M)
    (hMσnil : Group.IsNilpotent (section10Msigma M)) :
    Disjoint (section10SigmaPrimes M) (section10SigmaPrimes H) := by
  classical
  rw [Set.disjoint_left]
  intro p hpσM hpσH
  have : Fact p.val.Prime := ⟨p.property⟩
  let P : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  obtain ⟨T, hPGT⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hPGp
  have hT_eq_PG : (T : Subgroup G) = PG :=
    section10_sigma_ambient_sylow_eq_of_le_sylow hpσM P T (by simpa [PG] using hPGT)
  have hM_le_normPG :
      M ≤ Subgroup.normalizer (PG : Set G) := by
    simpa [PG] using
      section10_maximal_le_normalizer_sigma_sylow_of_msigma_nilpotent
        (G := G) hM hpσM hMσnil P
  rcases section10_exists_conjBy_le_of_isPGroup_of_sigma
      (G := G) (M := H) (Y := PG) hpσH hPGp with
    ⟨a, hPG_le_Ha⟩
  have hT_le_Ha : (T : Subgroup G) ≤ H.conjBy a := by
    intro x hx
    exact hPG_le_Ha (by simpa [hT_eq_PG] using hx)
  let THa : Sylow p.val (H.conjBy a) := T.subtype hT_le_Ha
  have hTHa_map :
      section10AmbientSylowSubgroup (H.conjBy a) THa = PG := by
    calc
      section10AmbientSylowSubgroup (H.conjBy a) THa =
          (T : Subgroup G) := by
            change ((T : Subgroup G).subgroupOf (H.conjBy a)).map
              (H.conjBy a).subtype = (T : Subgroup G)
            exact Subgroup.map_subgroupOf_eq_of_le
              (G := G) (H := (T : Subgroup G)) (K := H.conjBy a) hT_le_Ha
      _ = PG := hT_eq_PG
  have hnormPG_le_Ha : Subgroup.normalizer (PG : Set G) ≤ H.conjBy a := by
    have hpσHa : p ∈ section10SigmaPrimes (H.conjBy a) :=
      section10_sigma_conjBy hpσH a
    simpa [hTHa_map] using section10_sigma_sylow_normalizer_le hpσHa THa
  have hM_le_Ha : M ≤ H.conjBy a := hM_le_normPG.trans hnormPG_le_Ha
  have hHa : H.conjBy a ∈ section9MaximalSubgroups G :=
    section10_maximal_conjBy hH a
  have hHa_eq_M : H.conjBy a = M := (hM.le_iff_eq hHa.1).mp hM_le_Ha
  exact (hconj a) hHa_eq_M

/-- Lemma 10.12(b). -/
public theorem CFSG.lemma_10_12_b
    {M H : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hH : H ∈ section9MaximalSubgroups G) (hconj : ∀ g : G, H.conjBy g ≠ M)
    (hMσnil : Group.IsNilpotent (section10Msigma M)) :
    Disjoint (section10Msigma M) (section10Msigma H) ∧
      Disjoint (section10SigmaPrimes M) (section10SigmaPrimes H) := by
  classical
  have hprimes : Disjoint (section10SigmaPrimes M) (section10SigmaPrimes H) :=
    section10_sigma_primes_disjoint_of_nonconj_nilpotent hM hH hconj hMσnil
  exact
    ⟨section10_disjoint_of_hall_disjoint_primes
        (theorem_10_2_b (G := G) hM).1 (theorem_10_2_b (G := G) hH).1 hprimes,
      hprimes⟩

end Section10
