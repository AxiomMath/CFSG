module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOn
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharCoatom
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharUniRadical
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Subgroup CFSG GGUniRad

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem isCharacteristicP_uniProjStabilizer (h : UnitaryFieldData p f K)
    {W : Submodule K (HypIndex r ε → K)} (h0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) :
    IsCharacteristicP p ↥(projIsoStabilizer h r ε W) := by
  refine isCharacteristicP_of_normalPSubgroup_centralizer_le
    (Q := (uniRadical h r ε W).map (hypProj h r ε))
    (Subgroup.map_mono (uniRadical_le_isoStabilizer h W)) ?_
    ((isPGroup_uniRadical h W).map _) ?_
  · refine ⟨fun x hx y => ?_⟩
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨s, hs, hsy⟩ := y.2
    refine Subgroup.mem_subgroupOf.2 ⟨s * u * s⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.1 ((uniRadical_normal h W).conj_mem
        ⟨u, uniRadical_le_isoStabilizer h W hu⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨s, hs⟩)
    · simp only [map_mul, map_inv, hux, hsy]
      rfl
  · rintro x ⟨hxc, s, hs, rfl⟩
    have hcs : ∀ u ∈ uniRadical h r ε W, s * u * s⁻¹ * u⁻¹ ∈ hypScalars h r ε := by
      intro u hu
      rw [← ker_hypProj, MonoidHom.mem_ker]
      have h' := mem_centralizer_iff.1 hxc (hypProj h r ε u) ⟨u, hu, rfl⟩
      simp only [map_mul, map_inv]
      rw [← h']
      group
    obtain ⟨z, hz, q, hq, rfl⟩ := exists_scalar_mul_mem_uniRadical h h0 hW hs hcs
    have hz' : z ∈ (hypProj h r ε).ker := by
      rw [ker_hypProj]
      exact hz
    rw [map_mul, MonoidHom.mem_ker.1 hz', one_mul]
    exact ⟨q, hq, rfl⟩

theorem ggNormalizerOvergroupsChar_hypPSU (h : UnitaryFieldData p f K)
    (hr : 1 ≤ r) (hε : ε ≤ 1) : GGNormalizerOvergroupsChar p (hypPSU h r ε) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := h.finite
  refine GGNormalizerOvergroupsChar.of_coatoms fun S M hS hSi hNM hM => ?_
  have hmem : M ∈ maximalParabolics h r ε :=
    ⟨hM, normalizer (S : Set (hypPSU h r ε)),
      ⟨hS.toSylow hSi, by rw [IsPGroup.toSylow_coe]⟩, hNM⟩
  rw [(unitary_maximal_parabolics h hr hε).1] at hmem
  obtain ⟨W, ⟨h0, hW⟩, rfl⟩ := hmem
  exact isCharacteristicP_uniProjStabilizer h h0 hW

theorem ggLieParabolicCharInputOn_twistedA :
    GGLieParabolicCharInputOn fun d => ∃ r q, d.1 = .twistedA r q := by
  rintro K _ _ d ⟨r', q, hm⟩ ⟨e⟩ - S X hS hSi hNX hX
  have hp : d.1.characteristic = q.p := by
    rw [hm]
    exact TauCeti.LieTypeIndex.characteristic_twistedA r' q
  rw [hp] at hS hSi ⊢
  have hv : (TauCeti.LieTypeIndex.twistedA r' q).Valid := hm ▸ d.2
  obtain rfl : d = ⟨.twistedA r' q, hv⟩ := Subtype.ext hm
  obtain ⟨hadm, K', _, _, hcard, ⟨φ⟩⟩ :=
    QuasithinUnique.SQTK.statedClassicalModel_twistedA r' q hv e
  have hn3 : 3 ≤ r' + 1 := hadm.2.2.1
  have hU : UnitaryFieldData q.p q.exponent K' :=
    ⟨q.prime_p, q.exponent_pos, by rw [hcard, ← pow_mul, mul_comm]⟩
  generalize hn : r' + 1 = n at φ hn3
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) hU
  let ψ : K ≃* hypPSU hU r ε := φ.trans (hypPSUEquivStatedProj hU hR (by omega)).symm
  exact (GGNormalizerOvergroupsChar.of_mulEquiv ψ
    (ggNormalizerOvergroupsChar_hypPSU hU (by omega) hε)) S X hS hSi hNX hX

end CFSG.StandardType
