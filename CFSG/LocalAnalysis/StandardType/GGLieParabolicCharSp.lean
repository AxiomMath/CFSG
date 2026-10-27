module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOn
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharCoatom
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharSpRadical
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher Subgroup CFSG GGSpRad

variable {r : ℕ} {K : Type} [Field K]

theorem isCharacteristicP_spProjStabilizer (p : ℕ) [Fact p.Prime] [CharP K p]
    {W : Submodule K (Fin r ⊕ Fin r → K)} (h0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K r) W) :
    IsCharacteristicP p ↥(projStabilizer r K W) := by
  refine isCharacteristicP_of_normalPSubgroup_centralizer_le
    (Q := (spRadical W).map (proj r K)) (Subgroup.map_mono (spRadical_le_stabilizer W)) ?_
    ((isPGroup_spRadical p W).map _) ?_
  · refine ⟨fun x hx y => ?_⟩
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨s, hs, hsy⟩ := y.2
    refine Subgroup.mem_subgroupOf.2 ⟨s * u * s⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.1 ((spRadical_normal W).conj_mem
        ⟨u, spRadical_le_stabilizer W hu⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨s, hs⟩)
    · simp only [map_mul, map_inv, hux, hsy]
      rfl
  · rintro x ⟨hxc, s, hs, rfl⟩
    have hcs : ∀ u ∈ spRadical W, s * u * s⁻¹ * u⁻¹ ∈ spScalars r K := by
      intro u hu
      rw [← ker_proj, MonoidHom.mem_ker]
      have h := mem_centralizer_iff.1 hxc (proj r K u) ⟨u, hu, rfl⟩
      simp only [map_mul, map_inv]
      rw [← h]
      group
    obtain ⟨z, hz, q, hq, rfl⟩ := exists_scalar_mul_mem_spRadical h0 hW hs hcs
    have hz' : z ∈ (proj r K).ker := by
      rw [ker_proj]
      exact hz
    rw [map_mul, MonoidHom.mem_ker.1 hz', one_mul]
    exact ⟨q, hq, rfl⟩

theorem ggNormalizerOvergroupsChar_statedProjSp [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hr : 1 ≤ r) : GGNormalizerOvergroupsChar p (StatedProj (StatedSp r K)) := by
  refine GGNormalizerOvergroupsChar.of_coatoms fun S M hS hSi hNM hM => ?_
  have hmem : M ∈ spMaximalParabolics r K p :=
    ⟨hM, normalizer (S : Set (StatedProj (StatedSp r K))),
      ⟨hS.toSylow hSi, by rw [IsPGroup.toSylow_coe]⟩, hNM⟩
  rw [(maximal_parabolics (K := K) p hr).1] at hmem
  obtain ⟨W, h0, hW, rfl⟩ := hmem
  exact isCharacteristicP_spProjStabilizer p h0 hW

theorem ggLieParabolicCharInputOn_C :
    GGLieParabolicCharInputOn fun d => ∃ r q, d.1 = .C r q := by
  rintro K _ _ d ⟨r, q, hm⟩ ⟨e⟩ - S X hS hSi hNX hX
  have hp : d.1.characteristic = q.p := by
    rw [hm]
    exact TauCeti.LieTypeIndex.characteristic_C r q
  rw [hp] at hS hSi ⊢
  have hv : (TauCeti.LieTypeIndex.C r q).Valid := hm ▸ d.2
  obtain rfl : d = ⟨.C r q, hv⟩ := Subtype.ext hm
  obtain ⟨hadm, K', _, _, hcard, ⟨φ⟩⟩ := QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI := Fintype.ofFinite K'
  haveI : CharP K' q.p := charP_of_card_eq_prime_pow (f := q.exponent)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  exact (GGNormalizerOvergroupsChar.of_mulEquiv φ
    (ggNormalizerOvergroupsChar_statedProjSp q.p (by have := hadm.2.2; omega))) S X hS hSi hNX hX

end CFSG.StandardType
