module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOn
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharCoatom
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharLinRadical
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Subgroup CFSG GGLinRad

variable {F : Type*} [Field F] {n : ℕ}

theorem isCharacteristicP_linProjStabilizer (p : ℕ) [Fact p.Prime] [CharP F p]
    {W : Submodule F (Fin n → F)} (h0 : ⊥ < W) (htop : W < ⊤) :
    IsCharacteristicP p ↥(projStabilizer W) := by
  refine isCharacteristicP_of_normalPSubgroup_centralizer_le
    (Q := (radical W).map (proj n F)) (Subgroup.map_mono (radical_le_stabilizer W)) ?_
    ((isPGroup_radical p W).map _) ?_
  · refine ⟨fun x hx y => ?_⟩
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨s, hs, hsy⟩ := y.2
    refine Subgroup.mem_subgroupOf.2 ⟨s * u * s⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.1 ((radical_normal W).conj_mem
        ⟨u, radical_le_stabilizer W hu⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨s, hs⟩)
    · simp only [map_mul, map_inv, hux, hsy]
      rfl
  · rintro x ⟨hxc, s, hs, rfl⟩
    have hcs : ∀ u ∈ radical W, s * u * s⁻¹ * u⁻¹ ∈ scalars n F := by
      intro u hu
      rw [← ker_proj, MonoidHom.mem_ker]
      have h := mem_centralizer_iff.1 hxc (proj n F u) ⟨u, hu, rfl⟩
      simp only [map_mul, map_inv]
      rw [← h]
      group
    obtain ⟨z, hz, q, hq, rfl⟩ := exists_scalar_mul_mem_radical h0 htop hs hcs
    have hz' : z ∈ (proj n F).ker := by
      rw [ker_proj]
      exact hz
    rw [map_mul, MonoidHom.mem_ker.1 hz', one_mul]
    exact ⟨q, hq, rfl⟩

theorem ggNormalizerOvergroupsChar_projectiveSL [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 1 ≤ n) : GGNormalizerOvergroupsChar p (projectiveSL n F) := by
  refine GGNormalizerOvergroupsChar.of_coatoms fun S M hS hSi hNM hM => ?_
  have hmem : M ∈ maximalParabolics (projectiveSL n F) p :=
    ⟨hM, normalizer (S : Set (projectiveSL n F)),
      ⟨hS.toSylow hSi, by rw [IsPGroup.toSylow_coe]⟩, hNM⟩
  rw [(maximal_parabolics (K := F) p hn).1] at hmem
  obtain ⟨W, ⟨h0, htop⟩, rfl⟩ := hmem
  exact isCharacteristicP_linProjStabilizer p h0 htop

theorem ggLieParabolicCharInputOn_A :
    GGLieParabolicCharInputOn fun d => ∃ r q, d.1 = .A r q := by
  rintro K _ _ d ⟨r, q, hm⟩ ⟨e⟩ - S X hS hSi hNX hX
  have hp : d.1.characteristic = q.p := by
    rw [hm]
    exact TauCeti.LieTypeIndex.characteristic_A r q
  rw [hp] at hS hSi ⊢
  have hv : (TauCeti.LieTypeIndex.A r q).Valid := hm ▸ d.2
  obtain rfl : d = ⟨.A r q, hv⟩ := Subtype.ext hm
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let φ : K ≃* projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _)
  exact (GGNormalizerOvergroupsChar.of_mulEquiv φ
    (ggNormalizerOvergroupsChar_projectiveSL q.p (Nat.succ_pos r))) S X hS hSi hNX hX

end CFSG.StandardType
