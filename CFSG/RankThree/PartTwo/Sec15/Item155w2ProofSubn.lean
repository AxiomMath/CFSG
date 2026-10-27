module

import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof155w2

theorem le_normalizer_centralizerSection {H K M : Subgroup G}
    (hK : H ≤ Subgroup.normalizer (K : Set G)) (hM : H ≤ Subgroup.normalizer (M : Set G)) :
    H ≤ Subgroup.normalizer (centralizerSection K M : Set G) := by
  intro h hh
  refine Sec13.Item138Proof.mem_normalizer_of_map_le ?_
  rintro _ ⟨s, ⟨hsK, hsM, hs⟩, rfl⟩
  have hhK : h ∈ Subgroup.normalizer (K : Set G) := hK hh
  have hhM : h ∈ Subgroup.normalizer (M : Set G) := hM hh
  refine ⟨mul_mem (mul_mem hhK hsK) (inv_mem hhK), mul_mem (mul_mem hhM hsM) (inv_mem hhM),
    fun k hk => ?_⟩
  have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (inv_mem hhK) k).mp hk
  have h1 : ⁅h⁻¹ * k * h⁻¹⁻¹, s⁆ ∈ M := hs _ hk'
  have h2 : h * ⁅h⁻¹ * k * h⁻¹⁻¹, s⁆ * h⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp hhM _).mp h1
  have he : h * ⁅h⁻¹ * k * h⁻¹⁻¹, s⁆ * h⁻¹ = ⁅k, (MulAut.conj h).toMonoidHom s⁆ := by
    simp only [commutatorElement_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rwa [he] at h2

theorem inSubgroup_oResidual_two_le {R B : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRB : R ≤ Subgroup.normalizer (B : Set G)) : inSubgroup (oResidual 2) (R ⊔ B) ≤ B := by
  rw [inSubgroup_oResidual_eq_closure, Subgroup.closure_le]
  rintro x ⟨hx, hco⟩
  rw [sup_comm] at hx
  exact mem_left_of_coprime_of_isPGroup Nat.prime_two hRB hR2 hx hco

end Proof155w2

open Proof155w2

end CFSG.RankThree.PartTwo.Sec15
