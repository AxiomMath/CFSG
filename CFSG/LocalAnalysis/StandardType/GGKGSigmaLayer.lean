module

public import CFSG.LocalAnalysis.StandardType.GGE6KGLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGFamCentralizerBridge
import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvAll

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE8F CFSG.StandardType.LayerExc CFSG.StandardType.LayerSixE

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {τ : Tag} {K : Type} [Field K]


theorem ggLayerOf_map_famCentralizer (F : Set (Fin τ.rank → Kˣ))
    (hW : ∃ k, LayerFacts.ggDer (famStabilizerSubgroup F) k ≤ famReflectionGroup F)
    (hqs : IsQuasisimple (rootSpan τ K (famKernel F))) :
    GGLayerOf ((famCentralizer F).map (adjointGroup τ K).subtype) (rootSpan τ K (famKernel F)) := by
  obtain ⟨k, hk⟩ := hW
  let X : Subgroup (ModGL τ K) := (famCentralizer F).map (adjointGroup τ K).subtype
  let U : Subgroup (ModGL τ K) := rootSpan τ K (famKernel F)
  let M : Subgroup (ModGL τ K) := torusGroup τ K ⊔ U
  have hperf : ⁅U, U⁆ = U := Subgroup.isPerfect_iff.mp hqs.1
  have hUM : U ≤ M := le_sup_right
  have hMX : M ≤ X := torus_sup_rootSpan_le_map_famCentralizer (K := K) F
  have hcomm : ⁅M, M⁆ ≤ U :=
    commutator_torus_sup_rootSpan_le (S := famKernel F) (fun α hα => hα.1)
  have hUeq : U = ⁅M, M⁆ := by
    refine le_antisymm ?_ hcomm
    have hcm : ⁅U, U⁆ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hUM hUM
    rwa [hperf] at hcm
  have hMle : X ≤ M ⊔ (famWeylReps (K := K) F).map (monomialSubgroup τ K).subtype :=
    map_famCentralizer_le_sup (K := K) F
  have hYN : (famWeylReps (K := K) F).map (monomialSubgroup τ K).subtype ≤
      Subgroup.normalizer (M : Set (ModGL τ K)) :=
    map_famWeylReps_le_normalizer (K := K) F
  have hder : LayerFacts.ggDer X (k + 1) ≤ U := by
    rw [LayerFacts.ggDer_succ]
    have h1 := (LayerFacts.ggDer_mono hMle k).trans
      ((ggDer_sup_le_of_le_normalizer hYN k).trans
        (sup_le le_rfl (ggDer_map_famWeylReps_le hk)))
    exact (Subgroup.commutator_mono h1 h1).trans hcomm
  have hXN : X ≤ Subgroup.normalizer (U : Set (ModGL τ K)) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx u hu
    have hxM : x ∈ Subgroup.normalizer (M : Set (ModGL τ K)) :=
      map_famCentralizer_le_normalizer (K := K) F hx
    have hconj : ∀ m ∈ M, MulAut.conj x m ∈ M := by
      intro m hm
      have h := (Subgroup.mem_normalizer_iff.mp hxM m).mp hm
      simpa [MulAut.conj_apply] using h
    have hsub : ⁅M, M⁆ ≤ U.comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      change MulAut.conj x ⁅a, b⁆ ∈ U
      rw [MulAut.conj_apply, conjugate_commutatorElement]
      exact hcomm (Subgroup.commutator_mem_commutator (hconj a ha) (hconj b hb))
    rw [hUeq] at hu
    have h := Subgroup.mem_comap.mp (hsub hu)
    simpa [MulAut.conj_apply] using h
  change GGLayerOf X U
  refine ⟨hUM.trans hMX, Subgroup.normal_subgroupOf_of_le_normalizer hXN, hqs, ?_⟩
  intro P hPX hPperf
  have hPder : LayerFacts.ggDer P (k + 1) = P := LayerFacts.ggDer_of_perfect hPperf (k + 1)
  have hmono : LayerFacts.ggDer P (k + 1) ≤ LayerFacts.ggDer X (k + 1) :=
    LayerFacts.ggDer_mono hPX (k + 1)
  rw [hPder] at hmono
  exact hmono.trans hder

theorem ggLayerOf_map_famCentralizer_of_pPower [Finite K] {p : ℕ} (hp : p.Prime)
    (F : Set (Fin τ.rank → Kˣ)) (hF : ∀ a ∈ F, ∃ n : ℕ, a ^ p ^ n = 1)
    (hqs : IsQuasisimple (rootSpan τ K (famKernel F))) :
    GGLayerOf ((famCentralizer F).map (adjointGroup τ K).subtype) (rootSpan τ K (famKernel F)) :=
  ggLayerOf_map_famCentralizer F (exists_ggDer_famStabilizerSubgroup_le_reflection hp F hF) hqs

end CFSG.StandardType.KGL

end
