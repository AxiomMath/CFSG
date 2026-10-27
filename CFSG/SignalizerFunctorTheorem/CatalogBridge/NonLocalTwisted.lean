module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.RegularLemmaR
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.AdjointRep
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SignalizerFunctorTheorem.NonLocalExc

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem exists_orbit_mem (t : TwistTag) (i : Fin t.tag.rank) :
    ∃ a : Fin t.foldedTag.rank, i ∈ t.orbit a := by
  revert i
  cases t <;> decide

theorem count_orbit_perm (t : TwistTag) :
    ∀ (a : Fin t.foldedTag.rank) (i : Fin t.tag.rank), i ∈ t.orbit a →
      ((List.range (t.orbit a).card).map fun k => (t.perm ^ k) (t.orbitMin a)).count i = 1 := by
  cases t <;> decide

theorem hasCoord_orbitX_one
    {t : TwistTag} {K : Type} [Field K] (σ : K →+* K)
    (a : Fin t.foldedTag.rank) {i : Fin t.tag.rank} (hi : i ∈ t.orbit a) :
    HasCoord i (orbitX t K σ a 1 : ModGL t.tag K) 1 := by
  have h := hasCoord_list_prod_xUnit_one (K := K)
    ((List.range (t.orbit a).card).map fun k => (t.perm ^ k) (t.orbitMin a)) i
  rw [count_orbit_perm t a i hi, Nat.cast_one] at h
  rw [coe_orbitX]
  simpa [List.map_map, Function.comp_def] using h

theorem nonLocalized_twisted_of_simple
    (t : TwistTag) (r : ℕ) [Fact r.Prime] {K k : Type}
    [Field K] [Finite K] [CharP K r] [Field k] (ι : k →+* K) (σ : K →+* K) (σ₀ : k →+* k)
    (hσ₀ : Function.Surjective σ₀) (hσι : ∀ c, σ (ι c) = ι (σ₀ c))
    (hs : IsSimpleGroup ↥(((graphFixedRootGroup t k σ₀).map (baseChangeGL ι)).subgroupOf
      (graphFixedRootGroup t K σ)))
    (R : Subgroup ↥(graphFixedRootGroup t K σ))
    (hRJ : R ≤ ((graphFixedRootGroup t k σ₀).map (baseChangeGL ι)).subgroupOf
      (graphFixedRootGroup t K σ))
    (hR : ¬ Nat.card R ∣ (t.tag.rank + t.tag.rootCount).factorial) :
    NonLocalized (((graphFixedRootGroup t k σ₀).map (baseChangeGL ι)).subgroupOf
      (graphFixedRootGroup t K σ)) := by
  classical
  let C := graphFixedRootGroup t K σ
  let J : Subgroup (ModGL t.tag K) := (graphFixedRootGroup t k σ₀).map (baseChangeGL ι)
  have hXC : C ≤ adjointGroup t.tag K :=
    (graphFixedRootGroup_le t K σ).trans (twistedFixedGroup_le_adjointGroup t K σ)
  have hJX : J ≤ C := map_baseChangeGL_graphFixedRootGroup_le hσ₀ hσι
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ J := by
    refine ⟨canonicalRep (coxeterSystem t.tag) k w₀, ?_, baseChangeGL_canonicalRep ι w₀⟩
    exact canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hw₀)
  choose a ha using exists_orbit_mem t
  have hyJ : ∀ i, (orbitX t K σ (a i) 1 : ModGL t.tag K) ∈ J := by
    intro i
    refine ⟨(orbitX t k σ₀ (a i) 1 : ModGL t.tag k),
      graphFixedPosUnipotent_le_graphFixedRootGroup t k σ₀
        (orbitX_mem_graphFixedPosUnipotent t σ₀ (a i) 1), ?_⟩
    rw [baseChangeGL_orbitX hσι (a i) 1]
    congr 2
    exact Subtype.ext (map_one ι)
  have hyU : ∀ i, (orbitX t K σ (a i) 1 : ModGL t.tag K) ∈ posUnipotent t.tag K := fun i =>
    (Subgroup.mem_inf.1 (orbitX_mem_graphFixedPosUnipotent t σ (a i) 1)).1
  let F := AlgebraicClosure K
  have hFr : CharP F r := charP_of_injective_algebraMap (algebraMap K F).injective r
  let ρ : ↥C →* Module.End F (Label t.tag → F) := (adjRep t.tag K F).comp C.subtype
  have hρ : Function.Injective ρ := (adjRep_injective t.tag K F).comp Subtype.val_injective
  have hR' : ¬ Nat.card R ∣ (Module.finrank F (Label t.tag → F)).factorial := by
    rw [finrank_label_pi, card_label_eq]
    exact hR
  exact nonLocalized_of_regular_data (τ := t.tag) r hXC hJX hs
    (y := fun i => (orbitX t K σ (a i) 1 : ModGL t.tag K)) hyJ hyU (c := fun _ => 1)
    (fun _ => one_ne_zero) (fun i => hasCoord_orbitX_one σ (a i) (ha i)) hw₀ hn ρ hρ R hRJ hR'

end CFSG.SignalizerFunctorTheorem.CatalogBridge
