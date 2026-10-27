module

public import CFSG.LieType.Universal.RootData
public import CFSG.Timmesfeld.ARS.CaseEWeight
import CFSG.LieType.Steinberg.BruhatWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.Timmesfeld.ARS

theorem ggKGCent_exists_weyl {K : Type*} [Group K] {D : UniversalRootDatum K}
    {nn : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nn H)
    (hdiv : D.divisible = ∅) {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) :
    ∃ N ∈ D.rootGroup β ⊔ D.rootGroup (-β), ∀ z ∈ D.rootGroup (-β),
      N * z * N⁻¹ ∈ D.rootGroup β := by
  obtain ⟨w, j, rfl⟩ : ∃ w j, β = weylAction D.isFiniteType w (Pi.single j 1) := by
    rcases (hdiv ▸ hβ : β ∈ roots D.isFiniteType ∅) with h | ⟨w, i, hi, -⟩
    exacts [h, absurd hi (Set.notMem_empty i)]
  have hm := actsAs_nrep hct w
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Or.inl ⟨1, j, by simp⟩
  have hnα := OfCartan.neg_mem_roots D.isFiniteType hα
  refine ⟨nrep hct w * nn j * (nrep hct w)⁻¹, ?_, fun z hz => ?_⟩
  · have h := conj_mem_map_conj (g := nrep hct w) (hct.n_mem j)
    rwa [rankOne, Subgroup.map_sup, hm _ hα, hm _ hnα, map_neg] at h
  · have h1 := hm.inv_conj_mem (OfCartan.neg_mem_roots D.isFiniteType hβ) hz
    rw [map_neg, weylAction_inv_apply_apply] at h1
    have h2 := hct.conj_mem j _ hnα _ h1
    rw [map_neg, weylAction_simple_single, neg_neg] at h2
    simpa only [mul_assoc, mul_inv_rev, inv_inv] using hm.conj_mem hα h2

theorem ggKGCent_cartanPair_bound {K : Type*} [Group K] {D : UniversalRootDatum K}
    (hdiv : D.divisible = ∅) (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {β γ : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (hγ : γ ∈ D.roots) :
    -2 ≤ cartanPair D.cartan β γ ∧ cartanPair D.cartan β γ ≤ 2 := by
  have hsymm := cartan_symm_of_posDef hpd
  obtain ⟨w, j, rfl⟩ : ∃ w j, β = weylAction D.isFiniteType w (Pi.single j 1) := by
    rcases (hdiv ▸ hβ : β ∈ roots D.isFiniteType ∅) with h | ⟨w, i, hi, -⟩
    exacts [h, absurd hi (Set.notMem_empty i)]
  obtain ⟨γ', hr, rfl⟩ : ∃ γ' ∈ roots D.isFiniteType ∅, γ = weylAction D.isFiniteType w γ' :=
    ⟨_, weylAction_mem_roots _ w⁻¹ (hdiv ▸ hγ : γ ∈ roots D.isFiniteType ∅),
      (weylAction_apply_inv_apply _ w γ).symm⟩
  rw [cartanPair_weylAction D.isFiniteType hsymm, cartanPair_comm hsymm, cartanPair_single]
  have hjj := D.isFiniteType.apply_self j
  by_cases h1 : γ' = Pi.single j 1
  · rw [h1, coroot_single]
    omega
  by_cases h2 : γ' = -Pi.single j 1
  · rw [h2, map_neg, coroot_single]
    omega
  have hle := coroot_le_one D.isFiniteType hpd hr h1
  have hge := neg_one_le_coroot D.isFiniteType hpd hr h2
  omega

end CFSG.StandardType

end
