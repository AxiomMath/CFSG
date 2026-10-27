module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley

variable {L : Type} [Field L]

theorem map_conj_rootSubgroup {τ : Tag} (v : WeylGroup τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    (rootSubgroup τ L γ).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom =
      rootSubgroup τ L (v • γ) := by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v) hγ
  have hπ : weylQuotientHom τ L ⟨canonicalRep (coxeterSystem τ) L v,
      canonicalRep_mem_monomialSubgroup L v⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  rw [hπ] at hμ
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
    refine mem_rootSubgroup.2 ⟨(μ : L) * c, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (hμ c).symm
  · intro hx
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hx
    refine ⟨pinnedX τ L γ ((μ⁻¹ : Lˣ) * d), mem_rootSubgroup.2 ⟨_, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hμ, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem map_conj_rootSpan {τ : Tag} (v : WeylGroup τ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot τ γ) :
    (rootSpan τ L S).map (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom =
      rootSpan τ L ((fun γ => v • γ) '' S) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun α hα => ?_
    rw [← Subgroup.map_le_iff_le_comap, map_conj_rootSubgroup v (hS α hα)]
    exact le_iSup₂_of_le (v • α) ⟨α, hα, rfl⟩ le_rfl
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨α, hα, rfl⟩ := hr
    rw [← map_conj_rootSubgroup (L := L) v (hS α hα)]
    exact Subgroup.map_mono (le_iSup₂_of_le α hα le_rfl)

end CFSG.RankThree.PartOne.KE
