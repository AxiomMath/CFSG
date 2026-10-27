module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2NC
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Inner

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

theorem br2_false_of_one_L34 (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br2OneComp Y T L)
    (hshape : IsL3 ↥L 2) (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty)
    (h65f : Asch6_5Four) (hfin : FinG4L34) : False := by
  obtain ⟨hnc, hdyn⟩ := hfin ↥L hshape
  have hX₀ : innAutOf ↥L ≤ (psiOf Y L hL.normal).range := by
    rw [← imgOf_psiOf_L hL.core]
    exact imgOf_le_range _ _
  have hX₀n : ∀ r : ↥Y, ∀ x ∈ innAutOf ↥L,
      psiOf Y L hL.normal r * x * (psiOf Y L hL.normal r)⁻¹ ∈ innAutOf ↥L :=
    fun r x hx => psiOf_conj_mem_innAutOf hL.core r hx
  have hmem : ∀ D ∈ Γ, imgOf (psiOf Y L hL.normal) D ≤ innAutOf ↥L :=
    fun D hD => w183b2_inner_of_quadratic h65f hL.core hshape (hc.h131.le_G D hD)
      (hc.h131.isElemAb D hD) (hc.h131.quadratic D hD) (hrk D hD)
  exact w183b2_false_of_dynkin (X₀ := innAutOf ↥L) hc.toBr1Base hL hX₀ hX₀n hmem hnc hdyn hrk hne

end CFSG.LocalAnalysis.WeakClosure81

end
