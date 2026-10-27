module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveHyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open scoped Pointwise

theorem inFAS_mono {Q : Type} [Group Q] [Finite Q] {j j' : ℕ} (hjj : j ≤ j') {K : Subgroup Q}
    (h : InFAS j K) : InFAS j' K := by
  intro T hT Ω hΩ hne h1
  have h0 := h T hT Ω hΩ hne h1
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨e, he, t, ht, rfl⟩
    exact K.mul_mem (E1.eGen_le j' K T Ω he) (hT.le ht)
  · rw [← h0]
    exact Set.mul_subset_mul (fun x hx => E1.eGen_mono hjj K T Ω hx) subset_rfl

theorem inFSqAS_mono {G : Type} [Group G] [Finite G] {j j' : ℕ} (hjj : j ≤ j') {H : Subgroup G}
    (h : InFSqAS j H) : InFSqAS j' H :=
  inFAS_mono hjj h

theorem inFAS_top_iff_fourFiveFAS {R : Type} [Group R] [Finite R] (j : ℕ) :
    InFAS j (⊤ : Subgroup R) ↔ fourFiveFAS j R :=
  ⟨fun h T Ω hT hΩ hne hbot => h T hT Ω hΩ hne hbot,
    fun h T hT Ω hΩ hne hbot => h T Ω hT hΩ hne hbot⟩

theorem inFSqAS_iff_bar2_inFAS_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G]
    [Finite G'] {H : Subgroup G} {H' : Subgroup G'}
    (e : CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 H ≃*
      CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 H') (j : ℕ) :
    InFSqAS j H ↔ InFSqAS j H' :=
  ⟨fun h => (inFAS_top_iff_fourFiveFAS j).mpr
      (fourFive_fas_mulEquiv e ((inFAS_top_iff_fourFiveFAS j).mp h)),
    fun h => (inFAS_top_iff_fourFiveFAS j).mpr
      (fourFive_fas_mulEquiv e.symm ((inFAS_top_iff_fourFiveFAS j).mp h))⟩

end CFSG.LocalAnalysis.WeakClosure81
