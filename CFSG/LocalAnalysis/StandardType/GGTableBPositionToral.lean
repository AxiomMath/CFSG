module

public import CFSG.LocalAnalysis.StandardType.GGTableBCoverMarked
public import CFSG.LocalAnalysis.StandardType.GGWPlusPosition
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem exists_elemAbelian_of_forall_inner {R : Type} [Group R] (hZ : Subgroup.center R = ⊥)
    {p : ℕ} {M : Type} [Group M] {L' E : Subgroup M} (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)) (hEl : IsElemAbelian p E)
    (hinn : ∀ e : E, ggLAut L' θ ⟨e, hE e.2⟩ ∈ (MulAut.conj : R →* MulAut R).range) :
    ∃ E_R : Subgroup R, IsElemAbelian p E_R ∧ Nat.card E_R = Nat.card (ggLAutImage L' θ E) ∧
      ∀ e : E, ∃ x ∈ E_R, ggLAut L' θ ⟨e, hE e.2⟩ = MulAut.conj x := by
  have hφinj : Function.Injective (MulAut.conj : R →* MulAut R) := mulAut_conj_injective hZ
  have hĒelem : IsElemAbelian p (ggLAutImage L' θ E) :=
    (hEl.subgroupOf (Subgroup.normalizer (L' : Set M))).map (ggLAut L' θ)
  have hle : ggLAutImage L' θ E ≤ (MulAut.conj : R →* MulAut R).range := by
    intro a ha
    change a ∈ (E.subgroupOf (Subgroup.normalizer (L' : Set M))).map (ggLAut L' θ) at ha
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp ha
    let eE : E := ⟨e.1, Subgroup.mem_subgroupOf.mp he⟩
    obtain ⟨x, hx⟩ := hinn eE
    refine ⟨x, ?_⟩
    rw [show (⟨eE, hE eE.2⟩ : Subgroup.normalizer (L' : Set M)) = e from Subtype.ext rfl] at hx
    exact hx
  have hmap : ((ggLAutImage L' θ E).comap (MulAut.conj : R →* MulAut R)).map
      (MulAut.conj : R →* MulAut R) = ggLAutImage L' θ E :=
    Subgroup.map_comap_eq_self hle
  have hcard : Nat.card ((ggLAutImage L' θ E).comap (MulAut.conj : R →* MulAut R)) =
      Nat.card (ggLAutImage L' θ E) := by
    rw [← Subgroup.card_map_of_injective
      (f := (MulAut.conj : R →* MulAut R)) hφinj, hmap]
  refine ⟨(ggLAutImage L' θ E).comap (MulAut.conj : R →* MulAut R), ?_, hcard, ?_⟩
  · exact hĒelem.comap hφinj
  · intro e
    obtain ⟨x, hx⟩ := hinn e
    refine ⟨x, Subgroup.mem_comap.mpr ?_, hx.symm⟩
    rw [hx]
    exact Subgroup.mem_map.mpr ⟨⟨e, hE e.2⟩, Subgroup.mem_subgroupOf.mpr e.2, rfl⟩

theorem exists_conj_of_position_toral {R : Type} [Group R] [Finite R]
    (hZ : Subgroup.center R = ⊥) {p r : ℕ} (hp : p.Prime) (V : Subgroup R) (hL : GGTorusLift p r R)
    (hT : ∀ E' : Subgroup R, IsElemAbelian p E' → p ^ r ≤ Nat.card E' →
      ∃ g : R, E'.map (MulAut.conj g).toMonoidHom = V)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    {I : Set (MulAut R)} (hP : GGTableBPosition p L' E I θ hE)
    (hinn : ∀ e : E, ggLAut L' θ ⟨e, hE e.2⟩ ∈ (MulAut.conj : R →* MulAut R).range) :
    ∃ g : R, ∀ e : E, ∃ v ∈ V, ggLAut L' θ ⟨e, hE e.2⟩ = MulAut.conj (g⁻¹ * v * g) := by
  obtain ⟨E_R, hERelem, hERcard, hinner⟩ :=
    exists_elemAbelian_of_forall_inner hZ θ hE hP.2.1 hinn
  have hcard : p ^ r ≤ Nat.card E_R := by
    rw [hERcard]
    exact pow_le_card_ggLAutImage hP hp hL
  obtain ⟨g, hg⟩ := hT E_R hERelem hcard
  refine ⟨g, fun e => ?_⟩
  obtain ⟨x, hxmem, hxeq⟩ := hinner e
  refine ⟨g * x * g⁻¹, ?_, ?_⟩
  · rw [← hg]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hxmem
  · rw [show g⁻¹ * (g * x * g⁻¹) * g = x from by group]
    exact hxeq

end CFSG.StandardType
