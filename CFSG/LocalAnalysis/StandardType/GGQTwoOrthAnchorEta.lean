module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks

public section

namespace CFSG.StandardType.OrthAnchor

open Multiplicative

theorem exists_ggInduced_sgnAut_of_bCoordinateBlock {G : Type} [Group G]
    {L Bs : Subgroup G} {n m p : ℕ} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {i0 : Fin n}
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (π₀ : Fin m ≃ {i : Fin n // i ≠ i0}) (i : Fin m) :
    ∃ φ ∈ ggInduced L Bs, ∀ (y : ↥Bs) (j : Fin m),
      eta (φ y) (π₀ j) = SpCoord.sgnAut i (fun k => eta y (π₀ k)) j := by
  let c : Fin m → Fin n := fun j => (π₀ j : Fin n)
  have hc : Function.Injective c := fun j j' h => π₀.injective (Subtype.ext h)
  have hγ : SpCoord.sgnAut (c i) ∈ bCoordinateBlock n p i0 :=
    Subgroup.subset_closure (Or.inl ⟨c i, (π₀ i).2, rfl⟩)
  rw [← hA] at hγ
  obtain ⟨φ, hφ, hφeq⟩ := Subgroup.mem_map.mp hγ
  have hφind : φ ∈ ggInduced L Bs := by
    rw [ggAutomizer_eq] at hφ
    exact hφ
  refine ⟨φ, hφind, ?_⟩
  intro y j
  have h1 : eta (φ y) = SpCoord.sgnAut (c i) (eta y) := by
    have h2 := congrArg
      (fun f : MulAut (Fin n → Multiplicative (ZMod p)) => f (eta y)) hφeq
    simpa [MulAut.congr_apply, MulEquiv.symm_apply_apply] using h2
  rw [h1, SpCoord.sgnAut_apply]
  rw [SpCoord.sgnAut_apply]
  exact Function.update_apply_of_injective (eta y) hc i ((eta y) (c i))⁻¹ j

theorem exists_ggInduced_swap_of_bCoordinateBlock {G : Type} [Group G]
    {L Bs : Subgroup G} {n m p : ℕ} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {i0 : Fin n}
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (π₀ : Fin m ≃ {i : Fin n // i ≠ i0}) {a b : Fin m} (hab : a ≠ b) :
    ∃ φ ∈ ggInduced L Bs, ∀ (y : ↥Bs) (j : Fin m),
      eta (φ y) (π₀ j) = SpCoord.permAut (Equiv.swap a b) (fun k => eta y (π₀ k)) j := by
  let c : Fin m → Fin n := fun j => (π₀ j : Fin n)
  have hc : Function.Injective c := fun j j' h => π₀.injective (Subtype.ext h)
  have hcne : c a ≠ c b := fun h => hab (hc h)
  have hγ : SpCoord.permAut (Equiv.swap (c a) (c b)) ∈ bCoordinateBlock n p i0 :=
    Subgroup.subset_closure (Or.inr ⟨c a, c b, hcne, (π₀ a).2, (π₀ b).2, rfl⟩)
  rw [← hA] at hγ
  obtain ⟨φ, hφ, hφeq⟩ := Subgroup.mem_map.mp hγ
  have hφind : φ ∈ ggInduced L Bs := by
    rw [ggAutomizer_eq] at hφ
    exact hφ
  refine ⟨φ, hφind, ?_⟩
  intro y j
  have h1 : eta (φ y) = SpCoord.permAut (Equiv.swap (c a) (c b)) (eta y) := by
    have h2 := congrArg
      (fun f : MulAut (Fin n → Multiplicative (ZMod p)) => f (eta y)) hφeq
    simpa [MulAut.congr_apply, MulEquiv.symm_apply_apply] using h2
  rw [h1, SpCoord.permAut_apply]
  rw [SpCoord.permAut_apply]
  simp only [Function.comp_apply, Equiv.swap_inv]
  rw [Function.Injective.swap_apply hc a b j]

end CFSG.StandardType.OrthAnchor

end
