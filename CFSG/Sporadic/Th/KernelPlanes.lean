
module

public import CFSG.Sporadic.Th.KernelPlanesBase

public import CFSG.Sporadic.Th.KernelCentralizerBase1
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalData
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier TauCeti Pointwise MulAction

variable (h : KernelFacts)
include h

theorem isCoatom_K : IsCoatom K := by
  have := h.finite
  obtain ⟨hprim, hOm, -⟩ := isPreprimitive_Om h
  have : Nontrivial Om := by
    rw [← Finite.one_lt_card_iff_nontrivial, hOm]
    norm_num
  have hc := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := P) (pt 1)
  rwa [MulAction.stabilizer_quotient] at hc

theorem stabilizer_planeWSet_eq :
    MulAction.stabilizer J planeWSet = H ∧ Nat.card H = 634023936 := by
  have := h.finite
  obtain ⟨e, hK, -⟩ := exists_equiv h
  obtain ⟨-, -, hKc⟩ := isPreprimitive_Om h
  have hmapK : ∀ L : Subgroup J, (∀ i < 7, e (gen i) ∈ L) → K.map (e : P →* J) ≤ L := by
    intro L hL
    rw [K, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hL i i.2
  have hKS : K.map (e : P →* J) ≤ MulAction.stabilizer J planeWSet := by
    refine hmapK _ fun i hi => ?_
    rw [MulAction.mem_stabilizer_iff]
    exact (hK i hi).2
  have hKH : K.map (e : P →* J) ≤ H := hmapK _ fun i hi => (hK i hi).1
  have hcoat : IsCoatom (K.map (e : P →* J)) := by
    exact isCoatom_map_of_bijective (e : P →* J) e.bijective (isCoatom_K h)
  have hne : MulAction.stabilizer J planeWSet ≠ ⊤ := fun ht =>
    h.b_moves (MulAction.mem_stabilizer_iff.1 (ht ▸ Subgroup.mem_top b))
  have hSt : MulAction.stabilizer J planeWSet = K.map (e : P →* J) :=
    ((hcoat.le_iff.1 hKS).resolve_left hne)
  have hHS : H ≤ MulAction.stabilizer J planeWSet := by
    rw [H, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact MulAction.mem_stabilizer_iff.2 h.x_fix
    · exact MulAction.mem_stabilizer_iff.2 h.y_fix
  have hHeq : MulAction.stabilizer J planeWSet = H := le_antisymm (hSt ▸ hKH) hHS
  refine ⟨hHeq, ?_⟩
  rw [← hHeq, hSt, Subgroup.card_map_of_injective e.injective, hKc]

theorem card_H : Nat.card H = 634023936 := (stabilizer_planeWSet_eq h).2

theorem stabilizer_planeWSet : MulAction.stabilizer J planeWSet = localH := by
  rw [localH_eq]
  exact (stabilizer_planeWSet_eq h).1

theorem ncard_planeX : planeX.ncard = 143127000 := by
  have hJ := card_J_eq h
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer J planeWSet)
  rw [MulAction.index_stabilizer, (stabilizer_planeWSet_eq h).1, card_H h, hJ] at h1
  change 634023936 * planeX.ncard = 90745943887872000 at h1
  omega

theorem isPreprimitive_planeX : MulAction.IsPreprimitive J planeX := by
  have hnt : Nontrivial planeX := by
    rw [Set.nontrivial_coe_sort, ← Set.one_lt_ncard_iff_nontrivial, ncard_planeX h]
    norm_num
  have hmem : planeWSet ∈ planeX := MulAction.mem_orbit_self _
  have e : MulAction.stabilizer J (⟨planeWSet, hmem⟩ : planeX) =
      MulAction.stabilizer J planeWSet := by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  rw [← MulAction.isCoatom_stabilizer_iff_preprimitive (G := J) (⟨planeWSet, hmem⟩ : planeX), e,
    (stabilizer_planeWSet_eq h).1]
  obtain ⟨e', hK, -⟩ := exists_equiv h
  have hcoat : IsCoatom (K.map (e' : P →* J)) :=
    isCoatom_map_of_bijective (e' : P →* J) e'.bijective (isCoatom_K h)
  rw [← (stabilizer_planeWSet_eq h).1]
  have hKS : K.map (e' : P →* J) ≤ MulAction.stabilizer J planeWSet := by
    rw [K, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact MulAction.mem_stabilizer_iff.2 (hK i i.2).2
  have hne : MulAction.stabilizer J planeWSet ≠ ⊤ := fun ht =>
    h.b_moves (MulAction.mem_stabilizer_iff.1 (ht ▸ Subgroup.mem_top b))
  rw [(hcoat.le_iff.1 hKS).resolve_left hne]
  exact hcoat

end CFSG.Sporadic.Th.Kernel
