module

public import CFSG.YGroups.Y443.Native.Swap13
public import CFSG.YGroups.Y443.Native.TerminalInputs
public import CFSG.YGroups.Y443.RUpper
public import CFSG.YGroups.Y443.Tri.CosetCover

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.YGroups.Y443Edge

theorem exists_conj_qp
    : ∃ g : Q343, g * qp * g⁻¹ = qp * qc := by
  obtain ⟨h, hh, hconj⟩ := swap13_mem (Hbar_eq_centralizer fM_terminal_order)
  have hinj : Function.Injective y443Q343Hom := by
    have h : Function.Injective (fM ∘ y443Q343Hom) := rho_injective fM fM_terminal_order
    exact Function.Injective.of_comp h
  have e : h * y443C' * h⁻¹ = y443C' * y443C := by
    refine fM_injOn_H (y443H.mul_mem (y443H.mul_mem hh y443C'_mem_H) (y443H.inv_mem hh))
      (y443H.mul_mem y443C'_mem_H y443C_mem_H) ?_
    simpa only [map_mul, map_inv] using hconj
  rw [← y443Q343Hom_range] at hh
  obtain ⟨g, rfl⟩ := hh
  refine ⟨g, hinj ?_⟩
  rw [map_mul, map_mul, map_inv, y443Q343Hom_qp, map_mul, y443Q343Hom_qp, y443Q343Hom_qc]
  exact e

end CFSG.YGroups.Y443

namespace CFSG.YGroups.Y443Edge

open CFSG.Open (MonsterY443Derived)

variable {G : Type*} [Group G] (f : MonsterY443Derived →* G)

theorem inf_map_eq
    (hN : Q343N ≤ Nat.card (y443H.map f)) :
    y443H.map f ⊓ y443H'.map f = y443R.map f := by
  obtain ⟨g, hg⟩ := Y443.exists_conj_qp
  exact inf_map_eq_of_conj f hN hg

end CFSG.YGroups.Y443Edge

namespace CFSG.YGroups.Y443

theorem fM_inf_map_eq
    : y443H.map fM ⊓ y443H'.map fM = y443R.map fM :=
  Y443Edge.inf_map_eq fM fM_terminal_order

end CFSG.YGroups.Y443
