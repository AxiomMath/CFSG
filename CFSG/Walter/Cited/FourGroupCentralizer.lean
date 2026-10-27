module

public import CFSG.GroupTheory.HyperplaneGeneration
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.Walter.Suzuki

variable {M : Type*} [Group M] [Finite M]

theorem le_centralizer_of_isKleinFour {S N : Subgroup M} [N.Normal] (hS : IsKleinFour S)
    (hN : Odd (Nat.card N))
    (hab : ∀ s ∈ S, s ≠ 1 → IsMulCommutative (Subgroup.centralizer ({s} : Set M))) :
    S ≤ Subgroup.centralizer (N : Set M) := by
  have hSab : ∀ a b : S, a * b = b * a := mul_comm_of_exponent_two hS.exponent_two
  have : CFSG.IsElementaryAbelian 2 S :=
    { toIsMulCommutative := ⟨⟨hSab⟩⟩
      exponent_dvd_p := by rw [hS.exponent_two] }
  let : MulDistribMulAction S N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp S.subtype)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := S) (H := N)
    (by rw [hS.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h))
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hle : ⨆ (a : S) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) N ≤
      (Subgroup.centralizer ({s} : Set M)).comap N.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hya : (y : M) * a = a * y := by
      have h := congrArg Subtype.val hy
      change ((MulAut.conjNormal (a : M)) y : M) = y at h
      rw [MulAut.conjNormal_apply] at h
      calc (y : M) * a = (a * y * (a : M)⁻¹) * a := by rw [h]
        _ = a * y := by group
    have ha1 : (a : M) ≠ 1 := fun h => ha (Subtype.ext h)
    have hC := hab a a.2 ha1
    have hsC : s ∈ Subgroup.centralizer ({(a : M)} : Set M) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hSab ⟨s, hs⟩ a))
    have hyC : (y : M) ∈ Subgroup.centralizer ({(a : M)} : Set M) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hya
    have := congrArg Subtype.val (hC.is_comm.comm ⟨y, hyC⟩ ⟨s, hsC⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr this
  have hmem := hle (hgen.symm ▸ Subgroup.mem_top (⟨x, hx⟩ : N))
  exact (Subgroup.mem_centralizer_singleton_iff.mp hmem)

end CFSG.Walter.Suzuki
