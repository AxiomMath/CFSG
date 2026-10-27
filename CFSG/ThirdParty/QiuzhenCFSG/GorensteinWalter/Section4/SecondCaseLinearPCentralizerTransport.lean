module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPCentralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugation transport for the fixed-factor centralizer
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Conjugating the `F(U)`-centralizer of `P` by `h` gives the
`F(U)`-centralizer of `P^h`, provided `h` normalizes `F(U)`. -/
public theorem secondCase_linear_P_centralizer_FU_map_conj_eq
    {G : Type u} [Group G]
    {P X FU : Subgroup G} (h : G)
    (hX : X = conjugateSubgroup P h)
    (hFU : h ∈ Subgroup.normalizer (FU : Set G)) :
    ((Subgroup.centralizer (P : Set G)) ⊓ FU).map
        (MulAut.conj h).toMonoidHom =
      (Subgroup.centralizer (X : Set G)) ⊓ FU := by
  apply le_antisymm
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
    have hxfu : x ∈ FU := hx.2
    have hyfu : y ∈ FU := by
      have hnorm := (Subgroup.mem_normalizer_iff.mp hFU x)
      rw [show y = h * x * h⁻¹ by simpa [MulAut.conj_apply] using hxy.symm]
      exact hnorm.1 hxfu
    have hycent : y ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [hX] at hz
      rcases Subgroup.mem_map.mp hz with ⟨p, hp, hpz⟩
      have hxp : x * p = p * x :=
        ((Subgroup.mem_centralizer_iff.mp hx.1) p hp).symm
      have himage : (h * p * h⁻¹) * (h * x * h⁻¹) =
          (h * x * h⁻¹) * (h * p * h⁻¹) := by
        calc
          (h * p * h⁻¹) * (h * x * h⁻¹) = h * (p * x) * h⁻¹ := by group
          _ = h * (x * p) * h⁻¹ := by rw [hxp]
          _ = (h * x * h⁻¹) * (h * p * h⁻¹) := by group
      rw [← hpz, ← hxy]
      simpa [MulAut.conj_apply] using himage
    exact ⟨hycent, hyfu⟩
  · intro y hy
    have hhinv : h⁻¹ ∈ Subgroup.normalizer (FU : Set G) :=
      (Subgroup.normalizer (FU : Set G)).inv_mem hFU
    let x : G := h⁻¹ * y * h
    have hxfu : x ∈ FU := by
      have hnorm := (Subgroup.mem_normalizer_iff.mp hhinv y)
      have hyfu : y ∈ FU := hy.2
      simpa [x] using hnorm.mp hyfu
    have hxcent : x ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hzX : h * p * h⁻¹ ∈ X := by
        rw [hX]
        exact Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
      have hycomm : y * (h * p * h⁻¹) = (h * p * h⁻¹) * y :=
        ((Subgroup.mem_centralizer_iff.mp hy.1) _ hzX).symm
      calc
        p * x = p * (h⁻¹ * y * h) := by rfl
        _ = h⁻¹ * ((h * p * h⁻¹) * y) * h := by group
        _ = h⁻¹ * (y * (h * p * h⁻¹)) * h := by rw [hycomm]
        _ = (h⁻¹ * y * h) * p := by group
    exact Subgroup.mem_map.mpr ⟨x, ⟨hxcent, hxfu⟩, by
      change h * x * h⁻¹ = y
      simp [x, MulAut.conj_apply, mul_assoc]⟩

end CFSG.GorensteinWalter
