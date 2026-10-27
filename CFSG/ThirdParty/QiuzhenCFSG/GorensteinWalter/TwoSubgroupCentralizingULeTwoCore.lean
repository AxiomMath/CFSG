module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Two-subgroups centralizing the centralizer odd core

Theorem 2.6 identifies `S \inter C_G(U)` with `O2(Hhat)`.  A two-subgroup
of `Hhat` centralizing `U` can be conjugated into the fixed Sylow subgroup
`S`; normality of `O2(Hhat)` then transports the containment back.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- Every two-subgroup of `Hhat` that centralizes `U` lies in
`O2(Hhat)`. -/
public theorem twoSubgroup_le_twoCoreOf_Hhat_of_centralizes_U
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (h26 : CentralizerStructure c)
    (P : Subgroup G)
    (hPp : IsPGroup 2 P)
    (hPleHhat : P ≤ c.Hhat)
    (hPcentU : P ≤ Subgroup.centralizer (c.U : Set G)) :
    P ≤ twoCoreOf c.Hhat := by
  classical
  have hUnormalHhat : IsNormalIn c.U c.Hhat := by
    rw [h26.1]
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
    · intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨(⟨h, hh⟩ : c.Hhat) * x0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
          (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
            x0 hx0 (⟨h, hh⟩ : c.Hhat), rfl⟩
  let PH : Subgroup c.Hhat := P.subgroupOf c.Hhat
  have hPHp : IsPGroup 2 PH :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPleHhat).symm
  obtain ⟨R, hPR⟩ := IsPGroup.exists_le_sylow (G := c.Hhat) (p := 2) hPHp
  let SH : Sylow 2 c.Hhat :=
    c.S.subtype ((centralizerSetup_S_le_H c).trans c.H_le_Hhat)
  obtain ⟨h, hR⟩ := MulAction.exists_smul_eq c.Hhat SH R
  let g : G := h
  have hgHhat : g ∈ c.Hhat := h.property
  have hOnormal : IsNormalIn (twoCoreOf c.Hhat) c.Hhat := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · intro z hz x hx
      rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨(⟨z, hz⟩ : c.Hhat) * x0 * (⟨z, hz⟩ : c.Hhat)⁻¹,
          (pCore_normal (p := 2) (G := c.Hhat)).conj_mem
            x0 hx0 (⟨z, hz⟩ : c.Hhat), rfl⟩
  have hSinter : (c.S : Subgroup G) ⊓
      Subgroup.centralizer (c.U : Set G) = twoCoreOf c.Hhat := h26.2.1
  intro x hx
  have hxHhat : x ∈ c.Hhat := hPleHhat hx
  let xH : c.Hhat := ⟨x, hxHhat⟩
  have hxPH : xH ∈ PH := Subgroup.mem_subgroupOf.mpr hx
  have hxR : xH ∈ (R : Subgroup c.Hhat) := hPR hxPH
  have hxSmul : xH ∈ ((h • SH : Sylow 2 c.Hhat) : Subgroup c.Hhat) := by
    simpa [hR] using hxR
  have hxSmul' : xH ∈ MulAut.conj h • (SH : Subgroup c.Hhat) := by
    rw [Sylow.coe_subgroup_smul] at hxSmul
    exact hxSmul
  have hconjS : (MulAut.conj h)⁻¹ • xH ∈ (SH : Subgroup c.Hhat) :=
    (Subgroup.mem_pointwise_smul_iff_inv_smul_mem
      (a := MulAut.conj h) (S := SH) (x := xH)).mp hxSmul'
  have hconjS' : (h⁻¹ * xH * h : c.Hhat) ∈ (SH : Set c.Hhat) := hconjS
  let y : G := ((h⁻¹ * xH * h : c.Hhat) : G)
  have hyS : y ∈ (c.S : Subgroup G) := by
    have hSmap : (SH : Subgroup c.Hhat).map c.Hhat.subtype =
        (c.S : Subgroup G) := by
      dsimp [SH]
      exact Subgroup.map_subgroupOf_eq_of_le
        ((centralizerSetup_S_le_H c).trans c.H_le_Hhat)
    rw [← hSmap]
    exact Subgroup.mem_map.mpr
      ⟨(h⁻¹ * xH * h : c.Hhat), hconjS', rfl⟩
  have hyCentU : y ∈ Subgroup.centralizer (c.U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hgu : g * u * g⁻¹ ∈ c.U :=
      hUnormalHhat.2 g hgHhat u hu
    have hcomm : (g * u * g⁻¹) * x = x * (g * u * g⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (hPcentU hx))
        (g * u * g⁻¹) hgu
    change u * (g⁻¹ * x * g) = (g⁻¹ * x * g) * u
    calc
      u * (g⁻¹ * x * g) = g⁻¹ * ((g * u * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * u * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * x * g) * u := by group
  have hyO : y ∈ twoCoreOf c.Hhat := by
    have hy : y ∈ (c.S : Subgroup G) ⊓
        Subgroup.centralizer (c.U : Set G) := ⟨hyS, hyCentU⟩
    rwa [hSinter] at hy
  have hxy : x = g * y * g⁻¹ := by
    change x = (h : G) * ((h⁻¹ * xH * h : c.Hhat) : G) * (h : G)⁻¹
    simp [xH, Subgroup.coe_mul]
    group
  rw [hxy]
  exact hOnormal.2 g hgHhat y hyO

end CFSG.GorensteinWalter
