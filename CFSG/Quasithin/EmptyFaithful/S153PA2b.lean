module

public import CFSG.Quasithin.EmptyFaithful.S153PA2a

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise MatrixGroups

namespace S153P

section Defs

variable {G : Type} [Group G]

namespace Abs56

variable {U Z Mc : Subgroup G} {z y : G} (A : Abs56 U Z Mc z y)
include A

variable {u₀ : G} (hu₀ : u₀ ∈ U) (h₀ : ⁅u₀, zp z y⁆ = z)
include hu₀ h₀

theorem conj_rel : ((y⁻¹ * u₀ * y) * u₀) * (y⁻¹ * u₀ * y) * ((y⁻¹ * u₀ * y) * u₀)⁻¹ * u₀⁻¹ ∈
    Ng U Mc y := by
  have hY := PA2.yu A hu₀ h₀
  obtain ⟨c, hc⟩ : ∃ c : G, c = y * ((y⁻¹ * u₀ * y) * u₀)⁻¹ := ⟨_, rfl⟩
  have hcz : Commute c z := by rw [hc]; exact hY.scc_z
  have hcp : Commute c (zp z y) := by rw [hc]; exact hY.scc_p
  have hcM : c ∈ Mc := (PA2.mem_Mc A).2 hcz
  have hw : ((y⁻¹ * u₀ * y) * u₀) * (y⁻¹ * u₀ * y) * ((y⁻¹ * u₀ * y) * u₀)⁻¹ * u₀⁻¹ =
      c⁻¹ * u₀ * c * u₀⁻¹ := by
    rw [hc]; group
  rw [hw]
  apply Subgroup.mem_sup_left
  rw [PA2.mem_Fg A]
  refine ⟨?_, hY.comm_cuc hcz hcp⟩
  have h1 : c⁻¹ * u₀ * c⁻¹⁻¹ ∈ U := A.U_norm c⁻¹ (inv_mem hcM) u₀ hu₀
  rw [inv_inv] at h1
  exact mul_mem h1 (inv_mem hu₀)

set_option linter.unusedSectionVars false in
theorem mod_α1 : ∀ f ∈ Fg U Mc y, ⁅u₀, f⁆ ∈ Eg U Mc y := by
  intro f hf
  have hfU : f ∈ U := ((PA2.mem_Fg A).1 hf).1
  have hZ : ⁅u₀, f⁆ ∈ Z := A.U_comm u₀ hu₀ f hfU
  exact Subgroup.mem_inf.2 ⟨PA2.Z_le_Fg A hZ, PA2.Z_le_Xg A hZ⟩

theorem mod_α2 : ∀ r ∈ Ng U Mc y, ⁅u₀, r⁆ ∈ Fg U Mc y := by
  intro r hr
  have hY := PA2.yu A hu₀ h₀
  obtain ⟨hrz, hrp⟩ := PA2.Ng_cent A hr
  rw [PA2.mem_Fg A]
  refine ⟨?_, hY.comm_rr hrz hrp⟩
  have hrM : r ∈ Mc := (PA2.mem_Mc A).2 hrz
  have h1 : r * u₀⁻¹ * r⁻¹ ∈ U := A.U_norm r hrM u₀⁻¹ (inv_mem hu₀)
  have h2 := mul_mem hu₀ h1
  have e : u₀ * (r * u₀⁻¹ * r⁻¹) = ⁅u₀, r⁆ := by simp only [commutatorElement_def]; group
  rwa [e] at h2

theorem mod_δ1 : ∀ x ∈ Xg U Mc y,
    ((y⁻¹ * u₀ * y) * u₀) * x * ((y⁻¹ * u₀ * y) * u₀)⁻¹ ∈ Fg U Mc y := by
  intro x hx
  have hY := PA2.yu A hu₀ h₀
  obtain ⟨c, hc⟩ : ∃ c : G, c = y * ((y⁻¹ * u₀ * y) * u₀)⁻¹ := ⟨_, rfl⟩
  have hcz : Commute c z := by rw [hc]; exact hY.scc_z
  have hcp : Commute c (zp z y) := by rw [hc]; exact hY.scc_p
  have hcM : c ∈ Mc := (PA2.mem_Mc A).2 hcz
  have hw : y * x * y⁻¹ ∈ Fg U Mc y := mem_conjSubgroup_iff.1 hx
  obtain ⟨hwU, hwp⟩ := (PA2.mem_Fg A).1 hw
  have he : ((y⁻¹ * u₀ * y) * u₀) * x * ((y⁻¹ * u₀ * y) * u₀)⁻¹ = c⁻¹ * (y * x * y⁻¹) * c := by
    rw [hc]; group
  rw [he, PA2.mem_Fg A]
  refine ⟨?_, Commute.mul_left (Commute.mul_left (Commute.inv_left hcp) hwp) hcp⟩
  have h1 := A.U_norm c⁻¹ (inv_mem hcM) _ hwU
  rwa [inv_inv] at h1

theorem mod_δ2 : ∀ f ∈ Fg U Mc y,
    ((y⁻¹ * u₀ * y) * u₀)⁻¹ * f * ((y⁻¹ * u₀ * y) * u₀) ∈ Xg U Mc y := by
  intro f hf
  have hY := PA2.yu A hu₀ h₀
  obtain ⟨c, hc⟩ : ∃ c : G, c = y * ((y⁻¹ * u₀ * y) * u₀)⁻¹ := ⟨_, rfl⟩
  have hcz : Commute c z := by rw [hc]; exact hY.scc_z
  have hcp : Commute c (zp z y) := by rw [hc]; exact hY.scc_p
  have hcM : c ∈ Mc := (PA2.mem_Mc A).2 hcz
  obtain ⟨hfU, hfp⟩ := (PA2.mem_Fg A).1 hf
  rw [Xg, mem_conjSubgroup_iff]
  have he : y * (((y⁻¹ * u₀ * y) * u₀)⁻¹ * f * ((y⁻¹ * u₀ * y) * u₀)) * y⁻¹ = c * f * c⁻¹ := by
    rw [hc]; group
  rw [he, PA2.mem_Fg A]
  exact ⟨A.U_norm c hcM f hfU,
    Commute.mul_left (Commute.mul_left hcp hfp) (Commute.inv_left hcp)⟩

end Abs56

end Defs

end S153P

end CFSG.Quasithin
