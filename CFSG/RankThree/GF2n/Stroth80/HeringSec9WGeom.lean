module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem exists_swapFrame (hc : Ctx M Q Z B) {F : Subgroup G} (hF : IsConjB M B F) :
    ∃ g : G, conjSubgroup g B = Z ∧ conjSubgroup g Z = F ∧ conjSubgroup g Q = QB F ∧
      conjSubgroup g (QB B) = Q := by
  obtain ⟨m, hm, rfl⟩ := hF
  obtain ⟨n, h1, h2, h3, h4⟩ := hc.exists_swap'
  refine ⟨m * n, ?_, ?_, ?_, ?_⟩
  · rw [conjSubgroup_mul, h4, hc.conj_Z_eq hm]
  · rw [conjSubgroup_mul, h3]
  · rw [conjSubgroup_mul, h1, QB_conj]
  · rw [conjSubgroup_mul, h2, hc.conj_Q_eq hm]

theorem swap_conj_mem_LB (hc : Ctx M Q Z B) {F : Subgroup G} {g : G}
    (hgZ : conjSubgroup g Z = F) (hgQB : conjSubgroup g (QB B) = Q) {d : G} (hdQ : d ∈ Q)
    (hdF : d ∈ Subgroup.centralizer (F : Set G)) : g⁻¹ * d * g ∈ LB M Q B := by
  have h1 : g⁻¹ * d * g ∈ QB B := by
    have h : d ∈ conjSubgroup g (QB B) := hgQB ▸ hdQ
    exact mem_conjSubgroup.mp h
  have h2 : g⁻¹ * d * g ∈ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzF : g * z * g⁻¹ ∈ F := by
      rw [← hgZ, mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
      exact hz
    have hc' := Subgroup.mem_centralizer_iff.mp hdF _ hzF
    calc z * (g⁻¹ * d * g) = g⁻¹ * ((g * z * g⁻¹) * d) * g := by group
      _ = g⁻¹ * (d * (g * z * g⁻¹)) * g := by rw [hc']
      _ = g⁻¹ * d * g * z := by group
  have h3 : g⁻¹ * d * g ∈ QB B ⊓ M := by
    rw [hc.QB_inf_M_eq]
    exact ⟨h1, h2⟩
  exact Subgroup.mem_sup_right h3

theorem swap_conj_mem_Q_iff {F : Subgroup G} {g : G} (hgQ : conjSubgroup g Q = QB F) (d : G) :
    g⁻¹ * d * g ∈ Q ↔ d ∈ QB F := by
  rw [← hgQ, mem_conjSubgroup]

end HS9

end CFSG.RankThree.GF2n.Stroth80
