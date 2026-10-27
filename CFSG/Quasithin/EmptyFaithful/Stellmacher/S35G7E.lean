module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7Stmt
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChThat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Kb_le_Qv_nbr (hS : Sit H M S) {γ μ : Geo H M} (hγ : vtype γ = false) (hμ : μ ∈ nbrs γ) :
    Kb γ ≤ Qv μ := by
  intro u hu
  have hμv : vtype μ = true := vtype_nbr_S5 hγ hμ
  have hu1 : u ∈ stab μ := Qv_le_stab hS hμ hu.1
  have hu2 : u ∈ Subgroup.centralizer (Zv μ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := Subgroup.mem_centralizer_iff.mp hu.2 z (Zv_le_Vn hμ hz)
    exact this
  rw [← centralizer_Zv_eq_Qv_of_bAt hS.glob.amalg (hS.glob.crit μ hμv)]
  exact ⟨hu1, hu2⟩

theorem claim16d (hS : Sit H M S) (hI : CaseI H M) (hZ : HypZ H M) (hR : HypR H M) :
    Claim16d H M := by
  intro γ μ δ hγ hμ hδ hne u hu v hv
  have hC : Ch.Ctx H M S := ⟨hS, hI, hZ, hR⟩
  have hμv : vtype μ = true := vtype_nbr_S5 hγ hμ
  have hδv : vtype δ = false := vtype_nbr_S3 hμv hδ
  have hδμ : μ ∈ nbrs δ := mem_nbrs_symm.mp hδ
  have huμ : u ∈ Qv μ := Kb_le_Qv_nbr hS hγ hμ hu
  have huδ : u ∈ stab δ := Qv_le_stab hS hδ huμ
  have huμs : u ∈ stab μ := Ch.Qv_le_stab' μ huμ
  obtain ⟨c⟩ := hC.nonempty_chart hδv
  have hRle : Ch.Rl δ μ ≤ Vn γ ⊓ Vn δ := by
    refine le_inf ?_ ?_
    · exact (iInf₂_le γ (mem_nbrs_symm.mp hμ)).trans ((iInf_le _ hne.symm).trans inf_le_right)
    · exact (iInf₂_le γ (mem_nbrs_symm.mp hμ)).trans ((iInf_le _ hne.symm).trans inf_le_left)
  have hT : u ∈ Ch.Tcen δ μ := by
    rw [Ch.mem_Tcen_iff hS]
    refine ⟨⟨huδ, huμs⟩, fun r hr => ?_⟩
    have h1 : r ∈ Vn γ := (hRle hr).1
    have h2 : u * r * u⁻¹ * r⁻¹ = 1 := by
      have := Subgroup.mem_centralizer_iff.mp hu.2 r h1
      rw [← this]; group
    rw [h2]
    exact (Zv δ).one_mem
  have h := c.comm_mem_Rl_of_mem_Tcen hC hδv hδμ hT hv
  have e : ⁅v, u⁆ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e]
  exact (Vn γ ⊓ Vn δ).inv_mem (hRle h)

end S35.G7

end F53.Stellmacher

end CFSG.Quasithin
