module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtR
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.At

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Kb_le_Qv_nbr (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) : Kb β ≤ Qv l := by
  intro k hk
  have h1 : k ∈ stab l := Qv_le_stab hS hl hk.1
  have h2 : k ∈ Subgroup.centralizer (Zv l : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hk.2) z (Zv_le_Vn hl hz)
  rw [← centralizer_Zv_eq_Qv_of_bAt hS.glob.amalg (hS.glob.crit l (vtype_nbr_S5 hβ hl))]
  exact ⟨h1, h2⟩

theorem comm_Vn_Kb (hS : Sit H M S)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ))
    (hA : ArcDict H M) {γ μ δ : Geo H M} (hγ : vtype γ = false) (hμ : μ ∈ nbrs γ)
    (hδ : δ ∈ nbrs μ) (hne : δ ≠ γ) {u : G} (hu : u ∈ Kb γ) :
    ∀ w ∈ Vn δ, ⁅w, u⁆ ∈ Vn γ ⊓ Vn δ := by
  have hγμ : γ ∈ nbrs μ := mem_nbrs_symm.mp hμ
  have hδμ : μ ∈ nbrs δ := mem_nbrs_symm.mp hδ
  have hvδ : vtype δ = false := (vtype_eq_of_nbrs hδ hγμ).trans hγ
  obtain ⟨c⟩ := exists_chart hS hZ hvδ
  have hQ : u ∈ Qv μ := Kb_le_Qv_nbr hS hγ hμ hu
  have hus : u ∈ stab δ ⊓ stab μ := ⟨Qv_le_stab hS hδ hQ, Ch.Qv_le_stab' μ hQ⟩
  have hcen : ∀ r ∈ Vn δ ⊓ Vn γ, u * r * u⁻¹ = r := fun r hr => by
    have := (Subgroup.mem_centralizer_iff.mp hu.2) r hr.2
    rw [← this]; simp
  intro w hw
  rw [inf_comm]
  exact (Arc.thm hS hA c hvδ hδμ hγμ hne.symm hus hcen).2 w hw

theorem claim15c_of_dict (hS : Sit H M S)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ))
    (hA : ArcDict H M) : Claim15c H M := by
  intro β hβ
  rw [Subgroup.commutator_le]
  intro w hw k hk
  have hle : Wb β ≤ commSub (Vn β) k := by
    refine Wb_le fun ρ hρ u hu => ?_
    obtain ⟨l, hl, hρl, hne⟩ := dist_eq_two_iff.mp hρ
    have hstab : u ∈ stab β := Vn_le_stab_dist hS (by have := hS.b5; omega) hu
    exact ⟨Vn_normal β hstab, (comm_Vn_Kb hS hZ hA hβ hl hρl hne hk u hu).1⟩
  exact (hle hw).2

end S35.At

end F53.Stellmacher

end CFSG.Quasithin
