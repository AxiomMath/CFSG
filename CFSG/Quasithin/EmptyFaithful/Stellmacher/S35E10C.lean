module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10B
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.E10

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Wl_le_Qv_of_lam_empty (hS : Sit H M S)
    (hΛ : ∀ δ δ' : Geo H M, S34.PD δ δ' → Zv δ ≤ Vn δ')
    {β α' m γ' α : Geo H M} (hp : S34.PD β α') (hb : Back H M β α' m γ') (hα : α ∈ nbrs β)
    (hαZ : ¬ Zv α ≤ Qv α') : Wl α ≤ Qv γ' := by
  by_contra hW
  obtain ⟨hvm, hvγ, hd3, hd2, hne, hdγα⟩ := back_facts hS hp hb
  obtain ⟨hVQ, -, -⟩ := geodesic_facts hS hp.dist_eq hb.2.2.1 hb.2.2.2
  obtain ⟨ρ, hρ, hρQ⟩ : ∃ ρ ∈ nbrs α, ¬ Vn ρ ≤ Qv γ' := by
    by_contra hcon
    push Not at hcon
    exact hW (iSup₂_le fun μ hμ => hcon μ hμ)
  have hρβ : ρ ≠ β := by
    rintro rfl
    exact hρQ fun x hx => (hVQ hx).2
  have hvα : vtype α = true := vtype_nbr_S5 hp.vδ hα
  have hvρ : vtype ρ = false := vtype_nbr_S3 hvα hρ
  have hb5 := hS.b5
  have hup : dist ρ γ' + 1 ≤ bMin H M := by
    have h1 := dist_le_dist_nbr hα γ'
    have h2 := dist_le_dist_nbr hρ γ'
    have e1 : dist γ' β = dist β γ' := CosetGeom.dist_comm _ _
    have e2 : dist ρ γ' = dist γ' ρ := CosetGeom.dist_comm _ _
    omega
  have hlow : bMin H M ≤ dist ρ γ' + 1 := by
    by_contra hlt
    exact hρQ (Vn_le_Qv_dist hS (by omega))
  have hpd : S34.PD ρ γ' := ⟨hvρ, hvγ, by omega, hρQ⟩
  have hZρ : Zv ρ ≤ Vn γ' := hΛ ρ γ' hpd
  have hcomm : ∀ a ∈ Vn γ', ∀ c ∈ Vn α', a * c = c * a :=
    Vn_commute_dist hS (by omega)
  have hZβ : Zv β ≤ Vn α' := hΛ β α' hp
  have hsup := (Zv_ne hS hvα hρ (mem_nbrs_symm.mp hα) hρβ).2.1
  have hcen : Zv α ≤ Subgroup.centralizer (Vn α' : Set G) := by
    rw [← hsup]
    refine sup_le (fun z hz c hc => ?_) (fun z hz c hc => ?_)
    · exact (hcomm z (hZρ hz) c hc).symm
    · exact (isElemAbelian_comm (Vn_isElemAbelian hS α') (hZβ hz) hc).symm
  refine hαZ fun x hx => ?_
  have hxs : x ∈ stab α' := (PD_Vn_le_stab hS hp).1 (Zv_le_Vn hα hx)
  refine Vn_centralizer_le_Qv hS hp.vδ' x hxs fun v hv => ?_
  have hxv : v * x = x * v := Subgroup.mem_centralizer_iff.mp (hcen hx) v hv
  have : x * v * x⁻¹ * v⁻¹ = 1 := by
    rw [show x * v = v * x from hxv.symm]; group
  rw [this]
  exact one_mem _

end S35.E10

end F53.Stellmacher

end CFSG.Quasithin
