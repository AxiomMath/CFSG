module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step33
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3M8
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3M5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss33Step3At_of (hA : F53Amalgam H M S) (h28 : Hss28At H M) (h113a : Hss113aAt H M) :
    Hss33Step3At H M := by
  intro h32 α β α' hc hv hcomm hb6 heven
  have C : Step3Ctx H M S α β α' := ⟨hA, h28, h32, h113a, hc, hv, hcomm, heven, hb6⟩
  let P : CritPath α β α' := critPathOf hc
  have hU1 := fun (ν : Geo H M) (hν : vtype ν = false) (ξ : Geo H M) (hξ : ξ ∈ nbrs ν) =>
    C.comm_Ctilde_Qv_all P hν hξ
  obtain ⟨l, hl, hlγ⟩ := exists_mem_nbrs_ne hA α' (ν := P.γ) (mem_nbrs_comm (P.γ_adj (by omega)))
  have h1 := C.comm_inter_le_Ctilde P hl hlγ
  rw [C.Ctilde_γ_eq_Zv hU1 P, ← C.Zv_beta_eq_Zv_γ P] at h1
  exact C.not_comm_inter_le_Zv_beta P C.vhatDataBeta hl hlγ h1

end F53.Stellmacher

end CFSG.Quasithin
