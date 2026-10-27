module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.C56

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem not_inf_Qv_le (hS : Sit H M S) {β l δ : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδ : δ ≠ β) : ¬ Qv l ⊓ Qv δ ≤ Qv β := by
  have hα : vtype l = true := Std.vtype_nbr_S5 hβ hl
  obtain ⟨α', hc⟩ := exists_critData hS.glob.amalg (hS.glob.crit l hα)
    (Std.mem_nbrs_symm.mp hl : β ∈ nbrs l)
  obtain ⟨-, hvα', -, hnle, hp⟩ := Std.Zv_not_le_Qv_crit hS hc hα
  obtain ⟨m, γ', hm, hγ, h1, h2, hle, -, -⟩ := Std.PD_geodesic hS hp
  have hd := hp.dist_eq
  have hne : γ' ≠ α' := by
    rintro rfl
    omega
  have hmγ : m ∈ nbrs γ' := Std.mem_nbrs_symm.mp hγ
  obtain ⟨g, hg1, hg2, hg3⟩ := Std.arc_trans hS hvα' hm hmγ hne hβ hl hlδ hδ
  intro hle'
  apply hnle
  have := hle'
  rw [← hg1, ← hg2, ← hg3, Qv_smul, Qv_smul, Qv_smul, ← conjSub_inf,
    conjSub_le_conjSub_iff'] at this
  exact hle.trans this

end S35.C56

end F53.Stellmacher

end CFSG.Quasithin
