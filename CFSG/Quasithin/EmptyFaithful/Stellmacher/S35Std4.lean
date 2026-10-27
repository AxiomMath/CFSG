module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {δ δ' : Geo H M}

theorem PD_Vn_le_stab (hS : Sit H M S) (hp : S34.PD δ δ') :
    Vn δ ≤ stab δ' ∧ Vn δ' ≤ stab δ :=
  S34.pd_Vn_le_stab hS.glob hp

theorem PD_quadratic (hS : Sit H M S) (hp : S34.PD δ δ') :
    ⁅⁅Vn δ', Vn δ⁆, Vn δ⁆ = ⊥ ∧ ⁅⁅Vn δ, Vn δ'⁆, Vn δ'⁆ = ⊥ := by
  have h := hss114_d hS.glob.amalg hS.glob.three_le hp.dist_eq
  exact ⟨h.2.2.1, h.2.2.2⟩

theorem PD_comm_le (hS : Sit H M S) (hp : S34.PD δ δ') :
    ⁅Vn δ, Vn δ'⁆ ≤ Vn δ ⊓ Vn δ' := by
  obtain ⟨h1, h2⟩ := PD_Vn_le_stab hS hp
  have hn1 : Vn δ ≤ Subgroup.normalizer (Vn δ' : Set G) := h1.trans (Vn_normal δ')
  have hn2 : Vn δ' ≤ Subgroup.normalizer (Vn δ : Set G) := h2.trans (Vn_normal δ)
  exact commutator_le_inf_of_normalizes hn1 hn2

theorem Vn_centralizer_le_Qv (hS : Sit H M S) {δ' : Geo H M} (hδ' : vtype δ' = false) :
    ∀ x ∈ stab δ', (∀ v ∈ Vn δ', x * v * x⁻¹ * v⁻¹ ∈ Zv δ') → x ∈ Qv δ' :=
  hss114_e hS.glob.amalg (Zv_eq_omegaOneCenter_of_central hS.glob.amalg (hS.glob.central δ' hδ'))

theorem exists_geodesic (hS : Sit H M S) {δ δ' : Geo H M} (h : dist δ δ' + 1 = bMin H M) :
    ∃ m γ' : Geo H M, m ∈ nbrs δ' ∧ γ' ∈ nbrs m ∧ dist δ m + 1 = dist δ δ' ∧
      dist δ γ' + 1 = dist δ m := by
  have hb := hS.b5
  obtain ⟨m, hm, hdm⟩ := exists_nbr_dist_succ (δ := δ') (ρ := δ) (d := dist δ δ' - 1)
    (by rw [CosetGeom.dist_comm]; omega)
  rw [CosetGeom.dist_comm] at hdm
  obtain ⟨γ', hγ, hdγ⟩ := exists_nbr_dist_succ (δ := m) (ρ := δ) (d := dist δ m - 1)
    (by rw [CosetGeom.dist_comm]; omega)
  rw [CosetGeom.dist_comm] at hdγ
  exact ⟨m, γ', hm, hγ, by omega, by omega⟩

theorem geodesic_facts (hS : Sit H M S) {δ δ' m γ' : Geo H M} (h : dist δ δ' + 1 = bMin H M)
    (h1 : dist δ m + 1 = dist δ δ') (h2 : dist δ γ' + 1 = dist δ m) :
    Vn δ ≤ Qv m ⊓ Qv γ' ∧ (∀ a ∈ Vn δ, ∀ b ∈ Vn γ', a * b = b * a) ∧
      ∀ ν ∈ nbrs γ', Vn δ ≤ stab ν := by
  refine ⟨le_inf (Vn_le_Qv_dist hS (by omega)) (Vn_le_Qv_dist hS (by omega)),
    Vn_commute_dist hS (by omega), fun ν hν => Vn_le_stab_dist hS ?_⟩
  have := dist_le_dist_nbr hν δ
  have e : dist δ ν = dist ν δ := CosetGeom.dist_comm _ _
  have e' : dist δ γ' = dist γ' δ := CosetGeom.dist_comm _ _
  omega

theorem PD_geodesic (hS : Sit H M S) (hp : S34.PD δ δ') :
    ∃ m γ' : Geo H M, m ∈ nbrs δ' ∧ γ' ∈ nbrs m ∧ dist δ m + 1 = dist δ δ' ∧
      dist δ γ' + 1 = dist δ m ∧ Vn δ ≤ Qv m ⊓ Qv γ' ∧
      (∀ a ∈ Vn δ, ∀ b ∈ Vn γ', a * b = b * a) ∧ ∀ ν ∈ nbrs γ', Vn δ ≤ stab ν := by
  obtain ⟨m, γ', hm, hγ, h1, h2⟩ := exists_geodesic hS hp.dist_eq
  exact ⟨m, γ', hm, hγ, h1, h2, geodesic_facts hS hp.dist_eq h1 h2⟩

theorem Zv_not_le_Qv_crit (hS : Sit H M S) {α β α' : Geo H M} (hc : IsCritData α β α')
    (hα : vtype α = true) :
    vtype β = false ∧ vtype α' = false ∧ Zv α ≤ Vn β ∧ ¬ Vn β ≤ Qv α' ∧ S34.PD β α' := by
  have hvβ : vtype β = false := by
    cases h : vtype β
    · rfl
    · exact absurd (hα.trans h.symm) (vtype_ne_of_adj hc.adj)
  have hvα' : vtype α' = false := by
    have hodd : ¬ Even (dist α α') := by
      rw [hc.dist_eq]; exact Nat.not_even_iff_odd.mpr hS.glob.odd
    cases h : vtype α'
    · rfl
    · exact absurd ((vtype_eq_iff_even_dist hS.glob.amalg.amalgam.gen α α').mp
        (hα.trans h.symm)) hodd
  have hαβ : α ∈ nbrs β := hc.adj.symm
  have hZV : Zv α ≤ Vn β := Zv_le_Vn hαβ
  have hnle : ¬ Vn β ≤ Qv α' := fun hle => hc.not_le (hZV.trans hle)
  exact ⟨hvβ, hvα', hZV, hnle, ⟨hvβ, hvα', hc.dist_eq', hnle⟩⟩

end S35.Std

end F53.Stellmacher

end CFSG.Quasithin
