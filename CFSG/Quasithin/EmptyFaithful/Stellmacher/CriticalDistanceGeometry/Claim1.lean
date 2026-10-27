module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.ThreeOne

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem claim1_left (hA : F53Amalgam H M S) (h27 : Hss27S3At H M) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hb2 : 2 ≤ bMin H M) (hn : ¬ Zv β ≤ centerOf (stab β)) :
    ∀ γ ∈ nbrs α, γ ≠ β → ¬ ⁅Zv γ, Zv α'⁆ ≤ Zv α := by
  intro γ hγn hγβ hcon
  obtain ⟨hα', hZα'G⟩ := Zv_le_stab_of_comm_ne hA hc hcomm
  have hnle := not_le_Qv_of_comm_ne hA hcomm
  have hβn : β ∈ nbrs α := hc.adj
  have hZα'β : Zv α' ≤ stab β := by
    refine Zv_le_stab_of_dist_le hA ?_
    have := hc.dist_eq'
    rw [CosetGeom.dist_comm, hα']
    omega
  have hN1 : Zv α' ≤ Subgroup.normalizer ((Zv α ⊔ Zv γ : Subgroup G) : Set G) := by
    refine le_normalizer_sup_of_conj (fun z hz a ha => ?_) (fun z hz b hb => ?_)
    · exact Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α (hZα'G hz)) a).mp ha)
    · have hcm : z * b * z⁻¹ * b⁻¹ ∈ Zv α := by
        have h1 : z * b * z⁻¹ * b⁻¹ ∈ ⁅Zv α', Zv γ⁆ := Subgroup.commutator_mem_commutator hz hb
        rw [Subgroup.commutator_comm] at h1
        exact hcon h1
      have : z * b * z⁻¹ = (z * b * z⁻¹ * b⁻¹) * b := by group
      rw [this]
      exact (Zv α ⊔ Zv γ).mul_mem (Subgroup.mem_sup_left hcm) (Subgroup.mem_sup_right hb)
  have hN2 : stab α ⊓ stab γ ≤ Subgroup.normalizer ((Zv α ⊔ Zv γ : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer
      (inf_le_left.trans (stab_le_normalizer_Zv hA α))
      (inf_le_right.trans (stab_le_normalizer_Zv hA γ))
  have hstab : Zv α' ⊔ (stab α ⊓ stab γ) = stab α :=
    sup_edge_eq_stab hA hv hβn hγn hγβ.symm (le_inf hZα'G hZα'β) hnle
  have hN : stab α ≤ Subgroup.normalizer ((Zv α ⊔ Zv γ : Subgroup G) : Set G) := by
    rw [← hstab]; exact sup_le hN1 hN2
  obtain ⟨g, hg, hgγ⟩ := stab_transitive_on_nbrs hγn hβn
  have hZβ : Zv β = conjSub (g : G) (Zv γ) := by rw [← hgγ, Zv_smul]
  have hZα : conjSub (g : G) (Zv α) = Zv α := by
    rw [← Zv_smul, smul_eq_of_mem_stab hg]
  have hnorm : stab α ≤ Subgroup.normalizer ((Zv α ⊔ Zv β : Subgroup G) : Set G) := by
    have h1 : Zv α ⊔ Zv β = conjSub (g : G) (Zv α ⊔ Zv γ) := by
      rw [conjSub_sup, hZα, hZβ]
    rw [h1, conjSub_normalizer]
    calc stab α = conjSub (g : G) (stab α) := (conjSub_eq_of_mem hg).symm
      _ ≤ _ := conjSub_mono _ hN
  exact hn (h27 hb2 α β hc.adj hv hc.bAt_eq hnorm)

theorem not_central_of_vtype_eq (hA : F53Amalgam H M S) {β β' : Geo H M}
    (h : vtype β = vtype β') (hn : ¬ Zv β ≤ centerOf (stab β)) :
    ¬ Zv β' ≤ centerOf (stab β') := by
  intro hc
  have h1 := Zv_eq_omegaOneCenter_of_central hA hc
  have h2 := Zv_central_of_conj hA h.symm h1
  exact hn (h2 ▸ omegaOneCenter_le_centerOf_self _)

theorem not_central_partner (hA : F53Amalgam H M S) {α β α' β' : Geo H M}
    (hc : IsCritData α β α') (hc' : IsCritData α' β' α) (hv : vtype α = vtype α')
    (hn : ¬ Zv β ≤ centerOf (stab β)) : ¬ Zv β' ≤ centerOf (stab β') := by
  refine not_central_of_vtype_eq hA ?_ hn
  have h1 : vtype α ≠ vtype β := vtype_ne_of_adj hc.adj
  have h2 : vtype α' ≠ vtype β' := vtype_ne_of_adj hc'.adj
  cases h1' : vtype α <;> cases h2' : vtype β <;> cases h3' : vtype α' <;> cases h4' : vtype β' <;>
    simp_all

theorem claim1_right (hA : F53Amalgam H M S) (h27 : Hss27S3At H M) {α β α' β' : Geo H M}
    (hc : IsCritData α β α') (hc' : IsCritData α' β' α) (hvα : vtype α = true)
    (hvα' : vtype α' = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb2 : 2 ≤ bMin H M)
    (hn : ¬ Zv β ≤ centerOf (stab β)) :
    ∀ γ' ∈ nbrs α', γ' ≠ β' → ¬ ⁅Zv γ', Zv α⁆ ≤ Zv α' := by
  have hcomm' : ⁅Zv α', Zv α⁆ ≠ ⊥ := by rwa [Subgroup.commutator_comm]
  exact claim1_left hA h27 hc' hvα' hcomm' hb2
    (not_central_partner hA hc hc' (hvα.trans hvα'.symm) hn)

end F53.Stellmacher

end CFSG.Quasithin
