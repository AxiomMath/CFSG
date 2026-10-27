module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepC1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.StepC2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.LemmaP

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem hss32_b2_false (hA : F53Amalgam H M S) (h27 : Hss27S3At H M) (h113a : Hss113aAt H M)
    (hM6 : NoA5Transvection) {α β α' : Geo H M} (hc : IsCritData α β α')
    (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb2 : bMin H M = 2)
    (hn : ¬ Zv β ≤ centerOf (stab β)) : False := by
  have hβn : β ∈ nbrs α := hc.adj
  have hαβ : α ∈ nbrs β := alpha_mem_nbrs_beta hA h27 hc hv hcomm hb2 hn
  have hα'β : α' ∈ nbrs β := alpha'_mem_nbrs_beta hA h27 hc hv hcomm hb2 hn
  obtain ⟨γ, hγn, hγβ⟩ : ∃ γ, γ ∈ nbrs α ∧ γ ≠ β := by
    have h3 := card_nbrs_true hA hv
    have : Finite (nbrs α) := Nat.finite_of_card_ne_zero (by omega)
    have : Nontrivial (nbrs α) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨⟨μ, hμ⟩, hne⟩ := exists_ne (⟨β, hβn⟩ : nbrs α)
    exact ⟨μ, hμ, fun h => hne (Subtype.ext h)⟩
  have hvβ : vtype β = false := by
    have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj α β from hβn)
    revert this; cases hvβ : vtype β <;> simp [hv]
  obtain ⟨n, ψ, hnψ, hsurj, hker⟩ := exists_quotHom hA β
  rcases hnψ with ⟨rfl, -⟩ | ⟨-, hv'⟩
  swap
  · simp [hvβ] at hv'
  have hbb := bAt_eq_two hA h27 hc hv hcomm hb2 hn
  have hZγα := Zv_le_Qv_alpha_of_nbr hA h27 hc hv hcomm hb2 hn hγn
  have hZβα := Zv_le_Qv_alpha_of_nbr hA h27 hc hv hcomm hb2 hn hβn
  have hSβ := sup_Qv_eq hA h27 hc hv hcomm hb2 hn
  have hSγ := sup_Qv_eq_of_nbr hA h27 hc hv hcomm hb2 hn hγn
  have hZγ := not_le_Qv_beta hA h27 hc hv hcomm hb2 hn hγn hγβ
  have hcommN := comm_N_Zgamma_le hA h113a hM6 hb2 hv hβn hγn hγβ.symm (hbb β) (hbb γ)
    hSβ hSγ hZγ hZγα hZβα
  have hZedge : Zv γ ≤ stab β ⊓ stab α := by
    rw [inf_comm]; exact Zv_le_inf_edge hA h27 hc hv hcomm hb2 hn hγn
  have key := lemmaP hM6 G (stab β) (Qv β) (stab β ⊓ stab α) (Zv γ) ψ ↥(nbrs β)
    (fun μ => Qv (μ : Geo H M) ⊓ Qv β) ⟨α, hαβ⟩ hsurj hker
    (Qv_le_inf hA hαβ) inf_le_left hZedge (fun μ => inf_le_right)
    (family_relIndex hA h27 hc hv hcomm hb2 hn)
    (family_trans hA h27 hc hv hcomm hb2 hn) (family_inv hA h27 hc hv hcomm hb2 hn)
    (by
      rw [card_map_subgroupOf_eq ψ hker inf_le_left]
      exact relIndex_Qv_inf_false hA hαβ hvβ)
    (by
      intro s hs
      refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
      have h1 : s ∈ Subgroup.normalizer (Qv α : Set G) := le_normalizer_pCoreOf 2 _ hs.2
      have h2 : s ∈ Subgroup.normalizer (Qv β : Set G) := le_normalizer_pCoreOf 2 _ hs.1
      have e1 := Subgroup.mem_normalizer_iff.mp h1 x
      have e2 := Subgroup.mem_normalizer_iff.mp h2 x
      exact ⟨fun hx => ⟨e1.mp hx.1, e2.mp hx.2⟩, fun hx => ⟨e1.mpr hx.1, e2.mpr hx.2⟩⟩)
    hZγ
    (by
      intro s hs z hz
      exact normalizes_Zv_mod_Qv_beta hA h27 hc hv hcomm hb2 hn hγn s
        (by rw [inf_comm]; exact hs) z hz)
    (hcommN.trans (Zv_beta_le_iInf_family hA h27 hc hv hcomm hb2 hn))
    ⟨α', hα'β⟩
  have hZ' : Zv α' ≤ Qv α := by
    have h1 : Zv α' ≤ Qv α' ⊓ Qv β :=
      le_inf (Zv_le_Qv hA α') (Zv_alpha'_le_Qv_beta hA h27 hc hv hcomm hb2 hn)
    exact h1.trans (key.le.trans inf_le_left)
  exact not_le_Qv_of_comm_ne hA hcomm hZ'

theorem bMin_ne_two_of_not_central (hA : F53Amalgam H M S) (h27 : Hss27S3At H M)
    (h113a : Hss113aAt H M) (hM6 : NoA5Transvection) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hv : vtype α = true) (hcomm : ⁅Zv α, Zv α'⁆ ≠ ⊥)
    (hn : ¬ Zv β ≤ centerOf (stab β)) : bMin H M ≠ 2 :=
  fun hb2 => hss32_b2_false hA h27 h113a hM6 hc hv hcomm hb2 hn

end F53.Stellmacher

end CFSG.Quasithin
