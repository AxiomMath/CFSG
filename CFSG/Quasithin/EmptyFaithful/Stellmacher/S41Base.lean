module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem Zv_central_of_comm_eq_bot (hA : F53Amalgam H M S) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hz : ⁅Zv α, Zv α'⁆ = ⊥) : Zv β ≤ centerOf (stab β) := by
  have hle : Zv α ≤ stab α' :=
    Zv_le_stab_of_dist_le hA (by rw [hc.dist_eq, hc.bAt_eq])
  have hZ : Zv α' = quasithinOmegaOneCenter (stab α') := by
    rcases centralizer_Zv_dichotomy hA α' with hQ | hZ
    · exfalso
      apply hc.not_le
      rw [← hQ]
      exact le_inf hle (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hz)
    · exact hZ
  have hβ : Zv β = quasithinOmegaOneCenter (stab β) := by
    rcases (bMin_pos hA).lt_or_eq with hb | hb
    · exact Zv_central_of_conj hA (hss114_ab hA hc hz hb).2.2 hZ
    · have h0 : CosetGeom.dist β α' = 0 := by
        have := hc.dist_eq'
        omega
      rw [(CosetGeom.dist_eq_zero_iff hA.amalgam.gen).mp h0]
      exact hZ
  rw [hβ]
  exact omegaOneCenter_le_centerOf_self _

theorem Zv_central_of_vtype_eq (hA : F53Amalgam H M S) {δ δ' : Geo H M}
    (hv : vtype δ = vtype δ') (h : Zv δ ≤ centerOf (stab δ)) : Zv δ' ≤ centerOf (stab δ') := by
  rw [Zv_central_of_conj hA hv (Zv_eq_omegaOneCenter_of_central hA h)]
  exact omegaOneCenter_le_centerOf_self _

theorem commutator_Zv_inf_le (hA : F53Amalgam H M S) {μ δ : Geo H M} (hμ : vtype μ = true)
    (h : δ ∈ nbrs μ) :
    ⁅Zv μ, stab δ ⊓ stab μ⁆ ≤ quasithinOmegaOneCenter (stab δ ⊓ stab μ) := by
  have hidx : ((Qv μ).subgroupOf (stab δ ⊓ stab μ)).index = 2 := by
    have := relIndex_Qv_inf_true hA h hμ
    rw [inf_comm] at this
    exact this
  have hQT : Qv μ ≤ stab δ ⊓ stab μ := by
    have := Qv_le_inf hA h
    rw [inf_comm] at this
    exact this
  have hZQ : Zv μ ≤ Qv μ := Zv_le_Qv hA μ
  have hQC : Qv μ ≤ Subgroup.centralizer (Zv μ : Set G) := Qv_le_centralizer_Zv hA μ
  have hTN : stab δ ⊓ stab μ ≤ Subgroup.normalizer (Zv μ : Set G) :=
    inf_le_right.trans (stab_le_normalizer_Zv hA μ)
  have hsq : ∀ x ∈ Zv μ, x * x = 1 := fun x hx => by
    rw [← pow_two]; exact (isElemAbelian_Zv hA μ).2 x hx
  have hinv : ∀ x ∈ Zv μ, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_left (hsq x hx)
  have hcomm : ∀ x ∈ Zv μ, ∀ y ∈ Zv μ, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hQC (hZQ hy)) x hx
  have hqz : ∀ q ∈ Qv μ, ∀ x ∈ Zv μ, q * x * q⁻¹ = x := by
    intro q hq x hx
    have e : x * q = q * x := Subgroup.mem_centralizer_iff.mp (hQC hq) x hx
    calc q * x * q⁻¹ = x * q * q⁻¹ := by rw [e]
      _ = x := by group
  have hmul : ∀ a ∈ stab δ ⊓ stab μ, ∀ b ∈ stab δ ⊓ stab μ,
      (a * b ∈ Qv μ ↔ (a ∈ Qv μ ↔ b ∈ Qv μ)) := by
    intro a ha b hb
    have := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this
  rw [Subgroup.commutator_le]
  intro z hz d hd
  rw [commutatorElement_def]
  have hu : d * z * d⁻¹ ∈ Zv μ := (Subgroup.mem_normalizer_iff.mp (hTN hd) z).mp hz
  have hc : z * d * z⁻¹ * d⁻¹ = z * (d * z * d⁻¹)⁻¹ := by group
  have hcZ : z * d * z⁻¹ * d⁻¹ ∈ Zv μ := by
    rw [hc]
    exact mul_mem hz (inv_mem hu)
  have hfix : d * (z * d * z⁻¹ * d⁻¹) * d⁻¹ = z * d * z⁻¹ * d⁻¹ := by
    have hdd : d * d ∈ Qv μ := (hmul d hd d hd).mpr Iff.rfl
    have h1 : (d * d) * z⁻¹ * (d * d)⁻¹ = z⁻¹ := hqz _ hdd _ (inv_mem hz)
    have h2 : d * (z * d * z⁻¹ * d⁻¹) * d⁻¹ = (d * z * d⁻¹) * z⁻¹ := by
      calc d * (z * d * z⁻¹ * d⁻¹) * d⁻¹
          = (d * z * d⁻¹) * ((d * d) * z⁻¹ * (d * d)⁻¹) := by group
        _ = (d * z * d⁻¹) * z⁻¹ := by rw [h1]
    rw [h2, hc, hinv _ hu, hinv _ hz]
    exact hcomm _ hu _ hz
  have hconj : ∀ t ∈ stab δ ⊓ stab μ,
      t * (z * d * z⁻¹ * d⁻¹) * t⁻¹ = z * d * z⁻¹ * d⁻¹ := by
    intro t ht
    by_cases htQ : t ∈ Qv μ
    · exact hqz t htQ _ hcZ
    by_cases hdQ : d ∈ Qv μ
    · have e : z * d * z⁻¹ * d⁻¹ = 1 := by
        rw [hc, hqz d hdQ z hz, mul_inv_cancel]
      rw [e]
      group
    · have hq : d⁻¹ * t ∈ Qv μ :=
        (hmul d⁻¹ (inv_mem hd) t ht).mpr (iff_of_false (by rwa [inv_mem_iff]) htQ)
      calc t * (z * d * z⁻¹ * d⁻¹) * t⁻¹
          = d * ((d⁻¹ * t) * (z * d * z⁻¹ * d⁻¹) * (d⁻¹ * t)⁻¹) * d⁻¹ := by group
        _ = d * (z * d * z⁻¹ * d⁻¹) * d⁻¹ := by rw [hqz _ hq _ hcZ]
        _ = z * d * z⁻¹ * d⁻¹ := hfix
  apply Subgroup.subset_closure
  refine ⟨⟨hQT (hZQ hcZ), ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    calc t * (z * d * z⁻¹ * d⁻¹) = (t * (z * d * z⁻¹ * d⁻¹) * t⁻¹) * t := by group
      _ = z * d * z⁻¹ * d⁻¹ * t := by rw [hconj t ht]
  · rw [pow_two]
    exact hsq _ hcZ

end F53.Stellmacher

end CFSG.Quasithin
