module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CosetGeom

omit [Finite G] in
theorem relIndex_Qv_stab (δ : Geo H M) :
    (Qv δ).relIndex (stab δ) = Nat.card (OTwoQuot (stab δ)) := by
  have h : (Qv δ).subgroupOf (stab δ) = CFSG.Open.pCore 2 ↥(stab δ) := by
    unfold Qv pCoreOf
    exact Subgroup.comap_map_eq_self_of_injective (stab δ).subtype_injective _
  unfold Subgroup.relIndex
  rw [h]
  rfl

theorem Qv_le_inf (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    Qv δ ≤ stab δ ⊓ stab μ :=
  isSylowTwoOf_pCoreOf_le (sylow_stab_inf_left hA h)

theorem relIndex_Qv_inf_mul (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ) :
    (Qv δ).relIndex (stab δ ⊓ stab μ) * ((stab δ ⊓ stab μ).relIndex (stab δ)) =
      Nat.card (OTwoQuot (stab δ)) := by
  rw [← relIndex_Qv_stab, Subgroup.relIndex_mul_relIndex _ _ _ (Qv_le_inf hA h) inf_le_left]

theorem relIndex_Qv_inf_false (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ)
    (hv : vtype δ = false) : (Qv δ).relIndex (stab δ ⊓ stab μ) = 8 := by
  obtain ⟨φ⟩ := quot_stab_five hA hv
  have hcard : Nat.card (OTwoQuot (stab δ)) = 2 ^ 3 * 15 := by
    rw [Nat.card_congr φ.toEquiv, S152Fin.card_Perm_five]; norm_num
  have hidx : ((stab δ ⊓ stab μ).subgroupOf (stab δ)).index = 15 :=
    index_sylow_eq_of_card_quot (sylow_stab_inf_left hA h) (by decide) hcard
  have := relIndex_Qv_inf_mul hA h
  have h15 : (stab δ ⊓ stab μ).relIndex (stab δ) = 15 := hidx
  rw [h15, hcard] at this
  omega

theorem relIndex_Qv_inf_true (hA : F53Amalgam H M S) {δ μ : Geo H M} (h : μ ∈ nbrs δ)
    (hv : vtype δ = true) : (Qv δ).relIndex (stab δ ⊓ stab μ) = 2 := by
  obtain ⟨φ⟩ := quot_stab_three hA hv
  have hcard : Nat.card (OTwoQuot (stab δ)) = 2 ^ 1 * 3 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have hidx : ((stab δ ⊓ stab μ).subgroupOf (stab δ)).index = 3 :=
    index_sylow_eq_of_card_quot (sylow_stab_inf_left hA h) (by decide) hcard
  have := relIndex_Qv_inf_mul hA h
  have h3 : (stab δ ⊓ stab μ).relIndex (stab δ) = 3 := hidx
  rw [h3, hcard] at this
  omega

end F53

end CFSG.Quasithin
