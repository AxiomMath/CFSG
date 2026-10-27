module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasD
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem card_oTwoQuot_stab_true (hA : F53Amalgam H M S) {α : Geo H M} (hα : vtype α = true) :
    Nat.card (OTwoQuot (stab α)) = 2 ^ 1 * 3 := by
  obtain ⟨φ⟩ := quot_stab_three hA hα
  rw [Nat.card_congr φ.toEquiv, Nat.card_perm]
  simp [Nat.factorial]

theorem index_inf_stab_true (hA : F53Amalgam H M S) {α β : Geo H M} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) : ((stab α ⊓ stab β).subgroupOf (stab α)).index = 3 :=
  index_sylow_eq_of_card_quot (sylow_stab_inf_left hA hβ) (by decide)
    (card_oTwoQuot_stab_true hA hα)

theorem not_inf_stab_le_Qv (hA : F53Amalgam H M S) {α β : Geo H M} (hα : vtype α = true)
    (hβ : β ∈ nbrs α) : ¬ stab α ⊓ stab β ≤ Qv α := by
  intro hle
  have hS := sylow_stab_inf_left hA hβ
  have heq : stab α ⊓ stab β = Qv α := le_antisymm hle (isSylowTwoOf_pCoreOf_le hS)
  have hN := inf_normalizer_eq_of_card_quot hS (k := 1) (r := 3) le_rfl Nat.prime_three
    (by decide) (card_oTwoQuot_stab_true hA hα)
  have hQn : stab α ≤ Subgroup.normalizer ((stab α ⊓ stab β : Subgroup G) : Set G) := by
    rw [heq]
    exact le_normalizer_pCoreOf 2 (stab α)
  have h1 : stab α ≤ stab α ⊓ stab β := by
    rw [← hN]
    exact le_inf le_rfl hQn
  exact pCoreOf_ne_stab hA α (le_antisymm (pCoreOf_le 2 _) (heq ▸ h1))

theorem exists_three_nbrs (hA : F53Amalgam H M S) {α : Geo H M} (hα : vtype α = true) :
    ∃ β δ ε : Geo H M, β ≠ δ ∧ β ≠ ε ∧ δ ≠ ε ∧ nbrs α = {β, δ, ε} := by
  have h := card_nbrs_true hA hα
  rw [Nat.card_coe_set_eq] at h
  exact Set.ncard_eq_three.mp h

theorem eq_of_three_nbrs (hA : F53Amalgam H M S) {α β δ ε : Geo H M} (hα : vtype α = true)
    (hβδ : β ≠ δ) (hβε : β ≠ ε) (hδε : δ ≠ ε) (hβ : β ∈ nbrs α) (hδ : δ ∈ nbrs α)
    (hε : ε ∈ nbrs α) : nbrs α = {β, δ, ε} := by
  have h := card_nbrs_true hA hα
  rw [Nat.card_coe_set_eq] at h
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [h, Set.ncard_eq_three.mpr ⟨β, δ, ε, hβδ, hβε, hδε, rfl⟩]

theorem exists_third_nbr (hA : F53Amalgam H M S) {α β δ : Geo H M} (hα : vtype α = true)
    (hβδ : β ≠ δ) : ∃ ε ∈ nbrs α, ε ≠ β ∧ ε ≠ δ := by
  by_contra hcon
  push Not at hcon
  have h := card_nbrs_true hA hα
  rw [Nat.card_coe_set_eq] at h
  have hsub : nbrs α ⊆ {β, δ} := by
    intro x hx
    by_cases hxβ : x = β
    · exact Or.inl hxβ
    · exact Or.inr (hcon x hx hxβ)
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hβδ] at h2
  omega

theorem exists_swap (hA : F53Amalgam H M S) {α β δ ε : Geo H M} (hα : vtype α = true)
    (hβδ : β ≠ δ) (hβε : β ≠ ε) (hδε : δ ≠ ε) (hβ : β ∈ nbrs α) (hδ : δ ∈ nbrs α)
    (hε : ε ∈ nbrs α) : ∃ t : ↥(H ⊔ M), (t : G) ∈ stab α ⊓ stab β ∧ t • δ = ε := by
  have hn := eq_of_three_nbrs hA hα hβδ hβε hδε hβ hδ hε
  obtain ⟨x, hx, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp (not_inf_stab_le_Qv hA hα hβ)
  rw [Qv_eq_iInf hA α] at hxQ
  simp only [Subgroup.mem_iInf, not_forall] at hxQ
  obtain ⟨ν, hν, hxν⟩ := hxQ
  set g : ↥(H ⊔ M) := ⟨x, stab_le α hx.1⟩ with hg
  have hgα : g • α = α := smul_eq_of_mem_stab hx.1
  have hgβ : g • β = β := smul_eq_of_mem_stab hx.2
  have hnb : ∀ w ∈ nbrs α, g • w ∈ nbrs α := fun w hw => by
    have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj α w from hw)
    rwa [hgα] at this
  have hne : g • ν ≠ ν := by
    intro h
    exact hxν ⟨hx.1, mem_stab_of_smul_eq h⟩
  have hinj : ∀ u w : Geo H M, g • u = g • w → u = w := fun u w h => MulAction.injective g h
  rw [hn] at hν hnb
  have hnb' : ∀ w : Geo H M, w = β ∨ w = δ ∨ w = ε → g • w = β ∨ g • w = δ ∨ g • w = ε := by
    intro w hw
    have := hnb w (by rcases hw with rfl | rfl | rfl <;> simp)
    simpa using this
  rcases hν with rfl | rfl | rfl
  · exact absurd hgβ hne
  · rcases hnb' ν (Or.inr (Or.inl rfl)) with h | h | h
    · exact absurd (hinj _ _ (h.trans hgβ.symm)) hβδ.symm
    · exact absurd h hne
    · exact ⟨g, hx, h⟩
  · rcases hnb' ν (Or.inr (Or.inr rfl)) with h | h | h
    · exact absurd (hinj _ _ (h.trans hgβ.symm)) hβε.symm
    · refine ⟨g⁻¹, (stab α ⊓ stab β).inv_mem hx, ?_⟩
      rw [inv_smul_eq_iff]
      exact h.symm
    · exact absurd h hne

theorem stab_eq_sup_inf (hA : F53Amalgam H M S) {α β δ : Geo H M} (hα : vtype α = true)
    (hβδ : β ≠ δ) (hβ : β ∈ nbrs α) (hδ : δ ∈ nbrs α) :
    stab α = (stab α ⊓ stab β) ⊔ (stab α ⊓ stab δ) := by
  have hidx := index_inf_stab_true hA hα hβ
  have hle : stab α ⊓ stab β ≤ (stab α ⊓ stab β) ⊔ (stab α ⊓ stab δ) := le_sup_left
  have hK : (stab α ⊓ stab β) ⊔ (stab α ⊓ stab δ) ≤ stab α := sup_le inf_le_left inf_le_left
  rcases eq_or_eq_of_le_of_index_prime hle hK Nat.prime_three hidx with h | h
  · exfalso
    have h1 : stab α ⊓ stab δ ≤ stab α ⊓ stab β := h ▸ le_sup_right
    have hSδ := sylow_stab_inf_left hA hδ
    have h2 : stab α ⊓ stab δ = stab α ⊓ stab β :=
      F1.eq_of_isSylowTwoOf_le hSδ inf_le_left (sylow_stab_inf_left hA hβ).2.1 h1
    obtain ⟨ε, hε, hεβ, hεδ⟩ := exists_third_nbr hA hα hβδ
    obtain ⟨t, ht, htδ⟩ := exists_swap hA hα hβδ (Ne.symm hεβ) (Ne.symm hεδ) hβ hδ hε
    have ht' : (t : G) ∈ stab α ⊓ stab δ := by
      rw [h2]
      exact ht
    exact hεδ ((smul_eq_of_mem_stab ht'.2).symm.trans htδ).symm
  · exact h.symm

end F53B3

end CFSG.Quasithin
