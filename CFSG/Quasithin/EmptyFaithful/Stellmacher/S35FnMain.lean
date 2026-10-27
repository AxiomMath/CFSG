module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnCase1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnCase2a
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnCase2b
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChFacts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem delta0_nonempty (hS : Sit H M S) (hF : ChartFacts H M) (hclaimR : ClaimR H M)
    {β α' m γ' : Geo H M} (hL : Lam β α') (hB : Back H M β α' m γ') :
    (Delta0 β α').Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hall : ∀ l ∈ nbrs β, Vn α' ≤ Subgroup.normalizer (Zv l : Set G) := fun l hl => by
    by_contra h
    exact (Set.eq_empty_iff_forall_notMem.mp hne) l ⟨hl, h⟩
  have hQ : Vn α' ≤ Qv β := fun x hx =>
    hF.inf_eq β hL.1.vδ x (Vα'_le_stab_β hS hL hx) fun l hl => hall l hl hx
  have hc : ⁅Vn β, Vn α'⁆ ≤ Zv β ⊓ Vn α' :=
    le_inf ((Subgroup.commutator_mono le_rfl hQ).trans (Std.comm_Vn_Qv hS hL.1.vδ).le)
      ((Std.PD_comm_le hS hL.1).trans inf_le_right)
  have hz : Zv β ⊓ Vn α' = ⊥ := inf_eq_bot_of_card_two (hS.cardZ5 β hL.1.vδ) hL.2
  exact (hclaimR β α' m γ' hL.1 hB).1 (le_bot_iff.mp (hz ▸ hc))

theorem caseI_false_of_chart (hS : Sit H M S) (hF : ChartFacts H M)
    (hR : ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
      δ ≠ β → δ' ≠ β → δ' ≠ δ →
        Vn β ⊓ Vn δ = Vn β ⊓ Vn δ' ∧ Vn β ⊓ Vn δ = Vn δ ⊓ Vn δ' ∧
          stab l ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G))
    (h10 : Claim10 H M) (h16a : Claim16a H M) (h8a : Claim8a H M) (h14 : Claim14 H M)
    (h15a : Claim15a H M) (h15c : Claim15c H M) (hclaimR : ClaimR H M) : False := by
  obtain ⟨⟨β, α', hL⟩, hsym⟩ := h10
  obtain ⟨m, γ', hm1, hm2, hm3, hm4⟩ := Std.exists_geodesic hS (δ := β) (δ' := α') hL.1.dist_eq
  have hB : Back H M β α' m γ' := ⟨hm1, hm2, hm3, hm4⟩
  have hI2 : ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
      δ ≠ β → δ' ≠ β → Vn β ⊓ Vn δ = Vn β ⊓ Vn δ' := fun β l δ δ' hβ hl hδ hδ' hδβ hδ'β => by
    by_cases h : δ' = δ
    · rw [h]
    · exact (hR β l δ δ' hβ hl hδ hδ' hδβ hδ'β h).1
  obtain ⟨l0, hl0⟩ := delta0_nonempty hS hF hclaimR hL hB
  by_cases hc1 : ∃ l ∈ Delta0 β α', ∃ δ ∈ nbrs l, δ ≠ β ∧ ¬ Vn δ ≤ Qv γ'
  · obtain ⟨l, hl, δ, hδ, hδβ, hn⟩ := hc1
    exact case1 hS h14 h15a h15c hL hB hl.1 hl.2 hδ hδβ hn
  · push Not at hc1
    have hQ : ∀ l ∈ Delta0 β α', Wl l ≤ Qv γ' := fun l hl =>
      Std.Wl_le fun ρ hρ => by
        by_cases hρβ : ρ = β
        · rw [hρβ]
          have := dist_γ' hL hB
          exact Std.Vn_le_Qv_dist hS (by omega)
        · exact hc1 l hl ρ hρ hρβ
    by_cases hc2 : ∃ l ∈ Delta0 β α', Wl l ≤ stab α'
    · obtain ⟨l, hl, hW⟩ := hc2
      exact case2a hS hF h8a ⟨⟨β, α', hL⟩, hsym⟩ h14 h16a hL hl.1 hl.2 hW
    · push Not at hc2
      exact case2b hS hF h15c hI2 hL hB hl0 hQ hc2
theorem caseI_false (hS : Sit H M S) (hI : CaseI H M)
    (hZ : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (Zv δ) (Vn δ))
    (hR : ∀ β l δ δ' : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → l ∈ nbrs δ' →
      δ ≠ β → δ' ≠ β → δ' ≠ δ →
        Vn β ⊓ Vn δ = Vn β ⊓ Vn δ' ∧ Vn β ⊓ Vn δ = Vn δ ⊓ Vn δ' ∧
          stab l ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G))
    (h10 : Claim10 H M) (h16a : Claim16a H M) (h8a : Claim8a H M) (h14 : Claim14 H M)
    (h15a : Claim15a H M) (h15c : Claim15c H M) (hclaimR : ClaimR H M) : False :=
  caseI_false_of_chart hS (S35.Ch.chartFacts ⟨hS, hI, hZ, hR⟩) hR h10 h16a h8a h14 h15a h15c
    hclaimR

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin
