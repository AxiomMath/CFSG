module

public import CFSG.Quasithin.H13.A6S13812
public import CFSG.Quasithin.H13.A6S138Ia

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace A6Min

variable {G : Type} [Group G] [Finite G]

theorem exists_minimal {P : Subgroup G → Prop} {X : Subgroup G} (hX : P X) :
    ∃ H : Subgroup G, P H ∧ H ≤ X ∧ ∀ K : Subgroup G, P K → K ≤ H → K = H := by
  induction h : Nat.card X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases hall : ∀ K : Subgroup G, P K → K ≤ X → K = X
    · exact ⟨X, hX, le_rfl, hall⟩
    · push Not at hall
      obtain ⟨K, hK, hKX, hne⟩ := hall
      have hlt : Nat.card K < n := h ▸ Subgroup.card_lt_of_lt (lt_of_le_of_ne hKX hne)
      obtain ⟨H, hH, hHK, hmin⟩ := ih _ hlt hK rfl
      exact ⟨H, hH, hHK.trans hKX, hmin⟩

end A6Min

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_Hz_of {X : Subgroup G} (h1 : S.L1 ⊔ T ≤ X) (h2 : X ≤ S.G1)
    (h3 : ¬ X ≤ Subgroup.normalizer (L : Set G)) : X ∈ S.Hz := by
  have hV1T : fsuV1 T V ≤ T := ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V).trans S.V_le_T
  exact ⟨⟨h1, S.pCoreOf_ne_bot_of_le_G1 (hV1T.trans (le_sup_right.trans h1)) h2⟩, h2, h3⟩

end Setting4

theorem lem13813_of_core
    (hcore : ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
      S.Hyp138 → ∀ H ∈ S.Hz, Group.IsSolvable ↥H → (∀ K ∈ S.Hz, K ≤ H → K = H) → False) :
    Lem13813 := by
  intro G _ _ T L V S hS X h1 h2 hsol
  by_contra hXM
  obtain ⟨H, hH, hHX, hmin⟩ := A6Min.exists_minimal (S.mem_Hz_of h1 h2 hXM)
  have hsolH : Group.IsSolvable ↥H := by
    have := hsol
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hHX)
      (Subgroup.inclusion_injective hHX)
  exact hcore G T L V S hS H hH hsolH fun K hK hKH => hmin K hK hKH

end CFSG.Quasithin.H13.A6

