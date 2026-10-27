module

public import CFSG.Quasithin.Background.S1567Z2
public import CFSG.Quasithin.Background.S1567Z7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

@[expose] def Input15367Inspect : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G),
    Ctx67 G T Mc M V₁ V₂ E t →
      (∀ A : Subgroup G, IsMaxElemAbelian (TE153 T E) A →
        Nat.card (VE67 T M E) ≤ ((A ⊓ S1567.K167 T M E).relIndex A) ^ 2 *
          Nat.card ↥(VE67 T M E ⊓ Subgroup.centralizer (A : Set G))) →
      (∃ A : Subgroup G, IsMaxElemAbelian (TE153 T E) A ∧ ¬ A ≤ S1567.K167 T M E) →
      (∀ D : Subgroup G, D ≤ Subgroup.centralizer (E : Set G) →
        Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G) →
        S1567.K167 T M E ≤ D → (∀ d ∈ D, ∃ n : ℕ, d ^ 2 ^ n ∈ S1567.K167 T M E) →
          D ≤ S1567.K167 T M E) →
      ¬ 3 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E : Set G)) →
      Subgroup.normalizer (thompsonJ (TE153 T E) : Set G) ≤ M →
        (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) = 3

theorem input15367Inspect_of_step67Index (h : Step67Index) : Input15367Inspect :=
  fun G _ _ T Mc M V₁ V₂ E t k _ _ _ _ _ => h G T Mc M V₁ V₂ E t k

theorem step67Index_of_inspect (h113 : StageLemma14113) (hI : Input15367Inspect) : Step67Index := by
  intro G _ _ T Mc M V₁ V₂ E t k
  exact hI G T Mc M V₁ V₂ E t k
    (fun A hA => S1567.step67_count h113 k hA)
    (S1567.exists_isMaxElemAbelian_not_le_K167 h113 k)
    (fun D hDC hDn hKD hD2 => S1567.le_K167_of_normal_two_quotient h113 k hDC hDn hKD hD2)
    (S1567.not_three_dvd_card_M_inf_CE k)
    (S1567.commJ_data h113 k).2.2.2.2.1

theorem stage15367Rest_of_inspect (h113 : StageLemma14113) (hI : Input15367Inspect) :
    Stage15367Rest :=
  stage15367Rest_of_named_inputs h113 (step67Index_of_inspect h113 hI)

end CFSG.Quasithin
