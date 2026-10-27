module

public import CFSG.Quasithin.EmptyFaithful.T1531Stage4
public import CFSG.Quasithin.EmptyFaithful.T1531In47
public import CFSG.Quasithin.Background.C1PackS15348
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.F9Eighteen

public section

namespace CFSG.Quasithin.S1565

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section NParam

variable {G : Type} [Group G] [Finite G]

theorem even_card_of_pCoreOf_ne_bot {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) :
    Even (Nat.card H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hH
    rw [← Subgroup.card_eq_one]
    simpa using hk
  have hdvd : Nat.card (pCoreOf 2 H) ∣ Nat.card H := Subgroup.card_dvd_of_le (pCoreOf_le 2 H)
  rw [hk] at hdvd
  have h2 : 2 ∣ Nat.card H :=
    (dvd_pow_self 2 hk0).trans hdvd
  exact even_iff_two_dvd.mpr h2

theorem one_le_nParam {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) : 1 ≤ E1.nParam H := by
  by_contra h
  have h0 : E1.nParam H ≤ 0 := by
    have : E1.nParam H < 1 := not_le.mp h
    exact Order.lt_one_iff.mp this ▸ le_rfl
  have hodd := E1.odd_of_nParam_le_zero h0
  exact (Nat.not_even_iff_odd.mpr hodd) (even_card_of_pCoreOf_ne_bot hH)

end NParam

section Setup

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem sqtkGroup_of_isHStar (c : Ctx153 G T Mc M V₁ V₂ t) {H : Subgroup G} (hH : IsHStar T M H) :
    SQTKGroup ↥H :=
  ⟨stronglyQuasithin_of_pCoreOf_ne_bot c.hyp.qtfe.qtke hH.1.2,
    kGroup_of_pCoreOf_ne_bot c.hyp.qtfe.qtke c.hyp.qtfe.simple c.hyp.qtfe.nonabelian hH.1.2⟩

omit [Finite G] in
theorem isQuasisimple_quot_pCoreOf {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) :
    CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K) := by
  have e : (pCoreOf 2 K).subgroupOf K = CFSG.Open.pCore 2 ↥K := by
    rw [pCoreOf, map_subtype_subgroupOf']
  have key : ∀ (N₁ N₂ : Subgroup ↥K) [N₁.Normal] [N₂.Normal], N₁ = N₂ →
      CFSG.Open.IsQuasisimple (↥K ⧸ N₂) → CFSG.Open.IsQuasisimple (↥K ⧸ N₁) := by
    intro N₁ N₂ _ _ h
    subst h
    exact id
  exact A3.isQuasisimple_iff_open.mpr (key _ _ e hq)

theorem hypF918_of_e22 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (c : Ctx153 G T Mc M V₁ V₂ t) (r45 : Res15345 T Mc M V₁ V₂) (r46 : Res15346 T M V₁ V₂)
    (r49 : Res15349 T Mc M V₁) (r62 : Res15362 T Mc M) {H K : Subgroup G} (hH : IsHTM153 T M H)
    (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)) :
    HypF918 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H K := by
  have r47 : Res15347 T M V₁ := stage15347 G T Mc M V₁ V₂ t c r45 r46
  have hF := hypF91_of_stage15348 (stage15348 h11 h113) c r45 r46 r47 r49 hH
  have hF98 := hypF98_of_results c r47 r62 hF
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := hF.T_le_H
  have hK₀H : conjClosure K T ≤ H :=
    conjClosure_le fun _ ht _ hz => H.mul_mem (H.mul_mem (hTH ht) (hKH hz)) (H.inv_mem (hTH ht))
  refine ⟨hF98, hK, isQuasisimple_quot_pCoreOf hq, ?_, ?_⟩
  · refine le_antisymm ?_ (sup_le hK₀H inf_le_right)
    have hle : K ⊔ T ≤ conjClosure K T ⊔ ((Y153 Mc M ⊔ T) ⊓ H) :=
      sup_le (le_sup_of_le_left (le_conjClosure K T))
        (le_sup_of_le_right (le_inf le_sup_right hTH))
    exact hHK.le.trans hle
  · rw [hHK]
    exact (sup_le_sup_right (le_conjClosure K T) T).trans (HypF918.K₀T_le_normalizer_K₀ T K)

end Setup

end CFSG.Quasithin.S1565
