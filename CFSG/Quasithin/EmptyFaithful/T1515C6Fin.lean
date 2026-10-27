module

public import CFSG.Quasithin.EmptyFaithful.T1515C6Q

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_wreath_s3_z2 :
    Nat.card (Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) = 72 := by
  rw [RegularWreathProduct.card]
  have h1 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  rw [h1, h2]
  norm_num

theorem V154_eq_VZ_of_six {T Mc M : Subgroup G} (h6 : Ce15Six T Mc M 3) :
    V154 T Mc M = VZ T M := by
  by_cases hc : Case1512Six T Mc M
  · exfalso
    have h1 := h6.card_eq
    rw [V154_eq_uJ hc] at h1
    have h2 := hc.2.2.2.1
    omega
  · exact V154_eq_VZ hc


theorem not_le_mc_of_isMf {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) :
    ¬ M ≤ Mc := fun hMMc => hM.2.1 (hM.1.1.1.2 Mc hq.mc_max.1 hMMc).symm

theorem exists_six3Data {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h6 : Ce15Six T Mc M 3)
    (h110 : Nonempty (↥(autOn M (V154 T Mc M)) ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2))) :
    ∃ hVe : IsElemAbelian 2 (V154 T Mc M), ∃ d : Six3Data (V154 T Mc M) M T hVe,
      mBar0 T Mc M = d.A₁ ⊔ d.A₂ := by
  have hV : V154 T Mc M = VZ T M := V154_eq_VZ_of_six h6
  have hVe : IsElemAbelian 2 (V154 T Mc M) := by
    rw [hV]
    exact isElemAbelian_VZ hq hM.1.1
  refine ⟨hVe, ?_⟩
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hVe
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by
    rw [hV]
    exact le_normalizer_VZ T M
  have hTM : T ≤ M := hM.1.1.2
  have hsyl : IsSylowTwoOf T M := isSylowTwoOf_of_le151 hq.sylow hTM
  have hcardM : Nat.card (autOn M (V154 T Mc M)) = 72 := by
    obtain ⟨e⟩ := h110
    rw [Nat.card_congr e.toEquiv, card_wreath_s3_z2]
  obtain ⟨hcardV, A₁, A₂, hdir, ⟨e₁⟩, ⟨e₂⟩, ⟨t, ht, hconj⟩, hinf, hsup⟩ := h6
  have hA₀ : mBar0 T Mc M ≤ autOn M (V154 T Mc M) := by
    unfold mBar0 JhatOn
    simp only [hVe, dite_true]
    exact Jhat_le _
  have hA₀M : A₁ ⊔ A₂ ≤ autOn M (V154 T Mc M) := hdir.1 ▸ hA₀
  have hctx := sixCtx_of_data hVe hMN hsyl hcardV hcardM hA₀M ⟨e₁⟩ ⟨e₂⟩ hdir.2.1 hdir.2.2 ht hconj
    hinf hsup
  obtain ⟨s, u, hg⟩ := (SixCtx.exists_gens (h := hctx))
  exact ⟨⟨hMN, hsyl, A₁, A₂, t, ht, s, u, hctx, hg⟩, hdir.1⟩


theorem exists_setting_six3 {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h6 : Ce15Six T Mc M 3) (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (h110 : Nonempty (↥(autOn M (V154 T Mc M)) ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)))
    (h113 : Lemma15113Four T Mc M) :
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, Setting1516X T Mc M Z₁ Z₂ V₁ V₂ := by
  obtain ⟨hVe, d, hA₀⟩ := exists_six3Data hq hM h6 h110
  refine ⟨d.Z₁, d.Z₂, d.V₁, d.V₂, ?_⟩
  have hV : V154 T Mc M = VZ T M := V154_eq_VZ_of_six h6
  have hJ : autOn (thompsonJi T 1) (V154 T Mc M) =
      @sixT0 ↥(V154 T Mc M) (commGroupOfElemAbelian hVe) d.A₁ d.A₂ (autOn T (V154 T Mc M)) := by
    rcases h113 with ⟨h1, -⟩ | ⟨h3, -⟩
    · rw [h1, hA₀]
      rfl
    · exfalso
      have h4 := h3.1
      have h5 := h6.card_eq
      omega
  have hVT : V154 T Mc M ≤ T := by
    rw [hV]
    exact (isTwoReducedIn_VZ hq hM.1.1).2
  have hZV : quasithinOmegaOneCenter T ≤ V154 T Mc M := by
    rw [hV]
    exact le_conjClosure _ _
  have hJC : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf (thompsonJ_le_self151 T) (le_centralizer_of_commutator_eq_bot h19.one_commute)
  have hrank : 1 < CFSG.Open.pRank 2 T :=
    one_lt_pRank_of_card hVe hVT (by have := h6.card_eq; omega)
  have hJR : thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
    rw [thompsonJ_eq_thompsonJi_zero, thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_eq_of_le (by omega)
      (by rw [← thompsonJ_eq_thompsonJi_zero]; exact hJC) inf_le_left
  exact d.setting_of h6 rfl hV h15.centralizer_le hq.t_le_mc (not_le_mc_of_isMf hq hM) hJ hVT hZV
    (d.p_sub h19.six_autOn hJR)

end CFSG.Quasithin
