module

public import CFSG.Quasithin.Background.E6TwentyThreeL

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E623A6Detour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L U₀ X : Subgroup G) (g : G)
    (hV : IsElemAbelian 2 V),
    HypE61 T M V → 2 < E3.mParam (autI hV M) → E3.rParam V = 1 →
    U ≤ V → E3.mQuot V U = 1 → ¬ Subgroup.centralizer (U : Set G) ≤ M →
    CharTwo (Subgroup.centralizer (U : Set G)) →
    IsChi0Block (Subgroup.centralizer (U : Set G)) L → IsAltType L 3 → ¬ L ≤ M →
    U ⊓ (V ⊓ Subgroup.centralizer (T : Set G)) = ⊥ →
    U₀ < U → E3.mQuot V U₀ ≤ 2 →
    IsComponentIn X (Subgroup.centralizer (U₀ : Set G)) →
    Nonempty (↥X ≃* alternatingGroup (Fin 6)) → L ≤ X →
    g ∈ M ⊓ Subgroup.normalizer (V : Set G) → ¬ CFSG.conjugate L g ≤ X → False

theorem e623A6Config_of_detour (h311 : Theorem311Stmt) (hD : E623A6Detour) : E623A6Config := by
  intro G _ _ T M V U L U₀ X hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₀U hU₀q hX hXA6 hLX
  classical
  by_cases hall : ∀ g ∈ M ⊓ Subgroup.normalizer (V : Set G), CFSG.conjugate L g ≤ X
  · set MV := M ⊓ Subgroup.normalizer (V : Set G) with hMV
    set W : Subgroup G :=
      V ⊓ ⨅ g ∈ MV, Subgroup.centralizer (CFSG.conjugate L g : Set G) with hWdef
    have hmemW : ∀ w, w ∈ W ↔ w ∈ V ∧ ∀ g ∈ MV, ∀ k ∈ CFSG.conjugate L g, k * w = w * k := by
      intro w
      simp only [hWdef, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_centralizer_iff,
        SetLike.mem_coe]
    have hV2 : IsPGroup 2 V := h.isPGroup_V
    have h15 : HypE615 hV M := Or.inr hm
    have h6 : 6 ≤ E3.mQuot V ⊥ := (e6_17 h311 hV h h15 hr1).2
    have hU₀V : U₀ ≤ V := hU₀U.le.trans hUV
    have hU₀1 : U₀ ≠ ⊥ := by
      rintro rfl
      omega
    have hWV : W ≤ V := inf_le_left
    have hU₀W : U₀ ≤ W := by
      intro u hu
      refine (hmemW u).mpr ⟨hU₀V hu, fun g hg k hk => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp (hX.1 (hall g hg hk)) u hu).symm
    have hW1 : W ≠ ⊥ := fun h0 => hU₀1 (le_bot_iff.mp (h0 ▸ hU₀W))
    have hLW : L ≤ Subgroup.centralizer (W : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h1 : (1 : G) ∈ MV := one_mem _
      have hl1 : l ∈ CFSG.conjugate L 1 := ⟨l, hl, by simp⟩
      exact (((hmemW w).mp hw).2 1 h1 l hl1).symm
    have hWM : ¬ Subgroup.centralizer (W : Set G) ≤ M := fun hle => hLM (hLW.trans hle)
    have hWq : E3.mQuot V W < E3.mParam (autI hV M) := by
      have hadd := E3.mQuot_add hU₀W hWV
      omega
    have hWΓ := mem_gammaE64_of_mQuot_lt hV h hWV hW1 hWM hWq
    have hTMV : T ≤ MV := fun t ht => ⟨h.inM.2 ht, h.normal ht⟩
    have hconj : ∀ t ∈ T, ∀ w ∈ W, t * w * t⁻¹ ∈ W := by
      intro t ht w hw
      obtain ⟨hwV, hwC⟩ := (hmemW w).mp hw
      refine (hmemW _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (h.normal ht) w).mp hwV,
        fun g hg k hk => ?_⟩
      have hgt : g * t ∈ MV := mul_mem hg (hTMV ht)
      have hk' : t⁻¹ * k * t ∈ CFSG.conjugate L (g * t) := by
        obtain ⟨l, hl, rfl⟩ := hk
        refine ⟨l, hl, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have h1 := hwC (g * t) hgt _ hk'
      calc k * (t * w * t⁻¹) = t * ((t⁻¹ * k * t) * w) * t⁻¹ := by group
        _ = t * (w * (t⁻¹ * k * t)) * t⁻¹ := by rw [h1]
        _ = t * w * t⁻¹ * k := by group
    have hWT : T ≤ Subgroup.normalizer (W : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨hconj t ht w, fun hw => ?_⟩
      have := hconj t⁻¹ (inv_mem ht) _ hw
      rwa [show t⁻¹ * (t * w * t⁻¹) * t⁻¹⁻¹ = w by group] at this
    exact e6_13_not_mem h311 h hWV hW1 hWΓ.2.2.2 hWT hWΓ
  · push Not at hall
    obtain ⟨g, hg, hgX⟩ := hall
    exact hD G T M V U L U₀ X g hV h hm hr1 hUV hU1 hUM hH hLb hL3 hLM hZ hU₀U hU₀q hX hXA6
      hLX hg hgX

end CFSG.Quasithin.E6
