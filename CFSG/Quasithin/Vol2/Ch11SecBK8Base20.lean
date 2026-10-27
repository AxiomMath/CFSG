module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts36
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base15
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base18
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base8

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {W : Subgroup G} {hW : IsElemAbelian 2 W} {K : Type} [Field K]

theorem autI_zpowers' (hW : IsElemAbelian 2 W) {e : G}
    (he : e ∈ Subgroup.normalizer (W : Set G)) :
    autI hW (Subgroup.zpowers e) = Subgroup.zpowers (convI hW ⟨e, he⟩) := by
  ext φ
  rw [mem_autI hW, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk)
  · rintro ⟨k, rfl⟩
    exact ⟨⟨e, he⟩ ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, by simp⟩, map_zpow _ _ _⟩

theorem map_autI_zpowers (Φ : IntMod W hW ≃* W6 K) {e : G}
    (he : e ∈ Subgroup.normalizer (W : Set G)) :
    (autI hW (Subgroup.zpowers e)).map (congrHom Φ) = Subgroup.zpowers (hat Φ e he) := by
  rw [autI_zpowers' hW he, MonoidHom.map_zpowers]
  rfl

theorem commutator_zpowers_eq (Φ : IntMod W hW ≃* W6 K) {e : G}
    (he : e ∈ Subgroup.normalizer (W : Set G)) :
    ⁅Subgroup.zpowers e, W⁆ = (commSub ⊤ (Subgroup.zpowers (hat Φ e he))).map (psi Φ) := by
  rw [Subgroup.commutator_comm, commutator_eq_map Φ le_rfl (Subgroup.zpowers_le.mpr he),
    comap_psi_self, map_autI_zpowers]

theorem exists_model36 {L V X T V₁ V₂ : Subgroup G} {n : ℕ}
    (h : Flag36 L V W X T V₁ V₂ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ (Φ : IntMod W h.elemW ≃* W6 K) (a b : K), (autI h.elemW L).map (congrHom Φ) = diagSL K ∧
        (autI h.elemW X).map (congrHom Φ) ≤ normD K ∧ (a ≠ 0 ∨ b ≠ 0) ∧
        V.comap (psi Φ) = natSub a b ∧
        ∃ S₁ S₂ : Submodule K (Fin 3 → K), Module.finrank K S₁ = 1 ∧ Module.finrank K S₂ = 2 ∧
          V₁.comap (psi Φ) = natSubOf a b S₁ ∧ V₂.comap (psi Φ) = natSubOf a b S₂ := by
  obtain ⟨K, _, _, _, hK, Φ, hL, hX⟩ :=
    exists_model_X h.elemW h.L_le_W h.two h.normalizer_le_W
  have hcV := h.cV
  have hs₁ : IsEndStable L V ⊥ V₁ := by
    have := h.stable₁
    rwa [hcV] at this
  have hs₂ : IsEndStable L V ⊥ V₂ := by
    have := h.stable₂
    rwa [hcV] at this
  have hc₁ : Nat.card ↥V₁ = Nat.card K := by
    have := h.index₁
    rwa [hcV, Subgroup.relIndex_bot_left, ← hK] at this
  have hc₂ : Nat.card ↥V₂ = Nat.card K ^ 2 := by
    have := h.index₂
    rwa [hcV, Subgroup.relIndex_bot_left, pow_mul, ← hK] at this
  have hV₁V : V₁ ≤ V := h.le₁₂.trans h.le₂
  obtain ⟨a, b, hab, hV⟩ :=
    exists_natSub_V Φ hL h.L_le_W h.le_W h.le_normalizer hV₁V hs₁ hc₁
  have hscal : ∀ {U : Subgroup G}, U ≤ V → IsEndStable L V ⊥ U →
      ∀ (c : K) (x : W6 K), psi Φ x ∈ U → psi Φ (scalHom c x) ∈ U := by
    intro U hUV hU c x hx
    refine psi_mem_of_isEndStable Φ hL h.L_le_W h.le_W hUV hU (scalHom c) (fun y hy => ?_)
      (fun γ _ v => scalHom_comm c γ v) hx
    have h1 : y ∈ V.comap (psi Φ) := hy
    rw [hV] at h1
    have h2 : scalHom c y ∈ V.comap (psi Φ) := by
      rw [hV]
      exact scalHom_natSub c a b h1
    exact h2
  obtain ⟨S₁, hS₁⟩ := exists_subspace Φ hV hV₁V (hscal hV₁V hs₁)
  obtain ⟨S₂, hS₂⟩ := exists_subspace Φ hV h.le₂ (hscal h.le₂ hs₂)
  have hq : 1 < Nat.card K := Finite.one_lt_card
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, Φ, a, b, hL, hX, hab, hV, S₁, S₂,
    ?_, ?_, hS₁, hS₂⟩
  · have h1 := card_comap_psi Φ (hV₁V.trans h.le_W)
    rw [hS₁, card_natSubOf hab, hc₁, Module.natCard_eq_pow_finrank (K := K)] at h1
    exact Nat.pow_right_injective hq (h1.trans (pow_one _).symm)
  · have h1 := card_comap_psi Φ (h.le₂.trans h.le_W)
    rw [hS₂, card_natSubOf hab, hc₂, Module.natCard_eq_pow_finrank (K := K)] at h1
    exact Nat.pow_right_injective hq h1

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
