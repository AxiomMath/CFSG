module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationSeven
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationEightModel
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

theorem G22_facts [Finite G] {V V₁ L T H : Subgroup G} (h : AlmostSpecialHyp V V₁ L T H) :
    conjClosure V H ≤ pCoreOf 2 H ∧ conjClosure V H ≤ T ∧
      ∀ u ∈ conjClosure V H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁ := by
  have hU := h.G22_one.2
  have hcc := h.conjClosure_le_N
  have hmemY : ∀ u (hu : u ∈ conjClosure V H),
      tmk V₁ ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
    fun u hu => (secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu
  have hUQ : conjClosure V H ≤ pCoreOf 2 H := fun u hu => by
    have hQ : tmk V₁ ⟨u, hcc hu⟩ ∈ tildeOf V₁ (pCoreOf 2 H) :=
      omegaOneCenterOf_le _ (hmemY u hu)
    exact (secMk_mem_secImg_iff h.V₁_le_pCoreOf).1 hQ
  refine ⟨hUQ, h.G22_three.1, fun u hu q hq => ?_⟩
  have hqt : tmk V₁ ⟨q, h.H_le (pCoreOf_le 2 H hq)⟩ ∈ tildeOf V₁ (pCoreOf 2 H) :=
    secMk_mem_secImg hq
  have hcomm := mem_centralizer_of_mem_omegaOneCenterOf (hmemY u hu) hqt
  exact commutator_mem_of_secMk_commute hcomm.symm

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def Gz : Subgroup G := Subgroup.centralizer ({E.z} : Set G)

@[expose] def V₁ : Subgroup G := Subgroup.zpowers E.z

@[expose] def V₂ : Subgroup G := Vh.map E.ι

@[expose] def Lam : Set G := conjClassIn E.Gz E.t

theorem mem_Gz {g : G} : g ∈ E.Gz ↔ E.z * g = g * E.z := by
  simp only [Gz, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

theorem T_le_Gz : T ≤ E.Gz := E.T_le_centralizer_z

theorem mem_V₁ {x : G} : x ∈ E.V₁ ↔ x = 1 ∨ x = E.z := E.mem_zpowers_z_iff

theorem z_mem_V₁ : E.z ∈ E.V₁ := E.mem_V₁.2 (Or.inr rfl)

theorem conj_z {g : G} (hg : g ∈ E.Gz) : g * E.z * g⁻¹ = E.z := by
  have := E.mem_Gz.1 hg
  rw [← this]
  group

theorem comm_V₁ {g c : G} (hg : g ∈ E.Gz) (hc : c ∈ E.V₁) : g * c * g⁻¹ = c := by
  rcases E.mem_V₁.1 hc with rfl | rfl
  · group
  · exact E.conj_z hg

theorem mem_V₂ {x : G} : x ∈ E.V₂ ↔ x = 1 ∨ x = E.z ∨ x = E.t ∨ x = E.t * E.z := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases mem_Vh.1 hw with rfl | rfl | rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (map_mul _ _ _)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, one_mem _, map_one _⟩
    · exact ⟨z0, mem_Vh.2 (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨t0, mem_Vh.2 (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
    · exact ⟨t0 * z0, mem_Vh.2 (Or.inr (Or.inr (Or.inr rfl))), map_mul _ _ _⟩

theorem t_mem_V₂ : E.t ∈ E.V₂ := E.mem_V₂.2 (Or.inr (Or.inr (Or.inl rfl)))

theorem z_mem_V₂ : E.z ∈ E.V₂ := E.mem_V₂.2 (Or.inr (Or.inl rfl))

theorem V₁_le_V₂ : E.V₁ ≤ E.V₂ := by
  intro x hx
  rcases E.mem_V₁.1 hx with rfl | rfl
  · exact one_mem _
  · exact E.z_mem_V₂

theorem V₂_le_T : E.V₂ ≤ T := by
  have := Subgroup.map_mono (f := E.ι) Vh_le_Th
  rwa [E.map_Th] at this

theorem T_le_normalizer_V₂ : T ≤ Subgroup.normalizer (E.V₂ : Set G) := by
  have := E.map_le_normalizer Th_le_normalizer_Vh
  rwa [E.map_Th] at this

theorem t_ne_z : E.t ≠ E.z := fun h => t0_ne_z0 (E.injective h)

theorem V₁_ne_V₂ : E.V₁ ≠ E.V₂ := by
  intro h
  have : E.t ∈ E.V₁ := by rw [h]; exact E.t_mem_V₂
  rcases E.mem_V₁.1 this with h1 | h1
  · exact E.t_ne_one h1
  · exact E.t_ne_z h1

theorem Gz_le_normalizer_V₁ : E.Gz ≤ Subgroup.normalizer (E.V₁ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [E.mem_V₁] at hx ⊢
    rcases hx with rfl | rfl
    · left; group
    · right; exact E.conj_z hg
  · intro hx
    rw [E.mem_V₁] at hx ⊢
    rcases hx with h1 | h1
    · left
      have : g * x * g⁻¹ = 1 := h1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    · right
      have h2 : g * x * g⁻¹ = E.z := h1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * E.z * g := by rw [h2]
        _ = E.z := by
          have := E.conj_z (E.Gz.inv_mem hg)
          simpa using this

theorem bot_eq_oTwoUpper_bot : (⊥ : Subgroup G) = oTwoUpper ⊥ :=
  le_antisymm bot_le (oTwoUpper_le _)

theorem lOne_bot : lOne (⊥ : Subgroup G) E.V₁ = ⊥ := by
  unfold lOne
  rw [bot_inf_eq]
  exact bot_eq_oTwoUpper_bot.symm

theorem almostSpecialHyp [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) : AlmostSpecialHyp E.V₂ E.V₁ ⊥ T E.Gz := by
  have hlOne : lOne (⊥ : Subgroup G) E.V₁ ⊔ T = T := by rw [E.lOne_bot, bot_sup_eq]
  have hTGz : T ≤ E.Gz := E.T_le_Gz
  have hSyl : IsSylowTwoOf T E.Gz := by
    refine ⟨hTGz, hT.1, ?_⟩
    intro h
    exact hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTGz))
  refine
    { elemAbelian := isElemAbelian_map isElemAbelian_Vh E.ι
      ne_bot := ?_
      le_V := E.V₁_le_V₂
      oTwo_eq := bot_eq_oTwoUpper_bot
      V_le_T := E.V₂_le_T
      T_le_normV₁ := hTGz.trans E.Gz_le_normalizer_V₁
      T_le_normV := E.T_le_normalizer_V₂
      T_le_normL := ?_
      sylow_LT := ?_
      H_le := E.Gz_le_normalizer_V₁
      lOne_sup_le := by rw [hlOne]; exact hTGz
      sylow_H := hSyl
      charTwo := E.charTwo_centralizer_z hEven hT
      irred := ?_ }
  · intro h
    have : E.z ∈ E.V₁ := E.z_mem_V₁
    rw [h, Subgroup.mem_bot] at this
    exact E.z_ne_one this
  · intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]
  · rw [bot_sup_eq]
    refine ⟨le_rfl, hT.1, ?_⟩
    simp
  · rw [hlOne]
    refine ⟨lt_of_le_of_ne E.V₁_le_V₂ E.V₁_ne_V₂, E.T_le_normalizer_V₂,
      hTGz.trans E.Gz_le_normalizer_V₁, ?_⟩
    intro W hV₁W hWV _
    by_cases hW : W = E.V₁
    · exact Or.inl hW
    · right
      apply le_antisymm hWV
      obtain ⟨w, hwW, hwV₁⟩ : ∃ w ∈ W, w ∉ E.V₁ := by
        by_contra hcon
        push Not at hcon
        exact hW (le_antisymm hcon hV₁W)
      have htW : E.t ∈ W := by
        rcases E.mem_V₂.1 (hWV hwW) with h1 | h1 | h1 | h1
        · exact absurd (E.mem_V₁.2 (Or.inl h1)) hwV₁
        · exact absurd (E.mem_V₁.2 (Or.inr h1)) hwV₁
        · rw [← h1]; exact hwW
        · have hz : E.z ∈ W := hV₁W E.z_mem_V₁
          have : E.t = w * E.z⁻¹ := by
            calc E.t = E.t * E.z * E.z⁻¹ := by group
              _ = w * E.z⁻¹ := by rw [h1]
          rw [this]
          exact W.mul_mem hwW (W.inv_mem hz)
      intro x hx
      rcases E.mem_V₂.1 hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hV₁W E.z_mem_V₁
      · exact htW
      · exact W.mul_mem htW (hV₁W E.z_mem_V₁)

theorem U_facts [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T) :
    conjClosure E.V₂ E.Gz ≤ pCoreOf 2 E.Gz ∧ conjClosure E.V₂ E.Gz ≤ T ∧
      ∀ u ∈ conjClosure E.V₂ E.Gz, ∀ q ∈ pCoreOf 2 E.Gz, u * q * u⁻¹ * q⁻¹ ∈ E.V₁ :=
  G22_facts (E.almostSpecialHyp hEven hT)

end Emb

end CFSG.Quasithin.A10
