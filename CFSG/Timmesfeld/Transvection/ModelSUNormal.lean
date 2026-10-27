module

public import CFSG.Timmesfeld.Transvection.ModelRankSU
public import CFSG.Timmesfeld.Transvection.ModelSUGeometry

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {F : Type} [Field F] {m : ℕ}

@[expose] def SUCommStmt (σ : F ≃+* F) (m : ℕ) : Prop :=
  ∀ {K : Type} [Group K] {Φ : SU σ m →* K}, Φ.ker ≤ Subgroup.center (SU σ m) →
    ∀ {p r : Fin m → F} {X Y : Subgroup (SU σ m)}, IsUTransGroup σ p X → IsUTransGroup σ r Y →
      p ≠ 0 → r ≠ 0 → uForm σ p p = 0 → uForm σ r r = 0 →
      (Commuting (X.map Φ) (Y.map Φ) ↔ uForm σ p r = 0 ∨ ∃ l : F, r = l • p)

@[expose] def SUSL2Stmt (σ : F ≃+* F) (m : ℕ) : Prop :=
  ∀ {K : Type} [Group K] {Φ : SU σ m →* K}, Φ.ker ≤ Subgroup.center (SU σ m) →
    ∀ {a d : Fin m → F} {T Td : Subgroup (SU σ m)}, IsUTransGroup σ a T → IsUTransGroup σ d Td →
      uForm σ a a = 0 → uForm σ d d = 0 → uForm σ a d = 1 →
      ∀ β : MulAut K, (∀ x ∈ T.map Φ, β x = x) → (Td.map Φ).map β.toMonoidHom = Td.map Φ →
        ∀ x ∈ Td.map Φ, β x = x

end ModelRank

end CFSG.Timmesfeld.Transvection

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suCommStmt_holds [CharP F 2] (hσ : ∀ c, σ (σ c) = c) : SUCommStmt σ m := by
  intro K _ Φ hker p r X Y hX hY hp hr hpp hrr
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  refine ⟨fun hc => hX.uForm_eq_zero_of_center hσ one_ne_zero h1 hY hp hpp hrr
    (commutator_mem_center hker hc), fun h => commuting_map Φ (hX.commuting hσ hY ?_)⟩
  rcases h with h | ⟨l, rfl⟩
  · exact h
  · rw [uForm_smul_right, hpp, mul_zero]

theorem suMapEqStmt_holds [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) :
    ∀ {K : Type} [Group K] {Φ : SU σ m →* K}, Φ.ker ≤ Subgroup.center (SU σ m) →
      ∀ {p r : Fin m → F} {X Y : Subgroup (SU σ m)}, IsUTransGroup σ p X → IsUTransGroup σ r Y →
        p ≠ 0 → r ≠ 0 → uForm σ p p = 0 → uForm σ r r = 0 → X.map Φ = Y.map Φ →
        ∃ l : F, r = l • p := by
  intro K _ Φ hker p r X Y hX hY hp hr hpp hrr hmap
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  have hc₁ : Commuting (X.map Φ) (Y.map Φ) := by
    rw [← hmap]
    exact commuting_map Φ (hX.commuting hσ hX hpp)
  rcases hX.uForm_eq_zero_of_center hσ one_ne_zero h1 hY hp hpp hrr
      (commutator_mem_center hker hc₁) with hpr | hl
  swap
  · exact hl
  by_contra hne
  have hva : ∀ c : F, r ≠ c • p := fun c hc => hne ⟨c, hc⟩
  obtain ⟨z, hzz, hpz, hrz⟩ := exists_isotropic_perp_not_perp hσ htr hp hpp hrr hpr hva
  have hz : z ≠ 0 := by
    rintro rfl
    exact hpz (uForm_zero_right p)
  obtain ⟨Tz, hTz⟩ := exists_isUTransGroup hσ hzz
  have hc₂ : Commuting (Tz.map Φ) (X.map Φ) := by
    rw [hmap]
    exact commuting_map Φ (hTz.commuting hσ hY (uForm_eq_zero_comm hσ hrz))
  rcases hTz.uForm_eq_zero_of_center hσ one_ne_zero h1 hX hz hzz hpp
      (commutator_mem_center hker hc₂) with h | ⟨l, hl⟩
  · exact hpz (uForm_eq_zero_comm hσ h)
  · apply hpz
    rw [hl, uForm_smul_left, hzz, mul_zero]

theorem uTrans_sandwich_mulVec (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (had : uForm σ a d = 1) (e c : F) :
    (uTrans σ a e * uTrans σ d c * uTrans σ a e) *ᵥ a = (1 + e * c) • a + c • d := by
  have hda : uForm σ d a = 1 := by rw [← uForm_conj σ hσ, had, map_one]
  have h1 : uTrans σ a e *ᵥ a = a := by rw [uTrans_mulVec, haa, mul_zero, zero_smul, add_zero]
  have h2 : uTrans σ d c *ᵥ a = a + c • d := by rw [uTrans_mulVec, hda, mul_one]
  have h3 : uTrans σ a e *ᵥ (a + c • d) = (1 + e * c) • a + c • d := by
    rw [uTrans_mulVec, uForm_add_right, uForm_smul_right, haa, had, zero_add, mul_one, add_smul,
      one_smul]
    abel
  rw [← mulVec_mulVec, ← mulVec_mulVec, h1, h2, h3]

theorem suSL2Stmt_holds [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) : SUSL2Stmt σ m := by
  intro K _ Φ hker a d T Td hT hTd haa hdd had β hβT hβTd x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨c, hc, hyc⟩ := (hTd.1 y).1 hy
  by_cases hc0 : c = 0
  · have hy1 : y = 1 := suMat_injective σ (by rw [hyc, hc0, uTrans_zero, map_one])
    rw [hy1, map_one, map_one]
  have ha : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  have hd : d ≠ 0 := by
    rintro rfl
    rw [uForm_zero_right] at had
    exact zero_ne_one had
  have hda : uForm σ d a = 1 := by rw [← uForm_conj σ hσ, had, map_one]
  have hσc : σ c = -c := by linear_combination hc
  have he : c⁻¹ + σ c⁻¹ = 0 := by rw [map_inv₀, hσc, inv_neg, add_neg_cancel]
  obtain ⟨s, hs⟩ := hT.2 c⁻¹ he
  have hsT : s ∈ T := (hT.1 s).2 ⟨c⁻¹, he, hs⟩
  have hβs : β (Φ s) = Φ s := hβT _ ⟨s, hsT, rfl⟩
  have hw : suMat σ m (s * y * s) *ᵥ a = c • d := by
    rw [map_mul, map_mul, hs, hyc, uTrans_sandwich_mulVec hσ haa had, inv_mul_cancel₀ hc0,
      CharTwo.add_self_eq_zero, zero_smul, zero_add]
  have hTw : conjSub T (s * y * s) = Td := by
    have h := hT.conjSub (s * y * s)
    rw [hw] at h
    exact (h.of_smul hσ hc0).eq hTd
  obtain ⟨y', hy', hy'eq⟩ : ∃ y' ∈ Td, Φ y' = β (Φ y) := by
    have h : β (Φ y) ∈ (Td.map Φ).map β.toMonoidHom := ⟨Φ y, ⟨y, hy, rfl⟩, rfl⟩
    rw [hβTd] at h
    exact h
  obtain ⟨c', hc', hy'c⟩ := (hTd.1 y').1 hy'
  have hTβ : (T.map Φ).map β.toMonoidHom = T.map Φ := by
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hβT z' hz']
      exact hz'
    · intro hz
      exact ⟨z, hz, hβT z hz⟩
  have hβw : β.toMonoidHom (Φ (s * y * s)) = Φ (s * y' * s) := by
    simp only [MulEquiv.coe_toMonoidHom, map_mul, hβs, ← hy'eq]
  have key : Td.map Φ = (conjSub T (s * y' * s)).map Φ := by
    calc Td.map Φ = (Td.map Φ).map β.toMonoidHom := hβTd.symm
      _ = ((conjSub T (s * y * s)).map Φ).map β.toMonoidHom := by rw [hTw]
      _ = (conjSub (T.map Φ) (Φ (s * y * s))).map β.toMonoidHom := by rw [conjSub_map]
      _ = conjSub ((T.map Φ).map β.toMonoidHom) (β.toMonoidHom (Φ (s * y * s))) :=
        (conjSub_map _ _ _).symm
      _ = conjSub (T.map Φ) (Φ (s * y' * s)) := by rw [hTβ, hβw]
      _ = (conjSub T (s * y' * s)).map Φ := conjSub_map _ _ _
  obtain ⟨l, hl⟩ := suMapEqStmt_holds hσ htr hker hTd (hT.conjSub (s * y' * s)) hd
    (suMat_mulVec_ne_zero σ _ ha) hdd ((uForm_mulVec σ _ a a).trans haa) key
  rw [map_mul, map_mul, hs, hy'c, uTrans_sandwich_mulVec hσ haa had] at hl
  have h := congrArg (uForm σ d) hl
  simp only [uForm_add_right, uForm_smul_right, hdd, hda, mul_one, mul_zero, add_zero] at h
  have h3 : c⁻¹ * c' = 1 := by linear_combination h - (CharTwo.two_eq_zero : (2 : F) = 0)
  have hcc : c' = c := by
    calc c' = c * (c⁻¹ * c') := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      _ = c := by rw [h3, mul_one]
  have hyy : y' = y := suMat_injective σ (by rw [hy'c, hyc, hcc])
  rw [← hy'eq, hyy]

end ModelRank

end CFSG.Timmesfeld.Transvection
