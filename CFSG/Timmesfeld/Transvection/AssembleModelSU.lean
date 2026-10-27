module

public import CFSG.Timmesfeld.Transvection.AssembleGen
public import CFSG.Timmesfeld.Transvection.ModelRankSU
public import CFSG.Timmesfeld.Transvection.PresSUModel
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection.Pres

namespace ModelRank

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

@[expose] def PerpUU (j : ℕ) (v : Fin m → F) : Prop :=
  ∀ i : Fin (m / 2), i.val < j → v (lowIdx i) = 0 ∧ v (Fin.rev (lowIdx i)) = 0

theorem PerpUU.add {j : ℕ} {v w : Fin m → F} (hv : PerpUU j v) (hw : PerpUU j w) :
    PerpUU j (v + w) := fun i hi => by
  simp [(hv i hi).1, (hv i hi).2, (hw i hi).1, (hw i hi).2]

theorem PerpUU.sub {j : ℕ} {v w : Fin m → F} (hv : PerpUU j v) (hw : PerpUU j w) :
    PerpUU j (v - w) := fun i hi => by
  simp [(hv i hi).1, (hv i hi).2, (hw i hi).1, (hw i hi).2]

theorem PerpUU.smul {j : ℕ} {v : Fin m → F} (hv : PerpUU j v) (l : F) : PerpUU j (l • v) :=
  fun i hi => by simp [(hv i hi).1, (hv i hi).2]

theorem PerpUU.uForm_eq_zero {j : ℕ} {v : Fin m → F} (hv : PerpUU j v) {i : Fin (m / 2)}
    (hi : i.val < j) : uForm σ v (Pi.single (lowIdx i) 1) = 0 ∧
      uForm σ v (Pi.single (Fin.rev (lowIdx i)) 1) = 0 := by
  rw [uForm_single_right, uForm_single_right, Fin.rev_rev, (hv i hi).1, (hv i hi).2, map_zero]
  exact ⟨rfl, rfl⟩

theorem PerpUU.exists_uForm_ne_zero {j : ℕ} {w : Fin m → F} (hw : PerpUU j w) (hw0 : w ≠ 0) :
    ∃ a, PerpUU j a ∧ uForm σ w a ≠ 0 := by
  obtain ⟨s, hs⟩ := Function.ne_iff.1 hw0
  refine ⟨Pi.single (Fin.rev s) 1, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · have : lowIdx i ≠ Fin.rev s := fun h => hs (by
      rw [← Fin.rev_rev s, ← h]
      exact (hw i hi).2)
    simp [this]
  · have : Fin.rev (lowIdx i) ≠ Fin.rev s := fun h => hs (by
      rw [← Fin.rev_injective h]
      exact (hw i hi).1)
    simp [this]
  · rw [uForm_single_right, Fin.rev_rev, map_ne_zero]
    exact hs

variable (hσ : ∀ c, σ (σ c) = c)
include hσ

theorem PerpUU.exists_isotropic (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {j : ℕ}
    {w w' : Fin m → F} (hw : PerpUU j w) (hw' : PerpUU j w') (hw0 : w ≠ 0) (hw'0 : w' ≠ 0)
    (hww : uForm σ w w = 0) (hww' : uForm σ w w' = 0) :
    ∃ z, PerpUU j z ∧ uForm σ z z = 0 ∧ uForm σ w z ≠ 0 ∧ uForm σ w' z ≠ 0 := by
  obtain ⟨a, ha, hwa⟩ := hw.exists_uForm_ne_zero hw0
  obtain ⟨b, hb, hw'b⟩ := hw'.exists_uForm_ne_zero hw'0
  obtain ⟨y, hy, hwy, hw'y⟩ : ∃ y, PerpUU j y ∧ uForm σ w y ≠ 0 ∧ uForm σ w' y ≠ 0 := by
    by_cases h1 : uForm σ w' a = 0
    · by_cases h2 : uForm σ w b = 0
      · refine ⟨a + b, ha.add hb, ?_, ?_⟩
        · rw [uForm_add_right, h2, add_zero]
          exact hwa
        · rw [uForm_add_right, h1, zero_add]
          exact hw'b
      · exact ⟨b, hb, h2, hw'b⟩
    · exact ⟨a, ha, hwa, h1⟩
  obtain ⟨s, hs⟩ := htr (-uForm σ y y) (by rw [map_neg, uForm_conj σ hσ])
  have hσd : σ (uForm σ w y) ≠ 0 := (map_ne_zero σ).2 hwy
  have hw'w : uForm σ w' w = 0 := uForm_eq_zero_comm hσ hww'
  have hyw : uForm σ y w = σ (uForm σ w y) := (uForm_conj σ hσ w y).symm
  refine ⟨y + (s / σ (uForm σ w y)) • w, hy.add (hw.smul _), ?_, ?_, ?_⟩
  · simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hww, hyw]
    have e1 : s / σ (uForm σ w y) * σ (uForm σ w y) = s := div_mul_cancel₀ s hσd
    have e2 : σ (s / σ (uForm σ w y)) * uForm σ w y = σ s := by
      rw [map_div₀, hσ, div_mul_cancel₀ _ hwy]
    linear_combination e1 + e2 + hs
  · rw [uForm_add_right, uForm_smul_right, hww, mul_zero, add_zero]
    exact hwy
  · rw [uForm_add_right, uForm_smul_right, hw'w, mul_zero, add_zero]
    exact hw'y

theorem exists_suMat_mulVec_eq_fix {x y : Fin m → F} (hxx : uForm σ x x = 0)
    (hyy : uForm σ y y = 0) (hxy : uForm σ x y ≠ 0) (hxy' : uForm σ x y + σ (uForm σ x y) = 0) :
    ∃ g : SU σ m, suMat σ m g *ᵥ x = y ∧ ∀ z, uForm σ (y - x) z = 0 → suMat σ m g *ᵥ z = z := by
  have hyx : uForm σ y x = σ (uForm σ x y) := (uForm_conj σ hσ x y).symm
  have hσd : σ (uForm σ x y) = -uForm σ x y := by linear_combination hxy'
  have hσd0 : σ (uForm σ x y) ≠ 0 := (map_ne_zero σ).2 hxy
  have hu : uForm σ (y - x) (y - x) = 0 := by
    rw [uForm_sub_left, uForm_sub_right, uForm_sub_right, hxx, hyy, hyx]
    linear_combination -hxy'
  have hc : (σ (uForm σ x y))⁻¹ + σ (σ (uForm σ x y))⁻¹ = 0 := by
    rw [map_inv₀, hσ, hσd, inv_neg, neg_add_cancel]
  obtain ⟨g, hg⟩ := exists_suMat_eq_uTrans hσ hu hc
  refine ⟨g, ?_, fun z hz => ?_⟩
  · rw [hg, uTrans_mulVec, uForm_sub_left, hxx, sub_zero, hyx, inv_mul_cancel₀ hσd0, one_smul,
      add_sub_cancel]
  · rw [hg, uTrans_mulVec, hz, mul_zero, zero_smul, add_zero]

theorem exists_suMat_mulVec_eq_smul_of_perp (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {ζ : F}
    (hζ : ζ ≠ 0) (hζ' : ζ + σ ζ = 0) {j : ℕ} {w w' : Fin m → F} (hw : PerpUU j w)
    (hw' : PerpUU j w') (hw0 : w ≠ 0) (hw'0 : w' ≠ 0) (hww : uForm σ w w = 0)
    (hw'w' : uForm σ w' w' = 0) :
    ∃ (g : SU σ m) (l : F), l ≠ 0 ∧ suMat σ m g *ᵥ w = l • w' ∧ ∀ i : Fin (m / 2), i.val < j →
      suMat σ m g *ᵥ Pi.single (lowIdx i) 1 = Pi.single (lowIdx i) 1 ∧
      suMat σ m g *ᵥ Pi.single (Fin.rev (lowIdx i)) 1 = Pi.single (Fin.rev (lowIdx i)) 1 := by
  have step : ∀ {x y : Fin m → F}, PerpUU j x → PerpUU j y → uForm σ x x = 0 →
      uForm σ y y = 0 → uForm σ x y ≠ 0 → ∃ g : SU σ m,
        suMat σ m g *ᵥ x = (ζ / uForm σ x y) • y ∧ ∀ i : Fin (m / 2), i.val < j →
          suMat σ m g *ᵥ Pi.single (lowIdx i) 1 = Pi.single (lowIdx i) 1 ∧
          suMat σ m g *ᵥ Pi.single (Fin.rev (lowIdx i)) 1 = Pi.single (Fin.rev (lowIdx i)) 1 := by
    intro x y hx hy hxx hyy hxy
    have hxy1 : uForm σ x ((ζ / uForm σ x y) • y) = ζ := by
      rw [uForm_smul_right, div_mul_cancel₀ _ hxy]
    have hyy1 : uForm σ ((ζ / uForm σ x y) • y) ((ζ / uForm σ x y) • y) = 0 := by
      rw [uForm_smul_left, uForm_smul_right, hyy, mul_zero, mul_zero]
    obtain ⟨g, hg, hfix⟩ := exists_suMat_mulVec_eq_fix hσ hxx hyy1 (by rw [hxy1]; exact hζ)
      (by rw [hxy1]; exact hζ')
    have hu : PerpUU j ((ζ / uForm σ x y) • y - x) := (hy.smul _).sub hx
    exact ⟨g, hg, fun i hi => ⟨hfix _ (hu.uForm_eq_zero hi).1, hfix _ (hu.uForm_eq_zero hi).2⟩⟩
  by_cases hww' : uForm σ w w' = 0
  · obtain ⟨z, hz, hzz, hwz, hw'z⟩ := hw.exists_isotropic hσ htr hw' hw0 hw'0 hww hww'
    obtain ⟨g₁, hg₁, hfix₁⟩ := step hw hz hww hzz hwz
    set z₁ := (ζ / uForm σ w z) • z with hz₁
    have hz₁U : PerpUU j z₁ := hz.smul _
    have hz₁z₁ : uForm σ z₁ z₁ = 0 := by
      rw [hz₁, uForm_smul_left, uForm_smul_right, hzz, mul_zero, mul_zero]
    have hz₁w' : uForm σ z₁ w' ≠ 0 := by
      rw [hz₁, uForm_smul_left, ← uForm_conj σ hσ w' z]
      exact mul_ne_zero ((map_ne_zero σ).2 (div_ne_zero hζ hwz)) ((map_ne_zero σ).2 hw'z)
    obtain ⟨g₂, hg₂, hfix₂⟩ := step hz₁U hw' hz₁z₁ hw'w' hz₁w'
    refine ⟨g₂ * g₁, ζ / uForm σ z₁ w', div_ne_zero hζ hz₁w', ?_, fun i hi => ⟨?_, ?_⟩⟩
    · rw [map_mul, ← mulVec_mulVec, hg₁, hg₂]
    · rw [map_mul, ← mulVec_mulVec, (hfix₁ i hi).1, (hfix₂ i hi).1]
    · rw [map_mul, ← mulVec_mulVec, (hfix₁ i hi).2, (hfix₂ i hi).2]
  · obtain ⟨g, hg, hfix⟩ := step hw hw' hww hw'w' hww'
    exact ⟨g, ζ / uForm σ w w', div_ne_zero hζ hww', hg, hfix⟩

omit hσ in
theorem isUTransGroup_rootGroup_pos (hσ : ∀ c, σ (σ c) = c) {i : Fin (m / 2)}
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = 2 • Pi.single i 1) :
    IsUTransGroup σ (Pi.single (lowIdx i) 1) (Unitary.rootGroup σ hσ m γ) :=
  isUTransGroup_rootGroup_long' hσ (lowIdx_ne_rev i i) (by rw [hγ, weight_lowIdx])

omit hσ in
theorem isUTransGroup_rootGroup_neg (hσ : ∀ c, σ (σ c) = c) {i : Fin (m / 2)}
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = -(2 • Pi.single i 1)) :
    IsUTransGroup σ (Pi.single (Fin.rev (lowIdx i)) 1) (Unitary.rootGroup σ hσ m γ) :=
  isUTransGroup_rootGroup_long' hσ (rev_ne_rev_rev (lowIdx_ne_rev i i))
    (by rw [hγ, weight_rev_lowIdx, smul_neg])

theorem suMat_suElt_short_mulVec {a b : Fin (m / 2)} (hab : a ≠ b) (c : F) :
    suMat σ m (suElt σ hσ (Sum.inl a) (Sum.inr b) c) *ᵥ Pi.single (lowIdx b) 1 =
        Pi.single (lowIdx b) 1 + c • Pi.single (lowIdx a) 1 ∧
      suMat σ m (suElt σ hσ (Sum.inl a) (Sum.inr b) c) *ᵥ Pi.single (lowIdx a) 1 =
        Pi.single (lowIdx a) 1 := by
  have hidx : idx (Sum.inl a : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inr b) := hab
  have h1 : lowIdx (n := m) b ≠ Fin.rev (lowIdx a) := lowIdx_ne_rev b a
  have h2 : lowIdx (n := m) a ≠ Fin.rev (lowIdx a) := lowIdx_ne_rev a a
  have h3 : lowIdx (n := m) a ≠ lowIdx b := fun h => hab (by
    have := congrArg Fin.val h
    simp only [val_lowIdx] at this
    exact Fin.ext this)
  change mat σ m _ *ᵥ _ = _ ∧ mat σ m _ *ᵥ _ = _
  rw [mat_suElt hσ hidx c]
  simp only [crd_inl, crd_inr, Sum.swap_inl, Sum.swap_inr]
  refine ⟨?_, ?_⟩
  · rw [mulVec_single_one]
    funext x
    simp only [Matrix.col_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.single_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      Ne.symm h1, and_false, ite_false, sub_zero, and_true]
    by_cases hxa : x = lowIdx a
    · subst hxa
      simp [h3]
    · simp [hxa, Ne.symm hxa]
  · rw [mulVec_single_one]
    funext x
    simp only [Matrix.col_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.single_apply, Pi.single_apply, Ne.symm h2, and_false, ite_false, sub_zero,
      Ne.symm h3, add_zero]

end ModelRank

open ModelRank

@[expose] def modelLineSU {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ} {H : Type*} [Group H]
    (Φ : SU σ m →* H) (j : ℕ) (hj : j + 1 < m / 2) : Set (Subgroup H) :=
  {X | ∃ (v : Fin m → F) (T : Subgroup (SU σ m)), v ≠ 0 ∧
    (∃ α β : F, v = α • Pi.single (lowIdx (⟨j, by omega⟩ : Fin (m / 2))) 1 +
      β • Pi.single (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2))) 1) ∧ IsUTransGroup σ v T ∧ X = T.map Φ}

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {ζ : F} (hζ : ζ ≠ 0)
  (hζ' : ζ + σ ζ = 0) {m : ℕ} {H : Type*} [Group H] {Φ : SU σ m →* H}
  (hker : Φ.ker ≤ Subgroup.center _) {TP TQ : Fin (m / 2) → Subgroup (SU σ m)}
  (hTP : ∀ i, IsUTransGroup σ (Pi.single (lowIdx i) 1) (TP i))
  (hTQ : ∀ i, IsUTransGroup σ (Pi.single (Fin.rev (lowIdx i)) 1) (TQ i))
include hσ hζ hζ' hker hTP hTQ

theorem perpUU_of_mem_perpSet {Δ : Set (Subgroup H)} {j : ℕ} {w : Fin m → F}
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ w T) (hw0 : w ≠ 0) (hww : uForm σ w w = 0)
    (h : T.map Φ ∈ perpSet Δ (fun i => (TP i).map Φ) (fun i => (TQ i).map Φ) j) :
    PerpUU j w := by
  have horth : ∀ {u : Fin m → F} {Y : Subgroup (SU σ m)}, IsUTransGroup σ u Y →
      uForm σ u u = 0 → Commuting (T.map Φ) (Y.map Φ) → uForm σ w u = 0 := by
    intro u Y hY huu hc
    rcases hT.uForm_eq_zero_of_center hσ hζ hζ' hY hw0 hww huu
      (commutator_mem_center hker hc) with h | ⟨l, rfl⟩
    · exact h
    · rw [uForm_smul_right, hww, mul_zero]
  intro i hi
  obtain ⟨h1, h2⟩ := h.2 i hi
  have e1 := horth (hTP i) (uForm_single_self (lowIdx_ne_rev i i)) h1
  have e2 := horth (hTQ i) (uForm_single_self (rev_ne_rev_rev (lowIdx_ne_rev i i))) h2
  rw [uForm_single_right, map_eq_zero] at e1
  rw [uForm_single_right, Fin.rev_rev, map_eq_zero] at e2
  exact ⟨e2, e1⟩

theorem hc_su (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {Δ : Set (Subgroup H)}
    {X₀ : Subgroup (SU σ m)} {e : Fin m → F} (he : e ≠ 0) (hee : uForm σ e e = 0)
    (hX₀ : IsUTransGroup σ e X₀)
    (hΔM : ∀ X, X ∈ deltaIn Δ Φ.range ↔ ∃ g, X = (conjSub X₀ g).map Φ) (j : ℕ)
    (W : Subgroup H)
    (hW : W ∈ deltaIn Δ Φ.range ∩ perpSet Δ (fun i => (TP i).map Φ) (fun i => (TQ i).map Φ) j)
    (W' : Subgroup H)
    (hW' : W' ∈ deltaIn Δ Φ.range ∩ perpSet Δ (fun i => (TP i).map Φ) (fun i => (TQ i).map Φ) j) :
    ∃ g ∈ Φ.range, (∀ i : Fin (m / 2), i.val < j → conjSub ((TP i).map Φ) g = (TP i).map Φ ∧
      conjSub ((TQ i).map Φ) g = (TQ i).map Φ) ∧ conjSub W g = W' := by
  obtain ⟨g, rfl⟩ := (hΔM W).1 hW.1
  obtain ⟨g', rfl⟩ := (hΔM W').1 hW'.1
  have hw0 := suMat_mulVec_ne_zero σ g he
  have hw'0 := suMat_mulVec_ne_zero σ g' he
  have hww := (uForm_mulVec σ g e e).trans hee
  have hw'w' := (uForm_mulVec σ g' e e).trans hee
  have hwU := perpUU_of_mem_perpSet hσ hζ hζ' hker hTP hTQ (hX₀.conjSub g) hw0 hww hW.2
  have hw'U := perpUU_of_mem_perpSet hσ hζ hζ' hker hTP hTQ (hX₀.conjSub g') hw'0 hw'w' hW'.2
  obtain ⟨k, l, hl, hk, hfix⟩ :=
    exists_suMat_mulVec_eq_smul_of_perp hσ htr hζ hζ' hwU hw'U hw0 hw'0 hww hw'w'
  refine ⟨Φ k, ⟨k, rfl⟩, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · rw [conjSub_map]
    have h := (hTP i).conjSub k
    rw [(hfix i hi).1] at h
    rw [h.eq (hTP i)]
  · rw [conjSub_map]
    have h := (hTQ i).conjSub k
    rw [(hfix i hi).2] at h
    rw [h.eq (hTQ i)]
  · rw [conjSub_map]
    have h := (hX₀.conjSub g).conjSub k
    rw [hk] at h
    rw [(IsUTransGroup.of_smul hσ hl h).eq (hX₀.conjSub g')]

section Line

variable {j : ℕ} (hj : j + 1 < m / 2)
include hj

omit hζ hζ' hker hTQ in
theorem isUTransGroup_conjSub_suElt (c : F) :
    IsUTransGroup σ (Pi.single (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2))) 1 +
        c • Pi.single (lowIdx (⟨j, by omega⟩ : Fin (m / 2))) 1)
      (conjSub (TP ⟨j + 1, hj⟩) (suElt σ hσ (Sum.inl ⟨j, by omega⟩) (Sum.inr ⟨j + 1, hj⟩) c)) := by
  have h := (hTP ⟨j + 1, hj⟩).conjSub (suElt σ hσ (Sum.inl ⟨j, by omega⟩) (Sum.inr ⟨j + 1, hj⟩) c)
  rwa [(suMat_suElt_short_mulVec hσ (Fin.ne_of_val_ne (by simp)) c).1] at h

omit hTQ in
theorem modelLineSU_ne (c : F) :
    conjSub ((TP ⟨j + 1, hj⟩).map Φ)
      (Φ (suElt σ hσ (Sum.inl ⟨j, by omega⟩) (Sum.inr ⟨j + 1, hj⟩) c)) ≠
        (TP ⟨j, by omega⟩).map Φ := by
  intro h
  rw [conjSub_map] at h
  have hb : lowIdx (n := m) (⟨j + 1, hj⟩ : Fin (m / 2)) ≠ Fin.rev (lowIdx ⟨j + 1, hj⟩) :=
    lowIdx_ne_rev _ _
  have hyy : uForm σ (Pi.single (Fin.rev (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2)))) 1 : Fin m → F)
      (Pi.single (Fin.rev (lowIdx ⟨j + 1, hj⟩)) 1) = 0 := uForm_single_self (rev_ne_rev_rev hb)
  obtain ⟨Y, hY⟩ := exists_isUTransGroup hσ hyy
  have hne : lowIdx (n := m) (⟨j + 1, hj⟩ : Fin (m / 2)) ≠ lowIdx ⟨j, by omega⟩ :=
    Fin.ne_of_val_ne (by simp [val_lowIdx])
  have hc := commuting_map Φ ((hTP ⟨j, by omega⟩).commuting hσ hY (by
    rw [uForm_single_right, Fin.rev_rev, map_eq_zero]
    simp [hne]))
  rw [← h] at hc
  have hT := isUTransGroup_conjSub_suElt hσ hTP hj c
  have hw0 : Pi.single (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2))) 1 +
      c • Pi.single (lowIdx (⟨j, by omega⟩ : Fin (m / 2))) 1 ≠ (0 : Fin m → F) := fun h0 => by
    have := congrFun h0 (lowIdx ⟨j + 1, hj⟩)
    simp [hne] at this
  have hww : uForm σ (Pi.single (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2))) 1 +
      c • Pi.single (lowIdx (⟨j, by omega⟩ : Fin (m / 2))) 1)
      (Pi.single (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2))) 1 +
        c • Pi.single (lowIdx (⟨j, by omega⟩ : Fin (m / 2))) 1) = 0 := by
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right,
      uForm_single_left]
    simp [lowIdx_ne_rev]
  rcases hT.uForm_eq_zero_of_center hσ hζ hζ' hY hw0 hww hyy (commutator_mem_center hker hc)
    with h1 | ⟨l, hl⟩
  · rw [uForm_single_right, Fin.rev_rev] at h1
    simp [hne] at h1
  · have := congrFun hl (Fin.rev (lowIdx ⟨j + 1, hj⟩))
    simp [Ne.symm (lowIdx_ne_rev _ _)] at this

omit hTQ in
theorem modelLineSU_injective :
    Function.Injective fun c : F => conjSub ((TP ⟨j + 1, hj⟩).map Φ)
      (Φ (suElt σ hσ (Sum.inl ⟨j, by omega⟩) (Sum.inr ⟨j + 1, hj⟩) c)) := by
  intro c c' h
  simp only [conjSub_map] at h
  by_contra hcc
  set a : Fin m := lowIdx (⟨j, by omega⟩ : Fin (m / 2)) with ha
  set b : Fin m := lowIdx (⟨j + 1, hj⟩ : Fin (m / 2)) with hb
  have hab : a ≠ b := Fin.ne_of_val_ne (by simp [ha, hb, val_lowIdx])
  have har : a ≠ Fin.rev a := lowIdx_ne_rev _ _
  have hbr : b ≠ Fin.rev b := lowIdx_ne_rev _ _
  have habr : a ≠ Fin.rev b := lowIdx_ne_rev _ _
  have hbar : b ≠ Fin.rev a := lowIdx_ne_rev _ _
  have hrr : Fin.rev a ≠ Fin.rev b := fun e => hab (Fin.rev_injective e)
  set y : Fin m → F := Pi.single (Fin.rev a) 1 - σ c' • Pi.single (Fin.rev b) 1 with hy
  have hyy : uForm σ y y = 0 := by
    rw [hy]
    simp only [uForm_sub_left, uForm_sub_right, uForm_smul_left, uForm_smul_right,
      uForm_single_left, Fin.rev_rev]
    simp [habr, hbr, hbar, har]
  have hform : ∀ d : F, uForm σ (Pi.single b 1 + d • Pi.single a 1) y = σ d - σ c' := fun d => by
    rw [hy]
    simp only [uForm_add_left, uForm_sub_right, uForm_smul_left, uForm_smul_right,
      uForm_single_left]
    simp [hrr, Ne.symm hrr]
  obtain ⟨Y, hY⟩ := exists_isUTransGroup hσ hyy
  have hc := commuting_map Φ ((isUTransGroup_conjSub_suElt hσ hTP hj c').commuting hσ hY
    (by rw [hform, sub_self]))
  rw [← h] at hc
  have hw0 : Pi.single b 1 + c • Pi.single a 1 ≠ (0 : Fin m → F) := fun h0 => by
    have := congrFun h0 b
    simp [Ne.symm hab] at this
  have hww : uForm σ (Pi.single b 1 + c • Pi.single a 1) (Pi.single b 1 + c • Pi.single a 1) =
      0 := by
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right,
      uForm_single_left]
    simp [Ne.symm habr, Ne.symm hbr, Ne.symm hbar, Ne.symm har]
  rcases (isUTransGroup_conjSub_suElt hσ hTP hj c).uForm_eq_zero_of_center hσ hζ hζ' hY hw0 hww
    hyy (commutator_mem_center hker hc) with h1 | ⟨l, hl⟩
  · rw [hform, sub_eq_zero] at h1
    exact hcc (σ.injective h1)
  · have h3 := congrFun hl (Fin.rev a)
    simp [← ha, ← hb, hy, hrr, Ne.symm hbar, Ne.symm har] at h3

omit hζ hζ' hker hTQ in
theorem modelLineSU_eq :
    modelLineSU Φ j hj = insert ((TP ⟨j, by omega⟩).map Φ) (Set.range fun c : F =>
      conjSub ((TP ⟨j + 1, hj⟩).map Φ)
        (Φ (suElt σ hσ (Sum.inl ⟨j, by omega⟩) (Sum.inr ⟨j + 1, hj⟩) c))) := by
  ext X
  constructor
  · rintro ⟨v, T, hv0, ⟨α, β, rfl⟩, hT, rfl⟩
    by_cases hβ : β = 0
    · subst hβ
      left
      have hα : α ≠ 0 := fun h => hv0 (by rw [h]; simp)
      rw [zero_smul, add_zero] at hT
      rw [(hT.of_smul hσ hα).eq (hTP _)]
    · right
      refine ⟨α / β, ?_⟩
      simp only
      rw [conjSub_map]
      have hv : α • Pi.single (lowIdx (⟨j, by omega⟩ : Fin (m / 2))) (1 : F) +
          β • Pi.single (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2))) 1 =
            β • (Pi.single (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2))) 1 +
              (α / β) • Pi.single (lowIdx (⟨j, by omega⟩ : Fin (m / 2))) 1) := by
        rw [smul_add, smul_smul, mul_div_cancel₀ _ hβ, add_comm]
      rw [hv] at hT
      rw [(isUTransGroup_conjSub_suElt hσ hTP hj (α / β)).eq (hT.of_smul hσ hβ)]
  · rintro (rfl | ⟨c, rfl⟩)
    · refine ⟨Pi.single (lowIdx ⟨j, by omega⟩) 1, TP ⟨j, by omega⟩,
        fun h => by simpa using congrFun h (lowIdx ⟨j, by omega⟩), ⟨1, 0, ?_⟩, hTP _, rfl⟩
      simp
    · have hne : lowIdx (n := m) (⟨j + 1, hj⟩ : Fin (m / 2)) ≠ lowIdx ⟨j, by omega⟩ :=
        Fin.ne_of_val_ne (by simp [val_lowIdx])
      have hv0 : Pi.single (lowIdx (⟨j + 1, hj⟩ : Fin (m / 2))) 1 +
          c • Pi.single (lowIdx (⟨j, by omega⟩ : Fin (m / 2))) 1 ≠ (0 : Fin m → F) := fun h0 => by
        simpa [Pi.single_apply, hne] using congrFun h0 (lowIdx ⟨j + 1, hj⟩)
      refine ⟨_, _, hv0, ⟨c, 1, by rw [one_smul, add_comm]⟩,
        isUTransGroup_conjSub_suElt hσ hTP hj c, ?_⟩
      simp only
      rw [conjSub_map]

omit hTQ in
theorem modelLineSU_ncard [Finite F] : (modelLineSU Φ j hj).ncard = Nat.card F + 1 := by
  rw [modelLineSU_eq hσ hTP hj, Set.ncard_insert_of_notMem, Set.ncard_range_of_injective
    (modelLineSU_injective hσ hζ hζ' hker hTP hj)]
  rintro ⟨c, hc⟩
  exact modelLineSU_ne hσ hζ hζ' hker hTP hj c hc

end Line

end CFSG.Timmesfeld.Transvection
