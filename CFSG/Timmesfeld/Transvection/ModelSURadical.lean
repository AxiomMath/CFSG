module

public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.Timmesfeld.ARS.BasicRankOne
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

section

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed


variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suMat_inv_mulVec_suMat_mulVec (g : SU σ m) (v : Fin m → F) :
    suMat σ m g⁻¹ *ᵥ (suMat σ m g *ᵥ v) = v := by
  rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]

theorem suMat_mulVec_suMat_inv_mulVec (g : SU σ m) (v : Fin m → F) :
    suMat σ m g *ᵥ (suMat σ m g⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]

theorem eq_of_suMat_mulVec_eq {g h : SU σ m}
    (H : ∀ v, suMat σ m g *ᵥ v = suMat σ m h *ᵥ v) : g = h :=
  suMat_injective σ (Matrix.ext_iff_mulVec.2 H)

@[expose] def uLine (σ : F ≃+* F) (a : Fin m → F) : Subgroup (SU σ m) where
  carrier := {g | ∃ μ : F, μ ≠ 0 ∧ suMat σ m g *ᵥ a = μ • a}
  mul_mem' := by
    rintro g h ⟨μ, hμ, hg⟩ ⟨ν, hν, hh⟩
    refine ⟨μ * ν, mul_ne_zero hμ hν, ?_⟩
    rw [map_mul, ← mulVec_mulVec, hh, mulVec_smul, hg, smul_smul, mul_comm]
  one_mem' := ⟨1, one_ne_zero, by rw [map_one, one_mulVec, one_smul]⟩
  inv_mem' := by
    rintro g ⟨μ, hμ, hg⟩
    refine ⟨μ⁻¹, inv_ne_zero hμ, ?_⟩
    have h1 : μ • (suMat σ m g⁻¹ *ᵥ a) = a := by
      rw [← mulVec_smul, ← hg, suMat_inv_mulVec_suMat_mulVec]
    exact (eq_inv_smul_iff₀ hμ).2 h1

@[expose] def uRad (σ : F ≃+* F) (a : Fin m → F) : Subgroup (SU σ m) where
  carrier := {g | suMat σ m g *ᵥ a = a ∧
    ∀ u, uForm σ a u = 0 → ∃ c : F, suMat σ m g *ᵥ u = u + c • a}
  mul_mem' := by
    rintro g h ⟨hga, hg⟩ ⟨hha, hh⟩
    refine ⟨by rw [map_mul, ← mulVec_mulVec, hha, hga], fun u hu => ?_⟩
    obtain ⟨c, hc⟩ := hh u hu
    obtain ⟨d, hd⟩ := hg u hu
    refine ⟨c + d, ?_⟩
    rw [map_mul, ← mulVec_mulVec, hc, mulVec_add, hd, mulVec_smul, hga, add_smul]
    abel
  one_mem' := ⟨by rw [map_one, one_mulVec],
    fun u _ => ⟨0, by rw [map_one, one_mulVec, zero_smul, add_zero]⟩⟩
  inv_mem' := by
    rintro g ⟨hga, hg⟩
    refine ⟨?_, fun u hu => ?_⟩
    · have := suMat_inv_mulVec_suMat_mulVec g a
      rwa [hga] at this
    · have hu' : uForm σ a (suMat σ m g⁻¹ *ᵥ u) = 0 := by
        have h := uForm_mulVec σ g a (suMat σ m g⁻¹ *ᵥ u)
        rw [hga, suMat_mulVec_suMat_inv_mulVec] at h
        rw [← h]
        exact hu
      obtain ⟨c, hc⟩ := hg _ hu'
      refine ⟨-c, ?_⟩
      rw [suMat_mulVec_suMat_inv_mulVec] at hc
      rw [neg_smul, ← sub_eq_add_neg]
      exact eq_sub_of_add_eq hc.symm

end

section

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.LieType.BorelTits


@[expose] def SUGenStmt (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ) (m : ℕ) : Prop :=
  ∀ {L : Subgroup (SU (unitaryInvolution F 2 f) m)},
    (∀ (v : Fin m → F) (X : Subgroup (SU (unitaryInvolution F 2 f) m)),
      uForm (unitaryInvolution F 2 f) v v = 0 → IsUTransGroup (unitaryInvolution F 2 f) v X →
        X ≤ L) → L = ⊤

variable {F : Type} [Field F] (σ : F ≃+* F) (m : ℕ)

@[expose] def SUPartnerStmt : Prop :=
  ∀ {a : Fin m → F}, a ≠ 0 → uForm σ a a = 0 → ∃ d, uForm σ d d = 0 ∧ uForm σ a d = 1

@[expose] def SUBothStmt : Prop :=
  ∀ {a u : Fin m → F}, a ≠ 0 → u ≠ 0 → uForm σ a a = 0 → uForm σ u u = 0 →
    ∃ y, uForm σ y y = 0 ∧ uForm σ a y ≠ 0 ∧ uForm σ u y ≠ 0

@[expose] def SUPerpStmt : Prop :=
  ∀ {a v : Fin m → F}, a ≠ 0 → uForm σ a a = 0 → uForm σ v v = 0 → uForm σ a v = 0 →
    (∀ c : F, v ≠ c • a) → ∃ z, uForm σ z z = 0 ∧ uForm σ a z ≠ 0 ∧ uForm σ v z = 0

end

section

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed


variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem normalizer_eq_uLine [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a : Fin m → F} (ha : a ≠ 0)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) :
    Subgroup.normalizer (T : Set (SU σ m)) = uLine σ a := by
  ext g
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hg
    have hconj : conjSub T g = T := by
      ext x
      rw [mem_conjSub]
      have := hg (g⁻¹ * x * g)
      rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
      exact this
    have h1 := hT.conjSub g
    rw [hconj] at h1
    have h1' : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
    obtain ⟨μ, hμ⟩ := h1.exists_eq_smul one_ne_zero h1' hT
    refine ⟨μ, ?_, hμ⟩
    rintro rfl
    rw [zero_smul] at hμ
    exact suMat_mulVec_ne_zero σ g ha hμ
  · rintro ⟨μ, hμ, hga⟩
    have h1 : IsUTransGroup σ a (conjSub T g) :=
      IsUTransGroup.of_smul hσ hμ (by rw [← hga]; exact hT.conjSub g)
    have hconj : conjSub T g = T := h1.eq hT
    intro h
    have : g * h * g⁻¹ ∈ conjSub T g ↔ h ∈ T := by
      rw [mem_conjSub, show g⁻¹ * (g * h * g⁻¹) * g = h by group]
    rw [hconj] at this
    exact this.symm

theorem uRad_le_uLine (a : Fin m → F) : uRad σ a ≤ uLine σ a := by
  rintro g ⟨hga, -⟩
  exact ⟨1, one_ne_zero, by rw [hga, one_smul]⟩

theorem conj_mem_uRad {a : Fin m → F} {h : SU σ m} (hh : h ∈ uLine σ a) {x : SU σ m}
    (hx : x ∈ uRad σ a) : h * x * h⁻¹ ∈ uRad σ a := by
  obtain ⟨μ, hμ, hha⟩ := hh
  obtain ⟨hxa, hx⟩ := hx
  have hinv : suMat σ m h⁻¹ *ᵥ a = μ⁻¹ • a := by
    have h1 : μ • (suMat σ m h⁻¹ *ᵥ a) = a := by
      rw [← mulVec_smul, ← hha, suMat_inv_mulVec_suMat_mulVec]
    exact (eq_inv_smul_iff₀ hμ).2 h1
  refine ⟨?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hinv, mulVec_smul, hxa, mulVec_smul,
      hha, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  · have hu' : uForm σ a (suMat σ m h⁻¹ *ᵥ u) = 0 := by
      have h1 := uForm_mulVec σ h a (suMat σ m h⁻¹ *ᵥ u)
      rw [hha, suMat_mulVec_suMat_inv_mulVec, uForm_smul_left] at h1
      rw [← h1, hu, mul_zero]
    obtain ⟨c, hc⟩ := hx _ hu'
    refine ⟨c * μ, ?_⟩
    rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hc, mulVec_add, mulVec_smul, hha,
      suMat_mulVec_suMat_inv_mulVec, smul_smul]

theorem le_uRad_of_isUTransGroup {a : Fin m → F} (haa : uForm σ a a = 0)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) : T ≤ uRad σ a := by
  intro x hx
  obtain ⟨c, -, hc⟩ := (hT.1 x).1 hx
  refine ⟨?_, fun u hu => ⟨0, ?_⟩⟩
  · rw [hc, uTrans_mulVec, haa, mul_zero, zero_smul, add_zero]
  · rw [hc, uTrans_mulVec, hu, mul_zero, zero_smul, add_zero]

theorem isPGroup_uRad [CharP F 2] (a : Fin m → F) : IsPGroup 2 (uRad σ a) := by
  rintro ⟨x, hxa, hx⟩
  refine ⟨2, ?_⟩
  have key : ∀ v, ∃ c : F, suMat σ m x *ᵥ (suMat σ m x *ᵥ v) = v + c • a := by
    intro v
    have h0 : uForm σ a (suMat σ m x *ᵥ v + v) = 0 := by
      rw [uForm_add_right]
      have := uForm_mulVec σ x a v
      rw [hxa] at this
      rw [this, CharTwo.add_self_eq_zero]
    obtain ⟨c, hc⟩ := hx _ h0
    refine ⟨c, ?_⟩
    rw [mulVec_add] at hc
    have h2 : suMat σ m x *ᵥ (suMat σ m x *ᵥ v) + suMat σ m x *ᵥ v =
        (v + c • a) + suMat σ m x *ᵥ v := by
      rw [hc]; abel
    exact add_right_cancel h2
  have h4 : x ^ 4 = 1 := by
    apply eq_of_suMat_mulVec_eq
    intro v
    obtain ⟨c, hc⟩ := key v
    have h5 : suMat σ m (x ^ 4) *ᵥ v = suMat σ m x *ᵥ (suMat σ m x *ᵥ
        (suMat σ m x *ᵥ (suMat σ m x *ᵥ v))) := by
      rw [map_pow, show (4 : ℕ) = 1 + 1 + 1 + 1 by norm_num, pow_succ, pow_succ, pow_succ, pow_one,
        ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [h5, map_one, one_mulVec, hc, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hc]
    simp only [hxa]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  exact Subtype.ext h4

theorem uRad_le_pCoreOf [CharP F 2] (hσ : ∀ c, σ (σ c) = c) {a : Fin m → F} (ha : a ≠ 0)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) :
    uRad σ a ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (T : Set (SU σ m))) := by
  rw [normalizer_eq_uLine hσ ha hT]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (uRad_le_uLine a) ?_
    (isPGroup_uRad a)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_uRad hg hx
  · intro hx
    have := conj_mem_uRad (inv_mem hg) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

end

end ModelRank

end CFSG.Timmesfeld.Transvection
