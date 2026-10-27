module

public import CFSG.Timmesfeld.Transvection.ModelSUPerp
public import CFSG.Timmesfeld.Transvection.ModelRankSU
public import CFSG.Timmesfeld.Transvection.ModelSURadical

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

@[expose] def UTransLe (L : Subgroup (SU σ m)) (v : Fin m → F) : Prop :=
  ∀ (c : F) (x : SU σ m), c + σ c = 0 → suMat σ m x = uTrans σ v c → x ∈ L

theorem uTransLe_iff {L : Subgroup (SU σ m)} {v : Fin m → F} {X : Subgroup (SU σ m)}
    (hX : IsUTransGroup σ v X) : UTransLe L v ↔ X ≤ L := by
  constructor
  · intro h x hx
    obtain ⟨c, hc, hxc⟩ := (hX.1 x).1 hx
    exact h c x hc hxc
  · intro h c x hc hxc
    exact h ((hX.1 x).2 ⟨c, hc, hxc⟩)

theorem uTransLe_conj {L : Subgroup (SU σ m)} {v : Fin m → F} (h : UTransLe L v)
    {g : SU σ m} (hg : g ∈ L) : UTransLe L (suMat σ m g *ᵥ v) := by
  intro c x hc hx
  have hx' : suMat σ m (g⁻¹ * x * g⁻¹⁻¹) = uTrans σ v c := by
    rw [suMat_conj_of_eq σ hx g⁻¹, suMat_inv_mulVec_suMat_mulVec]
  have hmem := h c _ hc hx'
  have hxe : x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
  rw [hxe]
  exact L.mul_mem (L.mul_mem hg hmem) (L.inv_mem hg)

theorem uTransLe_smul (hσ : ∀ c, σ (σ c) = c) {L : Subgroup (SU σ m)} {v : Fin m → F}
    (h : UTransLe L v) (l : F) : UTransLe L (l • v) := by
  intro c x hc hx
  rw [uTrans_smul] at hx
  exact h _ x (traceZero_mul_norm hσ l hc) hx

theorem uTransLe_of_smul (hσ : ∀ c, σ (σ c) = c) {L : Subgroup (SU σ m)} {v : Fin m → F}
    {l : F} (hl : l ≠ 0) (h : UTransLe L (l • v)) : UTransLe L v := by
  have := uTransLe_smul hσ h l⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hl, one_smul] at this

theorem uTransLe_uTrans (hσ : ∀ c, σ (σ c) = c) {L : Subgroup (SU σ m)} {u v : Fin m → F}
    (hu : UTransLe L u) (hv : UTransLe L v) (huu : uForm σ u u = 0) {c : F}
    (hc : c + σ c = 0) : UTransLe L (v + (c * uForm σ u v) • u) := by
  obtain ⟨g, hg⟩ := exists_suMat_eq_uTrans hσ huu hc
  have := uTransLe_conj hv (hu c g hc hg)
  rwa [hg, uTrans_mulVec] at this

section CharTwo

variable [CharP F 2]

theorem mulVec_eichler_prod (hσ : ∀ c, σ (σ c) = c) {a w : Fin m → F}
    (haa : uForm σ a a = 0) (hww : uForm σ w w = 0) (haw : uForm σ a w = 0) (c ν : F)
    (u : Fin m → F) :
    uTrans σ (a + ν • w) c *ᵥ (uTrans σ a c *ᵥ (uTrans σ w (c * (ν * σ ν)) *ᵥ u)) =
      u + (c * ν * uForm σ a u) • w + (c * σ ν * uForm σ w u) • a := by
  have hwa : uForm σ w a = 0 := uForm_eq_zero_comm hσ haw
  rw [uTrans_mulVec, uTrans_mulVec, uTrans_mulVec]
  simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, haa, hww, haw,
    hwa, mul_zero, add_zero]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (c * uForm σ a u * a i + c * (ν * σ ν) * uForm σ w u * w i) *
    (CharTwo.two_eq_zero : (2 : F) = 0)

theorem exists_mem_eichler_of_uTransLe (hσ : ∀ c, σ (σ c) = c) {L : Subgroup (SU σ m)}
    {a w : Fin m → F} (haa : uForm σ a a = 0) (hww : uForm σ w w = 0) (haw : uForm σ a w = 0)
    {ν : F} (ha : UTransLe L a) (hw : UTransLe L w) (haw' : UTransLe L (a + ν • w)) {c : F}
    (hc : c + σ c = 0) :
    ∃ z ∈ L, ∀ u, suMat σ m z *ᵥ u =
      u + (c * ν * uForm σ a u) • w + (c * σ ν * uForm σ w u) • a := by
  have hwa : uForm σ w a = 0 := uForm_eq_zero_comm hσ haw
  have hsum : uForm σ (a + ν • w) (a + ν • w) = 0 := by
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, haa, hww,
      haw, hwa, mul_zero, add_zero]
  have hcN : c * (ν * σ ν) + σ (c * (ν * σ ν)) = 0 := by
    rw [mul_comm c]
    exact traceZero_mul_norm hσ ν hc
  obtain ⟨x₁, hx₁⟩ := exists_suMat_eq_uTrans hσ hsum hc
  obtain ⟨x₂, hx₂⟩ := exists_suMat_eq_uTrans hσ haa hc
  obtain ⟨x₃, hx₃⟩ := exists_suMat_eq_uTrans hσ hww hcN
  refine ⟨x₁ * x₂ * x₃, L.mul_mem (L.mul_mem (haw' c x₁ hc hx₁) (ha c x₂ hc hx₂))
    (hw _ x₃ hcN hx₃), fun u => ?_⟩
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hx₁, hx₂, hx₃]
  exact mulVec_eichler_prod hσ haa hww haw c ν u

theorem eichler_mem_uRad_radVec (hσ : ∀ c, σ (σ c) = c) {a d w : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    (hw : w ∈ perpPair σ a d) {c ν : F} {z : SU σ m}
    (hz : ∀ u, suMat σ m z *ᵥ u =
      u + (c * ν * uForm σ a u) • w + (c * σ ν * uForm σ w u) • a) :
    z ∈ uRad σ a ∧ radVec σ a d z = (c * ν) • w := by
  have hwa : uForm σ w a = 0 := uForm_eq_zero_comm hσ hw.1
  have hwd : uForm σ w d = 0 := uForm_eq_zero_comm hσ hw.2
  refine ⟨⟨?_, fun u hu => ⟨c * σ ν * uForm σ w u, ?_⟩⟩, ?_⟩
  · rw [hz, haa, hwa, mul_zero, mul_zero, zero_smul, zero_smul, add_zero, add_zero]
  · rw [hz, hu, mul_zero, zero_smul, add_zero]
  · rw [radVec, hz, had, hwd, mul_one, mul_zero, zero_smul, add_zero, projPair_add,
      projPair_d hdd had, zero_add, projPair_smul, projPair_of_mem hw]

end CharTwo

end CFSG.Timmesfeld.Transvection.ModelRank
