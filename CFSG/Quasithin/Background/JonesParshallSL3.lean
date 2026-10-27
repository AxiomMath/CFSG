module

public import CFSG.Quasithin.Background.JonesParshallSL2

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix

variable {F : Type} [Field F]

abbrev SL3 (F : Type) [Field F] : Type := SpecialLinearGroup (Fin 3) F

@[expose] def mu3 : SL3 F →* AddMonoid.End (Fin 3 → F) := DistribMulAction.toAddMonoidEnd _ _

theorem mu3_apply (g : SL3 F) (v : Fin 3 → F) : mu3 g v = g • v := rfl

theorem smul3_def (g : SL3 F) (v : Fin 3 → F) : g • v = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v :=
  rfl

theorem mulVec3 (M : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) (i : Fin 3) :
    (M *ᵥ v) i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 := by
  simp [mulVec, dotProduct, Fin.sum_univ_three]

@[expose] def e0 : Fin 3 → F := ![1, 0, 0]

theorem e0_zero : (e0 : Fin 3 → F) 0 = 1 := rfl

theorem e0_one : (e0 : Fin 3 → F) 1 = 0 := rfl

theorem e0_two : (e0 : Fin 3 → F) 2 = 0 := rfl

omit [Field F] in
theorem vec3_ext {v w : Fin 3 → F} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2) :
    v = w := by
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem smul_e0_eq {g : SL3 F} (h1 : (g • (e0 : Fin 3 → F)) 1 = 0)
    (h2 : (g • (e0 : Fin 3 → F)) 2 = 0) :
    g • (e0 : Fin 3 → F) = (g • (e0 : Fin 3 → F)) 0 • e0 := by
  refine vec3_ext ?_ ?_ ?_
  · rw [Pi.smul_apply]
    simp [e0]
  · rw [h1, Pi.smul_apply]
    simp [e0]
  · rw [h2, Pi.smul_apply]
    simp [e0]

@[expose] def qMat3 (r₁ r₂ : F) : SL3 F :=
  ⟨!![1, r₁, r₂; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def dMat3 (c₀ c₁ c₂ : F) (h : c₀ * c₁ * c₂ = 1) : SL3 F :=
  ⟨!![c₀, 0, 0; 0, c₁, 0; 0, 0, c₂], by simp [det_fin_three, h]⟩

theorem qMat3_coe (r₁ r₂ : F) :
    ((qMat3 r₁ r₂ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, r₁, r₂; 0, 1, 0; 0, 0, 1] := rfl

theorem dMat3_coe (c₀ c₁ c₂ : F) (h : c₀ * c₁ * c₂ = 1) :
    ((dMat3 c₀ c₁ c₂ h : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![c₀, 0, 0; 0, c₁, 0; 0, 0, c₂] := rfl

theorem qMat3_smul (r₁ r₂ : F) (v : Fin 3 → F) :
    qMat3 r₁ r₂ • v = ![v 0 + r₁ * v 1 + r₂ * v 2, v 1, v 2] := by
  funext i
  rw [smul3_def, mulVec3, qMat3_coe]
  fin_cases i <;> simp

theorem dMat3_smul (c₀ c₁ c₂ : F) (h : c₀ * c₁ * c₂ = 1) (v : Fin 3 → F) :
    dMat3 c₀ c₁ c₂ h • v = ![c₀ * v 0, c₁ * v 1, c₂ * v 2] := by
  funext i
  rw [smul3_def, mulVec3, dMat3_coe]
  fin_cases i <;> simp

theorem qMat3_mul (r₁ r₂ s₁ s₂ : F) : qMat3 r₁ r₂ * qMat3 s₁ s₂ = qMat3 (r₁ + s₁) (r₂ + s₂) := by
  apply Subtype.ext
  change !![(1 : F), r₁, r₂; 0, 1, 0; 0, 0, 1] * !![1, s₁, s₂; 0, 1, 0; 0, 0, 1] =
    !![1, r₁ + s₁, r₂ + s₂; 0, 1, 0; 0, 0, 1]
  rw [mul_fin_three]
  simp [add_comm]

theorem qMat3_zero : qMat3 (0 : F) 0 = 1 := by
  apply Subtype.ext
  change !![(1 : F), 0, 0; 0, 1, 0; 0, 0, 1] = 1
  exact one_fin_three.symm

theorem dMat3_inv (c₀ c₁ c₂ : F) (h : c₀ * c₁ * c₂ = 1) (h' : c₀⁻¹ * c₁⁻¹ * c₂⁻¹ = 1) :
    (dMat3 c₀ c₁ c₂ h)⁻¹ = dMat3 c₀⁻¹ c₁⁻¹ c₂⁻¹ h' := by
  have h0 : c₀ ≠ 0 := fun h0 => by simp [h0] at h
  have h1 : c₁ ≠ 0 := fun h1 => by simp [h1] at h
  have h2 : c₂ ≠ 0 := fun h2 => by simp [h2] at h
  refine inv_eq_of_mul_eq_one_right ?_
  apply Subtype.ext
  change !![c₀, 0, 0; 0, c₁, 0; 0, 0, c₂] * !![c₀⁻¹, 0, 0; 0, c₁⁻¹, 0; 0, 0, c₂⁻¹] = 1
  rw [mul_fin_three, one_fin_three]
  simp [h0, h1, h2]

theorem dMat3_conj (c₀ c₁ c₂ : F) (h : c₀ * c₁ * c₂ = 1) (r₁ r₂ : F) :
    dMat3 c₀ c₁ c₂ h * qMat3 r₁ r₂ * (dMat3 c₀ c₁ c₂ h)⁻¹ =
      qMat3 (c₀ * r₁ * c₁⁻¹) (c₀ * r₂ * c₂⁻¹) := by
  have h0 : c₀ ≠ 0 := fun h0 => by simp [h0] at h
  have h1 : c₁ ≠ 0 := fun h1 => by simp [h1] at h
  have h2 : c₂ ≠ 0 := fun h2 => by simp [h2] at h
  have h' : c₀⁻¹ * c₁⁻¹ * c₂⁻¹ = 1 := by
    rw [← mul_inv, ← mul_inv, h, inv_one]
  rw [dMat3_inv c₀ c₁ c₂ h h']
  apply Subtype.ext
  change !![c₀, 0, 0; 0, c₁, 0; 0, 0, c₂] * !![(1 : F), r₁, r₂; 0, 1, 0; 0, 0, 1] *
    !![c₀⁻¹, 0, 0; 0, c₁⁻¹, 0; 0, 0, c₂⁻¹] = !![1, c₀ * r₁ * c₁⁻¹, c₀ * r₂ * c₂⁻¹; 0, 1, 0; 0, 0, 1]
  rw [mul_fin_three, mul_fin_three]
  simp [h0, h1, h2]

@[expose] def lineStab : Subgroup (SL3 F) where
  carrier := {g | (g • (e0 : Fin 3 → F)) 1 = 0 ∧ (g • (e0 : Fin 3 → F)) 2 = 0}
  mul_mem' {g h} hg hh := by
    have hh' : h • (e0 : Fin 3 → F) = (h • (e0 : Fin 3 → F)) 0 • e0 := smul_e0_eq hh.1 hh.2
    change ((g * h) • (e0 : Fin 3 → F)) 1 = 0 ∧ ((g * h) • (e0 : Fin 3 → F)) 2 = 0
    rw [mul_smul, hh', smul_comm, Pi.smul_apply, Pi.smul_apply, hg.1, hg.2, smul_zero]
    exact ⟨rfl, rfl⟩
  one_mem' := by
    change ((1 : SL3 F) • (e0 : Fin 3 → F)) 1 = 0 ∧ ((1 : SL3 F) • (e0 : Fin 3 → F)) 2 = 0
    simp [e0]
  inv_mem' {g} hg := by
    have hg' : g • (e0 : Fin 3 → F) = (g • (e0 : Fin 3 → F)) 0 • e0 := smul_e0_eq hg.1 hg.2
    set c := (g • (e0 : Fin 3 → F)) 0
    have hc : c ≠ 0 := by
      intro hc
      have h0 : g • (e0 : Fin 3 → F) = 0 := by rw [hg', hc, zero_smul]
      have := congrFun (smul_eq_zero_iff_eq g |>.mp h0) 0
      simp [e0] at this
    have hinv : g⁻¹ • (e0 : Fin 3 → F) = c⁻¹ • e0 := by
      have h1 : (e0 : Fin 3 → F) = c • (g⁻¹ • e0) := by
        rw [← smul_comm g⁻¹ c, ← hg', inv_smul_smul]
      calc g⁻¹ • (e0 : Fin 3 → F) = c⁻¹ • (c • (g⁻¹ • e0)) := by
            rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c⁻¹ • e0 := by rw [← h1]
    change (g⁻¹ • (e0 : Fin 3 → F)) 1 = 0 ∧ (g⁻¹ • (e0 : Fin 3 → F)) 2 = 0
    rw [hinv]
    simp [e0]

theorem smul_e0_of_mem {p : SL3 F} (hp : p ∈ lineStab) :
    p • (e0 : Fin 3 → F) = (p • (e0 : Fin 3 → F)) 0 • e0 :=
  smul_e0_eq hp.1 hp.2

theorem eq_qMat3 {g : SL3 F} (h0 : g • (e0 : Fin 3 → F) = e0)
    (h1 : ∀ v : Fin 3 → F, (g • v) 1 = v 1 ∧ (g • v) 2 = v 2) :
    g = qMat3 ((g : Matrix (Fin 3) (Fin 3) F) 0 1) ((g : Matrix (Fin 3) (Fin 3) F) 0 2) := by
  have hc : ∀ i, (g : Matrix (Fin 3) (Fin 3) F) i 0 = e0 i := fun i => by
    have := congrFun h0 i
    rw [smul3_def, mulVec3] at this
    simpa [e0] using this
  have hr : ∀ j : Fin 3, (g : Matrix (Fin 3) (Fin 3) F) 1 j = (Pi.single 1 1 : Fin 3 → F) j ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 j = (Pi.single 2 1 : Fin 3 → F) j := fun j => by
    have h := h1 (Pi.single j 1)
    simp only [smul3_def, mulVec3] at h
    fin_cases j <;> simpa using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMat3_coe, hc 0, hc 1, hc 2, (hr 1).1, (hr 2).1, (hr 1).2, (hr 2).2, e0]

theorem inv_smul_e0_of_mem {p : SL3 F} (hp : p ∈ lineStab) :
    p⁻¹ • (e0 : Fin 3 → F) = ((p • (e0 : Fin 3 → F)) 0)⁻¹ • e0 := by
  have hp' := smul_e0_of_mem hp
  set c := (p • (e0 : Fin 3 → F)) 0
  have hc : c ≠ 0 := by
    intro hc
    have h0 : p • (e0 : Fin 3 → F) = 0 := by rw [hp', hc, zero_smul]
    have := congrFun (smul_eq_zero_iff_eq p |>.mp h0) 0
    simp [e0] at this
  have h1 : (e0 : Fin 3 → F) = c • (p⁻¹ • e0) := by
    rw [← smul_comm p⁻¹ c, ← hp', inv_smul_smul]
  calc p⁻¹ • (e0 : Fin 3 → F) = c⁻¹ • (c • (p⁻¹ • e0)) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • e0 := by rw [← h1]

theorem e0_coord_ne_zero {p : SL3 F} (hp : p ∈ lineStab) : (p • (e0 : Fin 3 → F)) 0 ≠ 0 := by
  intro hc
  have h0 : p • (e0 : Fin 3 → F) = 0 := by rw [smul_e0_of_mem hp, hc, zero_smul]
  have := congrFun (smul_eq_zero_iff_eq p |>.mp h0) 0
  simp [e0] at this

theorem qMat3_smul_e0 (r₁ r₂ : F) : qMat3 r₁ r₂ • (e0 : Fin 3 → F) = e0 := by
  rw [qMat3_smul]
  refine vec3_ext ?_ ?_ ?_ <;> simp [e0]

theorem qMat3_smul' (r₁ r₂ : F) (u : Fin 3 → F) :
    qMat3 r₁ r₂ • u = u + (r₁ * u 1 + r₂ * u 2) • e0 := by
  rw [qMat3_smul]
  refine vec3_ext ?_ ?_ ?_ <;> simp [e0, add_assoc]

theorem conj_qMat3 {p : SL3 F} (hp : p ∈ lineStab) (r₁ r₂ : F) :
    ∃ s₁ s₂ : F, p * qMat3 r₁ r₂ * p⁻¹ = qMat3 s₁ s₂ := by
  set c := (p • (e0 : Fin 3 → F)) 0
  have hc : c ≠ 0 := e0_coord_ne_zero hp
  refine ⟨_, _, eq_qMat3 ?_ fun v => ?_⟩
  · calc (p * qMat3 r₁ r₂ * p⁻¹) • (e0 : Fin 3 → F)
        = p • (qMat3 r₁ r₂ • (c⁻¹ • e0)) := by rw [mul_smul, mul_smul, inv_smul_e0_of_mem hp]
      _ = p • (c⁻¹ • e0) := by rw [smul_comm (qMat3 r₁ r₂) c⁻¹ e0, qMat3_smul_e0]
      _ = c⁻¹ • (c • e0) := by rw [smul_comm p c⁻¹ e0, smul_e0_of_mem hp]
      _ = e0 := by rw [smul_smul c⁻¹ c e0, inv_mul_cancel₀ hc, one_smul]
  · set u := p⁻¹ • v
    set t := r₁ * u 1 + r₂ * u 2
    have h : (p * qMat3 r₁ r₂ * p⁻¹) • v = v + (t * c) • (e0 : Fin 3 → F) := by
      calc (p * qMat3 r₁ r₂ * p⁻¹) • v = p • (u + t • e0) := by
            rw [mul_smul, mul_smul, qMat3_smul']
        _ = v + t • (c • e0) := by
            rw [smul_add, smul_inv_smul, smul_comm p t e0, smul_e0_of_mem hp]
        _ = v + (t * c) • e0 := by rw [smul_smul t c e0]
    rw [h]
    simp [e0]

@[expose] def zMat3 (l : F) (hl : l ≠ 0) : SL3 F :=
  dMat3 (l ^ 2)⁻¹ l l (by field_simp)

theorem zMat3_mem (l : F) (hl : l ≠ 0) : zMat3 l hl ∈ lineStab := by
  constructor <;> rw [zMat3, dMat3_smul] <;> simp [e0]

theorem zMat3_smul (l : F) (hl : l ≠ 0) (u : Fin 3 → F) :
    zMat3 l hl • u = l • u + (((l ^ 2)⁻¹ - l) * u 0) • (e0 : Fin 3 → F) := by
  rw [zMat3, dMat3_smul]
  refine vec3_ext ?_ ?_ ?_ <;> simp [e0]
  ring

theorem zMat3_inv_smul (l : F) (hl : l ≠ 0) (u : Fin 3 → F) :
    (zMat3 l hl)⁻¹ • u = l⁻¹ • u + ((l ^ 2 - l⁻¹) * u 0) • (e0 : Fin 3 → F) := by
  rw [zMat3, dMat3_inv _ _ _ _ (by field_simp), dMat3_smul]
  refine vec3_ext ?_ ?_ ?_ <;> simp [e0]
  ring

theorem zMat3_smul_e0 (l : F) (hl : l ≠ 0) :
    zMat3 l hl • (e0 : Fin 3 → F) = (l ^ 2)⁻¹ • e0 := by
  rw [zMat3, dMat3_smul]
  refine vec3_ext ?_ ?_ ?_ <;> simp [e0]

theorem zMat3_inv_smul_e0 (l : F) (hl : l ≠ 0) :
    (zMat3 l hl)⁻¹ • (e0 : Fin 3 → F) = (l ^ 2) • e0 := by
  rw [zMat3_inv_smul]
  refine vec3_ext ?_ ?_ ?_ <;> simp [e0]

theorem comm_zMat3 (l : F) (hl : l ≠ 0) {p : SL3 F} (hp : p ∈ lineStab) :
    ∃ s₁ s₂ : F, zMat3 l hl * p * (zMat3 l hl)⁻¹ * p⁻¹ = qMat3 s₁ s₂ := by
  set z := zMat3 l hl
  set c := (p • (e0 : Fin 3 → F)) 0
  have hc : c ≠ 0 := e0_coord_ne_zero hp
  refine ⟨_, _, eq_qMat3 ?_ fun v => ?_⟩
  · calc (z * p * z⁻¹ * p⁻¹) • (e0 : Fin 3 → F)
        = z • (p • (z⁻¹ • (c⁻¹ • e0))) := by
          rw [mul_smul, mul_smul, mul_smul, inv_smul_e0_of_mem hp]
      _ = z • (p • ((c⁻¹ * l ^ 2) • e0)) := by
          rw [smul_comm z⁻¹ c⁻¹ e0, zMat3_inv_smul_e0, smul_smul c⁻¹ (l ^ 2) e0]
      _ = z • ((c⁻¹ * l ^ 2 * c) • e0) := by
          rw [smul_comm p _ e0, smul_e0_of_mem hp, smul_smul (c⁻¹ * l ^ 2) c e0]
      _ = (c⁻¹ * l ^ 2 * c * (l ^ 2)⁻¹) • e0 := by
          rw [smul_comm z _ e0, zMat3_smul_e0, smul_smul (c⁻¹ * l ^ 2 * c) (l ^ 2)⁻¹ e0]
      _ = e0 := by
          rw [show c⁻¹ * l ^ 2 * c * (l ^ 2)⁻¹ = 1 by field_simp, one_smul]
  · set u := p⁻¹ • v
    set s := (l ^ 2 - l⁻¹) * u 0
    set t := ((l ^ 2)⁻¹ - l) * v 0
    have h : (z * p * z⁻¹ * p⁻¹) • v =
        v + (l⁻¹ * t + s * c * (l ^ 2)⁻¹) • (e0 : Fin 3 → F) := by
      calc (z * p * z⁻¹ * p⁻¹) • v = z • (p • (l⁻¹ • u + s • e0)) := by
            rw [mul_smul, mul_smul, mul_smul, zMat3_inv_smul]
        _ = z • (l⁻¹ • v + (s * c) • e0) := by
            rw [smul_add, smul_comm p l⁻¹ u, smul_inv_smul, smul_comm p s e0,
              smul_e0_of_mem hp, smul_smul s c e0]
        _ = l⁻¹ • (l • v + t • e0) + (s * c) • ((l ^ 2)⁻¹ • e0) := by
            rw [smul_add, smul_comm z l⁻¹ v, zMat3_smul, smul_comm z (s * c) e0, zMat3_smul_e0]
        _ = v + (l⁻¹ * t + s * c * (l ^ 2)⁻¹) • e0 := by
            rw [smul_add, smul_smul l⁻¹ l v, inv_mul_cancel₀ hl, one_smul, smul_smul l⁻¹ t e0,
              smul_smul (s * c) (l ^ 2)⁻¹ e0, add_assoc, ← add_smul]
    rw [h]
    simp [e0]

theorem mulVec3_e0_mem_orbit (v : Fin 3 → F) (hv : v ≠ 0) :
    v ∈ MulAction.orbit (SL3 F) (e0 : Fin 3 → F) := by
  rw [MulAction.mem_orbit_iff]
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := fun h2 => hv (vec3_ext (by simp [h0]) (by simp [h1]) (by simp [h2]))
      refine ⟨⟨!![0, (v 2)⁻¹, 0; 0, 0, 1; v 2, 0, 0], by simp [det_fin_three, h2]⟩, ?_⟩
      change !![0, (v 2)⁻¹, 0; 0, 0, 1; v 2, 0, 0] *ᵥ (e0 : Fin 3 → F) = v
      refine vec3_ext ?_ ?_ ?_ <;> rw [mulVec3] <;> simp [e0, h0, h1]
    · refine ⟨⟨!![0, -(v 1)⁻¹, 0; v 1, 0, 0; v 2, 0, 1], by simp [det_fin_three, h1]⟩, ?_⟩
      change !![0, -(v 1)⁻¹, 0; v 1, 0, 0; v 2, 0, 1] *ᵥ (e0 : Fin 3 → F) = v
      refine vec3_ext ?_ ?_ ?_ <;> rw [mulVec3] <;> simp [e0, h0]
  · refine ⟨⟨!![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1], by simp [det_fin_three, h0]⟩, ?_⟩
    change !![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1] *ᵥ (e0 : Fin 3 → F) = v
    refine vec3_ext ?_ ?_ ?_ <;> rw [mulVec3] <;> simp [e0]

theorem odd_index_lineStab [Fintype F] {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 0 < a) :
    Odd (lineStab (F := F)).index := by
  classical
  have hle : MulAction.stabilizer (SL3 F) (e0 : Fin 3 → F) ≤ lineStab := fun g hg => by
    have hg' : g • (e0 : Fin 3 → F) = e0 := hg
    constructor <;> rw [hg'] <;> simp [e0]
  have horbit : MulAction.orbit (SL3 F) (e0 : Fin 3 → F) = {0}ᶜ := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩ h0
      have := congrFun (smul_eq_zero_iff_eq g |>.mp h0) 0
      simp [e0] at this
    · exact mulVec3_e0_mem_orbit v
  have hidx : (MulAction.stabilizer (SL3 F) (e0 : Fin 3 → F)).index = 2 ^ (3 * a) - 1 := by
    rw [MulAction.index_stabilizer, horbit, Set.ncard_compl, Set.ncard_singleton,
      Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hF, ← pow_mul, mul_comm]
  have hodd : Odd (2 ^ (3 * a) - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, 3 * a = k + 1 := ⟨3 * a - 1, by omega⟩
    rw [hk, pow_succ]
    exact ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩
  rw [← hidx] at hodd
  exact Odd.of_dvd_nat hodd (Subgroup.index_dvd_of_le hle)

theorem mem_B1A_mu3 [Fintype F] [CharP F 2] {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a)
    {f : SL3 F → (Fin 3 → F)} (hf : f ∈ Z1A (mu3 (F := F))) : f ∈ B1A (mu3 (F := F)) := by
  classical
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by
      rw [Finset.card_univ, hF]
      calc ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
        _ < 2 ^ a := by
          calc 2 = 2 ^ 1 := by norm_num
            _ < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) ha)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  obtain ⟨hl0, hl1⟩ := hl
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : l ^ 2 ≠ 1 := by
    intro h
    have : (l - 1) ^ 2 = 0 := by linear_combination h + (1 - l) * h2F
    exact hl1' (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hsq' : (l ^ 2)⁻¹ - 1 ≠ 0 := by
    intro h
    apply hsq
    have := sub_eq_zero.mp h
    rw [inv_eq_one] at this
    exact this
  have hf1 : f 1 = 0 := Z1A_one hf
  have htor : ∀ (c₀ c₁ c₂ : F) (h : c₀ * c₁ * c₂ = 1) (r₁ r₂ : F),
      f (qMat3 (c₀ * r₁ * c₁⁻¹) (c₀ * r₂ * c₂⁻¹)) =
        dMat3 c₀ c₁ c₂ h • f (qMat3 r₁ r₂) + f (dMat3 c₀ c₁ c₂ h) -
          qMat3 (c₀ * r₁ * c₁⁻¹) (c₀ * r₂ * c₂⁻¹) • f (dMat3 c₀ c₁ c₂ h) := by
    intro c₀ c₁ c₂ h r₁ r₂
    rw [← dMat3_conj c₀ c₁ c₂ h r₁ r₂]
    exact Z1A_conj hf _ _
  have htorc : ∀ (c₀ c₁ c₂ : F) (h : c₀ * c₁ * c₂ = 1) (r₁ r₂ : F),
      f (qMat3 (c₀ * r₁ * c₁⁻¹) (c₀ * r₂ * c₂⁻¹)) 1 = c₁ * f (qMat3 r₁ r₂) 1 ∧
      f (qMat3 (c₀ * r₁ * c₁⁻¹) (c₀ * r₂ * c₂⁻¹)) 2 = c₂ * f (qMat3 r₁ r₂) 2 ∧
      f (qMat3 (c₀ * r₁ * c₁⁻¹) (c₀ * r₂ * c₂⁻¹)) 0 = c₀ * f (qMat3 r₁ r₂) 0 -
        (c₀ * r₁ * c₁⁻¹) * f (dMat3 c₀ c₁ c₂ h) 1 -
        (c₀ * r₂ * c₂⁻¹) * f (dMat3 c₀ c₁ c₂ h) 2 := by
    intro c₀ c₁ c₂ h r₁ r₂
    have e := htor c₀ c₁ c₂ h r₁ r₂
    refine ⟨?_, ?_, ?_⟩ <;> rw [e] <;>
      simp only [Pi.sub_apply, Pi.add_apply, dMat3_smul, qMat3_smul, cons_val_zero,
        cons_val_one, head_cons, cons_val_two, tail_cons] <;> ring
  have hcoc : ∀ r₁ r₂ s₁ s₂ : F, f (qMat3 (r₁ + s₁) (r₂ + s₂)) =
      f (qMat3 r₁ r₂) + qMat3 r₁ r₂ • f (qMat3 s₁ s₂) := fun r₁ r₂ s₁ s₂ => by
    rw [← qMat3_mul]
    exact hf _ _
  have hβ1 : ∀ s : F, f (qMat3 s 0) 1 = 0 ∧ f (qMat3 s 0) 2 = 0 := fun s => by
    have hd : l * l * (l ^ 2)⁻¹ = 1 := by field_simp
    obtain ⟨h1, h2, -⟩ := htorc l l (l ^ 2)⁻¹ hd s 0
    have e : l * s * l⁻¹ = s := by field_simp
    rw [e, mul_zero, zero_mul] at h1 h2
    constructor
    · have : (l - 1) * f (qMat3 s 0) 1 = 0 := by linear_combination -h1
      exact (mul_eq_zero.mp this).resolve_left hl1'
    · have : ((l ^ 2)⁻¹ - 1) * f (qMat3 s 0) 2 = 0 := by linear_combination -h2
      exact (mul_eq_zero.mp this).resolve_left hsq'
  have hβ2 : ∀ s : F, f (qMat3 0 s) 1 = 0 ∧ f (qMat3 0 s) 2 = 0 := fun s => by
    have hd : l * (l ^ 2)⁻¹ * l = 1 := by field_simp
    obtain ⟨h1, h2, -⟩ := htorc l (l ^ 2)⁻¹ l hd 0 s
    have e : l * s * l⁻¹ = s := by field_simp
    rw [e, mul_zero, zero_mul] at h1 h2
    constructor
    · have : ((l ^ 2)⁻¹ - 1) * f (qMat3 0 s) 1 = 0 := by linear_combination -h1
      exact (mul_eq_zero.mp this).resolve_left hsq'
    · have : (l - 1) * f (qMat3 0 s) 2 = 0 := by linear_combination -h2
      exact (mul_eq_zero.mp this).resolve_left hl1'
  have hβ : ∀ r₁ r₂ : F, f (qMat3 r₁ r₂) 1 = 0 ∧ f (qMat3 r₁ r₂) 2 = 0 := fun r₁ r₂ => by
    have h := hcoc r₁ 0 0 r₂
    rw [add_zero, zero_add] at h
    rw [h, Pi.add_apply, Pi.add_apply, qMat3_smul]
    simp [(hβ1 r₁).1, (hβ2 r₂).1, (hβ1 r₁).2, (hβ2 r₂).2]
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : F, ∀ s, f (qMat3 s 0) 0 = s * v₁ := by
    have hd : l * l * (l ^ 2)⁻¹ = 1 := by field_simp
    refine ⟨-(f (dMat3 l l (l ^ 2)⁻¹ hd) 1) / (1 - l), fun s => ?_⟩
    obtain ⟨-, -, h⟩ := htorc l l (l ^ 2)⁻¹ hd s 0
    have e : l * s * l⁻¹ = s := by field_simp
    rw [e, mul_zero, zero_mul] at h
    have h1l : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
    rw [mul_div_assoc', eq_div_iff h1l]
    linear_combination h
  obtain ⟨v₂, hv₂⟩ : ∃ v₂ : F, ∀ s, f (qMat3 0 s) 0 = s * v₂ := by
    have hd : l * (l ^ 2)⁻¹ * l = 1 := by field_simp
    refine ⟨-(f (dMat3 l (l ^ 2)⁻¹ l hd) 2) / (1 - l), fun s => ?_⟩
    obtain ⟨-, -, h⟩ := htorc l (l ^ 2)⁻¹ l hd 0 s
    have e : l * s * l⁻¹ = s := by field_simp
    rw [e, mul_zero, zero_mul] at h
    have h1l : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
    rw [mul_div_assoc', eq_div_iff h1l]
    linear_combination h
  have hα : ∀ r₁ r₂ : F, f (qMat3 r₁ r₂) 0 = r₁ * v₁ + r₂ * v₂ := fun r₁ r₂ => by
    have h := congrFun (hcoc r₁ 0 0 r₂) 0
    rw [add_zero, zero_add, Pi.add_apply, qMat3_smul] at h
    simp only [cons_val_zero] at h
    rw [h, hv₁, hv₂, (hβ 0 r₂).1, (hβ 0 r₂).2]
    ring
  set f' := f - coboundaryA (mu3 (F := F)) ![0, v₁, v₂] with hf'_def
  have hf' : f' ∈ Z1A (mu3 (F := F)) := sub_mem hf (B1A_le_Z1A _ ⟨_, rfl⟩)
  have hvan : ∀ r₁ r₂ : F, f' (qMat3 r₁ r₂) = 0 := fun r₁ r₂ => by
    rw [hf'_def, Pi.sub_apply, coboundaryA_apply, mu3_apply, qMat3_smul]
    refine vec3_ext ?_ ?_ ?_
    · simp only [Pi.sub_apply, cons_val_zero, cons_val_one, head_cons, cons_val_two, tail_cons,
        Pi.zero_apply, hα]
      ring
    · simp [(hβ r₁ r₂).1]
    · simp [(hβ r₁ r₂).2]
  have hline : ∀ p ∈ lineStab, f' p = (f' p 0) • (e0 : Fin 3 → F) := fun p hp => by
    have hfix : ∀ r₁ r₂ : F, qMat3 r₁ r₂ • (p⁻¹ • f' p) = p⁻¹ • f' p := fun r₁ r₂ => by
      obtain ⟨s₁, s₂, hs⟩ := conj_qMat3 hp r₁ r₂
      have h1 : f' (p * qMat3 r₁ r₂) = f' p := Z1A_mul_vanish hf' (hvan r₁ r₂)
      have h2 : p * qMat3 r₁ r₂ = (p * qMat3 r₁ r₂ * p⁻¹) * p := by group
      rw [h2, hf', hs, hvan, zero_add, ← hs, mu3_apply, mul_smul, mul_smul] at h1
      have := congrArg (fun v => p⁻¹ • v) h1
      simpa only [inv_smul_smul] using this
    set w := p⁻¹ • f' p
    have hw1 : w 1 = 0 := by
      have := congrFun (hfix 1 0) 0
      rw [qMat3_smul] at this
      simpa using this
    have hw2 : w 2 = 0 := by
      have := congrFun (hfix 0 1) 0
      rw [qMat3_smul] at this
      simpa using this
    have hw : w = (w 0) • (e0 : Fin 3 → F) := by
      refine vec3_ext ?_ ?_ ?_ <;> simp [e0, hw1, hw2]
    set c := (p • (e0 : Fin 3 → F)) 0
    have hpe : p • (e0 : Fin 3 → F) = c • e0 := smul_e0_of_mem hp
    have hfp' : f' p = (w 0 * c) • (e0 : Fin 3 → F) := by
      calc f' p = p • w := (smul_inv_smul p (f' p)).symm
        _ = p • ((w 0) • (e0 : Fin 3 → F)) := congrArg (fun x => p • x) hw
        _ = (w 0) • (p • (e0 : Fin 3 → F)) := smul_comm p (w 0) e0
        _ = (w 0 * c) • (e0 : Fin 3 → F) := by rw [hpe, smul_smul]
    rw [hfp']
    congr 1
    rw [Pi.smul_apply, e0_zero, smul_eq_mul, mul_one]
  set z := zMat3 l hl0
  have hzP : z ∈ lineStab := zMat3_mem l hl0
  have hcomm : ∀ p ∈ lineStab, f' (z * p) = f' (p * z) := fun p hp => by
    obtain ⟨s₁, s₂, hs⟩ := comm_zMat3 l hl0 hp
    have h1 : z * p = (z * p * z⁻¹ * p⁻¹) * (p * z) := by group
    have hpz := hline (p * z) (lineStab.mul_mem hp hzP)
    rw [h1, hf', hs, hvan, zero_add, mu3_apply, hpz, smul_comm (qMat3 s₁ s₂) _ e0,
      qMat3_smul_e0]
  set φz := f' z 0
  set w₀ := φz / ((l ^ 2)⁻¹ - 1)
  have hP : ∀ p ∈ lineStab, f' p = mu3 p (w₀ • (e0 : Fin 3 → F)) - w₀ • e0 := fun p hp => by
    set c := (p • (e0 : Fin 3 → F)) 0
    have hpe : p • (e0 : Fin 3 → F) = c • e0 := smul_e0_of_mem hp
    set φp := f' p 0
    have ep : f' p = φp • (e0 : Fin 3 → F) := hline p hp
    have ez : f' z = φz • (e0 : Fin 3 → F) := hline z hzP
    have h := congrFun (hcomm p hp) 0
    rw [hf', hf', mu3_apply, mu3_apply, ep, ez, smul_comm z φp e0, zMat3_smul_e0,
      smul_comm p φz e0, hpe] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e0_zero, mul_one] at h
    rw [ep, mu3_apply, smul_comm p w₀ e0, hpe, smul_smul, ← sub_smul]
    congr 1
    rw [show w₀ * c - w₀ = φz * (c - 1) / ((l ^ 2)⁻¹ - 1) by ring, eq_div_iff hsq']
    linear_combination h
  have h2 : ∀ m : Fin 3 → F, m + m = 0 := fun m => funext fun i => add_self_F (m i)
  have hB := mem_B1A_of_restrict h2 (odd_index_lineStab hF (by omega)) hf' hP
  have := add_mem hB (⟨![0, v₁, v₂], rfl⟩ : coboundaryA (mu3 (F := F)) ![0, v₁, v₂] ∈ B1A _)
  rwa [hf'_def, sub_add_cancel] at this

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_SL3_of_one_lt [Fintype F] [CharP F 2] {ρ : Representation (ZMod 2) Γ W}
    {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) {ε : Explicit.NatDual}
    (h : Explicit.BinaryNaturalSL ρ 3 F ε) : Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  obtain ⟨θ, β, hβ⟩ := BinaryNaturalSL.intertwiner h
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  have hβ' : ∀ γ w, β (ρ γ w) = mu3 (θ γ) (β w) := hβ
  have hZ : Z1A (mu3 (F := F)) = B1A (mu3 (F := F)) :=
    le_antisymm (fun f hf => mem_B1A_mu3 hF ha hf) (B1A_le_Z1A _)
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' (k := 1) (by rw [hZ, one_mul]), pow_zero]

end CFSG.Quasithin.JonesParshall
