module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open CFSG.GH74.QTGen4.DSGen4.L34
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open CFSG.LocalAnalysis.ComponentInitial.LinearCover
open CFSG.QuasithinUnique.Fin257.L3
open CFSG.Quasithin.H13.F431.L3.P3

theorem dcProp_of_forall_exists_extend {Y : Type} [Group Y] {A B : Subgroup Y}
    (h : ∀ σ : MulAut ↥(A ⊓ B),
      (∀ b : ↥(A ⊓ B), (b : Y) ∈ pCoreOf 2 A ↔
        ((σ b : ↥(A ⊓ B)) : Y) ∈ pCoreOf 2 A) →
        ∃ Ψ : MulAut Y, (∀ g, g ∈ A ↔ Ψ g ∈ A) ∧ (∀ g, g ∈ B ↔ Ψ g ∈ B) ∧
          ∀ b : ↥(A ⊓ B), (Ψ b : Y) = ((σ b : ↥(A ⊓ B)) : Y)) :
    DCProp A B := by
  intro σ hσ
  obtain ⟨Ψ, hA, hB, hΨ⟩ := h σ hσ
  let a₁ : MulAut ↥A :=
    { toFun := fun m => ⟨Ψ m, (hA m).mp m.2⟩
      invFun := fun m => ⟨Ψ⁻¹ m, (hA _).mpr (by simpa using m.2)⟩
      left_inv := fun m => Subtype.ext (by simp)
      right_inv := fun m => Subtype.ext (by simp)
      map_mul' := fun m n => Subtype.ext (map_mul Ψ _ _) }
  have ha₁ : ∀ m : ↥A, ((a₁ m : ↥A) : Y) = Ψ (m : Y) := fun m => rfl
  refine ⟨a₁, 1, ?_, ?_, ?_⟩
  · intro m
    rw [ha₁]
    exact hB (m : Y)
  · intro m
    exact Iff.rfl
  · intro b m₁ m₂ hm₁ hm₂
    have hσb : (Ψ (b : Y) : Y) = ((σ b : ↥(A ⊓ B)) : Y) := hΨ b
    have : (m₂ : Y) = ((σ b : ↥(A ⊓ B)) : Y) := by
      rw [← hm₂, ha₁, hm₁, hσb]
    simpa using this

private theorem conjAut_fieldAut_xP {F : Type} [Field F] (s t : Fˣ) (ρ : F ≃+* F) (a : F) :
    (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) (xP a) =
      xP ((s : F) * ρ a) := by
  rw [MulAut.mul_apply, fieldAut_xP, conjAut_nuDiag_xP]

private theorem conjAut_fieldAut_yP {F : Type} [Field F] (s t : Fˣ) (ρ : F ≃+* F) (b : F) :
    (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) (yP b) =
      yP ((t : F) * ρ b) := by
  rw [MulAut.mul_apply, fieldAut_yP, conjAut_nuDiag_yP]

private theorem conjAut_fieldAut_wP {F : Type} [Field F] (s t : Fˣ) (ρ : F ≃+* F) (c : F) :
    (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) (wP c) =
      wP ((s : F) * (t : F) * ρ c) := by
  rw [MulAut.mul_apply, fieldAut_wP, conjAut_nuDiag_wP]

private theorem conjAut_fieldAut_mem_V2 {F : Type} [Field F] [CharP F 2] (s t : Fˣ) (ρ : F ≃+* F)
    {g : projectiveSL 3 F} (hg : g ∈ V2) :
    (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) g ∈ V2 := by
  obtain ⟨b, c, rfl⟩ := mem_V2.mp hg
  rw [map_mul, conjAut_fieldAut_yP, conjAut_fieldAut_wP]
  exact mem_V2.mpr ⟨(t : F) * ρ b, (s : F) * (t : F) * ρ c, rfl⟩

private theorem conjAut_fieldAut_exists_mem_V2 {F : Type} [Field F] [CharP F 2]
    (s t : Fˣ) (ρ : F ≃+* F)
    {z : projectiveSL 3 F} (hz : z ∈ V2) :
    ∃ g ∈ V2, (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) g = z := by
  obtain ⟨b, c, rfl⟩ := mem_V2.mp hz
  refine ⟨yP (ρ.symm ((t : F)⁻¹ * b)) * wP (ρ.symm (((s : F) * (t : F))⁻¹ * c)),
    mem_V2.mpr ⟨_, _, rfl⟩, ?_⟩
  have hb : (t : F) * ρ (ρ.symm ((t : F)⁻¹ * b)) = b := by
    rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ t.ne_zero]
  have hc : (s : F) * (t : F) * ρ (ρ.symm (((s : F) * (t : F))⁻¹ * c)) = c := by
    rw [RingEquiv.apply_symm_apply,
      mul_inv_cancel_left₀ (mul_ne_zero s.ne_zero t.ne_zero)]
  rw [map_mul, conjAut_fieldAut_yP, conjAut_fieldAut_wP, hb, hc]

private theorem conjAut_fieldAut_mem_V1 {F : Type} [Field F] [CharP F 2] (s t : Fˣ) (ρ : F ≃+* F)
    {g : projectiveSL 3 F} (hg : g ∈ V1) :
    (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) g ∈ V1 := by
  obtain ⟨a, c, rfl⟩ := mem_V1.mp hg
  rw [map_mul, conjAut_fieldAut_xP, conjAut_fieldAut_wP]
  exact mem_V1.mpr ⟨(s : F) * ρ a, (s : F) * (t : F) * ρ c, rfl⟩

private theorem conjAut_fieldAut_exists_mem_V1 {F : Type} [Field F] [CharP F 2]
    (s t : Fˣ) (ρ : F ≃+* F)
    {z : projectiveSL 3 F} (hz : z ∈ V1) :
    ∃ g ∈ V1, (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) g = z := by
  obtain ⟨a, c, rfl⟩ := mem_V1.mp hz
  refine ⟨xP (ρ.symm ((s : F)⁻¹ * a)) * wP (ρ.symm (((s : F) * (t : F))⁻¹ * c)),
    mem_V1.mpr ⟨_, _, rfl⟩, ?_⟩
  have ha : (s : F) * ρ (ρ.symm ((s : F)⁻¹ * a)) = a := by
    rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ s.ne_zero]
  have hc : (s : F) * (t : F) * ρ (ρ.symm (((s : F) * (t : F))⁻¹ * c)) = c := by
    rw [RingEquiv.apply_symm_apply,
      mul_inv_cancel_left₀ (mul_ne_zero s.ne_zero t.ne_zero)]
  rw [map_mul, conjAut_fieldAut_xP, conjAut_fieldAut_wP, ha, hc]

theorem mem_Ln_iff_conjAut_fieldAut {F : Type} [Field F] [CharP F 2] (s t : Fˣ)
    (ρ : F ≃+* F) (g : projectiveSL 3 F) :
    g ∈ Ln F ↔ LinearFlag.conjAut 3 F (nuDiagGL s t) (LinearFlag.fieldAut 3 F ρ g) ∈ Ln F := by
  let Φ : MulAut (projectiveSL 3 F) :=
    LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ
  have hV2 : ∀ x, x ∈ V2 ↔ Φ x ∈ V2 := by
    intro x
    refine ⟨conjAut_fieldAut_mem_V2 s t ρ, fun hx => ?_⟩
    obtain ⟨y, hy, hyx⟩ := conjAut_fieldAut_exists_mem_V2 s t ρ hx
    have : y = x := Φ.injective hyx
    rwa [this] at hy
  have h := mem_normalizer_iff_of_aut Φ V2 hV2 g
  simpa [Ln, Φ] using h

theorem mem_Pt_iff_conjAut_fieldAut {F : Type} [Field F] [CharP F 2] (s t : Fˣ)
    (ρ : F ≃+* F) (g : projectiveSL 3 F) :
    g ∈ Pt F ↔ LinearFlag.conjAut 3 F (nuDiagGL s t) (LinearFlag.fieldAut 3 F ρ g) ∈ Pt F := by
  let Φ : MulAut (projectiveSL 3 F) :=
    LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ
  have hV1 : ∀ x, x ∈ V1 ↔ Φ x ∈ V1 := by
    intro x
    refine ⟨conjAut_fieldAut_mem_V1 s t ρ, fun hx => ?_⟩
    obtain ⟨y, hy, hyx⟩ := conjAut_fieldAut_exists_mem_V1 s t ρ hx
    have : y = x := Φ.injective hyx
    rwa [this] at hy
  have h := mem_normalizer_iff_of_aut Φ V1 hV1 g
  simpa [Pt, Φ] using h

private theorem xP_injective {F : Type} [Field F] [CharP F 2] :
    Function.Injective (xP : F → projectiveSL 3 F) := by
  intro a b h
  exact (xP_wP_inj (a := a) (c := 0) (a' := b) (c' := 0) (by simpa using h)).1

private theorem yP_injective {F : Type} [Field F] :
    Function.Injective (yP : F → projectiveSL 3 F) := by
  intro b b' h
  exact (yP_wP_inj (b := b) (c := 0) (b' := b') (c' := 0) (by simpa using h)).1

private theorem fieldAut_dMat {F : Type} [Field F] (ρ : F ≃+* F) (t1 t2 : Fˣ) :
    LinearFlag.fieldAut 3 F ρ (proj 3 F (dMat t1 t2)) =
      proj 3 F (dMat (Units.map ρ.toMonoidHom t1) (Units.map ρ.toMonoidHom t2)) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext i j
  rw [coe_sl_map_apply, coe_dMat, coe_dMat]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Units.coe_map, map_mul]

private theorem conjAut_fieldAut_mem_torus {F : Type} [Field F] (s t : Fˣ) (ρ : F ≃+* F)
    {g : projectiveSL 3 F} (hg : g ∈ torus3 F) :
    (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) g ∈ torus3 F := by
  obtain ⟨t1, t2, rfl⟩ := mem_torus3.mp hg
  rw [MulAut.mul_apply, fieldAut_dMat, conjAut_nuDiag_dMat]
  exact mem_torus3.mpr ⟨Units.map ρ.toMonoidHom t1, Units.map ρ.toMonoidHom t2, rfl⟩

private theorem conjAut_fieldAut_exists_mem_U {F : Type} [Field F] [CharP F 2] (s t : Fˣ)
    (ρ : F ≃+* F) {z : projectiveSL 3 F} (hz : z ∈ projUnitriangular 3 F) :
    ∃ g ∈ projUnitriangular 3 F,
      (LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ) g = z := by
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hz
  refine ⟨wP (ρ.symm (((s : F) * (t : F))⁻¹ * c)) * xP (ρ.symm ((s : F)⁻¹ * a)) *
    yP (ρ.symm ((t : F)⁻¹ * b)), mem_Ubar.mpr ⟨_, _, _, rfl⟩, ?_⟩
  have hc : (s : F) * (t : F) * ρ (ρ.symm (((s : F) * (t : F))⁻¹ * c)) = c := by
    rw [RingEquiv.apply_symm_apply,
      mul_inv_cancel_left₀ (mul_ne_zero s.ne_zero t.ne_zero)]
  have ha : (s : F) * ρ (ρ.symm ((s : F)⁻¹ * a)) = a := by
    rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ s.ne_zero]
  have hb : (t : F) * ρ (ρ.symm ((t : F)⁻¹ * b)) = b := by
    rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ t.ne_zero]
  rw [map_mul, map_mul, conjAut_fieldAut_wP, conjAut_fieldAut_xP, conjAut_fieldAut_yP,
    hc, ha, hb]

private theorem eq_one_of_mem_torus_centralizer {F : Type} [Field F] [CharP F 2]
    {t : projectiveSL 3 F} (ht : t ∈ torus3 F)
    (hc : ∀ y ∈ projUnitriangular 3 F, t * y * t⁻¹ = y) : t = 1 := by
  obtain ⟨t1, t2, rfl⟩ := mem_torus3.mp ht
  have hx1 : proj 3 F (dMat t1 t2) * xP 1 * (proj 3 F (dMat t1 t2))⁻¹ = xP 1 :=
    hc (xP 1) ((projRoots (K := F)).x_mem 1)
  have hy1 : proj 3 F (dMat t1 t2) * yP 1 * (proj 3 F (dMat t1 t2))⁻¹ = yP 1 :=
    hc (yP 1) ((projRoots (K := F)).y_mem 1)
  rw [dP_conj_xP] at hx1
  rw [dP_conj_yP] at hy1
  have h1 : (t1 : F) * (t2 : F)⁻¹ = 1 := by
    have := xP_injective (F := F) hx1
    simpa using this
  have h2 : (t1 : F) * (t2 : F) * (t2 : F) = 1 := by
    have := yP_injective (F := F) hy1
    simpa using this
  have h1u : t1 * t2⁻¹ = 1 := by
    apply Units.ext
    simpa using h1
  have ht12 : t1 = t2 := mul_inv_eq_one.mp h1u
  have h3 : (t1 : F) * (t1 : F) * (t1 : F) = 1 := by
    simpa [ht12] using h2
  have h3u : t1 ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    simpa [pow_three, mul_assoc] using h3
  have hsq : ((t1 * t1)⁻¹ : Fˣ) = t1 := by
    apply Units.ext
    rw [Units.val_inv_eq_inv_val, Units.val_mul]
    exact inv_eq_of_mul_eq_one_right h3
  rw [← ht12, proj_eq_one_iff, mem_scalars]
  refine ⟨t1, h3u, ?_⟩
  rw [coe_dMat, hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.scalar_apply]

theorem eq_on_inf_of_roots {F : Type} [Field F] [Finite F] [CharP F 2]
    (σ : MulAut ↥(Ln F ⊓ Pt F)) {u : projectiveSL 3 F}
    (hu : u ∈ projUnitriangular 3 F) (s t : Fˣ) (ρ : F ≃+* F)
    (hx : ∀ (x : ↥(Ln F ⊓ Pt F)) (a : F), (x : projectiveSL 3 F) = xP a →
      ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
        u * xP ((s : F) * ρ a) * u⁻¹)
    (hy : ∀ (x : ↥(Ln F ⊓ Pt F)) (b : F), (x : projectiveSL 3 F) = yP b →
      ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
        u * yP ((t : F) * ρ b) * u⁻¹)
    (hH : ∀ x : ↥(Ln F ⊓ Pt F), (x : projectiveSL 3 F) ∈ torus3 F →
      u⁻¹ * ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) * u ∈ torus3 F)
    (x : ↥(Ln F ⊓ Pt F)) :
    ((σ x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
      u * LinearFlag.conjAut 3 F (nuDiagGL s t)
        (LinearFlag.fieldAut 3 F ρ (x : projectiveSL 3 F)) * u⁻¹ := by
  let U : Subgroup (projectiveSL 3 F) := projUnitriangular 3 F
  let T : Subgroup (projectiveSL 3 F) := torus3 F
  let B0 : Subgroup (projectiveSL 3 F) := Ln F ⊓ Pt F
  let Φ : MulAut (projectiveSL 3 F) :=
    LinearFlag.conjAut 3 F (nuDiagGL s t) * LinearFlag.fieldAut 3 F ρ
  have hB0 : B0 = Subgroup.normalizer (U : Set (projectiveSL 3 F)) := B0_eq_normalizer
  have hU_le_B0 : U ≤ B0 := by
    rw [hB0]
    exact Subgroup.le_normalizer
  have hT_le_B0 : T ≤ B0 := by
    intro g hg
    rw [hB0]
    exact torus3_le_normalizer hg
  have hxP_mem : ∀ a : F, xP a ∈ B0 := fun a => hU_le_B0 ((projRoots (K := F)).x_mem a)
  have hyP_mem : ∀ b : F, yP b ∈ B0 := fun b => hU_le_B0 ((projRoots (K := F)).y_mem b)
  have hwP_mem : ∀ c : F, wP c ∈ B0 := fun c => hU_le_B0 ((projRoots (K := F)).w_mem c)
  have hσxP : ∀ a : F, ((σ ⟨xP a, hxP_mem a⟩ : B0) : projectiveSL 3 F) =
      u * Φ (xP a) * u⁻¹ := by
    intro a
    rw [hx ⟨xP a, hxP_mem a⟩ a rfl, conjAut_fieldAut_xP]
  have hσyP : ∀ b : F, ((σ ⟨yP b, hyP_mem b⟩ : B0) : projectiveSL 3 F) =
      u * Φ (yP b) * u⁻¹ := by
    intro b
    rw [hy ⟨yP b, hyP_mem b⟩ b rfl, conjAut_fieldAut_yP]
  have hΦ_mul : ∀ a b : projectiveSL 3 F,
      u * Φ (a * b) * u⁻¹ = (u * Φ a * u⁻¹) * (u * Φ b * u⁻¹) := by
    intro a b
    rw [map_mul]
    group
  have hσwP : ∀ c : F, ((σ ⟨wP c, hwP_mem c⟩ : B0) : projectiveSL 3 F) =
      u * Φ (wP c) * u⁻¹ := by
    intro c
    let aX : B0 := ⟨xP 1, hxP_mem 1⟩
    let aY : B0 := ⟨yP c, hyP_mem c⟩
    have hX : ((σ aX : B0) : projectiveSL 3 F) = u * Φ (xP 1) * u⁻¹ := hσxP 1
    have hY : ((σ aY : B0) : projectiveSL 3 F) = u * Φ (yP c) * u⁻¹ := hσyP c
    have hW : wP c = yP c * xP 1 * (yP c)⁻¹ * (xP 1)⁻¹ := by
      have h := (yP_mul_xP (F := F) (1 : F) c).symm
      have h' : wP c * xP 1 * yP c = yP c * xP 1 := by simpa using h
      calc wP c = (wP c * xP 1 * yP c) * (yP c)⁻¹ * (xP 1)⁻¹ := by group
        _ = (yP c * xP 1) * (yP c)⁻¹ * (xP 1)⁻¹ := by rw [h']
        _ = yP c * xP 1 * (yP c)⁻¹ * (xP 1)⁻¹ := by group
    have hexpr : (⟨wP c, hwP_mem c⟩ : B0) = aY * aX * aY⁻¹ * aX⁻¹ := by
      apply Subtype.ext
      exact hW
    calc ((σ ⟨wP c, hwP_mem c⟩ : B0) : projectiveSL 3 F)
        = ((σ (aY * aX * aY⁻¹ * aX⁻¹) : B0) : projectiveSL 3 F) := by rw [hexpr]
      _ = ((σ aY : B0) : projectiveSL 3 F) * ((σ aX : B0) : projectiveSL 3 F) *
            (((σ aY : B0) : projectiveSL 3 F))⁻¹ *
            (((σ aX : B0) : projectiveSL 3 F))⁻¹ := by
            simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      _ = (u * Φ (yP c) * u⁻¹) * (u * Φ (xP 1) * u⁻¹) *
            (u * Φ (yP c) * u⁻¹)⁻¹ * (u * Φ (xP 1) * u⁻¹)⁻¹ := by rw [hY, hX]
      _ = u * Φ (wP c) * u⁻¹ := by
            rw [hW]
            simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
            group
  have hσU : ∀ v : B0, (v : projectiveSL 3 F) ∈ U →
      ((σ v : B0) : projectiveSL 3 F) = u * Φ (v : projectiveSL 3 F) * u⁻¹ := by
    intro v hv
    obtain ⟨c, a, b, hv_eq⟩ := mem_Ubar.mp hv
    have hvsub : v = (⟨wP c, hwP_mem c⟩ : B0) * (⟨xP a, hxP_mem a⟩ : B0) *
        (⟨yP b, hyP_mem b⟩ : B0) := by
      apply Subtype.ext
      exact hv_eq
    calc ((σ v : B0) : projectiveSL 3 F)
        = ((σ ((⟨wP c, hwP_mem c⟩ : B0) * (⟨xP a, hxP_mem a⟩ : B0) *
            (⟨yP b, hyP_mem b⟩ : B0)) : B0) : projectiveSL 3 F) := by rw [hvsub]
      _ = ((σ ⟨wP c, hwP_mem c⟩ : B0) : projectiveSL 3 F) *
            ((σ ⟨xP a, hxP_mem a⟩ : B0) : projectiveSL 3 F) *
            ((σ ⟨yP b, hyP_mem b⟩ : B0) : projectiveSL 3 F) := by
            simp only [map_mul, Subgroup.coe_mul]
      _ = (u * Φ (wP c) * u⁻¹) * (u * Φ (xP a) * u⁻¹) * (u * Φ (yP b) * u⁻¹) := by
            rw [hσwP c, hσxP a, hσyP b]
      _ = u * Φ ((⟨wP c, hwP_mem c⟩ : B0) * (⟨xP a, hxP_mem a⟩ : B0) *
            (⟨yP b, hyP_mem b⟩ : B0) : projectiveSL 3 F) * u⁻¹ := by
            simp only [map_mul, Subgroup.coe_mul]
            group
      _ = u * Φ (v : projectiveSL 3 F) * u⁻¹ := by
            rw [hvsub]
            rfl
  have hφU : ∀ z : projectiveSL 3 F, z ∈ U →
      ∃ y : B0, (y : projectiveSL 3 F) ∈ U ∧ u * Φ (y : projectiveSL 3 F) * u⁻¹ = z := by
    intro z hz
    have hz' : u⁻¹ * z * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) hz) hu
    obtain ⟨y, hyU, hyz⟩ := conjAut_fieldAut_exists_mem_U s t ρ hz'
    refine ⟨⟨y, hU_le_B0 hyU⟩, hyU, ?_⟩
    calc u * Φ y * u⁻¹ = u * (u⁻¹ * z * u) * u⁻¹ := by rw [hyz]
      _ = z := by group
  have hσT : ∀ h : B0, (h : projectiveSL 3 F) ∈ T →
      ((σ h : B0) : projectiveSL 3 F) = u * Φ (h : projectiveSL 3 F) * u⁻¹ := by
    intro h hh
    have hΦT : Φ (h : projectiveSL 3 F) ∈ T := conjAut_fieldAut_mem_torus s t ρ hh
    have haT : u⁻¹ * ((σ h : B0) : projectiveSL 3 F) * u ∈ T := hH h hh
    let c : projectiveSL 3 F := (u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ *
      ((σ h : B0) : projectiveSL 3 F)
    have hcT : u⁻¹ * c * u ∈ T := by
      have hc_eq : u⁻¹ * c * u =
          (Φ (h : projectiveSL 3 F))⁻¹ * (u⁻¹ * ((σ h : B0) : projectiveSL 3 F) * u) := by
        show u⁻¹ * ((u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ *
          ((σ h : B0) : projectiveSL 3 F)) * u = _
        group
      rw [hc_eq]
      exact T.mul_mem (T.inv_mem hΦT) haT
    have hc_central : ∀ z : projectiveSL 3 F, z ∈ U → c * z * c⁻¹ = z := by
      intro z hz
      obtain ⟨y, hyU, hφy⟩ := hφU z hz
      have hhyU : ((h * y * h⁻¹ : B0) : projectiveSL 3 F) ∈ U := by
        have hhN : (h : projectiveSL 3 F) ∈
            Subgroup.normalizer (U : Set (projectiveSL 3 F)) := by
          rw [← hB0]
          exact h.2
        exact (Subgroup.mem_normalizer_iff.mp hhN (y : projectiveSL 3 F)).mp hyU
      have hconj : ((σ (h * y * h⁻¹) : B0) : projectiveSL 3 F) =
          u * Φ ((h : projectiveSL 3 F) * (y : projectiveSL 3 F) * (h : projectiveSL 3 F)⁻¹) *
            u⁻¹ := hσU _ hhyU
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hconj
      have hσy : ((σ y : B0) : projectiveSL 3 F) = u * Φ (y : projectiveSL 3 F) * u⁻¹ :=
        hσU y hyU
      rw [hσy] at hconj
      have hcz : c * (u * Φ (y : projectiveSL 3 F) * u⁻¹) * c⁻¹ =
          (u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ *
            (((σ h : B0) : projectiveSL 3 F) * (u * Φ (y : projectiveSL 3 F) * u⁻¹) *
              ((σ h : B0) : projectiveSL 3 F)⁻¹) *
            (u * Φ (h : projectiveSL 3 F) * u⁻¹) := by
        show ((u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ * ((σ h : B0) : projectiveSL 3 F)) *
            (u * Φ (y : projectiveSL 3 F) * u⁻¹) *
            ((u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ * ((σ h : B0) : projectiveSL 3 F))⁻¹ = _
        group
      calc c * z * c⁻¹ = c * (u * Φ (y : projectiveSL 3 F) * u⁻¹) * c⁻¹ := by rw [hφy]
        _ = (u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ *
              (((σ h : B0) : projectiveSL 3 F) * (u * Φ (y : projectiveSL 3 F) * u⁻¹) *
                ((σ h : B0) : projectiveSL 3 F)⁻¹) *
              (u * Φ (h : projectiveSL 3 F) * u⁻¹) := hcz
        _ = (u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ *
              (u * Φ (h : projectiveSL 3 F) * u⁻¹ * (u * Φ (y : projectiveSL 3 F) * u⁻¹) *
                (u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹) *
              (u * Φ (h : projectiveSL 3 F) * u⁻¹) := by
            rw [hconj]
            group
        _ = z := by rw [hφy]; group
    have hcT_central : ∀ z : projectiveSL 3 F, z ∈ U →
        (u⁻¹ * c * u) * z * (u⁻¹ * c * u)⁻¹ = z := by
      intro z hz
      have huz : u * z * u⁻¹ ∈ U := U.mul_mem (U.mul_mem hu hz) (U.inv_mem hu)
      have hz' := hc_central (u * z * u⁻¹) huz
      calc (u⁻¹ * c * u) * z * (u⁻¹ * c * u)⁻¹
          = u⁻¹ * (c * (u * z * u⁻¹) * c⁻¹) * u := by group
        _ = u⁻¹ * (u * z * u⁻¹) * u := by rw [hz']
        _ = z := by group
    have hcT_one : u⁻¹ * c * u = 1 := eq_one_of_mem_torus_centralizer hcT hcT_central
    have hc_one : c = 1 := by
      have hc_eq : c = u * (u⁻¹ * c * u) * u⁻¹ := by group
      rw [hcT_one] at hc_eq
      simpa using hc_eq
    have hmain : ((σ h : B0) : projectiveSL 3 F) = u * Φ (h : projectiveSL 3 F) * u⁻¹ := by
      have hc_eq : (u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ *
          ((σ h : B0) : projectiveSL 3 F) = 1 := hc_one
      calc ((σ h : B0) : projectiveSL 3 F)
          = (u * Φ (h : projectiveSL 3 F) * u⁻¹) *
              ((u * Φ (h : projectiveSL 3 F) * u⁻¹)⁻¹ *
                ((σ h : B0) : projectiveSL 3 F)) := by group
        _ = u * Φ (h : projectiveSL 3 F) * u⁻¹ := by rw [hc_eq, mul_one]
    exact hmain
  have hσB0 : ∀ y : B0, ((σ y : B0) : projectiveSL 3 F) =
      u * Φ (y : projectiveSL 3 F) * u⁻¹ := by
    intro y
    have hyN : (y : projectiveSL 3 F) ∈
        Subgroup.normalizer (U : Set (projectiveSL 3 F)) := by
      rw [← hB0]
      exact y.2
    obtain ⟨v, hvU, h, hhT, hyh⟩ := torus3_mul hyN
    let vB : B0 := ⟨v, hU_le_B0 hvU⟩
    let hB : B0 := ⟨h, hT_le_B0 hhT⟩
    have hysub : y = vB * hB := by
      apply Subtype.ext
      exact hyh
    calc ((σ y : B0) : projectiveSL 3 F)
        = ((σ (vB * hB) : B0) : projectiveSL 3 F) := by rw [hysub]
      _ = ((σ vB : B0) : projectiveSL 3 F) * ((σ hB : B0) : projectiveSL 3 F) := by
            rw [map_mul]
            rfl
      _ = (u * Φ (vB : projectiveSL 3 F) * u⁻¹) *
            (u * Φ (hB : projectiveSL 3 F) * u⁻¹) := by
            rw [hσU vB hvU, hσT hB hhT]
      _ = u * Φ ((vB : projectiveSL 3 F) * (hB : projectiveSL 3 F)) * u⁻¹ := by
            rw [hΦ_mul]
      _ = u * Φ (y : projectiveSL 3 F) * u⁻¹ := by
            rw [hysub]
            rfl
  exact hσB0 x

end CFSG.Quasithin.F112R.St84
