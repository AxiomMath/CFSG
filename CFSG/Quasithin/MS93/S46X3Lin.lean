module

public import CFSG.Quasithin.MS93.ML3Facts
public import CFSG.Quasithin.Background.G1Basic
public import CFSG.Quasithin.Background.G2SL2

public section

open Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.SL2Model CFSG.Quasithin.G1
open scoped MatrixGroups commutatorElement

namespace CFSG.Quasithin.MS93.S46.X3

variable {F : Type} [Field F]

private theorem coe_mul' (A B : SL3 F) :
    ((A * B : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem rootElt_mulVec_apply_zero_of_mem {B : SL3 F}
    (hB : B ∈ (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F))) (v : Fin 3 → F) :
    ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0 := by
  let S : Subgroup (SL3 F) :=
    { carrier := {B | ∀ v : Fin 3 → F, ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0}
      one_mem' := fun v => by
        show (((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0
        rw [coe_one_SL3, Matrix.one_mulVec]
      mul_mem' := fun {A B} hA hB v => by
        show (((A * B : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0
        rw [coe_mul', ← Matrix.mulVec_mulVec, hA, hB]
      inv_mem' := fun {B} hB v => by
        show (((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0
        have := hB (((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
        rw [Matrix.mulVec_mulVec, ← coe_mul', mul_inv_cancel, coe_one_SL3,
          Matrix.one_mulVec] at this
        exact this.symm }
  have hR : (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) ≤ S := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨c, rfl⟩ v <;>
      simp [rootElt_mulVec (show (1 : Fin 3) ≠ 0 by decide),
        rootElt_mulVec (show (2 : Fin 3) ≠ 0 by decide)]
  exact hR hB v

theorem apply_zero_of_mem_commN {x : Fin 3 → F}
    (hx : x ∈ commN (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F))) : x 0 = 0 := by
  have hle : commN (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) ≤
      LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 0) := by
    rw [commN, Submodule.span_le]
    rintro _ ⟨B, hB, v, rfl⟩
    simp [rootElt_mulVec_apply_zero_of_mem hB v]
  exact hle hx

theorem mem_commN_of_apply_zero {x : Fin 3 → F} (hx : x 0 = 0) :
    x ∈ commN (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) := by
  have h1 := sub_mem_commN (A := (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)))
    (Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 (x 1))) (Pi.single 0 1)
  have h2 := sub_mem_commN (A := (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)))
    (Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 (x 2))) (Pi.single 0 1)
  have e : x = (((rootElt 1 0 (x 1) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 -
      Pi.single 0 1) + (((rootElt 2 0 (x 2) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      Pi.single 0 1 - Pi.single 0 1) := by
    rw [rootElt_mulVec (show (1 : Fin 3) ≠ 0 by decide),
      rootElt_mulVec (show (2 : Fin 3) ≠ 0 by decide)]
    funext k
    fin_cases k <;> simp [hx]
  rw [e]
  exact Submodule.add_mem _ h1 h2

private theorem conj_eq_commutator_mul (A s : SL3 F) : A * s * A⁻¹ = ⁅A, s⁆ * s := by
  rw [commutatorElement_def]
  group

private theorem map_conj_rootElt12_le (c : F) :
    (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)).map (MulAut.conj (rootElt 1 2 c)).toMonoidHom
      ≤ rootGroup 1 0 ⊔ rootGroup 2 0 := by
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_ <;> rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩ <;>
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rw [(rootElt_commute (show (2 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 1 by decide) c
      e).eq, mul_inv_cancel_right]
    exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 e)
  · rw [conj_eq_commutator_mul, rootElt_commutator (show (1 : Fin 3) ≠ 2 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 0 by decide)]
    exact Subgroup.mul_mem_sup (rootElt_mem_rootGroup 1 0 _) (rootElt_mem_rootGroup 2 0 e)

private theorem map_conj_rootElt21_le (c : F) :
    (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)).map (MulAut.conj (rootElt 2 1 c)).toMonoidHom
      ≤ rootGroup 1 0 ⊔ rootGroup 2 0 := by
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_ <;> rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩ <;>
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rw [conj_eq_commutator_mul, rootElt_commutator (show (2 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide)]
    exact (rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)).mul_mem
      (Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 _))
      (Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 e))
  · rw [(rootElt_commute (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) c
      e).eq, mul_inv_cancel_right]
    exact Subgroup.mem_sup_right (rootElt_mem_rootGroup 2 0 e)

private theorem mem_normalizer_of_map_le {D : Subgroup (SL3 F)} {g : SL3 F}
    (h₁ : D.map (MulAut.conj g).toMonoidHom ≤ D) (h₂ : D.map (MulAut.conj g⁻¹).toMonoidHom ≤ D) :
    g ∈ Subgroup.normalizer (D : Set (SL3 F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h₁ ⟨x, hx, rfl⟩
  · intro hx
    have := h₂ ⟨_, hx, rfl⟩
    simpa [mul_assoc] using this

theorem rootElt12_mem_normalizer (c : F) : rootElt 1 2 c ∈
    Subgroup.normalizer ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F)) :=
  mem_normalizer_of_map_le (map_conj_rootElt12_le c)
    (by rw [← rootElt_neg]; exact map_conj_rootElt12_le (-c))

theorem rootElt21_mem_normalizer (c : F) : rootElt 2 1 c ∈
    Subgroup.normalizer ((rootGroup 1 0 ⊔ rootGroup 2 0 : Subgroup (SL3 F)) : Set (SL3 F)) :=
  mem_normalizer_of_map_le (map_conj_rootElt21_le c)
    (by rw [← rootElt_neg]; exact map_conj_rootElt21_le (-c))

theorem rootElt_mulVec_apply_zero {i j : Fin 3} (hi : i ≠ 0) (c : F) (v : Fin 3 → F) :
    (((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0 := by
  by_cases hij : i = j
  · rw [hij, rootElt_self, coe_one_SL3, Matrix.one_mulVec]
  · rw [rootElt_mulVec hij, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hi), add_zero]

theorem rootElt12_mul_rootElt21_mulVec_apply_zero (a b : F) (v : Fin 3 → F) :
    (((rootElt 1 2 a * rootElt 2 1 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0 := by
  rw [coe_mul', ← Matrix.mulVec_mulVec, rootElt_mulVec_apply_zero (by decide),
    rootElt_mulVec_apply_zero (by decide)]

theorem rootElt12_mul_rootElt21_pow_three [CharP F 2] {a : F} (ha : a ≠ 0) :
    (rootElt 1 2 a * rootElt 2 1 a⁻¹ : SL3 F) ^ 3 = 1 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have haa' : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  have hM : ((rootElt 1 2 a * rootElt 2 1 a⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 0, a; 0, a⁻¹, 1] := by
    rw [coe_mul', coe_rootElt (show (1 : Fin 3) ≠ 2 by decide),
      coe_rootElt (show (2 : Fin 3) ≠ 1 by decide)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply, haa, h2]
  have key : ∀ g : SL3 F, (g : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, a; 0, a⁻¹, 1] →
      g ^ 3 = 1 := by
    intro g hgM
    apply Subtype.ext
    change ((g ^ 3 : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F)
    rw [pow_three, coe_mul', coe_mul', hgM, coe_one_SL3]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, haa, haa', CharTwo.add_self_eq_zero]
  exact key _ hM

end CFSG.Quasithin.MS93.S46.X3
