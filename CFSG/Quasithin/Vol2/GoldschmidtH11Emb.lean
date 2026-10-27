module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Hilb

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

@[expose] noncomputable def embK (a : ℕ) : SL(2, (Kf a : Subfield F)) →* SL(2, F) :=
  Matrix.SpecialLinearGroup.map (Kf a : Subfield F).subtype

omit [Finite F] in
theorem coe_embK (γ : SL(2, (Kf a : Subfield F))) (i j : Fin 2) :
    (embK a γ : Matrix (Fin 2) (Fin 2) F) i j =
      ((γ : Matrix (Fin 2) (Fin 2) (Kf a : Subfield F)) i j : F) := by
  simp [embK, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

omit [Finite F] in
theorem embK_injective : Function.Injective (embK (F := F) a) := by
  intro γ δ hγδ
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun (congrArg Subtype.val hγδ) i) j
  rw [coe_embK, coe_embK] at this
  exact this

omit [Finite F] in
theorem embK_uSL (d : (Kf a : Subfield F)) : embK a (uSL d) = uSL (d : F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_embK, coe_uSL]

theorem sgMap_embK (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, (Kf a : Subfield F))) :
    sgMap h (embK a γ) = embK a γ := by
  apply Subtype.ext
  ext i j
  rw [sgMap_apply, coe_embK]
  exact (mem_Kf a).mp (γ i j).2

theorem exists_embK (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) (hγ : sgMap h γ = γ) :
    ∃ γ' : SL(2, (Kf a : Subfield F)), embK a γ' = γ := by
  have hmem : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) F) i j ∈ (Kf a : Subfield F) := fun i j => by
    have := congrFun (congrFun (congrArg Subtype.val hγ) i) j
    rw [sgMap_apply] at this
    exact (mem_Kf a).mpr this
  let M : Matrix (Fin 2) (Fin 2) (Kf a : Subfield F) := Matrix.of fun i j => ⟨γ i j, hmem i j⟩
  have hdet : M.det = 1 := by
    apply (Kf a : Subfield F).subtype.injective
    rw [RingHom.map_det]
    have : (Kf a : Subfield F).subtype.mapMatrix M = (γ : Matrix (Fin 2) (Fin 2) F) := by
      ext i j; rfl
    rw [this, γ.2]
    simp
  obtain ⟨γ', hγ'⟩ : ∃ γ' : SL(2, (Kf a : Subfield F)),
      (γ' : Matrix (Fin 2) (Fin 2) (Kf a : Subfield F)) = M := ⟨⟨M, hdet⟩, rfl⟩
  refine ⟨γ', ?_⟩
  apply Subtype.ext
  ext i j
  rw [coe_embK, hγ']
  rfl

end CFSG.Quasithin.H11
