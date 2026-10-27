module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChiModVec
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.SzC4

open scoped Matrix

namespace ChiMod

section Transport

variable {F F' : Type} [Field F] [Field F']

theorem mulVec_map (e : F ≃+* F') (B : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) :
    B.map e *ᵥ (e ∘ v) = e ∘ (B *ᵥ v) :=
  funext fun i => ((e : F →+* F').map_mulVec B v i).symm

theorem comp_add_eq_zero_iff (e : F ≃+* F') (a b c : Fin 3 → F) :
    e ∘ a + e ∘ b + e ∘ c = 0 ↔ a + b + c = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h i
    simp only [Function.comp_apply, Pi.add_apply, Pi.zero_apply] at this ⊢
    rw [← map_add, ← map_add] at this
    exact (map_eq_zero_iff e e.injective).1 this
  · intro h
    funext i
    have := congrFun h i
    simp only [Function.comp_apply, Pi.add_apply, Pi.zero_apply] at this ⊢
    rw [← map_add, ← map_add, this, map_zero]

theorem mem_kerP_map (e : F ≃+* F') (B : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) :
    (e ∘ v) ∈ kerP (B.map e) ↔ v ∈ kerP B := by
  simp only [kerP, Set.mem_ofPred_eq, mulVec_map]
  exact comp_add_eq_zero_iff e _ _ _

theorem mem_kerT_map (e : F ≃+* F') (B : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) :
    (e ∘ v) ∈ kerT (B.map e) ↔ v ∈ kerT B := by
  simp only [kerT, Set.mem_ofPred_eq, mulVec_map]
  exact comp_add_eq_zero_iff e _ _ _

theorem card_kerP_map (e : F ≃+* F') (B : Matrix (Fin 3) (Fin 3) F) :
    Nat.card (kerP (B.map e)) = Nat.card (kerP B) :=
  (Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ : Fin 3 => e.toEquiv)
    fun v => (mem_kerP_map e B v).symm)).symm

theorem card_kerT_map (e : F ≃+* F') (B : Matrix (Fin 3) (Fin 3) F) :
    Nat.card (kerT (B.map e)) = Nat.card (kerT B) :=
  (Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ : Fin 3 => e.toEquiv)
    fun v => (mem_kerT_map e B v).symm)).symm

end Transport

section Count

def kcP (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ℕ :=
  (Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
    B *ᵥ (B *ᵥ (B *ᵥ v)) + B *ᵥ (B *ᵥ v) + v = 0).card

def kcT (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ℕ :=
  (Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
    B *ᵥ (B *ᵥ (B *ᵥ v)) + B *ᵥ v + v = 0).card

theorem card_kerP_zmod (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Nat.card (kerP B) = kcP B := by
  have h : kerP B = ↑(Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
      B *ᵥ (B *ᵥ (B *ᵥ v)) + B *ᵥ (B *ᵥ v) + v = 0) := by
    ext v
    simp [kerP]
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, kcP]

theorem card_kerT_zmod (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Nat.card (kerT B) = kcT B := by
  have h : kerT B = ↑(Finset.univ.filter fun v : Fin 3 → ZMod 2 =>
      B *ᵥ (B *ᵥ (B *ᵥ v)) + B *ᵥ v + v = 0) := by
    ext v
    simp [kerT]
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset, kcT]

theorem fin_check :
    ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B ^ 7 = 1 →
      (kcP ((B ^ 6)ᵀ) = kcT B ∧ kcT ((B ^ 6)ᵀ) = kcP B) ∧
      (B ≠ 1 → (kcP B = 8 ∧ kcT B = 1) ∨ (kcP B = 1 ∧ kcT B = 8)) := by
  decide +kernel

end Count

theorem chiMat_map {F F' : Type} [Field F] [Field F'] (e : F ≃+* F')
    (B : Matrix (Fin 3) (Fin 3) F) : chiMat (B.map e) = chiMat B := by
  rw [chiMat, chiMat, card_kerP_map, card_kerT_map]

theorem chiMat_zmod (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    chiMat B = padicValNat 2 (kcP B) - padicValNat 2 (kcT B) := by
  rw [chiMat, card_kerP_zmod, card_kerT_zmod]

theorem chiMat_inv_transpose_zmod (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hB : B ^ 7 = 1) :
    chiMat ((B ^ 6)ᵀ) = - chiMat B := by
  obtain ⟨⟨h1, h2⟩, -⟩ := fin_check B hB
  rw [chiMat_zmod, chiMat_zmod, h1, h2]
  ring

theorem chiMat_ne_zero_zmod (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hB : B ^ 7 = 1)
    (hB1 : B ≠ 1) : chiMat B ≠ 0 := by
  obtain ⟨-, h⟩ := fin_check B hB
  have h8 : padicValNat 2 8 = 3 := by
    have := padicValNat.prime_pow (p := 2) 3
    simpa using this
  rw [chiMat_zmod]
  rcases h hB1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [h8]

theorem map_pow_seven_zmod {F : Type} [Field F] (e : F ≃+* ZMod 2) (B : Matrix (Fin 3) (Fin 3) F)
    (hB : B ^ 7 = 1) : (B.map e) ^ 7 = 1 := by
  have h := Matrix.map_pow B (e : F →+* ZMod 2) 7
  rw [hB, Matrix.map_one _ (map_zero _) (map_one _)] at h
  simpa using h.symm

end ChiMod

section General

variable {F : Type} [Field F] [Fintype F]

theorem chiMat_inv_transpose (hF : Fintype.card F = 2) (B : Matrix (Fin 3) (Fin 3) F)
    (hB : B ^ 7 = 1) : chiMat ((B ^ 6)ᵀ) = - chiMat B := by
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm
  have h1 : ((B ^ 6)ᵀ).map e = ((B.map e) ^ 6)ᵀ := by
    rw [Matrix.transpose_map]
    simpa using congrArg Matrix.transpose (Matrix.map_pow B (e : F →+* ZMod 2) 6)
  rw [← ChiMod.chiMat_map e ((B ^ 6)ᵀ), h1,
    ChiMod.chiMat_inv_transpose_zmod _ (ChiMod.map_pow_seven_zmod e B hB), ChiMod.chiMat_map]

theorem chiMat_ne_zero (hF : Fintype.card F = 2) (B : Matrix (Fin 3) (Fin 3) F) (hB : B ^ 7 = 1)
    (hB1 : B ≠ 1) : chiMat B ≠ 0 := by
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm
  have hBe : (B.map e).map e.symm = B := by
    ext i j
    simp
  rw [← ChiMod.chiMat_map e B]
  refine ChiMod.chiMat_ne_zero_zmod _ (ChiMod.map_pow_seven_zmod e B hB) fun h => hB1 ?_
  rw [← hBe, h, Matrix.map_one _ (map_zero _) (map_one _)]

end General

end CFSG.Quasithin.SzC4
