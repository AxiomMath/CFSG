module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

namespace Tensor

open Matrix

section Commutant

variable {K : Type} [Field K]

@[expose] def slU (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def slW [CharP K 2] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

@[expose] def slD (x : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(x : K), 0; 0, ((x⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem slU_mulVec (t : K) (v : Fin 2 → K) :
    ((slU t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      ![v 0 + t * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [slU, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem slW_mulVec [CharP K 2] (v : Fin 2 → K) :
    ((slW : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 1, v 0] := by
  ext i
  fin_cases i <;> simp [slW, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem slD_mulVec (x : Kˣ) (v : Fin 2 → K) :
    ((slD x : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      ![(x : K) * v 0, ((x⁻¹ : Kˣ) : K) * v 1] := by
  ext i
  fin_cases i <;> simp [slD, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem commutant_sl2 [CharP K 2] (S : (Fin 2 → K) → (Fin 2 → K))
    (hadd : ∀ u v, S (u + v) = S u + S v)
    (hcomm : ∀ (A : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      S ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ S v) :
    ∃ a : K, ∀ v, S v = a • v := by
  have hS0 : S 0 = 0 := by
    have := hadd 0 0
    simpa using this
  obtain ⟨a, b, hab⟩ : ∃ a b : K, S ![1, 0] = ![a, b] :=
    ⟨S ![1, 0] 0, S ![1, 0] 1, by ext i; fin_cases i <;> rfl⟩
  have hb : b = 0 := by
    have h1 := hcomm (slU 1) ![1, 0]
    rw [slU_mulVec] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at h1
    rw [hab, slU_mulVec] at h1
    have h2 := congrFun h1 0
    simp at h2
    exact h2
  subst hb
  have hx0 : ∀ x : K, S ![x, 0] = ![x * a, 0] := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have : (![0, 0] : Fin 2 → K) = 0 := by ext i; fin_cases i <;> rfl
      rw [this, hS0]
      ext i
      fin_cases i <;> simp
    · have h1 := hcomm (slD (Units.mk0 x hx)) ![1, 0]
      rw [slD_mulVec] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, Units.val_mk0] at h1
      rw [hab, slD_mulVec] at h1
      simpa using h1
  have hx1 : ∀ y : K, S ![0, y] = ![0, y * a] := by
    intro y
    have h1 := hcomm slW ![y, 0]
    rw [slW_mulVec] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    rw [hx0 y, slW_mulVec] at h1
    simpa using h1
  refine ⟨a, fun v => ?_⟩
  have hv : v = ![v 0, 0] + ![0, v 1] := by
    ext i
    fin_cases i <;> simp
  rw [hv, hadd, hx0, hx1]
  ext i
  fin_cases i <;> simp [mul_comm]

end Commutant

section RightMul

variable {K : Type} [Field K]

@[expose] def colOf (j : Fin 2) (X : Matrix (Fin 2) (Fin 2) K) : Fin 2 → K := fun r => X r j

@[expose] def colEmb (j : Fin 2) (v : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun r c => if c = j then v r else 0

theorem colOf_mul (A X : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) :
    colOf j (A * X) = A *ᵥ colOf j X := by
  ext r
  simp [colOf, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem colOf_add (X Y : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) :
    colOf j (X + Y) = colOf j X + colOf j Y := rfl

theorem mul_colEmb (A : Matrix (Fin 2) (Fin 2) K) (j : Fin 2) (v : Fin 2 → K) :
    A * colEmb j v = colEmb j (A *ᵥ v) := by
  ext r c
  by_cases hc : c = j
  · subst hc
    simp [colEmb, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp [colEmb, Matrix.mul_apply, hc]

theorem colEmb_add (j : Fin 2) (u v : Fin 2 → K) :
    colEmb j (u + v) = colEmb j u + colEmb j v := by
  ext r c
  by_cases hc : c = j <;> simp [colEmb, hc]

theorem eq_colEmb_add (X : Matrix (Fin 2) (Fin 2) K) :
    X = colEmb 0 (colOf 0 X) + colEmb 1 (colOf 1 X) := by
  ext r c
  fin_cases c <;> simp [colEmb, colOf]

theorem exists_mul_of_commute_sl2 [CharP K 2]
    (T : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K)
    (hadd : ∀ X Y, T (X + Y) = T X + T Y)
    (hcomm : ∀ (A : SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K),
      T (A * X) = A * T X) :
    ∃ B : Matrix (Fin 2) (Fin 2) K, ∀ X, T X = X * B := by
  have key : ∀ i j : Fin 2, ∃ a : K, ∀ v : Fin 2 → K, colOf i (T (colEmb j v)) = a • v := by
    intro i j
    refine commutant_sl2 (fun v => colOf i (T (colEmb j v))) (fun u v => ?_) (fun A v => ?_)
    · simp only [colEmb_add, hadd, colOf_add]
    · simp only [← mul_colEmb, hcomm, colOf_mul]
  choose a ha using key
  refine ⟨Matrix.of fun j i => a i j, fun X => ?_⟩
  ext r i
  have h1 := congrFun (congrArg (colOf i) (congrArg T (eq_colEmb_add X))) r
  rw [hadd, colOf_add, Pi.add_apply, ha, ha] at h1
  simp only [colOf] at h1 ⊢
  rw [h1]
  simp [colOf, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end RightMul

section Rigidity

variable {K : Type} [Field K] [Finite K]

theorem card_specialLinear_of_card_four (hK : Nat.card K = 4) :
    Nat.card (SpecialLinearGroup (Fin 2) K) = 60 := by
  let _ := Fintype.ofFinite K
  have hq : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_SL_field, hq, Fin.prod_univ_two]
  norm_num

theorem exists_mulEquiv_specialLinear {G : Type*} [Group G] (hK : Nat.card K = 4)
    (hperf : commutator G = ⊤) (hcard : Nat.card G = 60)
    (f : G →* Matrix (Fin 2) (Fin 2) K) (hf : Function.Injective f) :
    ∃ α : G ≃* SpecialLinearGroup (Fin 2) K,
      ∀ g, ((α g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = f g := by
  let fu : G →* GL (Fin 2) K := f.toHomUnits
  have hdet : ∀ g, (f g).det = 1 := by
    intro g
    have hle := Abelianization.commutator_subset_ker (Matrix.GeneralLinearGroup.det.comp fu)
    rw [hperf] at hle
    have h1 := MonoidHom.mem_ker.1 (hle (Subgroup.mem_top g))
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa [fu, Matrix.GeneralLinearGroup.val_det_apply] using h2
  let mk : G → SpecialLinearGroup (Fin 2) K := fun g => ⟨f g, hdet g⟩
  have hmk : ∀ g, ((mk g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = f g :=
    fun g => rfl
  let f' : G →* SpecialLinearGroup (Fin 2) K :=
    { toFun := mk
      map_one' := by
        have h : ((mk 1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
            ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [hmk, Matrix.SpecialLinearGroup.coe_one, map_one]
        exact Subtype.ext h
      map_mul' := fun a b => by
        have h : ((mk (a * b) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
            ((mk a * mk b : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, hmk, hmk, hmk, map_mul]
        exact Subtype.ext h }
  have hinj : Function.Injective f' := fun a b h => hf (congrArg Subtype.val h)
  have hbij : Function.Bijective f' :=
    (Nat.bijective_iff_injective_and_card f').2
      ⟨hinj, by rw [hcard, card_specialLinear_of_card_four hK]⟩
  exact ⟨MulEquiv.ofBijective f' hbij, fun g => rfl⟩

end Rigidity

end Tensor

end SzG11S

end G11

end CFSG.Quasithin
