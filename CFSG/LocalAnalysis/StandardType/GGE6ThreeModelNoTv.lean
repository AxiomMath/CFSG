module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModule
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm

public section

open scoped Matrix

namespace CFSG.StandardType.TableBExc.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private abbrev X := Fin 5 → ZMod 3

private def S : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  Matrix.of fun i j => ((Tag.E6.cartan (Fin.castSucc i) (Fin.castSucc j) : ℤ) : ZMod 3)

private def C5 : Matrix (Fin 5) (Fin Tag.E6.rank) (ZMod 3) :=
  Matrix.of fun j k => ((Tag.E6.cartan (Fin.castSucc j) k : ℤ) : ZMod 3)

private def v5 : X := ![1, 0, 2, 0, 1]

private def RmC (j : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  Matrix.of fun a b => (if a = b then 1 else 0) - (if a = j then S j b else 0)

private def RmL : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  Matrix.of fun a b => (if a = b then 1 else 0) - (if b = 4 then 2 * v5 a else 0)

private theorem S_symm : Sᵀ = S := by decide +kernel

private theorem S_det : S.det ≠ 0 := by decide +kernel

private theorem B_mem : ∀ c : X, NoOffRest.kDotP 3 (c ᵥ* C5) = 0 := by decide +kernel

private theorem B_inj : ∀ c : X, c ᵥ* C5 = 0 → c = 0 := by decide +kernel

private theorem refl_cast : ∀ (j : Fin 5) (c : X),
    adRefl .E6 3 (Fin.castSucc j) (c ᵥ* C5) = (RmC j *ᵥ c) ᵥ* C5 := by decide +kernel

private theorem refl_last : ∀ c : X,
    adRefl .E6 3 (Fin.last 5) (c ᵥ* C5) = (RmL *ᵥ c) ᵥ* C5 := by decide +kernel

private theorem form_cast : ∀ j : Fin 5, (RmC j)ᵀ * S * RmC j = S := by decide +kernel

private theorem form_last : RmLᵀ * S * RmL = S := by decide +kernel

private theorem exists_refl (i : Fin Tag.E6.rank) : ∃ R : Matrix (Fin 5) (Fin 5) (ZMod 3),
    (∀ c : X, adRefl .E6 3 i (c ᵥ* C5) = (R *ᵥ c) ᵥ* C5) ∧ Rᵀ * S * R = S := by
  fin_cases i
  · exact ⟨RmC 0, refl_cast 0, form_cast 0⟩
  · exact ⟨RmC 1, refl_cast 1, form_cast 1⟩
  · exact ⟨RmC 2, refl_cast 2, form_cast 2⟩
  · exact ⟨RmC 3, refl_cast 3, form_cast 3⟩
  · exact ⟨RmC 4, refl_cast 4, form_cast 4⟩
  · exact ⟨RmL, refl_last, form_last⟩

private theorem exists_matrix (u : WeylGroup .E6) :
    ∃ M : Matrix (Fin 5) (Fin 5) (ZMod 3),
      (∀ c : X, adAct .E6 3 u (c ᵥ* C5) = (M *ᵥ c) ᵥ* C5) ∧ Mᵀ * S * M = S := by
  refine weyl_induction (fun u => ∃ M : Matrix (Fin 5) (Fin 5) (ZMod 3),
    (∀ c : X, adAct .E6 3 u (c ᵥ* C5) = (M *ᵥ c) ᵥ* C5) ∧ Mᵀ * S * M = S)
    ⟨1, fun c => ?_, by simp⟩ ?_ u
  · rw [adAct_one, Matrix.one_mulVec]
  · rintro i w ⟨M, hM1, hM2⟩
    obtain ⟨R, hR1, hR2⟩ := exists_refl i
    refine ⟨R * M, fun c => ?_, ?_⟩
    · rw [adAct_mul, adAct_simple, hM1, hR1, Matrix.mulVec_mulVec]
    · calc (R * M)ᵀ * S * (R * M) = Mᵀ * (Rᵀ * S * R) * M := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = S := by rw [hR2, hM2]

private theorem card_X : Nat.card X = 3 ^ 5 := by
  rw [Nat.card_pi]
  simp [Nat.card_zmod]

theorem not_isTransvection_hypE6 (c : ZMod 3) (hc : c ≠ 0) (u : WeylGroup .E6)
    (t : NoOffRest.hypE6 →+ NoOffRest.hypE6)
    (ht : ∀ x : NoOffRest.hypE6, ((t x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) =
      c • adAct .E6 3 u (x : Fin Tag.E6.rank → ZMod 3))
    (hfix : Nat.card {x : NoOffRest.hypE6 // t x = x} * 3 = Nat.card NoOffRest.hypE6)
    (hN : ∀ x : NoOffRest.hypE6, t (t x - x) = t x - x) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨M, hM1, hM2⟩ := exists_matrix u
  let Bhom : X →+ (Fin Tag.E6.rank → ZMod 3) := (Matrix.vecMulLinear C5).toAddMonoidHom
  have hBhom : ∀ x : X, Bhom x = x ᵥ* C5 := fun x => rfl
  have hBmem : ∀ x : X, Bhom x ∈ NoOffRest.hypE6 := fun x => by
    rw [NoOffRest.mem_hypE6, hBhom]
    exact B_mem x
  let Bcod : X →+ NoOffRest.hypE6 := Bhom.codRestrict NoOffRest.hypE6 hBmem
  have hBinj : Function.Injective Bcod := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply B_inj
    rw [← hBhom]
    exact congrArg Subtype.val hx
  have hBbij : Function.Bijective Bcod :=
    hBinj.bijective_of_nat_card_le (by rw [NoOffRest.card_hypE6, card_X])
  let eB : X ≃+ NoOffRest.hypE6 := AddEquiv.ofBijective Bcod hBbij
  have heB_val : ∀ x : X, ((eB x : NoOffRest.hypE6) : Fin Tag.E6.rank → ZMod 3) = x ᵥ* C5 :=
    fun x => rfl
  let t' : X →+ X := AddMonoidHom.mk' (fun x => c • (M *ᵥ x)) (by
    intro x y
    rw [Matrix.mulVec_add, smul_add])
  have ht'_apply : ∀ x : X, t' x = c • (M *ᵥ x) := fun x => rfl
  have heB : ∀ x : X, eB (t' x) = t (eB x) := by
    intro x
    apply Subtype.ext
    rw [ht (eB x), heB_val, heB_val, ht'_apply, hM1, Matrix.smul_vecMul]
  have hform : ∀ x y : X, (M *ᵥ x) ⬝ᵥ (S *ᵥ (M *ᵥ y)) = x ⬝ᵥ (S *ᵥ y) := by
    intro x y
    calc (M *ᵥ x) ⬝ᵥ (S *ᵥ (M *ᵥ y))
        = (x ᵥ* Mᵀ) ⬝ᵥ (S *ᵥ (M *ᵥ y)) := by rw [Matrix.vecMul_transpose]
      _ = x ⬝ᵥ (Mᵀ *ᵥ (S *ᵥ (M *ᵥ y))) := by rw [← Matrix.dotProduct_mulVec]
      _ = x ⬝ᵥ ((Mᵀ * S * M) *ᵥ y) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ (S *ᵥ y) := by rw [hM2]
  have hB : ∀ x y : X, t' x ⬝ᵥ (S *ᵥ t' y) = (c * c) * (x ⬝ᵥ (S *ᵥ y)) := by
    intro x y
    rw [ht'_apply, ht'_apply, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hform,
      smul_eq_mul, smul_eq_mul]
    ring
  have hcardfix : Nat.card {x : X // t' x = x} = Nat.card {y : NoOffRest.hypE6 // t y = y} := by
    refine Nat.card_congr (Equiv.subtypeEquiv eB.toEquiv ?_)
    intro x
    constructor
    · intro hx
      change t (eB x) = eB x
      rw [← heB x, hx]
    · intro hy
      change t (eB x) = eB x at hy
      apply eB.injective
      rw [heB x]
      exact hy
  have hcardX : Nat.card NoOffRest.hypE6 = Nat.card X := Nat.card_congr eB.toEquiv.symm
  have hfix' : Nat.card {x : X // t' x = x} * 3 = Nat.card (Fin 5 → ZMod 3) := by
    rw [hcardfix, hfix, hcardX]
  have hN' : ∀ x : X, t' (t' x - x) = t' x - x := by
    intro x
    apply eB.injective
    calc eB (t' (t' x - x)) = t (eB (t' x - x)) := heB _
      _ = t (t (eB x) - eB x) := by rw [map_sub, heB]
      _ = t (eB x) - eB x := hN (eB x)
      _ = eB (t' x - x) := by rw [map_sub, heB]
  exact NoTvAut.false_of_isTransvection_similitude (p := 3) (n := Fin 5) (by norm_num)
    S_symm S_det t' (c * c) hB hfix' hN'

end CFSG.StandardType.TableBExc.E6Three
