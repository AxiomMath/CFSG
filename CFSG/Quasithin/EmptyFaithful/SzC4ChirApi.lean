module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.Quasithin.SzC4

structure ChiAPI : Type 1 where
  chi : (M : Type) → [Group M] → [Finite M] → MulAut M → ℤ
  chi_one : ∀ (M : Type) [Group M] [Finite M], chi M 1 = 0
  chi_congr : ∀ {M M' : Type} [Group M] [Group M'] [Finite M] [Finite M'] (e : M ≃* M')
    (φ : MulAut M) (φ' : MulAut M'), (∀ x : M, e (φ x) = φ' (e x)) → chi M' φ' = chi M φ
  chi_exact : ∀ {A M B : Type} [Group A] [Group M] [Group B] [Finite A] [Finite M] [Finite B],
    IsPGroup 2 M → ∀ (ι : A →* M) (π : M →* B), Function.Injective ι → Function.Surjective π →
      ι.range = π.ker → ∀ (φA : MulAut A) (φM : MulAut M) (φB : MulAut B), φM ^ 7 = 1 →
        (∀ a : A, φM (ι a) = ι (φA a)) → (∀ m : M, π (φM m) = φB (π m)) →
          chi M φM = chi A φA + chi B φB
  chiMat : ∀ {F : Type} [Field F] [Fintype F], Matrix (Fin 3) (Fin 3) F → ℤ
  vecAut : ∀ {F : Type} [Field F] (k : ℕ) (B : Matrix (Fin 3) (Fin 3) F), B ^ 7 = 1 →
    MulAut (Multiplicative (Fin k → Fin 3 → F))
  vecAut_apply : ∀ {F : Type} [Field F] (k : ℕ) (B : Matrix (Fin 3) (Fin 3) F) (hB : B ^ 7 = 1)
    (x : Multiplicative (Fin k → Fin 3 → F)) (i : Fin k),
    Multiplicative.toAdd (vecAut k B hB x) i = B.mulVec (Multiplicative.toAdd x i)
  chi_vecAut : ∀ {F : Type} [Field F] [Fintype F], Fintype.card F = 2 → ∀ (k : ℕ)
    (B : Matrix (Fin 3) (Fin 3) F) (hB : B ^ 7 = 1),
    chi (Multiplicative (Fin k → Fin 3 → F)) (vecAut k B hB) = k * chiMat B
  chiMat_ne_zero : ∀ {F : Type} [Field F] [Fintype F], Fintype.card F = 2 →
    ∀ (B : Matrix (Fin 3) (Fin 3) F), B ^ 7 = 1 → B ≠ 1 → chiMat B ≠ 0
  chiMat_inv_transpose : ∀ {F : Type} [Field F] [Fintype F], Fintype.card F = 2 →
    ∀ (B : Matrix (Fin 3) (Fin 3) F), B ^ 7 = 1 → chiMat ((B ^ 6).transpose) = - chiMat B

end CFSG.Quasithin.SzC4
