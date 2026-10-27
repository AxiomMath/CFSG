module

public import CFSG.Quasithin.EmptyFaithful.SzC4ChirApi
public import CFSG.Quasithin.EmptyFaithful.SzC4ChiGrpKey
public import CFSG.Quasithin.EmptyFaithful.SzC4ChiModImpl

public section

namespace CFSG.Quasithin.SzC4

theorem toAdd_vecAut_pow {F : Type} [Field F] (k : ℕ) (B : Matrix (Fin 3) (Fin 3) F)
    (hB : B ^ 7 = 1) (n : ℕ) (x : Multiplicative (Fin k → Fin 3 → F)) (i : Fin k) :
    Multiplicative.toAdd ((vecAut k B hB ^ n) x) i = (B ^ n).mulVec (Multiplicative.toAdd x i) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec]
    rfl

theorem vecAut_pow_seven {F : Type} [Field F] (k : ℕ) (B : Matrix (Fin 3) (Fin 3) F)
    (hB : B ^ 7 = 1) : vecAut k B hB ^ 7 = 1 := by
  refine MulEquiv.ext fun x => ?_
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_vecAut_pow, hB, Matrix.one_mulVec]
  rfl

theorem isExpTwo_vec2 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) (k : ℕ) :
    IsExpTwo (Multiplicative (Fin k → Fin 3 → F)) := by
  intro x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime hF
  apply Multiplicative.toAdd.injective
  funext i j
  simp [CharTwo.add_self_eq_zero]

theorem chi_vecAut_real {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) (k : ℕ)
    (B : Matrix (Fin 3) (Fin 3) F) (hB : B ^ 7 = 1) :
    chi deltaImpl (Multiplicative (Fin k → Fin 3 → F)) (vecAut k B hB) = k * chiMat B := by
  rw [chi_of_isExpTwo deltaImpl (Multiplicative (Fin k → Fin 3 → F)) (isExpTwo_vec2 hF k)
    (vecAut k B hB) (vecAut_pow_seven k B hB)]
  exact delta_vecAut hF k B hB

@[expose] noncomputable def chiAPI : ChiAPI where
  chi M _ _ φ := chi deltaImpl M φ
  chi_one M _ _ := chi_one deltaImpl M
  chi_congr e φ φ' h := chi_congr deltaImpl e φ φ' h
  chi_exact hM ι π hι hπ hex φA φM φB h7 h1 h2 :=
    chi_exact deltaImpl hM ι π hι hπ hex φA φM φB h7 h1 h2
  chiMat B := chiMat B
  vecAut k B hB := vecAut k B hB
  vecAut_apply _ _ _ _ _ := rfl
  chi_vecAut hF k B hB := chi_vecAut_real hF k B hB
  chiMat_ne_zero hF B hB hB1 := chiMat_ne_zero hF B hB hB1
  chiMat_inv_transpose hF B hB := chiMat_inv_transpose hF B hB

end CFSG.Quasithin.SzC4
