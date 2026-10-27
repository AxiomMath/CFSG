module

public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Classical.OrthogonalOrderThree
public import Mathlib.RingTheory.RootsOfUnity.Basic
import CFSG.RankThree.CentralCover.HigherClassicalFourGroupWitness
import CFSG.LieType.Universal.SpinOmega.Kernel
import CFSG.RankThree.CentralCover.SymplecticFourGroupWitness
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open

variable (n : ℕ) (F₀ : Type) [Field F₀]

@[expose] noncomputable def diagGL3 : F₀ˣ × F₀ˣ →* GL (Fin 3) F₀ :=
  (Units.map (Matrix.diagonalRingHom (Fin 3) F₀).toMonoidHom).comp
    (MulEquiv.piUnits.symm.toMonoidHom.comp
      (MonoidHom.pi ![MonoidHom.fst F₀ˣ F₀ˣ, MonoidHom.snd F₀ˣ F₀ˣ,
        (MonoidHom.fst F₀ˣ F₀ˣ * MonoidHom.snd F₀ˣ F₀ˣ)⁻¹]))

theorem coe_diagGL3 (x : F₀ˣ × F₀ˣ) :
    ((diagGL3 F₀ x : GL (Fin 3) F₀) : Matrix (Fin 3) (Fin 3) F₀) =
      Matrix.diagonal ![(x.1 : F₀), (x.2 : F₀), (((x.1 * x.2)⁻¹ : F₀ˣ) : F₀)] := by
  change Matrix.diagonal _ = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem diagGL3_mem_statedSU {a b : F₀ˣ} (ha : a ^ (2 ^ n + 1) = 1) (hb : b ^ (2 ^ n + 1) = 1) :
    diagGL3 F₀ (a, b) ∈ StatedSU 3 (2 ^ n) F₀ := by
  have key : ∀ u : F₀ˣ, u ^ (2 ^ n + 1) = 1 → (u : F₀) ^ 2 ^ n * u = 1 := fun u hu => by
    rw [← pow_succ, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hab : ((a * b)⁻¹) ^ (2 ^ n + 1) = 1 := by rw [inv_pow, mul_pow, ha, hb, mul_one, inv_one]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [coe_diagGL3, det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Units.val_inv_eq_inv_val, Units.val_mul]
    field_simp
  · rw [coe_diagGL3, diagonal_map (f := fun x : F₀ => x ^ 2 ^ n) (by simp), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · exact key a ha
    · exact key b hb
    · exact key _ hab

@[expose] noncomputable def diagSU :
    rootsOfUnity (2 ^ n + 1) F₀ × rootsOfUnity (2 ^ n + 1) F₀ →* ↥(StatedSU 3 (2 ^ n) F₀) :=
  ((diagGL3 F₀).comp ((rootsOfUnity (2 ^ n + 1) F₀).subtype.prodMap
    (rootsOfUnity (2 ^ n + 1) F₀).subtype)).codRestrict _ fun x =>
      diagGL3_mem_statedSU n F₀ ((mem_rootsOfUnity _ _).1 x.1.2) ((mem_rootsOfUnity _ _).1 x.2.2)

theorem coe_diagSU (x : rootsOfUnity (2 ^ n + 1) F₀ × rootsOfUnity (2 ^ n + 1) F₀) :
    (((diagSU n F₀ x : ↥(StatedSU 3 (2 ^ n) F₀)) : GL (Fin 3) F₀) : Matrix (Fin 3) (Fin 3) F₀) =
      Matrix.diagonal ![((x.1 : F₀ˣ) : F₀), ((x.2 : F₀ˣ) : F₀),
        ((((x.1 : F₀ˣ) * (x.2 : F₀ˣ))⁻¹ : F₀ˣ) : F₀)] :=
  coe_diagGL3 F₀ _

theorem permGL_mem_statedSU_three [CharP F₀ 2] (π : Equiv.Perm (Fin 3)) :
    CFSG.RankThree.Classical.permGL π ∈ StatedSU 3 (2 ^ n) F₀ :=
  CFSG.RankThree.CentralCover.permGL_mem_statedSU (pow_ne_zero n two_ne_zero) π

@[expose] noncomputable def permSU [CharP F₀ 2] : Equiv.Perm (Fin 3) →* ↥(StatedSU 3 (2 ^ n) F₀) :=
  (CFSG.RankThree.Classical.permGL (ι := Fin 3) (K := F₀)).codRestrict (StatedSU 3 (2 ^ n) F₀)
    (permGL_mem_statedSU_three n F₀)

theorem coe_permSU [CharP F₀ 2] (π : Equiv.Perm (Fin 3)) :
    ((permSU n F₀ π : ↥(StatedSU 3 (2 ^ n) F₀)) : GL (Fin 3) F₀) =
      CFSG.RankThree.Classical.permGL π :=
  rfl

end CFSG.LocalAnalysis.WeakClosure81

end
