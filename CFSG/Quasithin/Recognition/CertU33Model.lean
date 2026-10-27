module

public import CFSG.Quasithin.Recognition.CertF9
public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

open scoped Matrix

namespace CFSG.Quasithin

open CFSG.CosetTable

@[expose] def matOfDigits (rows : List (List ℕ)) : Matrix (Fin 3) (Fin 3) GF9 :=
  Matrix.of fun i j => GF9.ofNat' ((rows.getD i []).getD j 0)

@[expose] def u33Digits : List (List (List ℕ)) :=
  [[[2, 1, 8], [3, 7, 3], [8, 1, 2]], [[1, 4, 8], [5, 2, 4], [8, 7, 8]],
    [[2, 0, 0], [6, 1, 0], [2, 3, 2]], [[1, 6, 1], [3, 2, 0], [1, 0, 0]],
    [[6, 2, 6], [7, 7, 1], [3, 8, 8]]]

@[expose] def u33InvDigits : List (List (List ℕ)) :=
  [[[2, 6, 5], [1, 4, 1], [5, 6, 2]], [[5, 7, 5], [4, 2, 7], [5, 8, 1]],
    [[2, 0, 0], [6, 1, 0], [2, 3, 2]], [[0, 0, 1], [0, 2, 3], [1, 6, 1]],
    [[5, 1, 3], [5, 4, 2], [6, 4, 3]]]

@[expose] def u33M (i : Fin 5) : Matrix (Fin 3) (Fin 3) GF9 := matOfDigits (u33Digits.getD i [])

@[expose] def u33Minv (i : Fin 5) : Matrix (Fin 3) (Fin 3) GF9 :=
  matOfDigits (u33InvDigits.getD i [])

@[expose] def antidiag3 : Matrix (Fin 3) (Fin 3) GF9 := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem u33M_mul_inv : ∀ i : Fin 5, u33M i * u33Minv i = 1 ∧ u33Minv i * u33M i = 1 := by
  decide +kernel

theorem u33M_unitary : ∀ i : Fin 5,
    ((u33M i).map fun x => x ^ 3)ᵀ * antidiag3 * u33M i = antidiag3 := by
  decide +kernel

theorem u33M_det : ∀ i : Fin 5, (u33M i).det = 1 := by decide +kernel

theorem u33M_relators : ∀ w ∈ u33PresRels,
    (w.map fun l => cond l.2 (u33M l.1) (u33Minv l.1)).prod = 1 := by
  decide +kernel

@[expose] def u33GL (i : Fin 5) : GL (Fin 3) GF9 :=
  ⟨u33M i, u33Minv i, (u33M_mul_inv i).1, (u33M_mul_inv i).2⟩

theorem coe_prod_u33GL (w : List (Fin 5 × Bool)) :
    (((w.map fun l => cond l.2 (u33GL l.1) (u33GL l.1)⁻¹).prod : GL (Fin 3) GF9) :
      Matrix (Fin 3) (Fin 3) GF9) = (w.map fun l => cond l.2 (u33M l.1) (u33Minv l.1)).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    cases l.2 <;> rfl

noncomputable def u33GLHom : PG 5 u33PresRels →* GL (Fin 3) GF9 :=
  PresentedGroup.toGroup (f := u33GL) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    apply Units.ext
    rw [coe_prod_u33GL, Units.val_one]
    exact u33M_relators w hw)

theorem u33GLHom_of (i : Fin 5) : u33GLHom (PresentedGroup.of i) = u33GL i := by
  rw [u33GLHom, PresentedGroup.toGroup.of]

end CFSG.Quasithin
