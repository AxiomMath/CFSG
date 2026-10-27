module

public import CFSG.Sporadic.ThSchreier.Transporter
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.PlaneSepDataInputs
public import Certificates.Certificate2319
public import Certificates.Certificate1022

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def sepFRows : Array V4 := Array.ofFn (n := 248) fun i => v4OfNat (sepFNats.getD i.val 0)

noncomputable abbrev sepF : Matrix (Fin 248) (Fin 248) (ZMod 2) := rowsMatrix sepFRows

@[expose] noncomputable def sepBeta (v w : RowV) : ZMod 2 :=
  Matrix.vecMul (ofRow v) sepF ⬝ᵥ ofRow w

@[expose] noncomputable def sepT (i : ℕ) : J := wordG (pairLetters a b) (sepWords.getD i [])

@[expose] noncomputable def sepW (i : ℕ) : Set RowV := sepT i • planeWSet

@[expose] def sepC (j : ℕ) : RowV := toRow (rowOfNat (sepRowNats.getD j 0))

@[expose] def sepCRows : Array V4 :=
  Array.ofFn (n := 248) fun j => v4OfNat (sepRowNats.getD j.val 0)

noncomputable abbrev sepCMat : Matrix (Fin 248) (Fin 248) (ZMod 2) := rowsMatrix sepCRows

@[expose] noncomputable def sepK (i j : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun a b => sepBeta (sepC (2 * i + a)) (sepC (2 * j + b))

private theorem native_sep_lists :
    sepFNats.length = 248 ∧ (∀ n ∈ sepFNats, n < 2 ^ 248) ∧ sepWords.length = 124 ∧
    (∀ w ∈ sepWords, ∀ l ∈ w, l = 1 ∨ l = 2) ∧ sepRowNats.length = 248 ∧
    (∀ n ∈ sepRowNats, n < 2 ^ 248) ∧ sepWords.getD 0 [] = [] :=
  Certificates.certificate2319

theorem sepFNats_length : sepFNats.length = 248 := native_sep_lists.1

theorem sepFNats_lt : ∀ n ∈ sepFNats, n < 2 ^ 248 := native_sep_lists.2.1

theorem sepWords_length : sepWords.length = 124 := native_sep_lists.2.2.1

theorem sepWords_letters : ∀ w ∈ sepWords, ∀ l ∈ w, l = 1 ∨ l = 2 := native_sep_lists.2.2.2.1

theorem sepRowNats_length : sepRowNats.length = 248 := native_sep_lists.2.2.2.2.1

theorem sepRowNats_lt : ∀ n ∈ sepRowNats, n < 2 ^ 248 := native_sep_lists.2.2.2.2.2.1

theorem sepWords_zero : sepWords.getD 0 [] = [] := native_sep_lists.2.2.2.2.2.2

theorem cert_Th_plane_separation_data :
    sepFNats.length = 248 ∧ (∀ n ∈ sepFNats, n < 2 ^ 248) ∧ sepWords.length = 124 ∧
    (∀ w ∈ sepWords, ∀ l ∈ w, l = 1 ∨ l = 2) ∧ sepRowNats.length = 248 ∧
    (∀ n ∈ sepRowNats, n < 2 ^ 248) ∧
    (∀ i, sepW i = sepT i • planeWSet) ∧
    (∀ i j : ℕ, ∀ a b : Fin 2, sepK i j a b = sepBeta (sepC (2 * i + a)) (sepC (2 * j + b))) :=
  ⟨sepFNats_length, sepFNats_lt, sepWords_length, sepWords_letters, sepRowNats_length,
    sepRowNats_lt, fun _ => rfl, fun _ _ _ _ => rfl⟩

end CFSG.Sporadic.ThSchreier
