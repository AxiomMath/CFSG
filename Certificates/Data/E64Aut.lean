module

public import Certificates.Data.GH74.AE117
public import Certificates.Data.Holder255.E64Model

public section

namespace Certificates.E64Aut

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.E64Data Certificates.AE117

@[expose] def W0 (_ : Unit := ()) : List (Wr 7) :=
  [⟨vecOfN [2, 5], cycPerm [[2, 4], [5, 6]]⟩,
   ⟨vecOfN [2, 6], cycPerm [[2, 5], [4, 6]]⟩,
   ⟨vecOfN [2, 6], cycPerm [[2, 4], [5, 6]]⟩,
   ⟨vecOfN [2, 4], cycPerm [[2, 5], [4, 6]]⟩]

@[expose] def g0 (_ : Unit := ()) : Wr 7 :=
  ⟨vecOfN [0, 6], cycPerm [[0, 3, 2, 6, 4, 1, 5]]⟩

@[expose] def S0 (_ : Unit := ()) : List (Wr 7) := W0 () ++ [g0 ()]

@[expose] def rels : List (List ℕ) :=
  [[8, 3, 8, 3, 8, 3], [8, 1, 9, 9, 2, 9, 9, 2], [8, 0, 9, 2, 8, 3, 9, 3], [8, 1, 9, 6, 8, 3, 9, 7],
    [9, 9, 0, 9, 9, 0, 8, 3, 9], [5, 1, 9, 7, 8, 4, 9, 2, 8, 2], [8, 0, 5, 9, 0, 8, 4, 1, 9, 4],
    [3, 9, 1, 8, 2, 8, 8, 2, 9, 9], [8, 1, 3, 9, 2, 1, 8, 1, 2, 9, 0],
    [3, 1, 8, 2, 9, 4, 3, 1, 8, 4, 9, 4], [5, 0, 9, 1, 8, 7, 3, 9, 5, 3, 7, 8],
    [8, 2, 6, 9, 2, 7, 8, 2, 6, 9, 2, 7], [8, 7, 2, 9, 2, 2, 9, 0, 5, 8, 0, 5],
    [9, 1, 4, 8, 8, 6, 6, 9, 2, 7, 5, 1, 8, 0, 5, 9]]

@[expose] def words0 : List (List ℕ) :=
  [[], [7], [0, 3], [0, 9, 0, 2, 9, 3], [3, 8, 8, 6, 9, 5], [1], [4, 6], [8, 5, 9], [8, 2, 9], [5],
    [3], [0, 9, 0, 8, 1], [2, 9, 5, 8, 3], [9, 2, 8], [9, 4, 6, 8], [9, 2, 4, 8, 7, 9],
    [8, 8, 0, 8, 3], [0, 3, 9, 6, 8], [2, 9, 0, 8, 3], [8, 8, 2, 8, 1, 8], [3, 8, 2, 5, 8, 4],
    [0, 2, 9, 2, 8], [0, 9, 5, 8, 1], [2, 9, 1, 8, 0, 9], [9, 9, 7, 8, 8], [4], [2], [9, 5, 8],
    [9, 0, 2, 8], [0], [4, 7], [0, 8, 4, 9, 1], [0, 8, 3, 9, 1], [6], [0, 2], [9, 9, 4, 8, 8],
    [9, 1, 9, 9, 2], [0, 0], [9, 0, 8], [9, 6, 8], [9, 9, 0, 8, 8], [2, 9, 4, 8, 4, 9], [9, 1, 8],
    [9, 7, 8], [8, 0, 3, 9], [8, 6, 9], [0, 3, 9, 3, 8], [0, 9, 4, 8, 1], [3, 8, 0, 3, 9],
    [0, 8, 7, 9, 1], [0, 2, 9, 7, 8], [2, 9, 1, 8, 3], [8, 4, 7, 9], [8, 0, 9], [9, 4, 8],
    [0, 9, 1, 8, 1], [2, 9, 4, 8, 3], [9, 0, 3, 8], [0, 0, 9, 0, 0, 8], [9, 3, 8], [9, 4, 7, 8],
    [2, 8, 4, 7, 9], [0, 8, 1, 9, 1], [9, 0, 0, 8], [8, 4, 6, 9], [2, 8, 0, 9, 1, 8], [8, 1, 9],
    [2, 4, 8, 8, 6, 9], [3, 8, 4, 6, 9], [0, 8, 0, 9, 1], [2, 8, 4, 9, 4, 8], [2, 9, 1, 9, 9],
    [8, 0, 2, 9], [9, 9, 1, 8, 8], [8, 4, 9, 4, 8, 2], [8, 7, 9], [9, 9, 5, 8, 8], [3, 8, 8, 0, 8],
    [0, 2, 8, 8, 3, 9], [2, 5, 8, 2, 5, 8], [2, 8, 2, 8, 2, 8], [2, 8, 0, 2, 9],
    [8, 0, 9, 1, 8, 2], [9, 9, 6, 8, 8], [0, 8, 6, 9, 1], [3, 8, 2, 8, 2, 8], [0, 8, 5, 9, 1],
    [8, 4, 9], [0, 8, 2, 9, 1], [8, 3, 9], [8, 0, 0, 9], [0, 0, 8, 0, 0, 9]]

@[expose] def C8 (_ : Unit := ()) : List (Wr 7) :=
  [⟨vecOfN [], cycPerm []⟩,
   ⟨vecOfN [2, 4, 5, 6], cycPerm []⟩,
   ⟨vecOfN [1, 3], cycPerm []⟩,
   ⟨vecOfN [1, 2, 3, 4, 5, 6], cycPerm []⟩,
   ⟨vecOfN [0, 3], cycPerm []⟩,
   ⟨vecOfN [0, 2, 3, 4, 5, 6], cycPerm []⟩,
   ⟨vecOfN [0, 1], cycPerm []⟩,
   ⟨vecOfN [0, 1, 2, 4, 5, 6], cycPerm []⟩]

@[expose] def allMembers (_ : Unit := ()) : List (Wr 7) :=
  fanoLines.flatMap fun ℓ => memAtL ℓᶜ true ++ memAtL ℓᶜ false

@[expose] def finAll {α : Type} (s : Finset α) (f : α → Bool) : Bool := decide (∀ x ∈ s, f x = true)

@[expose] def evenColl (σ : Equiv.Perm (Fin 7)) : Bool :=
  fanoLines.all (fun s => decide (s.map σ.toEmbedding ∈ fanoLines) &&
    decide (s.map σ⁻¹.toEmbedding ∈ fanoLines)) && decide (Equiv.Perm.sign σ = 1)

@[expose] def inM (x : Wr 7) : Bool := decide (∑ i, x.vec i = 0) && evenColl x.perm

end Certificates.E64Aut
