module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial Module

@[expose] def e7S7W : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  wordMat .E7 [0, 2, 3, 4, 5, 6]

@[expose] def e7S7Rel : ℕ → List ℤ
  | 6 => [1, 1, 1, 1, 1, 1, 1]
  | _ => [-1, 0, 0, 0, 0, 0, 0, 1]

@[expose] noncomputable def e7S7Poly : ℕ → ℤ[X]
  | 6 => X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1
  | _ => (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1)

@[expose] noncomputable def e7S7Quot : ℕ → ℤ[X]
  | 6 => X - 1
  | _ => 1

@[expose] def e7S7WList : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, -1], [0, 1, 1, 0, 0, 0, -1],
   [0, 0, 0, 1, 0, 0, -1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1]]

@[expose] def e7S7CycInv : List (List ℤ) :=
  [[0, -1, 0, 1, -1, 0, 1], [-1, 0, 0, 0, 1, -1, 0], [1, 0, -1, 0, 0, 1, -1],
   [0, 0, 1, -1, 0, 0, 1], [-1, 0, 0, 1, -1, 0, 0], [1, 0, -1, 0, 1, -1, 0],
   [0, 0, 1, -1, 0, 1, -1]]

@[expose] def e7S7Certs : List QCert := [
  ⟨[-2, -2, -3, -4, -3, -2, -1], 7, 2,
    [[0, 0, 0, 0, 0, 1, 2], [1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 1, 0, 3], [0, 0, 0, 1, 0, 0, 4],
     [0, 0, 1, 0, 0, 0, 3], [0, 1, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1]],
    [[0, 1, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 1, -2], [0, 0, 0, 0, 1, 0, -3], [0, 0, 0, 1, 0, 0, -4],
     [0, 0, 1, 0, 0, 0, -3], [1, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 1]]⟩,
  ⟨[-1, -1, -2, -3, -3, -2, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2], [0, 0, 0, 1, 1, 2, 3],
     [0, 0, 1, 1, 1, 2, 3], [0, 1, 0, 1, 1, 2, 2], [1, 0, 0, 1, 0, 1, 1]],
    [[0, 0, 1, -1, 0, 0, 1], [1, 0, 0, -1, 0, 1, 0], [0, 0, 0, -1, 1, 0, 0],
     [0, -1, -1, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -3, -2, -2, -1], 7, 8,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2], [0, 0, 0, 1, 1, 2, 3],
     [0, 0, 1, 0, 1, 2, 2], [0, 1, 0, 1, 0, 1, 2], [1, 0, 1, -1, 1, 1, 1]],
    [[0, 0, -1, 1, -1, 0, 1], [-1, 0, 1, -1, 0, 1, 0], [1, -1, -1, 0, 1, 0, 0],
     [0, -1, -1, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -3, -2, -1, -1], 7, 8,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2], [0, 0, 0, 1, 1, 2, 3],
     [0, 0, 1, 1, 0, 2, 2], [0, 1, 1, 0, -1, 1, 1], [1, 1, 0, -1, 0, 0, 1]],
    [[0, 0, -1, 0, 1, -1, 1], [-1, -1, 0, 1, -1, 1, 0], [0, -1, 1, -1, 1, 0, 0],
     [0, -1, -1, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -2, -2, -2, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2], [1, 0, 0, 0, 1, 2, 2],
     [0, 0, 0, 1, 0, 1, 2], [0, 0, 1, 0, 1, 1, 2], [0, 1, 0, 0, 1, 1, 1]],
    [[1, -1, -1, 1, 0, 0, 0], [1, 0, -1, 0, 0, 0, 1], [0, 0, -1, 0, 0, 1, 0],
     [-1, -1, 0, 0, 1, 0, 0], [-1, -1, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -2, -2, -1, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2], [0, 0, 0, 1, 0, 2, 2],
     [0, 0, 1, 0, 0, 1, 2], [0, 1, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 1]],
    [[-1, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 0, 1, 0], [-1, -1, 0, 0, 1, 0, 0],
     [0, -2, 0, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, -1, -1, -1, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 1, 0],
     [0, 0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0], [1, 1, 1, 1, 1, 1, 0]],
    [[0, 0, 0, 0, 0, -1, 1], [0, 0, 0, 0, -1, 1, 0], [0, 0, 0, -1, 1, 0, 0], [0, 0, -1, 1, 0, 0, 0],
     [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, -1, -1, -1, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 1, 0],
     [0, 0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0], [1, 0, 1, 0, 1, 0, 0]],
    [[1, 0, -1, 1, -1, 0, 1], [0, 0, 0, 0, -1, 1, 0], [0, 0, 0, -1, 1, 0, 0],
     [0, 0, -1, 1, 0, 0, 0], [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, -1, -1, 0, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 1, 0],
     [0, 0, 1, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0]],
    [[0, 0, 1, -1, 0, 0, 1], [1, 0, 0, -1, 0, 1, 0], [0, 0, 0, -1, 1, 0, 0], [0, 0, -1, 1, 0, 0, 0],
     [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, -1, 0, 0, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 1, 0],
     [0, 0, 1, 1, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0]],
    [[0, 0, -1, 1, 0, -1, 1], [-1, 0, 1, 0, -1, 1, 0], [1, 0, 0, -1, 1, 0, 0],
     [0, 0, -1, 1, 0, 0, 0], [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, 0, 0, 0, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 0, 0],
     [0, 0, 1, 1, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0]],
    [[-1, 0, 1, -1, 1, -1, 1], [1, 0, -1, 1, -1, 1, 0], [-1, 0, 1, -1, 1, 0, 0],
     [1, 0, -1, 1, 0, 0, 0], [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, 0, 0, 0, 0, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0],
     [0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0],
     [0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[0, 1, 0, 0, 0, 0, 0], 7, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 1, 0],
     [0, 0, 1, 1, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0]],
    [[0, 0, -1, 1, 0, -1, 1], [-1, 0, 1, 0, -1, 1, 0], [1, 0, 0, -1, 1, 0, 0],
     [0, 0, -1, 1, 0, 0, 0], [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[0, 1, 0, 1, 0, 0, 0], 7, 8,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 0, 1],
     [0, 0, 1, 1, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0, 0]],
    [[-1, 1, 1, -1, 0, 0, 1], [1, 0, -1, 0, 0, 1, 0], [-2, 1, 1, -1, 1, 0, 0],
     [1, -1, -1, 1, 0, 0, 0], [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[0, 1, 0, 1, 1, 0, 0], 7, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [1, -1, 1, 0, 1, 0, 1],
     [0, 0, 1, 0, 0, 0, 1], [0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0]],
    [[0, 0, -1, 1, -1, 1, 0], [-1, 0, 0, 0, 0, 1, 0], [0, -1, 0, 0, 1, 0, 0],
     [1, 0, -1, 0, 0, 0, 1], [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[0, 1, 0, 1, 1, 1, 0], 7, 8,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 0, 0, 1],
     [0, 0, 1, 0, -1, 0, 1], [0, 1, 1, -1, -1, 0, 1], [1, 1, 0, -1, 0, 1, 0]],
    [[-1, 0, 0, 0, 1, -1, 1], [0, -1, 0, 1, -1, 1, 0], [-1, -1, 1, 0, 1, 0, 0],
     [0, -1, 0, 1, 0, 0, 0], [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[0, 1, 1, 1, 1, 0, 0], 7, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 1, 0, 1, 1],
     [0, 0, 1, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0, 0]],
    [[0, 1, 0, 0, -1, 0, 1], [0, 1, 0, -1, 0, 1, 0], [0, 0, -1, 0, 1, 0, 0],
     [-1, -1, 0, 1, 0, 0, 0], [0, -1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, 0, 0, 0, 0]]⟩,
  ⟨[1, 2, 2, 3, 2, 1, 0], 7, 2,
    [[0, 0, 0, 0, 0, 0, 1], [1, -2, -2, -2, 2, 2, 2], [0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 2, 3],
     [0, 0, 0, 1, 0, 1, 2], [0, 0, 1, 2, -1, 0, 1], [0, 1, 2, 3, -2, -1, 0]],
    [[0, 1, 0, 0, 0, -2, 2], [0, 0, 0, 0, 1, -2, 1], [0, 0, 0, 1, -2, 1, 0], [0, 0, -1, 0, 1, 0, 0],
     [1, 0, -2, 1, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]]⟩]

theorem e7S7W_eq : e7S7W = toMat Tag.E7.rank e7S7WList :=
  wordMat_eq_toMat .E7 _ (by decide +kernel)

theorem e7S7_pow : lpow Tag.E7.rank e7S7WList 7 = lid Tag.E7.rank := by
  decide +kernel

theorem e7S7_cycUnit : IsUnit (orbitMat (toMat Tag.E7.rank e7S7WList)
    (toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0]) Tag.E7.rank).det := by
  rw [orbitMat_eq_toMat]
  exact isUnit_det_of_lmul_eq_lid (N := e7S7CycInv) (by decide +kernel)

theorem e7S7_charpoly :
    (toMat Tag.E7.rank e7S7WList).charpoly =
      (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1) :=
  charpoly_eq_of_lists (cs := [-1, 0, 0, 0, 0, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [0, -1, 0, 0, 0, 0, 0] e7S7_cycUnit

theorem e7S7_check :
    e7S7Certs.all (fun c => c.check Tag.E7.rank e7S7WList (e7S7Rel c.k)) = true := by
  decide +kernel

theorem e7S7_cover : Tag.E7.artifactRoots.all (fun l =>
    (e7S7Certs.find? fun c => decide (l ∈ lorbit Tag.E7.rank e7S7WList c.rep 7)).isSome) =
      true := by
  decide +kernel

theorem e7S7_ks : e7S7Certs.all (fun c => decide (c.k ∈ [6, 7])) = true := by
  decide +kernel

theorem e7S7_kd :
    e7S7Certs.all (fun c => decide ((c.k, c.d) ∈ [(7, 1), (7, 2), (7, 8), (6, 1)])) = true := by
  decide +kernel

theorem e7S7_poly : ∀ k ∈ [6, 7], (e7S7Poly k).Monic ∧ (e7S7Poly k).natDegree = k ∧
    polyOfList (e7S7Rel k) = e7S7Poly k ∧
    (toMat Tag.E7.rank e7S7WList).charpoly = e7S7Poly k * e7S7Quot k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rw [e7S7_charpoly]
  rcases hk with rfl | rfl
  · refine ⟨by simp only [e7S7Poly]; monicity!, by simp only [e7S7Poly]; compute_degree!,
      by simp [e7S7Rel, e7S7Poly, polyOfList]; ring, by simp only [e7S7Poly, e7S7Quot]⟩
  · refine ⟨by simp only [e7S7Poly]; monicity!, by simp only [e7S7Poly]; compute_degree!,
      by simp [e7S7Rel, e7S7Poly, polyOfList]; ring, by simp only [e7S7Poly, e7S7Quot, mul_one]⟩

theorem e7S7_case :
    orderOf e7S7W = 7 ∧
    e7S7W.charpoly = (X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1) ∧
    (∃ v, IsRoot .E7 v ∧
      LinearIndependent ℤ (fun j : Fin Tag.E7.rank => (e7S7W ^ (j : ℕ)) *ᵥ v) ∧
      Submodule.span ℤ (Set.range fun j : Fin Tag.E7.rank => (e7S7W ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
    (∀ α, IsRoot .E7 α →
      LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e7S7W α)) =>
        (e7S7W ^ (j : ℕ)) *ᵥ α) ∧
      Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e7S7W α)) =>
        (e7S7W ^ (j : ℕ)) *ᵥ α) = orbitLattice e7S7W α) ∧
    (∀ α, IsRoot .E7 α →
      (finrank ℤ (orbitLattice e7S7W α) = Tag.E7.rank ∧
        (orbitLattice e7S7W α).toAddSubgroup.index ∈ [1, 2, 8]) ∨
      (finrank ℤ (orbitLattice e7S7W α) = 6 ∧
        saturation (orbitLattice e7S7W α) = orbitLattice e7S7W α ∧
        ∃ h : ratSpan (orbitLattice e7S7W α) ≤
            (ratSpan (orbitLattice e7S7W α)).comap (ratEnd e7S7W),
          ((ratEnd e7S7W).restrict h).charpoly = X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 ∧
          ((ratSpan (orbitLattice e7S7W α)).mapQ _ (ratEnd e7S7W) h).charpoly =
            X - 1)) ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S7W α) = 7 ∧
      satIndex (orbitLattice e7S7W α) = 1}.ncard = 42 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S7W α) = 7 ∧
      satIndex (orbitLattice e7S7W α) = 2}.ncard = 14 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S7W α) = 7 ∧
      satIndex (orbitLattice e7S7W α) = 8}.ncard = 28 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S7W α) = 6 ∧
      satIndex (orbitLattice e7S7W α) = 1}.ncard = 42 := by
  have hdata := QCert.root_data (by norm_num) e7S7_pow e7S7Rel e7S7Certs e7S7_check
    e7S7_cover [6, 7] e7S7_ks e7S7Poly e7S7Quot e7S7_poly
  have hcount := QCert.ncard_root (by norm_num) e7S7_pow e7S7Rel e7S7Certs e7S7_check
    e7S7_cover [6, 7] e7S7_ks e7S7Poly e7S7Quot e7S7_poly
  rw [e7S7W_eq]
  refine ⟨orderOf_toMat_eq (by norm_num) e7S7_pow (by decide +kernel), e7S7_charpoly,
    ⟨toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0], isRoot_toVec (by decide +kernel),
      (isBasis_iff_isUnit_det _ _).2 e7S7_cycUnit⟩, ?_, ?_,
    (hcount fun k d => k = 7 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 7 ∧ d = 2).trans (by decide +kernel),
    (hcount fun k d => k = 7 ∧ d = 8).trans (by decide +kernel),
    (hcount fun k d => k = 6 ∧ d = 1).trans (by decide +kernel)⟩
  · intro α hα
    obtain ⟨c, -, h1, -, -, h3, h4, -⟩ := hdata α hα
    rw [h1]
    exact ⟨h3, h4⟩
  · intro α hα
    obtain ⟨c, hc, h1, h2, hidx, -, -, h5⟩ := hdata α hα
    have hkd := List.all_eq_true.1 e7S7_kd c hc
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hkd
    rcases hkd with ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]; decide⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]; decide⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]; decide⟩
    · rw [hk] at h5
      exact Or.inr ⟨h1.trans hk, saturation_eq_self_of_satIndex (h2.trans hd),
        by simpa [e7S7Poly, e7S7Quot] using h5⟩

end CFSG.RankThree.Lattice
