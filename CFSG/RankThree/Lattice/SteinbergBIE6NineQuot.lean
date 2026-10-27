module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial Module

@[expose] def e6N9W : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  wordMat .E6 [4, 5, 2, 1, 3, 4, 1, 3, 1, 0]

@[expose] def e6N9Rel : ℕ → List ℤ
  | _ => [1, 0, 0, 1, 0, 0, 1]

@[expose] noncomputable def e6N9Poly : ℕ → ℤ[X]
  | _ => X ^ 6 + X ^ 3 + 1

@[expose] noncomputable def e6N9Quot : ℕ → ℤ[X]
  | _ => 1

@[expose] def e6N9WList : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0], [0, 0, 1, 0, -1, 1], [-1, 0, 2, -1, 0, 1], [0, 0, 2, -1, 0, 1],
   [0, 0, 2, -1, 0, 0], [0, -1, 1, 0, 0, 0]]

@[expose] def e6N9CycInv : List (List ℤ) :=
  [[-1, 0, 1, 0, -1, 1], [0, 1, 1, -1, 0, 0], [0, 0, 0, 0, 1, -1], [0, -1, 0, 1, -1, 1],
   [0, 1, 0, 0, -1, 1], [0, 1, 0, 0, 0, -1]]

@[expose] def e6N9Certs : List QCert := [
  ⟨[-1, -2, -2, -3, -2, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2], [0, 0, 0, 1, 1, 2], [0, 1, 0, 0, 1, 3],
     [0, 0, 1, 0, 1, 2], [1, 0, 1, 0, 1, 1]],
    [[1, 0, 0, 0, -1, 1], [-1, -1, 0, 1, 0, 0], [0, -1, 0, 0, 1, 0], [0, -1, 1, 0, 0, 0],
     [-2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -3, -2, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 2], [1, 1, 0, 1, 1, 3],
     [0, 1, 0, 0, 1, 2], [0, 0, 1, 0, 0, 1]],
    [[0, -1, 0, 1, -1, 0], [0, 0, -1, 0, 1, 0], [-1, 0, 0, 0, 0, 1], [-1, 1, 0, 0, 0, 0],
     [-2, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -2, -1, 0], 6, 3,
    [[0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 2], [0, 0, 0, 1, 0, 2],
     [0, 1, 2, 0, -1, 1], [0, 0, 1, 0, -1, 0]],
    [[-2, 1, 1, 0, -1, 2], [1, 0, -1, 0, 1, -2], [-2, 0, 1, 0, 0, 1], [-2, 0, 0, 1, 0, 0],
     [-2, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -1, -1, -1, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 1, 0, 1, 1], [0, 0, 0, 1, 2, 1],
     [0, 1, 0, 0, 1, 1], [1, 1, 0, -1, 0, 1]],
    [[0, -1, 0, 1, -1, 1], [0, -1, 0, 0, 1, 0], [0, -1, 1, 0, 0, 0], [1, -2, 0, 1, 0, 0],
     [-1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -1, -1, -1, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1],
     [1, 0, 0, 0, 1, 1], [0, 1, 0, 0, 0, 0]],
    [[0, 0, 0, -1, 1, 0], [0, 0, 0, 0, 0, 1], [0, 1, -1, 0, 0, 0], [-1, 0, 1, 0, 0, 0],
     [-1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -1, -1, 0, 0], 6, 3,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 0, 1], [0, 0, 1, 0, 1, 1],
     [0, 1, 1, 0, 1, 0], [1, 2, -1, 1, 0, 0]],
    [[-1, -1, -1, 3, -2, 1], [1, 0, 0, -1, 1, 0], [0, -1, 0, 1, 0, 0], [-1, 0, 1, 0, 0, 0],
     [-1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, -1, -1, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1],
     [0, 0, 0, 1, 1, 1], [0, 1, 0, 0, 1, 0]],
    [[-1, 0, 1, 0, 0, 0], [1, 0, 0, -1, 0, 1], [0, 1, 0, 0, 0, 0], [0, 0, 0, -1, 1, 0],
     [-1, 0, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, -1, 0, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1],
     [0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 1, 0]],
    [[0, 0, 0, 0, -1, 1], [0, 1, 1, -1, 0, 0], [-1, -1, 0, 1, 0, 0], [0, -1, 0, 0, 1, 0],
     [0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩]

theorem e6N9W_eq : e6N9W = toMat Tag.E6.rank e6N9WList :=
  wordMat_eq_toMat .E6 _ (by decide +kernel)

theorem e6N9_pow : lpow Tag.E6.rank e6N9WList 9 = lid Tag.E6.rank := by
  decide +kernel

theorem e6N9_cycUnit : IsUnit (orbitMat (toMat Tag.E6.rank e6N9WList)
    (toVec Tag.E6.rank [-1, 0, 0, 0, 0, 0]) Tag.E6.rank).det := by
  rw [orbitMat_eq_toMat]
  exact isUnit_det_of_lmul_eq_lid (N := e6N9CycInv) (by decide +kernel)

theorem e6N9_charpoly :
    (toMat Tag.E6.rank e6N9WList).charpoly = X ^ 6 + X ^ 3 + 1 :=
  charpoly_eq_of_lists (cs := [1, 0, 0, 1, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [-1, 0, 0, 0, 0, 0] e6N9_cycUnit

theorem e6N9_check :
    e6N9Certs.all (fun c => c.check Tag.E6.rank e6N9WList (e6N9Rel c.k)) = true := by
  decide +kernel

theorem e6N9_cover : Tag.E6.artifactRoots.all (fun l =>
    (e6N9Certs.find? fun c => decide (l ∈ lorbit Tag.E6.rank e6N9WList c.rep 9)).isSome) =
      true := by
  decide +kernel

theorem e6N9_ks : e6N9Certs.all (fun c => decide (c.k ∈ [6])) = true := by
  decide +kernel

theorem e6N9_kd :
    e6N9Certs.all (fun c => decide ((c.k, c.d) ∈ [(6, 1), (6, 3)])) = true := by
  decide +kernel

theorem e6N9_poly : ∀ k ∈ [6], (e6N9Poly k).Monic ∧ (e6N9Poly k).natDegree = k ∧
    polyOfList (e6N9Rel k) = e6N9Poly k ∧
    (toMat Tag.E6.rank e6N9WList).charpoly = e6N9Poly k * e6N9Quot k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rw [e6N9_charpoly]
  subst hk
  refine ⟨by simp only [e6N9Poly]; monicity!, by simp only [e6N9Poly]; compute_degree!,
    by simp [e6N9Rel, e6N9Poly, polyOfList]; ring, by simp only [e6N9Poly, e6N9Quot, mul_one]⟩

theorem e6N9_case :
    orderOf e6N9W = 9 ∧ e6N9W.charpoly = X ^ 6 + X ^ 3 + 1 ∧
    (∃ v, IsRoot .E6 v ∧
      LinearIndependent ℤ (fun j : Fin Tag.E6.rank => (e6N9W ^ (j : ℕ)) *ᵥ v) ∧
      Submodule.span ℤ (Set.range fun j : Fin Tag.E6.rank => (e6N9W ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
    (∀ α, IsRoot .E6 α →
      LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e6N9W α)) =>
        (e6N9W ^ (j : ℕ)) *ᵥ α) ∧
      Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e6N9W α)) =>
        (e6N9W ^ (j : ℕ)) *ᵥ α) = orbitLattice e6N9W α) ∧
    (∀ α, IsRoot .E6 α → finrank ℤ (orbitLattice e6N9W α) = Tag.E6.rank ∧
      (orbitLattice e6N9W α).toAddSubgroup.index ∈ [1, 3]) ∧
    {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6N9W α) = 6 ∧
      satIndex (orbitLattice e6N9W α) = 1}.ncard = 54 ∧
    {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6N9W α) = 6 ∧
      satIndex (orbitLattice e6N9W α) = 3}.ncard = 18 := by
  have hdata := QCert.root_data (by norm_num) e6N9_pow e6N9Rel e6N9Certs e6N9_check
    e6N9_cover [6] e6N9_ks e6N9Poly e6N9Quot e6N9_poly
  have hcount := QCert.ncard_root (by norm_num) e6N9_pow e6N9Rel e6N9Certs e6N9_check
    e6N9_cover [6] e6N9_ks e6N9Poly e6N9Quot e6N9_poly
  rw [e6N9W_eq]
  refine ⟨orderOf_toMat_eq (by norm_num) e6N9_pow (by decide +kernel), e6N9_charpoly,
    ⟨toVec Tag.E6.rank [-1, 0, 0, 0, 0, 0], isRoot_toVec (by decide +kernel),
      (isBasis_iff_isUnit_det _ _).2 e6N9_cycUnit⟩, ?_, ?_,
    (hcount fun k d => k = 6 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 6 ∧ d = 3).trans (by decide +kernel)⟩
  · intro α hα
    obtain ⟨c, -, h1, -, -, h3, h4, -⟩ := hdata α hα
    rw [h1]
    exact ⟨h3, h4⟩
  · intro α hα
    obtain ⟨c, hc, h1, -, hidx, -, -, -⟩ := hdata α hα
    have hkd := List.all_eq_true.1 e6N9_kd c hc
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hkd
    rcases hkd with ⟨hk, hd⟩ | ⟨hk, hd⟩
    · exact ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]; decide⟩
    · exact ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]; decide⟩

end CFSG.RankThree.Lattice
