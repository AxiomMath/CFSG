module

public import CFSG.RankThree.Lattice.SteinbergBIE7SevenQuot
public import CFSG.RankThree.Lattice.SteinbergBIE7CoxEighteen

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial Module

@[expose] def e7S14W : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ := e7CxW ^ 9 * e7S7W

@[expose] def e7S14Rel : ℕ → List ℤ
  | 6 => [1, -1, 1, -1, 1, -1, 1]
  | _ => [1, 0, 0, 0, 0, 0, 0, 1]

@[expose] noncomputable def e7S14Poly : ℕ → ℤ[X]
  | 6 => X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1
  | _ => (X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X + 1)

@[expose] noncomputable def e7S14Quot : ℕ → ℤ[X]
  | 6 => X + 1
  | _ => 1

@[expose] def e7S14WList : List (List ℤ) :=
  [[0, -1, 0, 0, 0, 0, 1], [0, -1, 0, 0, 0, 0, 0], [-1, -1, 0, 0, 0, 0, 1], [0, -1, -1, 0, 0, 0, 1],
   [0, 0, 0, -1, 0, 0, 1], [0, 0, 0, 0, -1, 0, 1], [0, 0, 0, 0, 0, -1, 1]]

@[expose] def e7S14CycInv : List (List ℤ) :=
  [[0, -1, 0, 1, -1, 0, 1], [1, 0, 0, 0, -1, 1, 0], [1, 0, -1, 0, 0, 1, -1],
   [0, 0, -1, 1, 0, 0, -1], [-1, 0, 0, 1, -1, 0, 0], [-1, 0, 1, 0, -1, 1, 0],
   [0, 0, 1, -1, 0, 1, -1]]

@[expose] def e7S14Certs : List QCert := [
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
     [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0]]⟩]

theorem e7S14W_eq : e7S14W = toMat Tag.E7.rank e7S14WList := by
  rw [e7S14W, e7CxW_eq, e7S7W_eq, ← toMat_lpow, ← toMat_lmul]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7S14_pow : lpow Tag.E7.rank e7S14WList 14 = lid Tag.E7.rank := by
  decide +kernel

theorem e7S14_cycUnit : IsUnit (orbitMat (toMat Tag.E7.rank e7S14WList)
    (toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0]) Tag.E7.rank).det := by
  rw [orbitMat_eq_toMat]
  exact isUnit_det_of_lmul_eq_lid (N := e7S14CycInv) (by decide +kernel)

theorem e7S14_charpoly :
    (toMat Tag.E7.rank e7S14WList).charpoly =
      (X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X + 1) :=
  charpoly_eq_of_lists (cs := [1, 0, 0, 0, 0, 0, 0, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [0, -1, 0, 0, 0, 0, 0] e7S14_cycUnit

theorem e7S14_check :
    e7S14Certs.all (fun c => c.check Tag.E7.rank e7S14WList (e7S14Rel c.k)) = true := by
  decide +kernel

theorem e7S14_cover : Tag.E7.artifactRoots.all (fun l =>
    (e7S14Certs.find? fun c => decide (l ∈ lorbit Tag.E7.rank e7S14WList c.rep 14)).isSome) =
      true := by
  decide +kernel

theorem e7S14_ks : e7S14Certs.all (fun c => decide (c.k ∈ [6, 7])) = true := by
  decide +kernel

theorem e7S14_kd :
    e7S14Certs.all (fun c => decide ((c.k, c.d) ∈ [(7, 1), (7, 2), (7, 8), (6, 1)])) = true := by
  decide +kernel

theorem e7S14_poly : ∀ k ∈ [6, 7], (e7S14Poly k).Monic ∧ (e7S14Poly k).natDegree = k ∧
    polyOfList (e7S14Rel k) = e7S14Poly k ∧
    (toMat Tag.E7.rank e7S14WList).charpoly = e7S14Poly k * e7S14Quot k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rw [e7S14_charpoly]
  rcases hk with rfl | rfl
  · refine ⟨by simp only [e7S14Poly]; monicity!, by simp only [e7S14Poly]; compute_degree!,
      by simp [e7S14Rel, e7S14Poly, polyOfList]; ring, by simp only [e7S14Poly, e7S14Quot]⟩
  · refine ⟨by simp only [e7S14Poly]; monicity!, by simp only [e7S14Poly]; compute_degree!,
      by simp [e7S14Rel, e7S14Poly, polyOfList]; ring, by simp only [e7S14Poly, e7S14Quot, mul_one]⟩

theorem e7S14_identities : e7CxW ^ 9 = -1 ∧ e7S14W = -e7S7W := by
  have h9 : e7CxW ^ 9 = -1 := by
    rw [e7CxW_eq, ← toMat_lpow, neg_one_eq_toMat]
    exact congrArg (toMat Tag.E7.rank) (by decide +kernel)
  refine ⟨h9, ?_⟩
  rw [e7S14W, h9, neg_one_mul]

theorem e7S14_case :
    orderOf e7S14W = 14 ∧
    e7S14W.charpoly = (X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1) * (X + 1) ∧
    (∃ v, IsRoot .E7 v ∧
      LinearIndependent ℤ (fun j : Fin Tag.E7.rank => (e7S14W ^ (j : ℕ)) *ᵥ v) ∧
      Submodule.span ℤ (Set.range fun j : Fin Tag.E7.rank => (e7S14W ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
    (∀ α, IsRoot .E7 α →
      LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e7S14W α)) =>
        (e7S14W ^ (j : ℕ)) *ᵥ α) ∧
      Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e7S14W α)) =>
        (e7S14W ^ (j : ℕ)) *ᵥ α) = orbitLattice e7S14W α) ∧
    (∀ α, IsRoot .E7 α →
      (finrank ℤ (orbitLattice e7S14W α) = Tag.E7.rank ∧
        (orbitLattice e7S14W α).toAddSubgroup.index ∈ [1, 2, 8]) ∨
      (finrank ℤ (orbitLattice e7S14W α) = 6 ∧
        saturation (orbitLattice e7S14W α) = orbitLattice e7S14W α ∧
        ∃ h : ratSpan (orbitLattice e7S14W α) ≤
            (ratSpan (orbitLattice e7S14W α)).comap (ratEnd e7S14W),
          ((ratEnd e7S14W).restrict h).charpoly =
            X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 + X ^ 2 - X + 1 ∧
          ((ratSpan (orbitLattice e7S14W α)).mapQ _ (ratEnd e7S14W) h).charpoly =
            X + 1)) ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S14W α) = 7 ∧
      satIndex (orbitLattice e7S14W α) = 1}.ncard = 42 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S14W α) = 7 ∧
      satIndex (orbitLattice e7S14W α) = 2}.ncard = 14 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S14W α) = 7 ∧
      satIndex (orbitLattice e7S14W α) = 8}.ncard = 28 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7S14W α) = 6 ∧
      satIndex (orbitLattice e7S14W α) = 1}.ncard = 42 := by
  have hdata := QCert.root_data (by norm_num) e7S14_pow e7S14Rel e7S14Certs e7S14_check
    e7S14_cover [6, 7] e7S14_ks e7S14Poly e7S14Quot e7S14_poly
  have hcount := QCert.ncard_root (by norm_num) e7S14_pow e7S14Rel e7S14Certs e7S14_check
    e7S14_cover [6, 7] e7S14_ks e7S14Poly e7S14Quot e7S14_poly
  rw [e7S14W_eq]
  refine ⟨orderOf_toMat_eq (by norm_num) e7S14_pow (by decide +kernel), e7S14_charpoly,
    ⟨toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0], isRoot_toVec (by decide +kernel),
      (isBasis_iff_isUnit_det _ _).2 e7S14_cycUnit⟩, ?_, ?_,
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
    have hkd := List.all_eq_true.1 e7S14_kd c hc
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hkd
    rcases hkd with ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]; decide⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]; decide⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]; decide⟩
    · rw [hk] at h5
      exact Or.inr ⟨h1.trans hk, saturation_eq_self_of_satIndex (h2.trans hd),
        by simpa [e7S14Poly, e7S14Quot] using h5⟩

end CFSG.RankThree.Lattice
