module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial Module

@[expose] def e7CxW : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  wordMat .E7 [0, 1, 2, 3, 4, 5, 6]

@[expose] def e7CxRel : ℕ → List ℤ
  | 6 => [1, 0, 0, -1, 0, 0, 1]
  | _ => [1, 1, 0, -1, -1, 0, 1, 1]

@[expose] noncomputable def e7CxPoly : ℕ → ℤ[X]
  | 6 => X ^ 6 - X ^ 3 + 1
  | _ => (X ^ 6 - X ^ 3 + 1) * (X + 1)

@[expose] noncomputable def e7CxQuot : ℕ → ℤ[X]
  | 6 => X + 1
  | _ => 1

@[expose] def e7CxWList : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, -1], [0, 0, 1, 0, 0, 0, -1], [1, 1, 0, 0, 0, 0, -1], [0, 1, 1, 0, 0, 0, -1],
   [0, 0, 0, 1, 0, 0, -1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1]]

@[expose] def e7CxCycInv : List (List ℤ) :=
  [[0, -1, 0, 0, 1, 0, -1], [0, 0, 0, -1, 1, 1, -1], [0, 0, 0, 0, -1, 1, 1],
   [-1, 0, 0, 1, -1, -1, 2], [0, 0, -1, 1, 0, -1, 0], [1, 0, 0, -1, 1, 0, -1],
   [0, 0, 1, -1, 0, 1, -1]]

@[expose] def e7CxCerts : List QCert := [
  ⟨[-2, -2, -3, -4, -3, -2, -1], 6, 1,
    [[0, 0, 0, 0, 1, 2, 0], [1, -1, 1, 0, 0, 2, 1], [0, 0, 0, 1, 0, 3, 0], [0, 0, 1, 0, 0, 4, 0],
     [0, 1, 0, 0, 0, 3, 0], [1, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 1, 0]],
    [[0, 0, 0, 0, 0, 1, -2], [0, 0, 0, 0, 1, 0, -3], [0, 0, 0, 1, 0, 0, -4], [0, 0, 1, 0, 0, 0, -3],
     [1, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 1], [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -2, -2, -3, -3, -2, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2], [0, 0, 0, 0, 1, 0, 2], [0, 0, 0, 1, 2, 0, 3],
     [0, 0, 1, 1, 1, 1, 3], [0, 1, 1, 1, 1, 0, 2], [1, 0, 1, 0, 1, 0, 1]],
    [[1, 1, -2, 1, -1, 0, 1], [-1, 1, 0, 0, -1, 1, 0], [0, -1, 1, -1, 1, 0, 0],
     [1, 0, -2, 1, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 0], [-2, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -2, -2, -3, -2, -2, -1], 6, 3,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0], [0, 0, 0, 1, 0, 2, 0], [0, 0, 1, 2, 0, 3, 0],
     [0, 1, 2, 2, 0, 2, 0], [1, 2, 1, 0, 1, 2, 0], [1, 1, 0, 0, 0, 1, 1]],
    [[-1, -1, -2, 3, -2, 1, 0], [0, 0, 2, -2, 1, 0, 0], [1, 0, -2, 1, 0, 0, 0],
     [-2, 0, 1, 0, 0, 0, 0], [-2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -1, -2, -2, -2, -2, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 0, 1, 2, 0], [0, 0, 0, 1, 2, 2, 0],
     [0, 0, 1, 1, 1, 2, 0], [0, 1, 1, 0, 1, 2, 0], [0, 1, 0, 0, 1, 1, 1]],
    [[-1, -1, 1, 0, 0, 0, 0], [0, -2, 0, 1, -1, 1, 0], [-1, 1, 0, -1, 1, 0, 0],
     [0, -2, 0, 1, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -1, -2, -2, -2, -1, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 2], [0, 0, 0, 1, 0, 2, 2],
     [0, 0, 1, 1, 0, 1, 2], [1, 0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 0, 0, 1]],
    [[1, 0, 0, 0, -1, 1, 0], [0, -1, 0, 1, -1, 0, 1], [-1, 1, 0, -1, 1, 0, 0],
     [0, -2, 0, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -1, -2, -1, -1, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 0], [1, 0, 0, 1, 1, 2, 0],
     [0, 0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 0, 1, 0], [1, 1, 0, 0, 0, 1, 1]],
    [[0, -1, -1, 1, 0, 0, 0], [-1, 0, 1, 0, -1, 1, 0], [1, -1, -1, 0, 1, 0, 0],
     [-1, 1, 0, 0, 0, 0, 0], [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -1, -1, -1, -1, -1, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 1, 1],
     [0, 0, 1, 1, 1, 0, 1], [0, 1, 1, 0, 0, 0, 1], [1, 1, 0, -1, 0, 0, 1]],
    [[0, -1, 0, 0, 1, -1, 1], [0, 0, -1, 1, -1, 1, 0], [-1, 0, 1, -1, 1, 0, 0],
     [1, -1, -1, 1, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0], [-1, 0, 1, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩]

theorem e7CxW_eq : e7CxW = toMat Tag.E7.rank e7CxWList :=
  wordMat_eq_toMat .E7 _ (by decide +kernel)

theorem e7Cx_pow : lpow Tag.E7.rank e7CxWList 18 = lid Tag.E7.rank := by
  decide +kernel

theorem e7Cx_cycUnit : IsUnit (orbitMat (toMat Tag.E7.rank e7CxWList)
    (toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0]) Tag.E7.rank).det := by
  rw [orbitMat_eq_toMat]
  exact isUnit_det_of_lmul_eq_lid (N := e7CxCycInv) (by decide +kernel)

theorem e7Cx_charpoly :
    (toMat Tag.E7.rank e7CxWList).charpoly = (X ^ 6 - X ^ 3 + 1) * (X + 1) :=
  charpoly_eq_of_lists (cs := [1, 1, 0, -1, -1, 0, 1, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [0, -1, 0, 0, 0, 0, 0] e7Cx_cycUnit

theorem e7Cx_check :
    e7CxCerts.all (fun c => c.check Tag.E7.rank e7CxWList (e7CxRel c.k)) = true := by
  decide +kernel

theorem e7Cx_cover : Tag.E7.artifactRoots.all (fun l =>
    (e7CxCerts.find? fun c => decide (l ∈ lorbit Tag.E7.rank e7CxWList c.rep 18)).isSome) =
      true := by
  decide +kernel

theorem e7Cx_ks : e7CxCerts.all (fun c => decide (c.k ∈ [6, 7])) = true := by
  decide +kernel

theorem e7Cx_kd :
    e7CxCerts.all (fun c => decide ((c.k, c.d) ∈ [(7, 1), (6, 1), (6, 3)])) = true := by
  decide +kernel

theorem e7Cx_poly : ∀ k ∈ [6, 7], (e7CxPoly k).Monic ∧ (e7CxPoly k).natDegree = k ∧
    polyOfList (e7CxRel k) = e7CxPoly k ∧
    (toMat Tag.E7.rank e7CxWList).charpoly = e7CxPoly k * e7CxQuot k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rw [e7Cx_charpoly]
  rcases hk with rfl | rfl
  · refine ⟨by simp only [e7CxPoly]; monicity!, by simp only [e7CxPoly]; compute_degree!,
      by simp [e7CxRel, e7CxPoly, polyOfList]; ring, by simp only [e7CxPoly, e7CxQuot]⟩
  · refine ⟨by simp only [e7CxPoly]; monicity!, by simp only [e7CxPoly]; compute_degree!,
      by simp [e7CxRel, e7CxPoly, polyOfList]; ring, by simp only [e7CxPoly, e7CxQuot, mul_one]⟩

theorem e7Cx_case :
    orderOf e7CxW = 18 ∧ e7CxW.charpoly = (X ^ 6 - X ^ 3 + 1) * (X + 1) ∧
    (∃ v, IsRoot .E7 v ∧
      LinearIndependent ℤ (fun j : Fin Tag.E7.rank => (e7CxW ^ (j : ℕ)) *ᵥ v) ∧
      Submodule.span ℤ (Set.range fun j : Fin Tag.E7.rank => (e7CxW ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
    (∀ α, IsRoot .E7 α →
      LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e7CxW α)) =>
        (e7CxW ^ (j : ℕ)) *ᵥ α) ∧
      Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e7CxW α)) =>
        (e7CxW ^ (j : ℕ)) *ᵥ α) = orbitLattice e7CxW α) ∧
    (∀ α, IsRoot .E7 α →
      (finrank ℤ (orbitLattice e7CxW α) = Tag.E7.rank ∧
        (orbitLattice e7CxW α).toAddSubgroup.index = 1) ∨
      (finrank ℤ (orbitLattice e7CxW α) = 6 ∧
        satIndex (orbitLattice e7CxW α) ∈ [1, 3] ∧
        ∃ h : ratSpan (orbitLattice e7CxW α) ≤
            (ratSpan (orbitLattice e7CxW α)).comap (ratEnd e7CxW),
          ((ratEnd e7CxW).restrict h).charpoly = X ^ 6 - X ^ 3 + 1 ∧
          ((ratSpan (orbitLattice e7CxW α)).mapQ _ (ratEnd e7CxW) h).charpoly =
            X + 1)) ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7CxW α) = 7 ∧
      satIndex (orbitLattice e7CxW α) = 1}.ncard = 54 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7CxW α) = 6 ∧
      satIndex (orbitLattice e7CxW α) = 1}.ncard = 54 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice e7CxW α) = 6 ∧
      satIndex (orbitLattice e7CxW α) = 3}.ncard = 18 := by
  have hdata := QCert.root_data (by norm_num) e7Cx_pow e7CxRel e7CxCerts e7Cx_check
    e7Cx_cover [6, 7] e7Cx_ks e7CxPoly e7CxQuot e7Cx_poly
  have hcount := QCert.ncard_root (by norm_num) e7Cx_pow e7CxRel e7CxCerts e7Cx_check
    e7Cx_cover [6, 7] e7Cx_ks e7CxPoly e7CxQuot e7Cx_poly
  rw [e7CxW_eq]
  refine ⟨orderOf_toMat_eq (by norm_num) e7Cx_pow (by decide +kernel), e7Cx_charpoly,
    ⟨toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0], isRoot_toVec (by decide +kernel),
      (isBasis_iff_isUnit_det _ _).2 e7Cx_cycUnit⟩, ?_, ?_,
    (hcount fun k d => k = 7 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 6 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 6 ∧ d = 3).trans (by decide +kernel)⟩
  · intro α hα
    obtain ⟨c, -, h1, -, -, h3, h4, -⟩ := hdata α hα
    rw [h1]
    exact ⟨h3, h4⟩
  · intro α hα
    obtain ⟨c, hc, h1, h2, hidx, -, -, h5⟩ := hdata α hα
    have hkd := List.all_eq_true.1 e7Cx_kd c hc
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hkd
    rcases hkd with ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]⟩
    · rw [hk] at h5
      exact Or.inr ⟨h1.trans hk, by rw [h2, hd]; decide, by simpa [e7CxPoly, e7CxQuot] using h5⟩
    · rw [hk] at h5
      exact Or.inr ⟨h1.trans hk, by rw [h2, hd]; decide, by simpa [e7CxPoly, e7CxQuot] using h5⟩

end CFSG.RankThree.Lattice
