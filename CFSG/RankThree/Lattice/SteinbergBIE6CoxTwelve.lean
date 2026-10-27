module

public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial Module

@[expose] def e6CxW : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  wordMat .E6 [0, 1, 2, 3, 4, 5]

@[expose] def e6CxRel : ℕ → List ℤ
  | 4 => [1, 0, -1, 0, 1]
  | _ => [1, 1, 0, -1, 0, 1, 1]

@[expose] noncomputable def e6CxPoly : ℕ → ℤ[X]
  | 4 => X ^ 4 - X ^ 2 + 1
  | _ => (X ^ 4 - X ^ 2 + 1) * (X ^ 2 + X + 1)

@[expose] noncomputable def e6CxQuot : ℕ → ℤ[X]
  | 4 => X ^ 2 + X + 1
  | _ => 1

@[expose] def e6CxWList : List (List ℤ) :=
  [[0, 1, 0, 0, 0, -1], [0, 0, 1, 0, 0, -1], [1, 1, 0, 0, 0, -1], [0, 1, 1, 0, 0, -1],
   [0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 1, -1]]

@[expose] def e6CxCycInv : List (List ℤ) :=
  [[0, 0, -1, 1, -1, 1], [0, -1, -1, 1, 0, 0], [0, 0, 0, -1, 1, 0], [0, 0, 1, -1, 0, 0],
   [0, 1, 0, 0, -1, 0], [1, 0, -1, 1, -1, 0]]

@[expose] def e6CxCerts : List QCert := [
  ⟨[-1, -2, -2, -3, -2, -1], 4, 1,
    [[0, 0, 0, 1, 0, 0], [0, 0, 1, 2, 0, 0], [0, 1, 0, 2, 0, 0], [1, 2, 0, 3, 0, 0],
     [1, 2, 0, 2, 1, 0], [1, 1, 0, 1, 0, 1]],
    [[1, 0, -2, 1, 0, 0], [-2, 0, 1, 0, 0, 0], [-2, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0],
     [1, 0, 0, -1, 1, 0], [0, 0, 1, -1, 0, 1]]⟩,
  ⟨[-1, -1, -2, -2, -2, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 2], [0, 0, 0, 1, 2, 2],
     [0, 0, 1, 1, 1, 2], [1, 1, 1, 0, 1, 1]],
    [[2, -1, -1, 1, -1, 1], [-1, -1, 1, 0, 0, 0], [-1, 1, 0, -1, 1, 0], [0, -2, 0, 1, 0, 0],
     [-1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -2, -1, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 2], [0, 0, 1, 0, 2, 2],
     [1, 0, 2, -1, 1, 1], [0, 1, 1, 0, 0, 1]],
    [[-1, 2, 1, -2, 1, 0], [-1, 2, 0, -1, 0, 1], [0, -2, 0, 1, 0, 0], [-1, -1, 1, 0, 0, 0],
     [-1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -1, -2, -1, -1], 4, 1,
    [[0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [1, 1, 1, 2, 0, 0],
     [1, 1, 1, 1, 1, 0], [1, 1, 0, 1, 0, 1]],
    [[0, -1, -1, 1, 0, 0], [-1, 1, 0, 0, 0, 0], [-1, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0],
     [1, 0, 0, -1, 1, 0], [0, 0, 1, -1, 0, 1]]⟩,
  ⟨[-1, -1, -1, -1, -1, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 1, 1],
     [0, 1, 1, 1, 0, 1], [1, 1, 0, 0, 0, 1]],
    [[0, 0, -1, 1, -1, 1], [-1, 0, 1, -1, 1, 0], [1, -1, -1, 1, 0, 0], [-1, 1, 0, 0, 0, 0],
     [-1, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, -1, -1, 0], 6, 1,
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 1],
     [0, 0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0]],
    [[-1, -1, 1, 0, 0, 0], [0, -1, 0, 0, 0, 1], [-1, -1, 0, 0, 1, 0], [-1, -1, 0, 1, 0, 0],
     [0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0]]⟩]

theorem e6CxW_eq : e6CxW = toMat Tag.E6.rank e6CxWList :=
  wordMat_eq_toMat .E6 _ (by decide +kernel)

theorem e6Cx_pow : lpow Tag.E6.rank e6CxWList 12 = lid Tag.E6.rank := by
  decide +kernel

theorem e6Cx_cycUnit : IsUnit (orbitMat (toMat Tag.E6.rank e6CxWList)
    (toVec Tag.E6.rank [0, 0, 0, 0, 0, 1]) Tag.E6.rank).det := by
  rw [orbitMat_eq_toMat]
  exact isUnit_det_of_lmul_eq_lid (N := e6CxCycInv) (by decide +kernel)

theorem e6Cx_charpoly :
    (toMat Tag.E6.rank e6CxWList).charpoly = (X ^ 4 - X ^ 2 + 1) * (X ^ 2 + X + 1) :=
  charpoly_eq_of_lists (cs := [1, 1, 0, -1, 0, 1, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [0, 0, 0, 0, 0, 1] e6Cx_cycUnit

theorem e6Cx_check :
    e6CxCerts.all (fun c => c.check Tag.E6.rank e6CxWList (e6CxRel c.k)) = true := by
  decide +kernel

theorem e6Cx_cover : Tag.E6.artifactRoots.all (fun l =>
    (e6CxCerts.find? fun c => decide (l ∈ lorbit Tag.E6.rank e6CxWList c.rep 12)).isSome) =
      true := by
  decide +kernel

theorem e6Cx_ks : e6CxCerts.all (fun c => decide (c.k ∈ [4, 6])) = true := by
  decide +kernel

theorem e6Cx_kd :
    e6CxCerts.all (fun c => decide ((c.k, c.d) ∈ [(6, 1), (4, 1)])) = true := by
  decide +kernel

theorem e6Cx_poly : ∀ k ∈ [4, 6], (e6CxPoly k).Monic ∧ (e6CxPoly k).natDegree = k ∧
    polyOfList (e6CxRel k) = e6CxPoly k ∧
    (toMat Tag.E6.rank e6CxWList).charpoly = e6CxPoly k * e6CxQuot k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rw [e6Cx_charpoly]
  rcases hk with rfl | rfl
  · refine ⟨by simp only [e6CxPoly]; monicity!, by simp only [e6CxPoly]; compute_degree!,
      by simp [e6CxRel, e6CxPoly, polyOfList]; ring, by simp only [e6CxPoly, e6CxQuot]⟩
  · refine ⟨by simp only [e6CxPoly]; monicity!, by simp only [e6CxPoly]; compute_degree!,
      by simp [e6CxRel, e6CxPoly, polyOfList]; ring, by simp only [e6CxPoly, e6CxQuot, mul_one]⟩

theorem e6Cx_case :
    orderOf e6CxW = 12 ∧ e6CxW.charpoly = (X ^ 4 - X ^ 2 + 1) * (X ^ 2 + X + 1) ∧
    (∃ v, IsRoot .E6 v ∧
      LinearIndependent ℤ (fun j : Fin Tag.E6.rank => (e6CxW ^ (j : ℕ)) *ᵥ v) ∧
      Submodule.span ℤ (Set.range fun j : Fin Tag.E6.rank => (e6CxW ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
    (∀ α, IsRoot .E6 α →
      LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice e6CxW α)) =>
        (e6CxW ^ (j : ℕ)) *ᵥ α) ∧
      Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice e6CxW α)) =>
        (e6CxW ^ (j : ℕ)) *ᵥ α) = orbitLattice e6CxW α) ∧
    (∀ α, IsRoot .E6 α →
      (finrank ℤ (orbitLattice e6CxW α) = Tag.E6.rank ∧
        (orbitLattice e6CxW α).toAddSubgroup.index = 1) ∨
      (finrank ℤ (orbitLattice e6CxW α) = 4 ∧
        satIndex (orbitLattice e6CxW α) = 1 ∧
        ∃ h : ratSpan (orbitLattice e6CxW α) ≤
            (ratSpan (orbitLattice e6CxW α)).comap (ratEnd e6CxW),
          ((ratEnd e6CxW).restrict h).charpoly = X ^ 4 - X ^ 2 + 1 ∧
          ((ratSpan (orbitLattice e6CxW α)).mapQ _ (ratEnd e6CxW) h).charpoly =
            X ^ 2 + X + 1)) ∧
    {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6CxW α) = 6 ∧
      satIndex (orbitLattice e6CxW α) = 1}.ncard = 48 ∧
    {α | IsRoot .E6 α ∧ finrank ℤ (orbitLattice e6CxW α) = 4 ∧
      satIndex (orbitLattice e6CxW α) = 1}.ncard = 24 := by
  have hdata := QCert.root_data (by norm_num) e6Cx_pow e6CxRel e6CxCerts e6Cx_check
    e6Cx_cover [4, 6] e6Cx_ks e6CxPoly e6CxQuot e6Cx_poly
  have hcount := QCert.ncard_root (by norm_num) e6Cx_pow e6CxRel e6CxCerts e6Cx_check
    e6Cx_cover [4, 6] e6Cx_ks e6CxPoly e6CxQuot e6Cx_poly
  rw [e6CxW_eq]
  refine ⟨orderOf_toMat_eq (by norm_num) e6Cx_pow (by decide +kernel), e6Cx_charpoly,
    ⟨toVec Tag.E6.rank [0, 0, 0, 0, 0, 1], isRoot_toVec (by decide +kernel),
      (isBasis_iff_isUnit_det _ _).2 e6Cx_cycUnit⟩, ?_, ?_,
    (hcount fun k d => k = 6 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 4 ∧ d = 1).trans (by decide +kernel)⟩
  · intro α hα
    obtain ⟨c, -, h1, -, -, h3, h4, -⟩ := hdata α hα
    rw [h1]
    exact ⟨h3, h4⟩
  · intro α hα
    obtain ⟨c, hc, h1, h2, hidx, -, -, h5⟩ := hdata α hα
    have hkd := List.all_eq_true.1 e6Cx_kd c hc
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hkd
    rcases hkd with ⟨hk, hd⟩ | ⟨hk, hd⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]⟩
    · rw [hk] at h5
      exact Or.inr ⟨h1.trans hk, h2.trans hd, by simpa [e6CxPoly, e6CxQuot] using h5⟩

end CFSG.RankThree.Lattice
