module

public import CFSG.RankThree.Lattice.SteinbergBIE7CoxEighteen

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial Module

@[expose] def e7Cx2Rel : ℕ → List ℤ
  | 6 => [1, 0, 0, 1, 0, 0, 1]
  | _ => [-1, 1, 0, -1, 1, 0, -1, 1]

@[expose] noncomputable def e7Cx2Poly : ℕ → ℤ[X]
  | 6 => X ^ 6 + X ^ 3 + 1
  | _ => (X ^ 6 + X ^ 3 + 1) * (X - 1)

@[expose] noncomputable def e7Cx2Quot : ℕ → ℤ[X]
  | 6 => X - 1
  | _ => 1

@[expose] def e7Cx2WList : List (List ℤ) :=
  [[0, 0, 1, 0, 0, -1, 0], [1, 1, 0, 0, 0, -1, 0], [0, 1, 1, 0, 0, -1, -1], [1, 1, 1, 0, 0, -1, -1],
   [0, 1, 1, 0, 0, -1, 0], [0, 0, 0, 1, 0, -1, 0], [0, 0, 0, 0, 1, -1, 0]]

@[expose] def e7Cx2CycInv : List (List ℤ) :=
  [[-1, -1, 0, 1, 0, 0, 0], [1, 0, 0, -1, 0, 1, 0], [0, 0, -1, 1, 0, -1, 0],
   [-1, 0, 1, 0, -1, 1, 0], [1, 0, 0, -1, 1, 0, -1], [0, 0, 0, 1, -1, -1, 1],
   [0, 0, 0, 0, 0, 1, -1]]

@[expose] def e7Cx2Certs : List QCert := [
  ⟨[-2, -2, -3, -4, -3, -2, -1], 6, 1,
    [[1, -1, 0, 0, 1, 2, 0], [0, 0, 0, 1, 0, 2, 0], [0, 0, 0, 0, 1, 3, 0], [0, 0, 1, 2, 0, 4, 0],
     [0, 1, 1, 1, 0, 3, 0], [0, 1, 0, 0, 0, 2, 1], [0, 0, 0, 0, 0, 1, 0]],
    [[1, 1, -1, -1, 1, 0, 0], [0, 1, 0, -1, 1, 0, -1], [0, -2, 0, 1, 0, 0, 0],
     [0, 1, 0, 0, 0, 0, -2], [0, 0, 1, 0, 0, 0, -3], [0, 0, 0, 0, 0, 0, 1],
     [0, -1, 0, 1, -1, 1, -1]]⟩,
  ⟨[-1, -2, -3, -4, -3, -2, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0], [0, 1, 0, 0, 1, 3, 0], [0, 0, 0, 1, 1, 4, 0],
     [0, 0, 1, 1, 0, 3, 0], [1, -1, 1, 1, 0, 2, 0], [1, -1, 0, 1, 0, 1, 1]],
    [[0, -1, 1, 0, -1, 1, 0], [-1, -1, 1, 0, 0, 0, 0], [-1, 1, 0, -1, 1, 0, 0],
     [-2, -1, 0, 1, 0, 0, 0], [-2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -2, -2, -3, -3, -2, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 2], [0, 0, 1, 1, 0, 1, 2], [0, 0, 0, 1, 0, 2, 3],
     [0, 0, 0, 0, 1, 2, 3], [0, 1, 1, 0, 1, 1, 2], [1, 1, 1, 0, 1, 1, 1]],
    [[1, 0, 0, 0, 0, -1, 1], [0, 0, -1, 1, -1, 1, 0], [-1, 1, 1, -1, 0, 0, 0],
     [1, -2, 0, 1, 0, 0, 0], [1, -2, 0, 0, 1, 0, 0], [-2, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -2, -2, -3, -2, -2, -1], 6, 3,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0], [0, 0, 0, 1, 1, 2, 0], [0, 0, 1, 1, 2, 3, 0],
     [0, 1, 2, 1, 2, 2, 0], [1, -1, 1, 1, 1, 2, 0], [1, -2, 0, 1, 0, 1, 1]],
    [[-1, 2, 1, -3, 1, 1, 0], [0, 1, 1, -2, 1, 0, 0], [1, -1, -1, 1, 0, 0, 0],
     [0, -1, 1, 0, 0, 0, 0], [-2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -1, -2, -3, -2, -2, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1, 0, 2], [0, 0, 0, 0, 0, 1, 3],
     [0, 0, 1, 0, -1, 1, 2], [0, 1, 1, -1, 0, 1, 2], [1, 0, 0, 0, 1, 0, 1]],
    [[1, 0, -1, 0, 0, 0, 1], [1, 1, -1, 0, -1, 1, 0], [-1, 0, 1, -1, 1, 0, 0],
     [-1, 1, 0, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 0], [-3, 0, 0, 1, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -3, -2, -1, -1], 6, 3,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0], [-1, -2, 0, 2, 1, 3, 1],
     [0, 0, 1, 2, 0, 2, 0], [1, 3, 2, 2, -1, 1, 0], [0, 1, 1, 1, 0, 1, 0]],
    [[-1, -1, 1, 0, 1, 1, -3], [0, 1, 0, 0, -1, 0, 1], [0, -2, 0, 0, 1, 0, 0],
     [-1, 1, 0, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, -1, 0, 1, -1, 1, -1]]⟩,
  ⟨[-1, -1, -2, -2, -2, -2, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 2, 0], [0, 0, 0, 0, 1, 2, 0],
     [0, 0, 1, 0, 1, 2, 0], [0, 0, 0, 1, 0, 2, 0], [-1, 0, -1, 1, 0, 1, 1]],
    [[-1, 1, 0, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 0], [0, 0, 0, -1, 1, 0, 0], [-2, 0, 0, 0, 0, 1, 0],
     [-2, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -1, -2, -2, -2, -1, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 2], [0, 1, 0, 0, 1, 0, 2],
     [0, 0, 0, 1, 1, 0, 2], [1, 0, 0, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, 1]],
    [[0, -1, 0, 0, 0, 1, 0], [-1, -1, 0, 1, 0, 0, 0], [0, -1, 0, 0, 0, 0, 1],
     [-1, -1, 0, 0, 1, 0, 0], [-1, 1, 0, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -2, -2, -1, -1, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 2, 0], [0, 1, 0, 2, 0, 2, 0],
     [0, 0, 1, 2, -1, 1, 0], [1, -1, 1, 1, 0, 1, 0], [1, 0, 0, 0, 1, 1, 1]],
    [[1, -1, -1, 1, -1, 1, 0], [0, -2, 0, 1, 0, 0, 0], [-1, -2, 1, 0, 1, 0, 0],
     [-1, 1, 0, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -1, -1, -2, -1, -1, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 0, 1, 0], [0, 1, 0, 1, 1, 2, 0],
     [0, 0, 1, 0, 1, 1, 0], [1, 0, 1, 0, 1, 1, 0], [1, 1, 0, 1, 0, 1, 1]],
    [[0, 0, 0, 0, -1, 1, 0], [0, -1, -1, 1, 0, 0, 0], [0, -1, 0, 0, 1, 0, 0],
     [-1, 0, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, -1, -1, -2, -1, -1, 0], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 2, 2],
     [1, 0, 0, 0, 1, 1, 1], [0, 0, 1, 0, 1, 1, 1], [0, 1, 0, 0, 0, 0, 0]],
    [[0, 0, -1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, -1, 0, 0, 1, 0], [0, -1, -1, 1, 0, 0, 0],
     [0, -1, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, -1, -1, -1, -1, -1, -1], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0, 1], [1, -1, 0, 0, 0, 1, 1],
     [0, 0, 0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, 1]],
    [[0, -1, -1, 1, 0, 1, 0], [0, 0, -1, 0, 0, 1, 0], [0, 0, -1, 0, 0, 0, 1],
     [0, -1, 0, 0, 1, 0, 0], [-1, 0, 1, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 0]]⟩,
  ⟨[-1, 0, -1, -1, -1, -1, -1], 6, 1,
    [[0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 1, 0],
     [0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0], [-1, -1, 0, 1, 0, 1, 1]],
    [[1, 1, 0, -1, 0, 0, 0], [-1, 0, 0, 0, 1, 0, 0], [-1, 0, 0, 1, 0, 0, 0], [-1, 0, 0, 0, 0, 1, 0],
     [-1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 1, 0, -1, 1, -1, 1]]⟩,
  ⟨[-1, 0, -1, -1, -1, -1, 0], 7, 1,
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1],
     [0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 1], [1, 1, -1, 1, 0, 0, 0]],
    [[0, -1, -1, 0, 1, 0, 1], [-1, 0, 1, 0, 0, 0, 0], [-1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0],
     [-1, 0, 0, 0, 0, 1, 0], [-1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0]]⟩]

theorem e7Cx2W_eq : e7CxW ^ 2 = toMat Tag.E7.rank e7Cx2WList := by
  rw [e7CxW_eq, ← toMat_lpow]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Cx2_pow : lpow Tag.E7.rank e7Cx2WList 9 = lid Tag.E7.rank := by
  decide +kernel

theorem e7Cx2_cycUnit : IsUnit (orbitMat (toMat Tag.E7.rank e7Cx2WList)
    (toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0]) Tag.E7.rank).det := by
  rw [orbitMat_eq_toMat]
  exact isUnit_det_of_lmul_eq_lid (N := e7Cx2CycInv) (by decide +kernel)

theorem e7Cx2_charpoly :
    (toMat Tag.E7.rank e7Cx2WList).charpoly = (X ^ 6 + X ^ 3 + 1) * (X - 1) :=
  charpoly_eq_of_lists (cs := [-1, 1, 0, -1, 1, 0, -1, 1]) (by monicity!) (by compute_degree!)
    (by simp [polyOfList]; ring) (by decide +kernel) [0, -1, 0, 0, 0, 0, 0] e7Cx2_cycUnit

theorem e7Cx2_check :
    e7Cx2Certs.all (fun c => c.check Tag.E7.rank e7Cx2WList (e7Cx2Rel c.k)) = true := by
  decide +kernel

theorem e7Cx2_cover : Tag.E7.artifactRoots.all (fun l =>
    (e7Cx2Certs.find? fun c => decide (l ∈ lorbit Tag.E7.rank e7Cx2WList c.rep 9)).isSome) =
      true := by
  decide +kernel

theorem e7Cx2_ks : e7Cx2Certs.all (fun c => decide (c.k ∈ [6, 7])) = true := by
  decide +kernel

theorem e7Cx2_kd :
    e7Cx2Certs.all (fun c => decide ((c.k, c.d) ∈ [(7, 1), (6, 1), (6, 3)])) = true := by
  decide +kernel

theorem e7Cx2_poly : ∀ k ∈ [6, 7], (e7Cx2Poly k).Monic ∧ (e7Cx2Poly k).natDegree = k ∧
    polyOfList (e7Cx2Rel k) = e7Cx2Poly k ∧
    (toMat Tag.E7.rank e7Cx2WList).charpoly = e7Cx2Poly k * e7Cx2Quot k := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rw [e7Cx2_charpoly]
  rcases hk with rfl | rfl
  · refine ⟨by simp only [e7Cx2Poly]; monicity!, by simp only [e7Cx2Poly]; compute_degree!,
      by simp [e7Cx2Rel, e7Cx2Poly, polyOfList]; ring, by simp only [e7Cx2Poly, e7Cx2Quot]⟩
  · refine ⟨by simp only [e7Cx2Poly]; monicity!, by simp only [e7Cx2Poly]; compute_degree!,
      by simp [e7Cx2Rel, e7Cx2Poly, polyOfList]; ring, by simp only [e7Cx2Poly, e7Cx2Quot, mul_one]⟩

theorem e7Cx2_case :
    orderOf (e7CxW ^ 2) = 9 ∧ (e7CxW ^ 2).charpoly = (X ^ 6 + X ^ 3 + 1) * (X - 1) ∧
    (∃ v, IsRoot .E7 v ∧
      LinearIndependent ℤ (fun j : Fin Tag.E7.rank => ((e7CxW ^ 2) ^ (j : ℕ)) *ᵥ v) ∧
      Submodule.span ℤ (Set.range fun j : Fin Tag.E7.rank => ((e7CxW ^ 2) ^ (j : ℕ)) *ᵥ v) = ⊤) ∧
    (∀ α, IsRoot .E7 α →
      LinearIndependent ℤ (fun j : Fin (finrank ℤ (orbitLattice (e7CxW ^ 2) α)) =>
        ((e7CxW ^ 2) ^ (j : ℕ)) *ᵥ α) ∧
      Submodule.span ℤ (Set.range fun j : Fin (finrank ℤ (orbitLattice (e7CxW ^ 2) α)) =>
        ((e7CxW ^ 2) ^ (j : ℕ)) *ᵥ α) = orbitLattice (e7CxW ^ 2) α) ∧
    (∀ α, IsRoot .E7 α →
      (finrank ℤ (orbitLattice (e7CxW ^ 2) α) = Tag.E7.rank ∧
        (orbitLattice (e7CxW ^ 2) α).toAddSubgroup.index = 1) ∨
      (finrank ℤ (orbitLattice (e7CxW ^ 2) α) = 6 ∧
        satIndex (orbitLattice (e7CxW ^ 2) α) ∈ [1, 3] ∧
        ∃ h : ratSpan (orbitLattice (e7CxW ^ 2) α) ≤
            (ratSpan (orbitLattice (e7CxW ^ 2) α)).comap (ratEnd (e7CxW ^ 2)),
          ((ratEnd (e7CxW ^ 2)).restrict h).charpoly = X ^ 6 + X ^ 3 + 1 ∧
          ((ratSpan (orbitLattice (e7CxW ^ 2) α)).mapQ _ (ratEnd (e7CxW ^ 2)) h).charpoly =
            X - 1)) ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice (e7CxW ^ 2) α) = 7 ∧
      satIndex (orbitLattice (e7CxW ^ 2) α) = 1}.ncard = 54 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice (e7CxW ^ 2) α) = 6 ∧
      satIndex (orbitLattice (e7CxW ^ 2) α) = 1}.ncard = 54 ∧
    {α | IsRoot .E7 α ∧ finrank ℤ (orbitLattice (e7CxW ^ 2) α) = 6 ∧
      satIndex (orbitLattice (e7CxW ^ 2) α) = 3}.ncard = 18 := by
  have hdata := QCert.root_data (by norm_num) e7Cx2_pow e7Cx2Rel e7Cx2Certs e7Cx2_check
    e7Cx2_cover [6, 7] e7Cx2_ks e7Cx2Poly e7Cx2Quot e7Cx2_poly
  have hcount := QCert.ncard_root (by norm_num) e7Cx2_pow e7Cx2Rel e7Cx2Certs e7Cx2_check
    e7Cx2_cover [6, 7] e7Cx2_ks e7Cx2Poly e7Cx2Quot e7Cx2_poly
  rw [e7Cx2W_eq]
  refine ⟨orderOf_toMat_eq (by norm_num) e7Cx2_pow (by decide +kernel), e7Cx2_charpoly,
    ⟨toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0], isRoot_toVec (by decide +kernel),
      (isBasis_iff_isUnit_det _ _).2 e7Cx2_cycUnit⟩, ?_, ?_,
    (hcount fun k d => k = 7 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 6 ∧ d = 1).trans (by decide +kernel),
    (hcount fun k d => k = 6 ∧ d = 3).trans (by decide +kernel)⟩
  · intro α hα
    obtain ⟨c, -, h1, -, -, h3, h4, -⟩ := hdata α hα
    rw [h1]
    exact ⟨h3, h4⟩
  · intro α hα
    obtain ⟨c, hc, h1, h2, hidx, -, -, h5⟩ := hdata α hα
    have hkd := List.all_eq_true.1 e7Cx2_kd c hc
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hkd
    rcases hkd with ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩
    · exact Or.inl ⟨h1.trans hk, by rw [hidx (hk.trans rfl), hd]⟩
    · rw [hk] at h5
      exact Or.inr ⟨h1.trans hk, by rw [h2, hd]; decide, by simpa [e7Cx2Poly, e7Cx2Quot] using h5⟩
    · rw [hk] at h5
      exact Or.inr ⟨h1.trans hk, by rw [h2, hd]; decide, by simpa [e7Cx2Poly, e7Cx2Quot] using h5⟩

end CFSG.RankThree.Lattice
