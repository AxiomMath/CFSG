module

public import CFSG.RankThree.PartOne.KE8F.E8Lat

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE

section Coordinates

@[expose] def gA (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : ℤ :=
  (e8P4Binv *ᵥ x) ⟨2 * j.val, by have : Tag.E8.rank = 8 := rfl; omega⟩

@[expose] def gB (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : ℤ :=
  (e8P4Binv *ᵥ x) ⟨2 * j.val + 1, by have : Tag.E8.rank = 8 := rfl; omega⟩

theorem e8P4Binv_mul_V : e8P4Binv * e8P4V = e8P4J * e8P4Binv := by
  calc e8P4Binv * e8P4V = e8P4Binv * e8P4V * (e8P4B * e8P4Binv) := by
        rw [e8P4B_mul_Binv, Matrix.mul_one]
    _ = e8P4Binv * (e8P4V * e8P4B) * e8P4Binv := by simp only [Matrix.mul_assoc]
    _ = e8P4Binv * (e8P4B * e8P4J) * e8P4Binv := by rw [e8P4V_mul_B]
    _ = (e8P4Binv * e8P4B) * e8P4J * e8P4Binv := by simp only [Matrix.mul_assoc]
    _ = e8P4J * e8P4Binv := by rw [e8P4Binv_mul_B, Matrix.one_mul]

theorem e8P4J_even' (c : Fin 8 → ℤ) (j : Fin 4) :
    ((toMat 8 e8P4JRows) *ᵥ c) ⟨2 * j.val, by omega⟩ = - c ⟨2 * j.val + 1, by omega⟩ := by
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, toMat, lget, e8P4JRows]

theorem e8P4J_odd' (c : Fin 8 → ℤ) (j : Fin 4) :
    ((toMat 8 e8P4JRows) *ᵥ c) ⟨2 * j.val + 1, by omega⟩ = c ⟨2 * j.val, by omega⟩ := by
  fin_cases j <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_eight, toMat, lget, e8P4JRows]

theorem e8P4J_even (c : Fin Tag.E8.rank → ℤ) (j : Fin 4) :
    (e8P4J *ᵥ c) ⟨2 * j.val, by have : Tag.E8.rank = 8 := rfl; omega⟩ =
      - c ⟨2 * j.val + 1, by have : Tag.E8.rank = 8 := rfl; omega⟩ :=
  e8P4J_even' c j

theorem e8P4J_odd (c : Fin Tag.E8.rank → ℤ) (j : Fin 4) :
    (e8P4J *ᵥ c) ⟨2 * j.val + 1, by have : Tag.E8.rank = 8 := rfl; omega⟩ =
      c ⟨2 * j.val, by have : Tag.E8.rank = 8 := rfl; omega⟩ :=
  e8P4J_odd' c j

theorem gA_V (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : gA (e8P4V *ᵥ x) j = - gB x j := by
  unfold gA gB
  rw [Matrix.mulVec_mulVec, e8P4Binv_mul_V, ← Matrix.mulVec_mulVec]
  exact e8P4J_even _ j

theorem gB_V (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : gB (e8P4V *ᵥ x) j = gA x j := by
  unfold gA gB
  rw [Matrix.mulVec_mulVec, e8P4Binv_mul_V, ← Matrix.mulVec_mulVec]
  exact e8P4J_odd _ j

theorem gA_neg (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : gA (-x) j = - gA x j := by
  unfold gA
  rw [Matrix.mulVec_neg]
  rfl

theorem gB_neg (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : gB (-x) j = - gB x j := by
  unfold gB
  rw [Matrix.mulVec_neg]
  rfl


end Coordinates

section Checks

theorem coord_getD (α : Fin Tag.E8.rank → ℤ) (i : Fin Tag.E8.rank) :
    (e8P4Coord (List.ofFn α)).getD i 0 = (e8P4Binv *ᵥ α) i := by
  have h := congrFun (toVec_lmulVec Tag.E8.rank e8P4BinvRows (List.ofFn α)) i
  have h2 : toVec Tag.E8.rank (List.ofFn α) = α := toVec_vofFn α
  rw [h2] at h
  exact h

@[expose] def gRowOf (x : Fin Tag.E8.rank → ℤ) : GRow :=
  ((gA x 0, gB x 0), (gA x 1, gB x 1), (gA x 2, gB x 2), (gA x 3, gB x 3))

theorem e8P4G_coord (α : Fin Tag.E8.rank → ℤ) :
    e8P4G (e8P4Coord (List.ofFn α)) = gRowOf α := by
  have h : ∀ i : Fin Tag.E8.rank, (e8P4Coord (List.ofFn α)).getD i 0 = (e8P4Binv *ᵥ α) i :=
    coord_getD α
  simp only [e8P4G, gRowOf, gA, gB, Prod.mk.injEq]
  exact ⟨⟨h ⟨0, by decide⟩, h ⟨1, by decide⟩⟩, ⟨h ⟨2, by decide⟩, h ⟨3, by decide⟩⟩,
    ⟨h ⟨4, by decide⟩, h ⟨5, by decide⟩⟩, ⟨h ⟨6, by decide⟩, h ⟨7, by decide⟩⟩⟩

theorem e8P4_coord_nonzero {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) :
    ∃ j : Fin 4, 1 ≤ gA α j ^ 2 + gB α j ^ 2 ∧ gA α j ^ 2 + gB α j ^ 2 ≤ 4 := by
  have hl := e8P4_coord_nonzero_list (List.ofFn α) (isRoot_iff_mem_artifactRoots.1 hα)
  rw [List.any_eq_true] at hl
  obtain ⟨j, hj, h⟩ := hl
  rw [decide_eq_true_eq] at h
  have hj4 : j < 4 := List.mem_range.1 hj
  refine ⟨⟨j, hj4⟩, ?_⟩
  have h1 := coord_getD α ⟨2 * j, by have : Tag.E8.rank = 8 := rfl; omega⟩
  have h2 := coord_getD α ⟨2 * j + 1, by have : Tag.E8.rank = 8 := rfl; omega⟩
  simp only [e8P4Nrm] at h
  simp only [gA, gB]
  rw [h1, h2] at h
  constructor <;> nlinarith [h.1, h.2]

@[expose] def GRow.get (u : GRow) : Fin 4 → GZ := ![u.1, u.2.1, u.2.2.1, u.2.2.2]

theorem gRowMinorOK_spec {u w : GRow} (h : gRowMinorOK u w = true) :
    ∃ j k : Fin 4, j ≠ k ∧ (gminorNorm (u.get j) (u.get k) (w.get j) (w.get k) = 1 ∨
      gminorNorm (u.get j) (u.get k) (w.get j) (w.get k) = 2) := by
  unfold gRowMinorOK at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact ⟨0, 1, by decide, by simpa [GRow.get] using h⟩
  · exact ⟨0, 2, by decide, by simpa [GRow.get] using h⟩
  · exact ⟨0, 3, by decide, by simpa [GRow.get] using h⟩
  · exact ⟨1, 2, by decide, by simpa [GRow.get] using h⟩
  · exact ⟨1, 3, by decide, by simpa [GRow.get] using h⟩
  · exact ⟨2, 3, by decide, by simpa [GRow.get] using h⟩

theorem gRowOf_get (x : Fin Tag.E8.rank → ℤ) (j : Fin 4) : (gRowOf x).get j = (gA x j, gB x j) := by
  fin_cases j <;> rfl

theorem toVec_e8P4Neg (n : ℕ) (l : List ℤ) : toVec n (e8P4Neg l) = - toVec n l := by
  funext i
  simp only [toVec, vget, e8P4Neg, Pi.neg_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i.val]? <;> simp

theorem toVec_ofFn' (β : Fin Tag.E8.rank → ℤ) : toVec Tag.E8.rank (List.ofFn β) = β :=
  toVec_vofFn β

theorem toVec_V_ofFn (α : Fin Tag.E8.rank → ℤ) :
    toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (List.ofFn α)) = e8P4V *ᵥ α := by
  rw [toVec_lmulVec, ← e8P4V_eq, toVec_ofFn']

theorem e8P4_minor {α β : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) (hβ : IsRoot .E8 β)
    (hne : ¬ (β = α ∨ β = -α ∨ β = e8P4V *ᵥ α ∨ β = -(e8P4V *ᵥ α))) :
    ∃ j k : Fin 4, j ≠ k ∧
      (gminorNorm (gA α j, gB α j) (gA α k, gB α k) (gA β j, gB β j) (gA β k, gB β k) = 1 ∨
        gminorNorm (gA α j, gB α j) (gA α k, gB α k) (gA β j, gB β j) (gA β k, gB β k) = 2) := by
  have hx : e8P4Entry (List.ofFn α) ∈ e8P4Table :=
    List.mem_map_of_mem (isRoot_iff_mem_artifactRoots.1 hα)
  have hy : e8P4Entry (List.ofFn β) ∈ e8P4Table :=
    List.mem_map_of_mem (isRoot_iff_mem_artifactRoots.1 hβ)
  have h := e8P4_minor_table _ hx _ hy
  unfold e8P4PairOK at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · exact absurd (Or.inl (List.ofFn_injective h)) hne
  · refine absurd (Or.inr (Or.inl ?_)) hne
    have h' : List.ofFn β = e8P4Neg (List.ofFn α) := h
    have h3 := congrArg (toVec Tag.E8.rank) h'
    rw [toVec_ofFn', toVec_e8P4Neg, toVec_ofFn'] at h3
    exact h3
  · refine absurd (Or.inr (Or.inr (Or.inl ?_))) hne
    have h' : List.ofFn β = lmulVec Tag.E8.rank e8P4VList (List.ofFn α) := h
    have h3 := congrArg (toVec Tag.E8.rank) h'
    rw [toVec_ofFn', toVec_V_ofFn] at h3
    exact h3
  · refine absurd (Or.inr (Or.inr (Or.inr ?_))) hne
    have h' : List.ofFn β = e8P4Neg (lmulVec Tag.E8.rank e8P4VList (List.ofFn α)) := h
    have h3 := congrArg (toVec Tag.E8.rank) h'
    rw [toVec_ofFn', toVec_e8P4Neg, toVec_V_ofFn] at h3
    exact h3
  · obtain ⟨j, k, hjk, hn⟩ := gRowMinorOK_spec h
    refine ⟨j, k, hjk, ?_⟩
    simp only [e8P4Entry] at hn
    rw [e8P4G_coord, e8P4G_coord] at hn
    simpa [gRowOf_get] using hn

end Checks

end CFSG.RankThree.PartOne.KE8F
