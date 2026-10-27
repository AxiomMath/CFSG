module

public import CFSG.RankThree.PartOne.KE.E8A2Sigma
public import CFSG.RankThree.PartOne.KE6.E8T3Tables

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE

@[expose] def e8A2Trans : List (Fin Tag.E8.rank × Fin Tag.E8.rank × List (Fin Tag.E8.rank)) :=
  [(0, 2, []), (1, 3, [4, 3, 2, 1, 3, 4, 0, 2, 3]), (2, 3, [0, 2, 3]), (3, 4, [2, 3, 4, 0, 2, 3]),
   (4, 5, [3, 4, 5, 2, 3, 4, 0, 2, 3]), (5, 6, [4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3]),
   (6, 7, [5, 6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3])]

theorem e8A2Trans_edges : ∀ e ∈ e8Edges, ∃ ent ∈ e8A2Trans, ent.1 = e.1 ∧ ent.2.1 = e.2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8A2Trans_forward : ∀ ent ∈ e8A2Trans,
    ∀ x ∈ e8RootsIn [0, 2], ent.2.2.foldr (reflect Tag.E8) x ∈
      e8RootsIn [ent.1, ent.2.1] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8A2Trans_backward : ∀ ent ∈ e8A2Trans,
    ∀ y ∈ e8RootsIn [ent.1, ent.2.1], ∃ x ∈ e8RootsIn [0, 2],
      ent.2.2.foldr (reflect Tag.E8) x = y := by
  decide +kernel

theorem mem_parabolicRoots_iff_E8 (J : List (Fin Tag.E8.rank)) {v : V8} :
    v ∈ parabolicRoots Tag.E8 {i | i ∈ J} ↔ v ∈ e8RootsIn J := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hv
    rw [e8RootsIn, List.mem_filter]
    refine ⟨List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
    rw [List.all_eq_true]
    intro i _
    by_cases hi : i ∈ J
    · simp [hi]
    · simp [hs i hi]
  · intro h
    rw [e8RootsIn, List.mem_filter] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h1
    refine ⟨isRoot_toVec hl, fun i hi => ?_⟩
    have := (List.all_eq_true.1 h2) i (List.mem_finRange i)
    simp only [Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq] at this
    rcases this with h | h
    · exact absurd h hi
    · exact h

theorem e8support13_eq : e8support13 = {i | i ∈ ([0, 2] : List (Fin Tag.E8.rank))} := by
  ext i
  simp only [e8support13, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    List.mem_cons, List.not_mem_nil, or_false]
  rfl

theorem e8A2Trans_image {ent : Fin Tag.E8.rank × Fin Tag.E8.rank × List (Fin Tag.E8.rank)}
    (hent : ent ∈ e8A2Trans) :
    (fun γ => (coxeterSystem Tag.E8).wordProd ent.2.2 • γ) '' parabolicRoots Tag.E8 e8support13 =
      parabolicRoots Tag.E8 {i | i ∈ ([ent.1, ent.2.1] : List (Fin Tag.E8.rank))} := by
  ext y
  simp only [Set.mem_image, e8support13_eq, mem_parabolicRoots_iff_E8]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [wordProd_smul]
    exact e8A2Trans_forward ent hent x hx
  · intro hy
    obtain ⟨x, hx, hxy⟩ := e8A2Trans_backward ent hent y hy
    exact ⟨x, hx, by rw [wordProd_smul]; exact hxy⟩

theorem exists_v_of_A2 {u : WeylGroup Tag.E8} {S : Set (Fin Tag.E8.rank → ℤ)}
    {ent : Fin Tag.E8.rank × Fin Tag.E8.rank × List (Fin Tag.E8.rank)} (hent : ent ∈ e8A2Trans)
    (hS : (fun γ => u • γ) '' S =
      parabolicRoots Tag.E8 {i | i ∈ ([ent.1, ent.2.1] : List (Fin Tag.E8.rank))}) :
    S = sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2) := by
  have himg := e8A2Trans_image hent
  set t := (coxeterSystem Tag.E8).wordProd ent.2.2 with ht
  have h1 : ∀ x, u • x ∈ parabolicRoots Tag.E8
      {i | i ∈ ([ent.1, ent.2.1] : List (Fin Tag.E8.rank))} ↔ x ∈ S := fun x => by
    rw [← hS]
    constructor
    · rintro ⟨z, hz, hzx⟩
      rw [smul_left_cancel_iff] at hzx
      exact hzx ▸ hz
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext x
  constructor
  · intro hx
    have h2 := (h1 x).2 hx
    rw [← himg] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    refine ⟨y, hy, ?_⟩
    show (u⁻¹ * t) • y = x
    rw [mul_smul]
    have hyx' : t • y = u • x := hyx
    rw [hyx', inv_smul_smul]
  · rintro ⟨y, hy, rfl⟩
    have h2 : t • y ∈ parabolicRoots Tag.E8
        {i | i ∈ ([ent.1, ent.2.1] : List (Fin Tag.E8.rank))} := by
      rw [← himg]
      exact ⟨y, hy, rfl⟩
    have h3 : u • ((u⁻¹ * t) • y) ∈ parabolicRoots Tag.E8
        {i | i ∈ ([ent.1, ent.2.1] : List (Fin Tag.E8.rank))} := by
      rw [mul_smul, smul_inv_smul]
      exact h2
    exact (h1 _).1 h3

end CFSG.RankThree.PartOne.KE6
