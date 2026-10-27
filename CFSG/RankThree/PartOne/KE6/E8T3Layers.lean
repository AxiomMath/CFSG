module

public import CFSG.RankThree.PartOne.KE6.E8T3Layers1
public import CFSG.RankThree.PartOne.KE6.E8T3Supports
public import CFSG.RankThree.PartOne.KE6.E8T3Trans

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem e8T3_supports_cases {J : Finset (Fin Tag.E8.rank)} (h : J ∈ e8T3Supports) :
    J = ∅ ∨ (∃ e ∈ e8Edges, J = {e.1, e.2}) ∨
      (∃ q ∈ e8TwoA2, J = {q.1, q.2.1, q.2.2.1, q.2.2.2}) ∨ J = {1, 2, 3, 4} ∨
      J = {0, 1, 2, 3, 4, 5} ∨ J = {1, 2, 3, 4, 6, 7} := by
  revert J
  decide +kernel

theorem smul_apply_eq_sum {T : WeylGroup Tag.E8} (js : List (Fin Tag.E8.rank))
    (hnd : js.Nodup) (x : V8) (hx : ∀ i, i ∉ js → x i = 0) (i : Fin Tag.E8.rank) :
    (T • x) i = ∑ k ∈ js.toFinset, x k * colT T k i := by
  rw [← foldl_colT_eq_smul js hnd x hx, foldl_add_eq_sum, zero_add, ← List.sum_toFinset _ hnd,
    Finset.sum_apply]
  simp [Pi.smul_apply]

theorem maps_of_supp {T : WeylGroup Tag.E8} (js : List (Fin Tag.E8.rank))
    (hnd : js.Nodup) (hsupp : ∀ j ∈ js, ∀ i, i ∉ js → colT T j i = 0) :
    ∀ β ∈ parabolicRoots Tag.E8 {i | i ∈ js}, T • β ∈ parabolicRoots Tag.E8 {i | i ∈ js} := by
  intro β hβ
  refine ⟨IsRoot.smul hβ.1 T, fun i hi => ?_⟩
  have hi' : i ∉ js := hi
  rw [smul_apply_eq_sum js hnd β (fun i hi => hβ.2 i hi) i]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [hsupp k (List.mem_toFinset.1 hk) i hi', mul_zero]

theorem rotCols_supp {a b : Fin Tag.E8.rank} :
    ∀ cs ∈ rotCols a b, ∀ c ∈ cs, ∀ i : Fin Tag.E8.rank, i ≠ a → i ≠ b → c i = 0 := by
  intro cs hcs c hc i hia hib
  simp only [rotCols, List.mem_cons, List.not_mem_nil, or_false] at hcs
  rcases hcs with rfl | rfl <;>
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      simp [hia, hib]

theorem colsA2_supp {T : WeylGroup Tag.E8} {a b : Fin Tag.E8.rank}
    (h : [colT T a, colT T b] ∈ rotCols a b) :
    ∀ j ∈ ([a, b] : List (Fin Tag.E8.rank)), ∀ i, i ∉ ([a, b] : List (Fin Tag.E8.rank)) →
      colT T j i = 0 := by
  intro j hj i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj hi
  rcases hj with rfl | rfl
  · exact rotCols_supp _ h (colT T j) (by simp) i hi.1 hi.2
  · exact rotCols_supp _ h (colT T j) (by simp) i hi.1 hi.2

theorem maps_of_colsA2 {T : WeylGroup Tag.E8} {a b : Fin Tag.E8.rank} (hab : a ≠ b)
    (h : [colT T a, colT T b] ∈ rotCols a b) :
    ∀ β ∈ parabolicRoots Tag.E8 {i | i ∈ ([a, b] : List (Fin Tag.E8.rank))},
      T • β ∈ parabolicRoots Tag.E8 {i | i ∈ ([a, b] : List (Fin Tag.E8.rank))} :=
  maps_of_supp [a, b] (by simp [hab]) (colsA2_supp h)

set_option maxRecDepth 100000 in
theorem d4Cols_supp : ∀ cs ∈ d4Cols, ∀ c ∈ cs, ∀ i : Fin Tag.E8.rank,
    i ∉ ([1, 2, 3, 4] : List (Fin Tag.E8.rank)) → c i = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8TwoA2_union_fwd : ∀ q ∈ e8TwoA2, ∀ x ∈ e8RootsIn [q.1, q.2.1, q.2.2.1, q.2.2.2],
    x ∈ e8RootsIn [q.1, q.2.1] ∨ x ∈ e8RootsIn [q.2.2.1, q.2.2.2] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8TwoA2_union_bwd : ∀ q ∈ e8TwoA2,
    (∀ x ∈ e8RootsIn [q.1, q.2.1], x ∈ e8RootsIn [q.1, q.2.1, q.2.2.1, q.2.2.2]) ∧
    (∀ x ∈ e8RootsIn [q.2.2.1, q.2.2.2], x ∈ e8RootsIn [q.1, q.2.1, q.2.2.1, q.2.2.2]) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8TwoA2_orth : ∀ q ∈ e8TwoA2, ∀ x ∈ e8RootsIn [q.1, q.2.1],
    ∀ y ∈ e8RootsIn [q.2.2.1, q.2.2.2], iform (τ := Tag.E8) x y = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8TwoA2_edges : ∀ q ∈ e8TwoA2, (q.1, q.2.1) ∈ e8Edges ∧ (q.2.2.1, q.2.2.2) ∈ e8Edges := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8D4A2_union_fwd : ∀ x ∈ e8RootsIn [1, 2, 3, 4, 6, 7],
    x ∈ e8RootsIn [1, 2, 3, 4] ∨ x ∈ e8RootsIn [6, 7] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8D4A2_union_bwd :
    (∀ x ∈ e8RootsIn [1, 2, 3, 4], x ∈ e8RootsIn [1, 2, 3, 4, 6, 7]) ∧
    (∀ x ∈ e8RootsIn [6, 7], x ∈ e8RootsIn [1, 2, 3, 4, 6, 7]) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e8D4A2_orth : ∀ x ∈ e8RootsIn [1, 2, 3, 4], ∀ y ∈ e8RootsIn [6, 7],
    iform (τ := Tag.E8) x y = 0 := by
  decide +kernel

section Dispatch

variable {ε : ℤ}

theorem parabolicRoots_neg {J : Set (Fin Tag.E8.rank)} {β : V8} (h : β ∈ parabolicRoots Tag.E8 J) :
    -β ∈ parabolicRoots Tag.E8 J :=
  ⟨IsRoot.neg h.1, fun i hi => by simp [h.2 i hi]⟩

theorem parabolicRoots_zsmul {J : Set (Fin Tag.E8.rank)} {β : V8}
    (h : β ∈ parabolicRoots Tag.E8 J) (hε : ε = 1 ∨ ε = -1) : ε • β ∈ parabolicRoots Tag.E8 J := by
  rcases hε with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]
    exact parabolicRoots_neg h

theorem image_preimage_smul (u : WeylGroup Tag.E8) (A : Set V8) :
    (fun γ => u • γ) '' {α | u • α ∈ A} = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨u⁻¹ • x, by simpa using hx, by simp⟩

theorem conj_smul_apply (u : WeylGroup Tag.E8) (α : V8) :
    (u * e8T3W * u⁻¹) • (u • α) = u • (e8T3W • α) := by
  rw [mul_smul, mul_smul, inv_smul_smul]

theorem stab_preimage (hε : ε = 1 ∨ ε = -1) (u : WeylGroup Tag.E8) (A : Set V8)
    (hA : ∀ β ∈ A, (u * e8T3W * u⁻¹) • β ∈ A) (hAn : ∀ β ∈ A, ε • β ∈ A) :
    ∀ α ∈ {α : V8 | u • α ∈ A}, e8T3We ε • α ∈ {α : V8 | u • α ∈ A} := by
  intro α hα
  have h1 : u • (e8T3We ε • α) = ε • ((u * e8T3W * u⁻¹) • (u • α)) := by
    rw [e8T3We_smul hε, smul_zsmul_E8, conj_smul_apply]
  show u • (e8T3We ε • α) ∈ A
  rw [h1]
  exact hAn _ (hA _ hα)

theorem neg_preimage (A : Set V8) (u : WeylGroup Tag.E8) (hA : ∀ β ∈ A, -β ∈ A) :
    ∀ α ∈ {α : V8 | u • α ∈ A}, -α ∈ {α : V8 | u • α ∈ A} := by
  intro α hα
  show u • (-α) ∈ A
  rw [smul_neg_E8]
  exact hA _ hα

end Dispatch

section Cases

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {k : Type}
  [Field k] [Algebra k L] [IsAlgClosure k L] {ε : ℤ}

theorem e8T3_coe_edge (a b : Fin Tag.E8.rank) :
    (↑({a, b} : Finset (Fin Tag.E8.rank)) : Set (Fin Tag.E8.rank)) =
      {i | i ∈ ([a, b] : List (Fin Tag.E8.rank))} := by
  ext i
  simp

theorem e8T3_coe_two (a b c d : Fin Tag.E8.rank) :
    (↑({a, b, c, d} : Finset (Fin Tag.E8.rank)) : Set (Fin Tag.E8.rank)) =
      {i | i ∈ ([a, b, c, d] : List (Fin Tag.E8.rank))} := by
  ext i
  simp

theorem e8T3_coe_d4a2 :
    (↑({1, 2, 3, 4, 6, 7} : Finset (Fin Tag.E8.rank)) : Set (Fin Tag.E8.rank)) =
      {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))} := by
  ext i
  simp

theorem e8T3_coe_d4 :
    (↑({1, 2, 3, 4} : Finset (Fin Tag.E8.rank)) : Set (Fin Tag.E8.rank)) =
      {i | i ∈ ([1, 2, 3, 4] : List (Fin Tag.E8.rank))} := by
  ext i
  simp

theorem e8T3_coe_e6 :
    (↑({0, 1, 2, 3, 4, 5} : Finset (Fin Tag.E8.rank)) : Set (Fin Tag.E8.rank)) = e6Nodes Tag.E8 := by
  ext i
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
    e6Nodes, Set.mem_ofPred_eq]
  revert i
  decide +kernel

theorem d4Nodes_eq_list : d4Nodes Tag.E8 = {i | i ∈ ([1, 2, 3, 4] : List (Fin Tag.E8.rank))} := by
  ext i
  exact mem_d4Nodes_iff i

theorem dispatch_A2 (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    {ent : Fin Tag.E8.rank × Fin Tag.E8.rank × List (Fin Tag.E8.rank)} (hent : ent ∈ e8A2Trans)
    (hS : (fun γ => u • γ) '' S =
      parabolicRoots Tag.E8 {i | i ∈ ([ent.1, ent.2.1] : List (Fin Tag.E8.rank))})
    (hSneg : ∀ α ∈ S, -α ∈ S) (hSw : ∀ α ∈ S, e8T3We ε • α ∈ S) :
    LayerConclusion n (iterateFrobenius L ℓ f) S k := by
  have hSeq := exists_v_of_A2 hent hS
  subst hSeq
  exact layer_A2_conclusion hf hk hε hq2 _ n hnm hnC hnW hSw hSneg

theorem cols_2A2_split {T : WeylGroup Tag.E8} {a b c d : Fin Tag.E8.rank}
    (h : [colT T a, colT T b, colT T c, colT T d] ∈ rot2Cols a b c d) :
    [colT T a, colT T b] ∈ rotCols a b ∧ [colT T c, colT T d] ∈ rotCols c d := by
  simp only [rot2Cols, List.mem_flatMap, List.mem_map] at h
  obtain ⟨r, hr, s, hs, hrs⟩ := h
  have hr2 : r.length = 2 := by
    simp only [rotCols, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  have hrs' : r ++ s = [colT T a, colT T b] ++ [colT T c, colT T d] := hrs
  obtain ⟨h1, h2⟩ := List.append_inj hrs' hr2
  rw [← h1, ← h2]
  exact ⟨hr, hs⟩

theorem d4Cols_length : ∀ c ∈ d4Cols, c.length = 4 := by decide +kernel

theorem cols_D4A2_split {T : WeylGroup Tag.E8}
    (h : [colT T 1, colT T 2, colT T 3, colT T 4, colT T 6, colT T 7] ∈ d4a2Cols) :
    [colT T 1, colT T 2, colT T 3, colT T 4] ∈ d4Cols ∧ [colT T 6, colT T 7] ∈ rotCols 6 7 := by
  simp only [d4a2Cols, List.mem_flatMap, List.mem_map] at h
  obtain ⟨c, hc, r, hr, hcr⟩ := h
  have hc4 := d4Cols_length c hc
  have hcr' : c ++ r = [colT T 1, colT T 2, colT T 3, colT T 4] ++ [colT T 6, colT T 7] := hcr
  obtain ⟨h1, h2⟩ := List.append_inj hcr' hc4
  rw [← h1, ← h2]
  exact ⟨hc, hr⟩

theorem preimage_eq_image_inv (u : WeylGroup Tag.E8) (A : Set V8) :
    {α : V8 | u • α ∈ A} = (fun γ => u⁻¹ • γ) '' A := by
  ext x
  constructor
  · intro hx
    exact ⟨u • x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    show u • u⁻¹ • y ∈ A
    rwa [smul_inv_smul]

theorem set_eq_preimage (u : WeylGroup Tag.E8) {S A : Set V8}
    (hS : (fun γ => u • γ) '' S = A) : S = {α : V8 | u • α ∈ A} := by
  ext x
  constructor
  · intro hx
    show u • x ∈ A
    rw [← hS]
    exact ⟨x, hx, rfl⟩
  · intro hx
    have : u • x ∈ (fun γ => u • γ) '' S := by rw [hS]; exact hx
    obtain ⟨y, hy, hyx⟩ := this
    rw [smul_left_cancel_iff] at hyx
    exact hyx ▸ hy

theorem dispatch_2A2 (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (u : WeylGroup Tag.E8) {S : Set V8} {a b c d : Fin Tag.E8.rank}
    (hq : (a, b, c, d) ∈ e8TwoA2)
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 {i | i ∈ ([a, b, c, d] : List _)})
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 {i | i ∈ ([a, b, c, d] : List (Fin Tag.E8.rank))},
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 {i | i ∈ ([a, b, c, d] : List _)}) :
    LayerConclusion n (iterateFrobenius L ℓ f) S k := by
  obtain ⟨hq1, hq2'⟩ := e8TwoA2_edges (a, b, c, d) hq
  obtain ⟨ent₁, hent₁, h11, h12⟩ := e8A2Trans_edges (a, b) hq1
  obtain ⟨ent₂, hent₂, h21, h22⟩ := e8A2Trans_edges (c, d) hq2'
  have hcols := e8T3_cols_2A2 hrelT hq (by rw [e8T3_coe_two]; exact hmapsT)
  obtain ⟨hc1, hc2⟩ := cols_2A2_split hcols
  have hm1 := maps_of_colsA2 (e8Edges_ne _ hq1) hc1
  have hm2 := maps_of_colsA2 (e8Edges_ne _ hq2') hc2
  have hSeq := set_eq_preimage u hS
  have hSu : S = {α : V8 | u • α ∈ parabolicRoots Tag.E8 {i | i ∈ ([a, b] : List _)}} ∪
      {α : V8 | u • α ∈ parabolicRoots Tag.E8 {i | i ∈ ([c, d] : List _)}} := by
    rw [hSeq]
    ext α
    simp only [Set.mem_union, Set.mem_ofPred_eq, mem_parabolicRoots_iff_E8]
    constructor
    · intro h
      exact e8TwoA2_union_fwd (a, b, c, d) hq _ h
    · rintro (h | h)
      · exact (e8TwoA2_union_bwd (a, b, c, d) hq).1 _ h
      · exact (e8TwoA2_union_bwd (a, b, c, d) hq).2 _ h
  have hS₁ : (fun γ => u • γ) '' {α : V8 | u • α ∈ parabolicRoots Tag.E8
      {i | i ∈ ([a, b] : List _)}} = parabolicRoots Tag.E8
        {i | i ∈ ([ent₁.1, ent₁.2.1] : List (Fin Tag.E8.rank))} := by
    rw [image_preimage_smul]
    simp only [h11, h12]
  have hS₂ : (fun γ => u • γ) '' {α : V8 | u • α ∈ parabolicRoots Tag.E8
      {i | i ∈ ([c, d] : List _)}} = parabolicRoots Tag.E8
        {i | i ∈ ([ent₂.1, ent₂.2.1] : List (Fin Tag.E8.rank))} := by
    rw [image_preimage_smul]
    simp only [h21, h22]
  have hv₁ := exists_v_of_A2 hent₁ hS₁
  have hv₂ := exists_v_of_A2 hent₂ hS₂
  have hSv₁ : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₁.2.2),
      e8T3We ε • α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₁.2.2) := by
    rw [← hv₁]
    exact stab_preimage hε u _ hm1 (fun β hβ => parabolicRoots_zsmul hβ hε)
  have hSv₂ : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₂.2.2),
      e8T3We ε • α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₂.2.2) := by
    rw [← hv₂]
    exact stab_preimage hε u _ hm2 (fun β hβ => parabolicRoots_zsmul hβ hε)
  have hSn₁ : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₁.2.2),
      -α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₁.2.2) := by
    rw [← hv₁]
    exact neg_preimage _ u (fun β hβ => parabolicRoots_neg hβ)
  have hSn₂ : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₂.2.2),
      -α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₂.2.2) := by
    rw [← hv₂]
    exact neg_preimage _ u (fun β hβ => parabolicRoots_neg hβ)
  have horth : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₁.2.2),
      ∀ β ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent₂.2.2),
        iform (τ := Tag.E8) α β = 0 := by
    intro α hα β hβ
    rw [← hv₁] at hα
    rw [← hv₂] at hβ
    have hxa : u • α ∈ e8RootsIn [a, b] := (mem_parabolicRoots_iff_E8 _).1 hα
    have hyb : u • β ∈ e8RootsIn [c, d] := (mem_parabolicRoots_iff_E8 _).1 hβ
    rw [← iform_smul u]
    exact e8TwoA2_orth (a, b, c, d) hq _ hxa _ hyb
  rw [hSu, hv₁, hv₂]
  exact layer_2A2 hf hk hε hq2 _ _ n hnm hnC hnW hSv₁ hSn₁ hSv₂ hSn₂ horth

theorem dispatch_D4 (hD4 : D4TrialityLayer Tag.E8) (hε : ε = 1 ∨ ε = -1) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 (d4Nodes Tag.E8))
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8)) :
    LayerConclusion n (iterateFrobenius L ℓ f) S k := by
  have hcols := e8T3_cols_D4 hrelT (by rw [e8T3_coe_d4, ← d4Nodes_eq_list]; exact hmapsT)
  obtain ⟨a, b, c, hab, hbc, hac, ha, hb, hc, u', hu', hcert⟩ := e8T3_D4_cert hcols hε
  have hSeq : S = (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) := by
    rw [← preimage_eq_image_inv]
    exact set_eq_preimage u hS
  rw [hSeq]
  refine layer_D4 hD4 hf hk u⁻¹ n hnm hnC a b c hab hbc hac ha hb hc ⟨u', hu', fun α hα => ?_⟩
  have h1 : ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α =
      ε • ((u * e8T3W * u⁻¹) • α) := by
    have := conj_smul_eq hε hnW u⁻¹ α
    simpa using this
  rw [h1]
  exact hcert α hα

theorem dispatch_E6 (hE6 : E6Layer Tag.E8) (hε : ε = 1 ∨ ε = -1) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 (e6Nodes Tag.E8))
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8)) :
    LayerConclusion n (iterateFrobenius L ℓ f) S k := by
  have hSeq : S = (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    rw [← preimage_eq_image_inv]
    exact set_eq_preimage u hS
  rw [hSeq]
  have h1 : ∀ α : V8, ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α =
      ε • ((u * e8T3W * u⁻¹) • α) := fun α => by
    have := conj_smul_eq hε hnW u⁻¹ α
    simpa using this
  refine layer_E6 hE6 hf hk hε u⁻¹ n hnm hnC (fun α hα => ?_) (fun α hα => ?_)
  · rw [h1]
    exact parabolicRoots_zsmul (hmapsT α hα) hε
  · have hee : ∀ x : V8, ε • ε • x = x := fun x => by
      have : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
      rw [smul_smul, this, one_smul]
    rw [h1 α, h1 (ε • (u * e8T3W * u⁻¹) • α), smul_zsmul_E8, hee, hee]
    exact hrelT α

theorem dispatch_D4A2 (hD4 : D4TrialityLayer Tag.E8) (hε : ε = 1 ∨ ε = -1)
    (hq2 : ε = -1 → 2 < ℓ ^ f) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (u : WeylGroup Tag.E8) {S : Set V8}
    (hS : (fun γ => u • γ) '' S =
      parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))})
    (hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x = 0)
    (hmapsT : ∀ β ∈ parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))},
      (u * e8T3W * u⁻¹) • β ∈
        parabolicRoots Tag.E8 {i | i ∈ ([1, 2, 3, 4, 6, 7] : List (Fin Tag.E8.rank))}) :
    LayerConclusion n (iterateFrobenius L ℓ f) S k := by
  have hcols := e8T3_cols_D4A2 hrelT (by rw [e8T3_coe_d4a2]; exact hmapsT)
  obtain ⟨hcD, hcA⟩ := cols_D4A2_split hcols
  obtain ⟨a, b, c, hab, hbc, hac, ha, hb, hc, u', hu', hcert⟩ := e8T3_D4_cert hcD hε
  have h67 : ((6 : Fin Tag.E8.rank), (7 : Fin Tag.E8.rank)) ∈ e8Edges := by decide
  obtain ⟨ent, hent, h1, h2⟩ := e8A2Trans_edges (6, 7) h67
  have hm := maps_of_colsA2 (e8Edges_ne _ h67) hcA
  have hSeq := set_eq_preimage u hS
  have hSu : S = {α : V8 | u • α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8)} ∪
      {α : V8 | u • α ∈ parabolicRoots Tag.E8 {i | i ∈ ([6, 7] : List (Fin Tag.E8.rank))}} := by
    rw [hSeq]
    ext α
    simp only [Set.mem_union, Set.mem_ofPred_eq, d4Nodes_eq_list, mem_parabolicRoots_iff_E8]
    constructor
    · intro h
      exact e8D4A2_union_fwd _ h
    · rintro (h | h)
      · exact e8D4A2_union_bwd.1 _ h
      · exact e8D4A2_union_bwd.2 _ h
  have hS₂ : (fun γ => u • γ) '' {α : V8 | u • α ∈ parabolicRoots Tag.E8
      {i | i ∈ ([6, 7] : List (Fin Tag.E8.rank))}} = parabolicRoots Tag.E8
        {i | i ∈ ([ent.1, ent.2.1] : List (Fin Tag.E8.rank))} := by
    rw [image_preimage_smul]
    simp only [h1, h2]
  have hv₂ := exists_v_of_A2 hent hS₂
  have hSv₂ : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2),
      e8T3We ε • α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2) := by
    rw [← hv₂]
    exact stab_preimage hε u _ hm (fun β hβ => parabolicRoots_zsmul hβ hε)
  have hSn₂ : ∀ α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2),
      -α ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2) := by
    rw [← hv₂]
    exact neg_preimage _ u (fun β hβ => parabolicRoots_neg hβ)
  have horth : ∀ α ∈ (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      ∀ β ∈ sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2),
        iform (τ := Tag.E8) α β = 0 := by
    intro α hα β hβ
    rw [← preimage_eq_image_inv] at hα
    rw [← hv₂] at hβ
    have hxa : u • α ∈ e8RootsIn [1, 2, 3, 4] := by
      have : u • α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8) := hα
      rw [d4Nodes_eq_list] at this
      exact (mem_parabolicRoots_iff_E8 _).1 this
    have hyb : u • β ∈ e8RootsIn [6, 7] := (mem_parabolicRoots_iff_E8 _).1 hβ
    rw [← iform_smul u]
    exact e8D4A2_orth _ hxa _ hyb
  have hSeq' : S = (fun γ => u⁻¹ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) ∪
      sigmaSetE8 (u⁻¹ * (coxeterSystem Tag.E8).wordProd ent.2.2) := by
    rw [hSu, hv₂, preimage_eq_image_inv]
  rw [hSeq']
  refine layer_D4A2 hD4 hf hk hε hq2 u⁻¹ _ n hnm hnC hnW a b c hab hbc hac ha hb hc
    ⟨u', hu', fun α hα => ?_⟩ hSv₂ hSn₂ horth
  have h1 : ((u⁻¹)⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * u⁻¹) • α =
      ε • ((u * e8T3W * u⁻¹) • α) := by
    have := conj_smul_eq hε hnW u⁻¹ α
    simpa using this
  rw [h1]
  exact hcert α hα

theorem e8T3_layers (hD4 : D4TrialityLayer Tag.E8) (hE6 : E6Layer Tag.E8)
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (u : WeylGroup Tag.E8) (J : Finset (Fin Tag.E8.rank)) (hJ : J ≠ Finset.univ) {S : Set V8}
    (hS : (fun γ => u • γ) '' S = parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)))
    (hSneg : ∀ α ∈ S, -α ∈ S) (hSw : ∀ α ∈ S, e8T3We ε • α ∈ S) :
    LayerConclusion n (iterateFrobenius L ℓ f) S k := by
  classical
  have hS3 : ∀ α ∈ S, e8T3W • α ∈ S := stab_of_We hε hSneg hSw
  have hrelT : ∀ x : V8, (u * e8T3W * u⁻¹) • (u * e8T3W * u⁻¹) • x + (u * e8T3W * u⁻¹) • x + x
      = 0 := fun x => rel_conj e8T3W_rel u x
  have hmapsT : ∀ β ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)),
      (u * e8T3W * u⁻¹) • β ∈ parabolicRoots Tag.E8 (↑J : Set (Fin Tag.E8.rank)) := by
    intro β hβ
    rw [← hS] at hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    show (u * e8T3W * u⁻¹) • u • α ∈ _
    rw [conj_smul_apply, ← hS]
    exact ⟨_, hS3 α hα, rfl⟩
  have hsup := e8T3_supports hJ hrelT hmapsT
  rcases e8T3_supports_cases hsup with hJe | ⟨e, he, hJe⟩ | ⟨q, hq, hJe⟩ | hJe | hJe | hJe
  ·
    subst hJe
    have hSe : S = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun α hα => ?_
      have h1 : u • α ∈ parabolicRoots Tag.E8 (↑(∅ : Finset (Fin Tag.E8.rank)) :
          Set (Fin Tag.E8.rank)) := by
        rw [← hS]
        exact ⟨α, hα, rfl⟩
      exact isRoot_ne_zero h1.1 (funext fun i => h1.2 i (by simp))
    rw [hSe]
    exact layer_empty n _ k
  ·
    obtain ⟨ent, hent, h1, h2⟩ := e8A2Trans_edges e he
    refine dispatch_A2 hε hq2 hf hk n hnm hnC hnW u hent ?_ hSneg hSw
    rw [hS, hJe, e8T3_coe_edge, h1, h2]
  ·
    obtain ⟨⟨a, b, c, d⟩, hq', rfl⟩ : ∃ q' : Fin Tag.E8.rank × Fin Tag.E8.rank × Fin Tag.E8.rank ×
        Fin Tag.E8.rank, q' ∈ e8TwoA2 ∧ q' = q := ⟨q, hq, rfl⟩
    have hJ' : J = {a, b, c, d} := hJe
    subst hJ'
    exact dispatch_2A2 hε hq2 hf hk n hnm hnC hnW u hq (by rw [← e8T3_coe_two]; exact hS) hrelT
      (by rw [← e8T3_coe_two]; exact hmapsT)
  ·
    subst hJe
    exact dispatch_D4 hD4 hε hf hk n hnm hnC hnW u (by rw [← coe_d4_finset]; exact hS) hrelT
      (by rw [← coe_d4_finset]; exact hmapsT)
  ·
    subst hJe
    exact dispatch_E6 hE6 hε hf hk n hnm hnC hnW u (by rw [← e8T3_coe_e6]; exact hS) hrelT
      (by rw [← e8T3_coe_e6]; exact hmapsT)
  ·
    subst hJe
    exact dispatch_D4A2 hD4 hε hq2 hf hk n hnm hnC hnW u (by rw [← e8T3_coe_d4a2]; exact hS)
      hrelT (by rw [← e8T3_coe_d4a2]; exact hmapsT)

end Cases

end CFSG.RankThree.PartOne.KE6
