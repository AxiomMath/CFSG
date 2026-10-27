module

public import CFSG.Sporadic.Schreier.TitsGraph
public import CFSG.Sporadic.Schreier.TitsGraphCheck
public import CFSG.Sporadic.Schreier.TitsPrim
public import CFSG.Sporadic.Schreier.TitsCentral
public import Mathlib.Combinatorics.SimpleGraph.Maps

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def titsGraphAut : Subgroup (Equiv.Perm (Fin 1755)) where
  carrier := {σ | ∀ x y, titsPointGraph.Adj (σ x) (σ y) ↔ titsPointGraph.Adj x y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := fun ha hb x y => (ha _ _).trans (hb x y)
  inv_mem' := fun {σ} h x y => by
    rw [← h (σ⁻¹ x) (σ⁻¹ y), perm_apply_inv, perm_apply_inv]

theorem mem_titsGraphAut {σ : Equiv.Perm (Fin 1755)} :
    σ ∈ titsGraphAut ↔ ∀ x y, titsPointGraph.Adj (σ x) (σ y) ↔ titsPointGraph.Adj x y :=
  Iff.rfl

theorem mem_titsGraphAut_iff (σ : Equiv.Perm (Fin 1755)) :
    σ ∈ titsGraphAut ↔
      ∃ e : SimpleGraph.Iso titsPointGraph titsPointGraph, e.toEquiv = σ := by
  constructor
  · intro h
    exact ⟨⟨σ, fun {a b} => h a b⟩, rfl⟩
  · rintro ⟨e, rfl⟩ x y
    exact e.map_adj_iff

theorem mem_titsLine {v : Fin 2925} {x : Fin 1755} :
    x ∈ titsLine v ↔ ∃ j, titsKappa j = v ∧ titsBeta j = x := by
  simp [titsLine]

theorem adj_iff_line {x y : Fin 1755} :
    titsPointGraph.Adj x y ↔ x ≠ y ∧ ∃ v, x ∈ titsLine v ∧ y ∈ titsLine v := by
  show (x ≠ y ∧ ∃ e f : Fin 8775, titsBeta e = x ∧ titsBeta f = y ∧
    titsKappa e = titsKappa f) ↔ _
  simp only [mem_titsLine]
  constructor
  · rintro ⟨h, e, f, he, hf, hef⟩
    exact ⟨h, titsKappa e, ⟨e, rfl, he⟩, ⟨f, hef.symm, hf⟩⟩
  · rintro ⟨h, v, ⟨e, he, hex⟩, ⟨f, hf, hfy⟩⟩
    exact ⟨h, e, f, hex, hfy, he.trans hf.symm⟩

theorem titsA_le_titsGraphAut :
    titsA ≤ titsGraphAut := by
  intro g hg x y
  rw [adj_iff_line, adj_iff_line]
  have hmem : ∀ v (z : Fin 1755), g z ∈ titsLine (titsLineHom ⟨g, hg⟩ v) ↔ z ∈ titsLine v := by
    intro v z
    rw [titsLine_lineHom]
    exact Finset.smul_mem_smul_finset_iff g
  constructor
  · rintro ⟨hne, w, hx, hy⟩
    obtain ⟨v, rfl⟩ := (titsLineHom ⟨g, hg⟩).surjective w
    exact ⟨fun h => hne (by rw [h]), v, (hmem v x).1 hx, (hmem v y).1 hy⟩
  · rintro ⟨hne, v, hx, hy⟩
    exact ⟨fun h => hne (g.injective h), _, (hmem v x).2 hx, (hmem v y).2 hy⟩

theorem ptsHas_iff
    {v : ℕ} (hv : v < 2925) {u : Fin 1755} :
    ptsHas v u = true ↔ u ∈ titsLine ⟨v, hv⟩ := by
  rw [titsLine_eq, ptsHas]
  simp only [Bool.or_eq_true, beq_iff_eq, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
    titsLinePt_val ⟨v, hv⟩ (by norm_num : 0 < 3), titsLinePt_val ⟨v, hv⟩ (by norm_num : 1 < 3),
    titsLinePt_val ⟨v, hv⟩ (by norm_num : 2 < 3), Nat.add_zero]
  constructor
  · rintro ((h | h) | h) <;> simp [h]
  · rintro (h | h | h) <;> simp [h]

theorem mem_nbr_lt
    {x : Fin 1755} {n : ℕ} (h : n ∈ (titsNbr[(x : ℕ)]!).toList) : n < 1755 := by
  obtain ⟨hsz, -, -, hentry⟩ := titsGraph_check.1 x x.2
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at h
  obtain ⟨i, hi, rfl⟩ := h
  have := (hentry i (hsz ▸ hi)).1
  rwa [getElem!_pos (titsNbr[(x : ℕ)]!) i hi] at this

theorem adj_iff_mem_nbr
    {x y : Fin 1755} :
    titsPointGraph.Adj x y ↔ (y : ℕ) ∈ (titsNbr[(x : ℕ)]!).toList := by
  obtain ⟨hsz, -, -, hentry⟩ := titsGraph_check.1 x x.2
  constructor
  · intro h
    obtain ⟨hne, v, hx, hy⟩ := adj_iff_line.1 h
    have key : ∀ k < 3, ∀ k' < 3, x = titsLinePt v k → y = titsLinePt v k' →
        (y : ℕ) ∈ (titsNbr[(x : ℕ)]!).toList := by
      intro k hk k' hk' ex ey
      have hkk : k ≠ k' := by
        rintro rfl
        exact hne (ex.trans ey.symm)
      have := titsGraph_check.2.1 v v.2 k hk k' hk' hkk
      rw [Array.contains_iff_mem] at this
      rw [Array.mem_toList_iff, ex, ey, titsLinePt_val v hk, titsLinePt_val v hk']
      exact this
    rw [titsLine_eq] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;>
      exact key _ (by norm_num) _ (by norm_num) hx hy
  · intro h
    rw [Array.mem_toList_iff, Array.mem_iff_getElem] at h
    obtain ⟨i, hi, hiy⟩ := h
    obtain ⟨-, hne, hvl, hpx, hpy⟩ := hentry i (hsz ▸ hi)
    rw [getElem!_pos (titsNbr[(x : ℕ)]!) i hi, hiy] at hne hpy
    refine adj_iff_line.2 ⟨fun e => hne (by rw [e]), ⟨_, hvl⟩, (ptsHas_iff hvl).1 hpx,
      (ptsHas_iff hvl).1 hpy⟩

theorem nbr_nodup
    (x : Fin 1755) : (titsNbr[(x : ℕ)]!).toList.Nodup :=
  (titsGraph_check.1 x x.2).2.2.1.imp ne_of_lt

theorem ncard_neighborSet
    (x : Fin 1755) : (titsPointGraph.neighborSet x).ncard = 10 := by
  have himg : Fin.val '' titsPointGraph.neighborSet x = {n | n ∈ (titsNbr[(x : ℕ)]!).toList} := by
    ext n
    simp only [Set.mem_image, SimpleGraph.mem_neighborSet, adj_iff_mem_nbr, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hn
      exact ⟨⟨n, mem_nbr_lt hn⟩, hn, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, himg, ncard_list_set (nbr_nodup x),
    Array.length_toList, (titsGraph_check.1 x x.2).1]

@[expose] def Preserves (σ : Equiv.Perm (Fin 1755)) (col : Array ℕ) : Prop :=
  ∀ x : Fin 1755, col[((σ x : Fin 1755) : ℕ)]! = col[(x : ℕ)]!

@[expose] def permN (σ : Equiv.Perm (Fin 1755)) (w : ℕ) : ℕ :=
  if h : w < 1755 then ((σ ⟨w, h⟩ : Fin 1755) : ℕ) else w

theorem permN_of_lt (σ : Equiv.Perm (Fin 1755)) {w : ℕ} (h : w < 1755) :
    permN σ w = ((σ ⟨w, h⟩ : Fin 1755) : ℕ) := by
  simp [permN, h]

theorem nbr_perm
    {σ : Equiv.Perm (Fin 1755)} (hσ : σ ∈ titsGraphAut) (x : Fin 1755) :
    (titsNbr[((σ x : Fin 1755) : ℕ)]!).toList.Perm
      ((titsNbr[(x : ℕ)]!).toList.map (permN σ)) := by
  have hnd : ((titsNbr[(x : ℕ)]!).toList.map (permN σ)).Nodup := by
    refine (nbr_nodup x).map_on fun a ha b hb e => ?_
    rw [permN_of_lt σ (mem_nbr_lt ha), permN_of_lt σ (mem_nbr_lt hb)] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e))
  refine (List.perm_ext_iff_of_nodup (nbr_nodup (σ x)) hnd).2 fun n => ?_
  constructor
  · intro hn
    have hlt := mem_nbr_lt hn
    refine List.mem_map.2 ⟨((σ⁻¹ ⟨n, hlt⟩ : Fin 1755) : ℕ), ?_, ?_⟩
    · have hadj : titsPointGraph.Adj (σ x) (σ (σ⁻¹ ⟨n, hlt⟩)) := by
        rw [perm_apply_inv]
        exact adj_iff_mem_nbr.2 hn
      exact adj_iff_mem_nbr.1 ((hσ x _).1 hadj)
    · rw [permN_of_lt σ (σ⁻¹ ⟨n, hlt⟩).2]
      simp only [Fin.eta, perm_apply_inv]
  · intro hn
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hn
    have hlt := mem_nbr_lt hw
    rw [permN_of_lt σ hlt]
    exact adj_iff_mem_nbr.1 ((hσ x ⟨w, hlt⟩).2 (adj_iff_mem_nbr.2 hw))

theorem pairwise_mergeSort_le (l : List ℕ) :
    (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b col hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  simpa using this

theorem mergeSort_eq_of_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    l₁.mergeSort (fun a b => decide (a ≤ b)) = l₂.mergeSort fun a b => decide (a ≤ b) :=
  List.Perm.eq_of_pairwise' (r := fun a b : ℕ => a ≤ b) (pairwise_mergeSort_le l₁)
    (pairwise_mergeSort_le l₂)
    (((List.mergeSort_perm l₁ _).trans h).trans (List.mergeSort_perm l₂ _).symm)

theorem nbrColors_eq
    {σ : Equiv.Perm (Fin 1755)} (hσ : σ ∈ titsGraphAut) {col : Array ℕ}
    (hc : Preserves σ col) (x : Fin 1755) :
    nbrColors col ((σ x : Fin 1755) : ℕ) = nbrColors col (x : ℕ) := by
  unfold nbrColors
  apply mergeSort_eq_of_perm
  refine ((nbr_perm hσ x).map _).trans ?_
  rw [List.map_map]
  refine List.Perm.of_eq (List.map_congr_left fun w hw => ?_)
  have hlt := mem_nbr_lt hw
  simp only [Function.comp_apply, permN_of_lt σ hlt]
  exact hc ⟨w, hlt⟩

theorem sigCode_eq
    {σ : Equiv.Perm (Fin 1755)} (hσ : σ ∈ titsGraphAut) {col : Array ℕ}
    (hc : Preserves σ col) (x : Fin 1755) :
    sigCode col ((σ x : Fin 1755) : ℕ) = sigCode col (x : ℕ) := by
  unfold sigCode
  rw [nbrColors_eq hσ hc x, hc x]

theorem refineStep_get (col : Array ℕ) (y : Fin 1755) :
    (refineStep col)[(y : ℕ)]! = CFSG.SectionRank.Native.Tits.bsearch
      (sortedValues (Array.ofFn (n := 1755) fun x => sigCode col x)) (sigCode col y) := by
  rw [refineStep, relabel, getElem!_pos _ _ (by simp), Array.getElem_map, Array.getElem_ofFn]

theorem refineStep_preserves
    {σ : Equiv.Perm (Fin 1755)} (hσ : σ ∈ titsGraphAut) {col : Array ℕ}
    (hc : Preserves σ col) : Preserves σ (refineStep col) := by
  intro x
  rw [refineStep_get, refineStep_get, sigCode_eq hσ hc x]

theorem iterate_preserves
    {σ : Equiv.Perm (Fin 1755)} (hσ : σ ∈ titsGraphAut) {col : Array ℕ}
    (hc : Preserves σ col) (r : ℕ) : Preserves σ (Nat.iterate refineStep r col) := by
  induction r with
  | zero => exact hc
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact refineStep_preserves hσ ih

@[expose] def titsIndivPt (k : ℕ) : Fin 1755 := finPt 1755 titsIndiv[k]!

theorem titsIndiv_lt {k : ℕ} (hk : k < 6) : titsIndiv[k]! < 1755 := by
  interval_cases k <;> decide

theorem titsIndivPt_val {k : ℕ} (hk : k < 6) : ((titsIndivPt k : Fin 1755) : ℕ) = titsIndiv[k]! :=
  finPt_val (titsIndiv_lt hk)

theorem mem_take_titsIndiv {i : ℕ} (hi : i ≤ 6) {y : ℕ} :
    y ∈ titsIndiv.take i ↔ ∃ k < i, titsIndiv[k]! = y := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < i := by simp at hk; omega
    refine ⟨k, hk', ?_⟩
    rw [List.getElem_take, getElem!_pos titsIndiv k (by simp [titsIndiv]; omega)]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k, by simp [titsIndiv]; omega, ?_⟩
    rw [List.getElem_take, getElem!_pos titsIndiv k (by simp [titsIndiv]; omega)]

theorem initColor_get (i : ℕ) (y : Fin 1755) : (initColor i)[(y : ℕ)]! =
    if (titsIndiv.take i).contains (y : ℕ) then (titsIndiv.take i).idxOf (y : ℕ) + 1 else 0 := by
  rw [initColor, getElem!_pos _ _ (by simp), Array.getElem_ofFn]

theorem initColor_preserves {σ : Equiv.Perm (Fin 1755)} {i : ℕ} (hi : i ≤ 6)
    (hfix : ∀ k < i, σ (titsIndivPt k) = titsIndivPt k) : Preserves σ (initColor i) := by
  intro x
  rw [initColor_get, initColor_get]
  by_cases hx : (titsIndiv.take i).contains (x : ℕ) = true
  · rw [List.contains_iff_mem, mem_take_titsIndiv hi] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    have : x = titsIndivPt k := Fin.ext (by rw [titsIndivPt_val (by omega), hkx])
    rw [this, hfix k hk]
  · have hσx : (titsIndiv.take i).contains ((σ x : Fin 1755) : ℕ) = false := by
      rw [Bool.eq_false_iff]
      intro h
      rw [List.contains_iff_mem, mem_take_titsIndiv hi] at h
      obtain ⟨k, hk, hkx⟩ := h
      apply hx
      rw [List.contains_iff_mem, mem_take_titsIndiv hi]
      refine ⟨k, hk, ?_⟩
      have : σ x = σ (titsIndivPt k) := by
        rw [hfix k hk]
        exact Fin.ext (by rw [titsIndivPt_val (by omega), hkx])
      rw [σ.injective this, titsIndivPt_val (by omega)]
    rw [Bool.not_eq_true] at hx
    rw [hσx, hx]
    rfl

@[expose] def titsAutStab (i : ℕ) : Subgroup (Equiv.Perm (Fin 1755)) where
  carrier := {σ | σ ∈ titsGraphAut ∧ ∀ k < i, σ (titsIndivPt k) = titsIndivPt k}
  one_mem' := ⟨one_mem _, fun _ _ => rfl⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, fun k hk => by
    rw [Equiv.Perm.mul_apply, hb.2 k hk, ha.2 k hk]⟩
  inv_mem' := fun h => ⟨inv_mem h.1, fun k hk => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (h.2 k hk).symm⟩

theorem mem_titsAutStab {i : ℕ} {σ : Equiv.Perm (Fin 1755)} :
    σ ∈ titsAutStab i ↔ σ ∈ titsGraphAut ∧ ∀ k < i, σ (titsIndivPt k) = titsIndivPt k :=
  Iff.rfl

theorem titsAutStab_zero : titsAutStab 0 = titsGraphAut := by
  ext σ
  simp [mem_titsAutStab]

theorem stableColor_preserves
    {i : ℕ} (hi : i ≤ 6) {σ : Equiv.Perm (Fin 1755)}
    (hσ : σ ∈ titsAutStab i) : Preserves σ (stableColor i) :=
  iterate_preserves hσ.1 (initColor_preserves hi hσ.2) _

theorem refineOK_facts {i : ℕ} (hi : i < 7) :
    (stableColor i).size = 1755 ∧ numCells (stableColor i) = titsCellCounts[i]! ∧
      numCells (refineStep (stableColor i)) = numCells (stableColor i) ∧
      (i < 6 → cellSize (stableColor i) titsIndiv[i]! = titsCellSizes[i]!) := by
  have h := titsRefine_check.1 i hi
  simp only [refineOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun hi6 => ?_⟩
  rcases h4 with h4 | h4
  · omega
  · exact h4

theorem ncard_cell (col : Array ℕ) (a : ℕ) :
    {y : Fin 1755 | col[(y : ℕ)]! = a}.ncard =
      ((List.range 1755).filter fun y => col[y]! == a).length := by
  have himg : Fin.val '' {y : Fin 1755 | col[(y : ℕ)]! = a} =
      {n | n ∈ (List.range 1755).filter fun y => col[y]! == a} := by
    ext n
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_filter, List.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hn, hy⟩
      exact ⟨⟨n, hn⟩, hy, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, himg,
    ncard_list_set ((List.nodup_range).filter _)]

theorem orbit_titsAutStab_le
    {i : ℕ} (hi : i < 6) :
    (MulAction.orbit (titsAutStab i) (titsIndivPt i)).ncard ≤ titsCellSizes[i]! := by
  have hsub : MulAction.orbit (titsAutStab i) (titsIndivPt i) ⊆
      {y : Fin 1755 | (stableColor i)[(y : ℕ)]! =
        (stableColor i)[((titsIndivPt i : Fin 1755) : ℕ)]!} := by
    rintro _ ⟨g, rfl⟩
    exact stableColor_preserves (by omega) g.2 (titsIndivPt i)
  calc (MulAction.orbit (titsAutStab i) (titsIndivPt i)).ncard
      ≤ {y : Fin 1755 | (stableColor i)[(y : ℕ)]! =
          (stableColor i)[((titsIndivPt i : Fin 1755) : ℕ)]!}.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = titsCellSizes[i]! := by
        rw [ncard_cell, titsIndivPt_val hi, ← (refineOK_facts (by omega)).2.2.2 hi]
        rfl

theorem stableColor6_injective {x y : Fin 1755}
    (h : (stableColor 6)[(x : ℕ)]! = (stableColor 6)[(y : ℕ)]!) : x = y := by
  have hsz := (refineOK_facts (by norm_num : 6 < 7)).1
  have hnd : (stableColor 6).toList.Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.1 (titsRefine_check.2.imp ne_of_lt)
  rw [getElem!_pos _ _ (by rw [hsz]; exact x.2), getElem!_pos _ _ (by rw [hsz]; exact y.2),
    ← Array.getElem_toList, ← Array.getElem_toList] at h
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h)

theorem titsAutStab_six :
    titsAutStab 6 = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  exact Equiv.ext fun x => stableColor6_injective (stableColor_preserves le_rfl hσ x)

theorem map_stabilizer_titsAutStab (i : ℕ) :
    (MulAction.stabilizer (titsAutStab i) (titsIndivPt i)).map (titsAutStab i).subtype =
      titsAutStab (i + 1) := by
  ext σ
  simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype,
    mem_titsAutStab]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g.2.1, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact g.2.2 k hk
    · exact hg
  · rintro ⟨hσ, hfix⟩
    exact ⟨⟨σ, hσ, fun k hk => hfix k (Nat.lt_succ_of_lt hk)⟩, hfix i (Nat.lt_succ_self i), rfl⟩

theorem card_titsAutStab_le
    {i : ℕ} (hi : i < 6) :
    Nat.card (titsAutStab i) ≤ titsCellSizes[i]! * Nat.card (titsAutStab (i + 1)) := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer (titsAutStab i) (titsIndivPt i))
  rw [MulAction.index_stabilizer,
    ← Subgroup.card_map_of_injective (titsAutStab i).subtype_injective,
    map_stabilizer_titsAutStab] at h
  rw [← h, mul_comm]
  exact Nat.mul_le_mul_right _ (orbit_titsAutStab_le hi)

theorem card_titsGraphAut_le :
    Nat.card titsGraphAut ≤ 35942400 := by
  have h6 : Nat.card (titsAutStab 6) = 1 := by rw [titsAutStab_six, Subgroup.card_bot]
  have h0 := card_titsAutStab_le (i := 0) (by norm_num)
  have h1 := card_titsAutStab_le (i := 1) (by norm_num)
  have h2 := card_titsAutStab_le (i := 2) (by norm_num)
  have h3 := card_titsAutStab_le (i := 3) (by norm_num)
  have h4 := card_titsAutStab_le (i := 4) (by norm_num)
  have h5 := card_titsAutStab_le (i := 5) (by norm_num)
  rw [titsAutStab_zero] at h0
  simp only [titsCellSizes] at h0 h1 h2 h3 h4 h5
  norm_num at h0 h1 h2 h3 h4 h5
  rw [h6] at h5
  omega

theorem titsGraphAut_eq :
    titsGraphAut = titsA :=
  (Subgroup.eq_of_le_of_card_ge titsA_le_titsGraphAut
    (by rw [card_titsA]; exact card_titsGraphAut_le)).symm

theorem titsH0_le_titsGraphAut :
    titsH0 ≤ titsGraphAut := by
  rw [titsGraphAut_eq]
  exact titsH0_le_titsD.trans titsD_le_titsA

theorem neighborSet_zero :
    titsPointGraph.neighborSet 0 = MulAction.orbit titsH0 (1 : Fin 1755) := by
  have horb : (MulAction.orbit titsH0 (1 : Fin 1755)).ncard = 10 := by
    have := titsH0_orbit_ncard (c := 1) (by norm_num)
    exact this
  have hsub : MulAction.orbit titsH0 (1 : Fin 1755) ⊆ titsPointGraph.neighborSet 0 := by
    rintro _ ⟨g, rfl⟩
    have h01 : titsPointGraph.Adj 0 1 := by
      rw [adj_iff_mem_nbr, Array.mem_toList_iff, ← Array.contains_iff_mem]
      exact titsGraph_check.2.2
    have := (titsH0_le_titsGraphAut g.2 0 1).2 h01
    rw [titsH0_fix g g.2] at this
    exact this
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [horb, ncard_neighborSet]) (Set.toFinite _)).symm

theorem CTUC_Tits_point_graph_full_automorphism_group :
    (∀ x, (titsPointGraph.neighborSet x).ncard = 10) ∧
    (∀ σ : Equiv.Perm (Fin 1755),
      σ ∈ titsA ↔ ∃ e : SimpleGraph.Iso titsPointGraph titsPointGraph, e.toEquiv = σ) ∧
    titsGraphAut = titsA ∧ Nat.card titsGraphAut = 35942400 ∧
    (∀ i < 7, numCells (refineStep (stableColor i)) = numCells (stableColor i) ∧
      numCells (stableColor i) = titsCellCounts[i]!) ∧
    (∀ i < 6, cellSize (stableColor i) titsIndiv[i]! = titsCellSizes[i]! ∧
      (MulAction.orbit (titsAutStab i) (titsIndivPt i)).ncard ≤ titsCellSizes[i]!) ∧
    numCells (stableColor 6) = 1755 ∧
    (∀ x y : Fin 1755, (stableColor 6)[(x : ℕ)]! = (stableColor 6)[(y : ℕ)]! → x = y) ∧
    titsAutStab 6 = ⊥ ∧
    titsPointGraph.neighborSet 0 = MulAction.orbit titsH0 (1 : Fin 1755) ∧
    (MulAction.orbit titsH0 (1 : Fin 1755)).ncard = 10 := by
  refine ⟨ncard_neighborSet, fun σ => by rw [← mem_titsGraphAut_iff, titsGraphAut_eq],
    titsGraphAut_eq, by rw [titsGraphAut_eq, card_titsA],
    fun i hi => ⟨(refineOK_facts hi).2.2.1, (refineOK_facts hi).2.1⟩,
    fun i hi => ⟨(refineOK_facts (by omega)).2.2.2 hi, orbit_titsAutStab_le hi⟩,
    (refineOK_facts (by norm_num : 6 < 7)).2.1, fun _ _ h => stableColor6_injective h,
    titsAutStab_six, neighborSet_zero, ?_⟩
  rw [← neighborSet_zero, ncard_neighborSet]

end CFSG.Sporadic.Schreier.Tits
