module

public import CFSG.RankThree.PartOne.SEITZ6.G2Span

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6

abbrev Mask : Type := GIdx → Bool

@[expose] def mxor (a b : Mask) : Mask := fun c => xor (a c) (b c)

@[expose] def mzero : Mask := fun _ => false

@[expose] def mxors : List Mask → Mask
  | [] => mzero
  | a :: l => mxor a (mxors l)

@[expose] def munit (c : GIdx) : Mask := fun c' => decide (c' = c)

@[expose] def colMask : Col (Tag.rootCertificate .G2) → Mask
  | none => mzero
  | some (a, z) => fun c' => decide (c' = a) && decide (z % 2 = 1)

@[expose] def gCol (ox : Bool) (i : Fin (Tag.rank .G2)) (j : ℕ) (c : GIdx) :
    Col (Tag.rootCertificate .G2) :=
  if ox then xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i j c
  else yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i j c

@[expose] def nMask (ox : Bool) (i : Fin (Tag.rank .G2)) (c : GIdx) : Mask :=
  mxors [colMask (gCol ox i 1 c), colMask (gCol ox i 2 c), colMask (gCol ox i 3 c)]

@[expose] def nMap (ox : Bool) (i : Fin (Tag.rank .G2)) (m : Mask) : Mask :=
  mxors (gIdxList.map fun c => if m c then nMask ox i c else mzero)

@[expose] def ei : Bool → Fin (Tag.rank .G2)
  | false => e0
  | true => e1

inductive Step
  | n (ox : Bool) (i : Bool) (j : ℕ)
  | add (j j' : ℕ)

@[expose] def applyStep (L : List Mask) : Step → Mask
  | .n ox i j => nMap ox (ei i) (L.getD j mzero)
  | .add j j' => mxor (L.getD j mzero) (L.getD j' mzero)

@[expose] def runSteps : List Mask → List Step → List Mask
  | L, [] => L
  | L, s :: ss => runSteps (L ++ [applyStep L s]) ss

@[expose] def longMasks : List Mask := longIdx.map munit

@[expose] def script : List Step :=
  [Step.n true true 0, Step.n false false 0, Step.n false true 1, Step.n false false 6,
    Step.n false true 7, Step.n true false 9, Step.n false true 9, Step.n false false 10,
    Step.add 1 7, Step.add 8 10, Step.add 15 12, Step.add 8 10, Step.add 2 6, Step.add 18 11,
    Step.add 5 13, Step.add 3 5, Step.add 21 8, Step.add 22 13]

@[expose] def maskBEq (a b : Mask) : Bool := gIdxList.all fun c => a c == b c

@[expose] def allUnitsB : Bool :=
  gIdxList.all fun c => (runSteps longMasks script).any fun m => maskBEq (munit c) m

theorem allUnitsB_eq : allUnitsB = true := by decide +kernel

theorem gIdxList_nodup : gIdxList.Nodup := by decide +kernel

theorem sum_univ_eq_list {M : Type*} [AddCommMonoid M] (f : GIdx → M) :
    ∑ c : GIdx, f c = (gIdxList.map f).sum := by
  have h : gIdxList.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun c => List.mem_toFinset.2 (mem_gIdxList c)
  rw [← List.sum_toFinset f gIdxList_nodup, h]

theorem getD_mem {P : Mask → Prop} (hz : P mzero) {L : List Mask} (hL : ∀ m ∈ L, P m) (j : ℕ) :
    P (L.getD j mzero) := by
  by_cases hj : j < L.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hL _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (not_lt.1 hj)]
    exact hz

theorem runSteps_mem {P : Mask → Prop} (hz : P mzero)
    (hn : ∀ ox i m, P m → P (nMap ox (ei i) m)) (hadd : ∀ a b, P a → P b → P (mxor a b)) :
    ∀ (ss : List Step) (L : List Mask), (∀ m ∈ L, P m) → ∀ m ∈ runSteps L ss, P m := by
  intro ss
  induction ss with
  | nil => intro L hL; exact hL
  | cons s ss ih =>
    intro L hL
    refine ih (L ++ [applyStep L s]) ?_
    intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hL m hm
    · rw [List.mem_singleton] at hm
      subst hm
      cases s with
      | n ox i j => exact hn ox i _ (getD_mem hz hL j)
      | add j j' => exact hadd _ _ (getD_mem hz hL j) (getD_mem hz hL j')

variable {K : Type} [Field K]

noncomputable def g2MaskVec (K : Type) [Field K] (m : Mask) : RootModule .G2 K :=
  ∑ c : GIdx, if m c then Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c) 1 else 0

section Sound

variable [CharP K 2]

theorem vadd_self (v : RootModule .G2 K) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

omit [CharP K 2] in
theorem g2MaskVec_mzero : g2MaskVec K mzero = 0 := by simp [g2MaskVec, mzero]

theorem g2MaskVec_mxor (a b : Mask) : g2MaskVec K (mxor a b) = g2MaskVec K a + g2MaskVec K b := by
  unfold g2MaskVec
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mxor]
  by_cases ha : a c = true <;> by_cases hb : b c = true <;> simp [ha, hb, vadd_self]

theorem g2MaskVec_mxors (l : List Mask) : g2MaskVec K (mxors l) = (l.map (g2MaskVec K)).sum := by
  induction l with
  | nil => simp [mxors, g2MaskVec_mzero]
  | cons a l ih => simp [mxors, g2MaskVec_mxor, ih]

omit [CharP K 2] in
theorem g2MaskVec_munit (c : GIdx) :
    g2MaskVec K (munit c) = Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c) 1 := by
  unfold g2MaskVec munit
  simp [Finset.sum_ite_eq']

theorem toVec_colMask (u : Col (Tag.rootCertificate .G2)) :
    toVec (Tag.rootCertificate_check .G2) K u = g2MaskVec K (colMask u) := by
  rcases u with _ | ⟨a, z⟩
  · simp [colMask, g2MaskVec_mzero]
  · rw [toVec_some]
    have h1 : g2MaskVec K (colMask (some (a, z))) =
        if z % 2 = 1 then Finsupp.single (toLabel (Tag.rootCertificate_check .G2) a) 1 else 0 := by
      unfold g2MaskVec colMask
      by_cases hz : z % 2 = 1
      · simp [hz]
      · simp [hz]
    rw [h1]
    by_cases hz : z % 2 = 1
    · obtain ⟨q, hq⟩ : ∃ q : ℤ, z = 2 * q + 1 := ⟨z / 2, by omega⟩
      have h2 : (z : K) = 1 := by
        rw [hq]
        push_cast
        rw [show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul, zero_add]
      rw [ite_eq_left hz, h2, one_smul]
    · obtain ⟨q, hq⟩ : ∃ q : ℤ, z = 2 * q := ⟨z / 2, by omega⟩
      have h2 : (z : K) = 0 := by
        rw [hq]
        push_cast
        rw [show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul]
      rw [ite_eq_right hz, h2, zero_smul]

noncomputable def nOp (K : Type) [Field K] (ox : Bool) (i : Fin (Tag.rank .G2)) :
    Module.End K (RootModule .G2 K) :=
  if ox then xCoeff .G2 K i 1 + xCoeff .G2 K i 2 + xCoeff .G2 K i 3
  else yCoeff .G2 K i 1 + yCoeff .G2 K i 2 + yCoeff .G2 K i 3

theorem nOp_single (ox : Bool) (i : Fin (Tag.rank .G2)) (c : GIdx) :
    nOp K ox i (Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c) 1) =
      g2MaskVec K (nMask ox i c) := by
  have hcol : ∀ j : ℕ, (if ox then xCoeff .G2 K i j else yCoeff .G2 K i j)
      (Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c) 1) =
        g2MaskVec K (colMask (gCol ox i j c)) := by
    intro j
    cases ox
    · simp only [gCol, Bool.false_eq_true, ite_false]
      rw [yCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i j c,
        toVec_colMask]
    · simp only [gCol, ite_true]
      rw [xCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i j c,
        toVec_colMask]
  have h1 := hcol 1
  have h2 := hcol 2
  have h3 := hcol 3
  unfold nMask
  rw [g2MaskVec_mxors]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← h1, ← h2, ← h3]
  cases ox <;> simp [nOp, add_assoc]

theorem nOp_g2MaskVec (ox : Bool) (i : Fin (Tag.rank .G2)) (m : Mask) :
    nOp K ox i (g2MaskVec K m) = g2MaskVec K (nMap ox i m) := by
  have h1 : g2MaskVec K (nMap ox i m) =
      ∑ c : GIdx, if m c then g2MaskVec K (nMask ox i c) else 0 := by
    unfold nMap
    rw [g2MaskVec_mxors, List.map_map, sum_univ_eq_list]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    by_cases hc : m c = true <;> simp [hc, g2MaskVec_mzero]
  rw [h1]
  unfold g2MaskVec
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : m c = true
  · simp only [hc, ite_true]
    exact nOp_single ox i c
  · simp [hc]

end Sound

section Span

variable [CharP K 2] (k : Subfield K) {R : Subgroup (adjointGroup .G2 K)}

omit [CharP K 2] in
theorem nOp_eq (ox : Bool) (i : Fin (Tag.rank .G2)) (w : RootModule .G2 K) :
    nOp K ox i w = (if ox then xOp .G2 K i 1 w else yOp .G2 K i 1 w) - w := by
  cases ox
  · have h := congrArg (fun f => f w) (yOp_eq_sum_yCoeff (τ := .G2) (R := K) i (1 : K))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow, one_smul,
      yCoeff_zero, LinearMap.add_apply, Module.End.one_apply] at h
    simp only [nOp, Bool.false_eq_true, ite_false, LinearMap.add_apply]
    rw [h]
    abel
  · have h := congrArg (fun f => f w) (xOp_eq_sum_xCoeff (τ := .G2) (R := K) i (1 : K))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow, one_smul,
      xCoeff_zero, LinearMap.add_apply, Module.End.one_apply] at h
    simp only [nOp, ite_true, LinearMap.add_apply]
    rw [h]
    abel

omit [CharP K 2] in
theorem nOp_mem_span (hR : ∀ p < 12, xp p (1 : K) ∈ R) (ox : Bool) (i : Fin (Tag.rank .G2))
    {w : RootModule .G2 K} (hw : w ∈ Submodule.span k (longOrbit R)) :
    nOp K ox i w ∈ Submodule.span k (longOrbit R) := by
  rw [nOp_eq]
  refine Submodule.sub_mem _ ?_ hw
  have hi : i = e0 ∨ i = e1 := by
    fin_cases i
    · exact .inl rfl
    · exact .inr rfl
  cases ox <;> rcases hi with rfl | rfl
  · simp only [Bool.false_eq_true, ite_false]
    rw [← xp2_smul]
    exact smul_mem_span k (hR 2 (by norm_num)) hw
  · simp only [Bool.false_eq_true, ite_false]
    rw [← xp5_smul]
    exact smul_mem_span k (hR 5 (by norm_num)) hw
  · simp only [ite_true]
    rw [← xp0_smul]
    exact smul_mem_span k (hR 0 (by norm_num)) hw
  · simp only [ite_true]
    rw [← xp1_smul]
    exact smul_mem_span k (hR 1 (by norm_num)) hw

theorem g2MaskVec_mem_span (hR : ∀ p < 12, xp p (1 : K) ∈ R) :
    ∀ m ∈ runSteps longMasks script, g2MaskVec K m ∈ Submodule.span k (longOrbit R) := by
  refine runSteps_mem (P := fun m => g2MaskVec K m ∈ Submodule.span k (longOrbit R)) ?_ ?_ ?_ script
    longMasks ?_
  · simp [g2MaskVec_mzero]
  · intro ox i m hm
    rw [← nOp_g2MaskVec]
    exact nOp_mem_span k hR ox (ei i) hm
  · intro a b ha hb
    rw [g2MaskVec_mxor]
    exact add_mem ha hb
  · intro m hm
    simp only [longMasks, List.mem_map] at hm
    obtain ⟨c, hc, rfl⟩ := hm
    simp only [longIdx, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hc
    obtain ⟨m, hm, rfl⟩ := hc
    rw [g2MaskVec_munit, single_toLabel_inr]
    refine Submodule.subset_span ⟨1, R.one_mem, m.val, ?_, by rw [one_smul]⟩
    simp only [longPos, Finset.mem_insert, Finset.mem_singleton]
    simpa using hm

theorem single_mem_span_f2 (hR : ∀ p < 12, xp p (1 : K) ∈ R) (b : Label .G2) :
    Finsupp.single b 1 ∈ Submodule.span k (longOrbit R) := by
  obtain ⟨c, rfl⟩ := surjective_toLabel (Tag.rootCertificate_check .G2) b
  have h : munit c ∈ runSteps longMasks script := by
    have h1 := allUnitsB_eq
    simp only [allUnitsB, List.all_eq_true, List.any_eq_true] at h1
    obtain ⟨m, hm, hmb⟩ := h1 c (mem_gIdxList c)
    have : munit c = m := by
      funext c'
      simp only [maskBEq, List.all_eq_true, beq_iff_eq] at hmb
      exact hmb c' (mem_gIdxList c')
    rwa [this]
  have := g2MaskVec_mem_span k hR _ h
  rwa [g2MaskVec_munit] at this

end Span

end CFSG.RankThree.PartOne.SEITZ2
