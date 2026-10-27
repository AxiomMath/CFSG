module

public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveData
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Matrix

@[expose] def phi5 : List ℤ := [1, 1, 1, 1, 1]

@[expose] def congOK (f m F q : List ℤ) : Bool :=
  pnorm (padd f (pscale (-1) (pmul m F))) == pnorm (pmul q phi5)

@[expose] def unitOK (m m' : List ℤ) (n : ℤ) (q : List ℤ) : Bool :=
  pnorm (padd (pmul m m') [-n]) == pnorm (pmul q phi5)

@[expose] def e8F5Coeffs (l : List ℤ) : List ℤ := lmulVec Tag.E8.rank e8F5BInv l

@[expose] def entryOK (F G : List ℤ) (e : E8F5Entry) : Bool :=
  congOK ((e8F5Coeffs e.root).take 4) e.m F e.q₁ &&
    congOK ((e8F5Coeffs e.root).drop 4) e.m G e.q₂ && unitOK e.m e.m' e.n e.q₃ &&
    (e.n == 1 || e.n == -1)

@[expose] def e8F5ClassesOK : Bool :=
  (List.range 12).all fun i => (e8F5Classes.getD i []).length == 20 &&
    (e8F5Classes.getD i []).all (entryOK (e8F5Reps.getD i default).1 (e8F5Reps.getD i default).2)

theorem e8F5ClassesOK_eq : e8F5ClassesOK = true := by
  decide +kernel

@[expose] def e8F5ClassRoots (i : ℕ) : List (List ℤ) := (e8F5Classes.getD i []).map (·.root)

theorem e8F5_perm : ((List.range 12).flatMap e8F5ClassRoots).Perm Tag.E8.artifactRoots := by
  decide +kernel

@[expose] def unitRepOK (F G : List ℤ) (w : E8F5Unit) : Bool :=
  unitOK (if w.isF then F else G) w.cof w.n w.q && (w.n == 1 || w.n == -1)

@[expose] def e8F5UnitsOK : Bool :=
  (List.range 12).all fun i =>
    unitRepOK (e8F5Reps.getD i default).1 (e8F5Reps.getD i default).2 (e8F5Units.getD i default)

theorem e8F5UnitsOK_eq : e8F5UnitsOK = true := by
  decide +kernel

@[expose] def crossPoly (i j : ℕ) : List ℤ :=
  padd (pmul (e8F5Reps.getD i default).1 (e8F5Reps.getD j default).2)
    (pscale (-1) (pmul (e8F5Reps.getD j default).1 (e8F5Reps.getD i default).2))

@[expose] def e8F5CrossOK : Bool :=
  (List.range 12).all fun i => (List.range 12).all fun j => !(decide (i < j)) ||
    e8F5Crosses.any fun x => x.i == i && x.j == j && unitOK (crossPoly i j) x.cof x.n x.q &&
      (x.n == 1 || x.n == -1 || x.n == 5 || x.n == -5)

theorem e8F5CrossOK_eq : e8F5CrossOK = true := by
  decide +kernel

section Sound

variable {K : Type*} [CommRing K]

theorem peval_eq_of_congOK {f m F q : List ℤ} (h : congOK f m F q = true) {r : K}
    (hr : peval phi5 r = 0) : peval f r = peval m r * peval F r := by
  have h1 := congrArg (fun cs => peval cs r) (beq_iff_eq.1 h)
  simp only [peval_pnorm, peval_padd, peval_pscale, peval_pmul, hr, mul_zero, Int.cast_neg,
    Int.cast_one] at h1
  linear_combination h1

theorem peval_mul_of_unitOK {m m' : List ℤ} {n : ℤ} {q : List ℤ} (h : unitOK m m' n q = true)
    {r : K} (hr : peval phi5 r = 0) : peval m r * peval m' r = n :=
  peval_mul_eq_of_cong (beq_iff_eq.1 h) hr

end Sound

theorem intCast_ne_zero_of_small {p : ℕ} [Fact p.Prime] (hp5 : 5 < p) {n : ℤ}
    (hn : n = 1 ∨ n = -1 ∨ n = 5 ∨ n = -5) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by
    rcases hn with rfl | rfl | rfl | rfl <;> simp <;> omega)
  rcases hn with rfl | rfl | rfl | rfl <;> simp at h0

section Char

variable {K : Type*} [CommRing K]

@[expose] def e8F5Y (r a b : K) : Fin Tag.E8.rank → K :=
  fun k => if (k : ℕ) < 4 then r ^ (k : ℕ) * a else r ^ ((k : ℕ) - 4) * b

@[expose] def e8F5Z (r a b : K) : Fin Tag.E8.rank → K :=
  (((toMat Tag.E8.rank e8F5BInv).map (Int.cast : ℤ → K)).transpose).mulVec (e8F5Y r a b)

@[expose] def e8RootKernel (z : Fin Tag.E8.rank → K) : Set (Fin Tag.E8.rank → ℤ) :=
  {α | IsRoot Tag.E8 α ∧ charVal z α = 0}

theorem charVal_e8F5Z (r a b : K) (l : List ℤ) :
    charVal (e8F5Z r a b) (toVec Tag.E8.rank l) =
      peval ((e8F5Coeffs l).take 4) r * a + peval ((e8F5Coeffs l).drop 4) r * b := by
  rw [e8F5Z, charVal_mulVec, ← toVec_lmulVec]
  have hc : e8F5Coeffs l = List.ofFn (toVec Tag.E8.rank (lmulVec Tag.E8.rank e8F5BInv l)) :=
    (ofFn_toVec (length_lmulVec _ _)).symm
  rw [hc]
  generalize toVec Tag.E8.rank (lmulVec Tag.E8.rank e8F5BInv l) = c
  show (∑ i : Fin 8, ((c i : ℤ) : K) * e8F5Y r a b i) =
    peval [c (0 : Fin 8), c (1 : Fin 8), c (2 : Fin 8), c (3 : Fin 8)] r * a +
      peval [c (4 : Fin 8), c (5 : Fin 8), c (6 : Fin 8), c (7 : Fin 8)] r * b
  rw [Fin.sum_univ_eight]
  simp only [e8F5Y, peval_cons, peval_nil]
  norm_num
  ring

end Char

@[expose] def e8F5DisjointOK : Bool :=
  (List.range 12).all fun i => (e8F5ClassRoots i).Nodup && (List.range 12).all fun j =>
    i == j || (e8F5ClassRoots i).all fun l => !((e8F5ClassRoots j).contains l)

theorem e8F5DisjointOK_eq : e8F5DisjointOK = true := by
  decide +kernel

theorem e8F5ClassRoots_nodup {i : ℕ} (hi : i < 12) : (e8F5ClassRoots i).Nodup := by
  have h := List.all_eq_true.1 e8F5DisjointOK_eq i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem e8F5ClassRoots_disjoint {i j : ℕ} (hi : i < 12) (hj : j < 12) (hij : i ≠ j) {l : List ℤ}
    (hli : l ∈ e8F5ClassRoots i) : l ∉ e8F5ClassRoots j := by
  have h := List.all_eq_true.1 e8F5DisjointOK_eq i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at h
  have h2 := List.all_eq_true.1 h.2 j (List.mem_range.2 hj)
  simp only [Bool.or_eq_true, beq_iff_eq, hij, false_or, List.all_eq_true] at h2
  have h3 := h2 l hli
  simpa using h3

theorem mem_artifactRoots_of_class {i : ℕ} (hi : i < 12) {l : List ℤ}
    (hl : l ∈ e8F5ClassRoots i) : l ∈ Tag.E8.artifactRoots :=
  e8F5_perm.subset (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, hl⟩)

theorem exists_class_of_mem {l : List ℤ} (hl : l ∈ Tag.E8.artifactRoots) :
    ∃ i < 12, l ∈ e8F5ClassRoots i := by
  obtain ⟨i, hi, hl'⟩ := List.mem_flatMap.1 (e8F5_perm.symm.subset hl)
  exact ⟨i, List.mem_range.1 hi, hl'⟩

@[expose] def e8F5ClassSet (i : ℕ) : Set (Fin Tag.E8.rank → ℤ) :=
  {α | List.ofFn α ∈ e8F5ClassRoots i}

theorem isRoot_of_mem_classSet {i : ℕ} (hi : i < 12) {α : Fin Tag.E8.rank → ℤ}
    (h : α ∈ e8F5ClassSet i) : IsRoot Tag.E8 α :=
  isRoot_iff_mem_artifactRoots.2 (mem_artifactRoots_of_class hi h)

theorem exists_classSet {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) :
    ∃ i < 12, α ∈ e8F5ClassSet i :=
  exists_class_of_mem (isRoot_iff_mem_artifactRoots.1 hα)

theorem classSet_unique {i j : ℕ} (hi : i < 12) (hj : j < 12) {α : Fin Tag.E8.rank → ℤ}
    (h₁ : α ∈ e8F5ClassSet i) (h₂ : α ∈ e8F5ClassSet j) : i = j := by
  by_contra hij
  exact e8F5ClassRoots_disjoint hi hj hij h₁ h₂

theorem ncard_classSet {i : ℕ} (hi : i < 12) : (e8F5ClassSet i).ncard = 20 := by
  classical
  have e : e8F5ClassSet i = toVec Tag.E8.rank '' ↑(e8F5ClassRoots i).toFinset := by
    ext α
    simp only [e8F5ClassSet, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe,
      List.mem_toFinset]
    constructor
    · intro h
      exact ⟨_, h, toVec_ofFn α⟩
    · rintro ⟨l, hl, rfl⟩
      rwa [ofFn_toVec (length_of_mem_artifactRoots (mem_artifactRoots_of_class hi hl))]
  have hinj : Set.InjOn (toVec Tag.E8.rank) ↑(e8F5ClassRoots i).toFinset := by
    intro l hl l' hl' h
    simp only [Finset.mem_coe, List.mem_toFinset] at hl hl'
    exact toVec_injOn_artifactRoots Tag.E8 (mem_artifactRoots_of_class hi hl)
      (mem_artifactRoots_of_class hi hl') h
  rw [e, hinj.ncard_image, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (e8F5ClassRoots_nodup hi)]
  have h := List.all_eq_true.1 e8F5ClassesOK_eq i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [e8F5ClassRoots, List.length_map]
  exact h.1

section Lines

variable {p : ℕ}

@[expose] def e8F5F (r : ZMod p) (i : ℕ) : ZMod p := peval (e8F5Reps.getD i default).1 r

@[expose] def e8F5G (r : ZMod p) (i : ℕ) : ZMod p := peval (e8F5Reps.getD i default).2 r

@[expose] def e8F5Line (r : ZMod p) (i : ℕ) : Set (ZMod p × ZMod p) :=
  {ab | e8F5F r i * ab.1 + e8F5G r i * ab.2 = 0}

@[expose] def e8F5Pt (r : ZMod p) (i : ℕ) : ZMod p × ZMod p := (e8F5G r i, -e8F5F r i)

theorem e8F5Pt_mem (r : ZMod p) (i : ℕ) : e8F5Pt r i ∈ e8F5Line r i := by
  show e8F5F r i * e8F5G r i + e8F5G r i * -e8F5F r i = 0
  ring

end Lines

section Classes

variable {p : ℕ} [Fact p.Prime]

theorem charVal_classSet (hp5 : 5 < p) {r : ZMod p} (hr : peval phi5 r = 0) (a b : ZMod p)
    {i : ℕ} (hi : i < 12) {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8F5ClassSet i) :
    ∃ μ : ZMod p, μ ≠ 0 ∧
      charVal (e8F5Z r a b) α = μ * (e8F5F r i * a + e8F5G r i * b) := by
  obtain ⟨e, he, hroot⟩ := List.mem_map.1 (show List.ofFn α ∈ e8F5ClassRoots i from hα)
  have hok := List.all_eq_true.1 e8F5ClassesOK_eq i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at hok
  have hentry := List.all_eq_true.1 hok.2 e he
  simp only [entryOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hentry
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hentry
  have hα' : α = toVec Tag.E8.rank e.root := by rw [hroot, toVec_ofFn]
  rw [hα', charVal_e8F5Z, peval_eq_of_congOK h₁ hr, peval_eq_of_congOK h₂ hr]
  refine ⟨peval e.m r, fun h0 => ?_, by rw [e8F5F, e8F5G]; ring⟩
  have hu := peval_mul_of_unitOK h₃ hr
  rw [h0, zero_mul] at hu
  exact intCast_ne_zero_of_small hp5 (by rcases h₄ with h | h <;> simp [h]) hu.symm

theorem mem_e8RootKernel_iff (hp5 : 5 < p) {r : ZMod p} (hr : peval phi5 r = 0) (a b : ZMod p)
    {i : ℕ} (hi : i < 12) {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ e8F5ClassSet i) :
    α ∈ e8RootKernel (e8F5Z r a b) ↔ (a, b) ∈ e8F5Line r i := by
  obtain ⟨μ, hμ, h⟩ := charVal_classSet hp5 hr a b hi hα
  simp only [e8RootKernel, Set.mem_ofPred_eq, e8F5Line, h, mul_eq_zero, hμ, false_or,
    isRoot_of_mem_classSet hi hα, true_and]

theorem e8F5_rep_ne_zero (hp5 : 5 < p) {r : ZMod p} (hr : peval phi5 r = 0) {i : ℕ}
    (hi : i < 12) : e8F5F r i ≠ 0 ∨ e8F5G r i ≠ 0 := by
  have h := List.all_eq_true.1 e8F5UnitsOK_eq i (List.mem_range.2 hi)
  simp only [unitRepOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h₁, h₂⟩ := h
  have hu := peval_mul_of_unitOK h₁ hr
  have hn := intCast_ne_zero_of_small (p := p) hp5 (n := (e8F5Units.getD i default).n)
    (by rcases h₂ with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  by_cases hF : (e8F5Units.getD i default).isF = true
  · left
    intro h0
    rw [ite_eq_left hF, ← e8F5F, h0, zero_mul] at hu
    exact hn hu.symm
  · right
    intro h0
    rw [ite_eq_right hF, ← e8F5G, h0, zero_mul] at hu
    exact hn hu.symm

theorem e8F5_cross_ne_zero (hp5 : 5 < p) {r : ZMod p} (hr : peval phi5 r = 0) {i j : ℕ}
    (hi : i < 12) (hj : j < 12) (hij : i < j) :
    e8F5F r i * e8F5G r j - e8F5F r j * e8F5G r i ≠ 0 := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 e8F5CrossOK_eq i (List.mem_range.2 hi)) j
    (List.mem_range.2 hj)
  simp only [hij, decide_true, Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨x, -, ⟨⟨⟨-, -⟩, hx⟩, hn⟩⟩ := h
  have hu := peval_mul_of_unitOK hx hr
  have hD : peval (crossPoly i j) r = e8F5F r i * e8F5G r j - e8F5F r j * e8F5G r i := by
    simp only [crossPoly, peval_padd, peval_pmul, peval_pscale, e8F5F, e8F5G, Int.cast_neg,
      Int.cast_one]
    ring
  intro h0
  rw [hD, h0, zero_mul] at hu
  refine intCast_ne_zero_of_small hp5 ?_ hu.symm
  rcases hn with ((h | h) | h) | h <;> simp [h]

theorem e8F5_line_unique (hp5 : 5 < p) {r : ZMod p} (hr : peval phi5 r = 0) {i j : ℕ}
    (hi : i < 12) (hj : j < 12) {ab : ZMod p × ZMod p} (hab : ab ≠ 0) (h₁ : ab ∈ e8F5Line r i)
    (h₂ : ab ∈ e8F5Line r j) : i = j := by
  by_contra hij
  have key : ∀ i j, i < 12 → j < 12 → i < j → ab ∈ e8F5Line r i → ab ∈ e8F5Line r j →
      False := by
    intro i j hi hj hij h₁ h₂
    have hD := e8F5_cross_ne_zero hp5 hr hi hj hij
    simp only [e8F5Line, Set.mem_ofPred_eq] at h₁ h₂
    have ha : (e8F5F r i * e8F5G r j - e8F5F r j * e8F5G r i) * ab.1 = 0 := by
      linear_combination e8F5G r j * h₁ - e8F5G r i * h₂
    have hb : (e8F5F r i * e8F5G r j - e8F5F r j * e8F5G r i) * ab.2 = 0 := by
      linear_combination e8F5F r i * h₂ - e8F5F r j * h₁
    apply hab
    ext
    · exact (mul_eq_zero.1 ha).resolve_left hD
    · exact (mul_eq_zero.1 hb).resolve_left hD
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j hi hj h h₁ h₂
  · exact key j i hj hi h h₂ h₁

theorem e8F5Pt_ne_zero (hp5 : 5 < p) {r : ZMod p} (hr : peval phi5 r = 0) {i : ℕ}
    (hi : i < 12) : e8F5Pt r i ≠ 0 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [e8F5Pt, Prod.fst_zero, Prod.snd_zero] at h1 h2
  rcases e8F5_rep_ne_zero hp5 hr hi with h | h
  · exact h (neg_eq_zero.1 h2)
  · exact h h1

theorem e8RootKernel_eq_classSet (hp5 : 5 < p) {r : ZMod p} (hr : peval phi5 r = 0)
    {ab : ZMod p × ZMod p} (hab : ab ≠ 0) {i : ℕ} (hi : i < 12) (hl : ab ∈ e8F5Line r i) :
    e8RootKernel (e8F5Z r ab.1 ab.2) = e8F5ClassSet i := by
  ext α
  constructor
  · intro hα
    obtain ⟨j, hj, hαj⟩ := exists_classSet hα.1
    have hlj := (mem_e8RootKernel_iff hp5 hr ab.1 ab.2 hj hαj).1 hα
    rw [e8F5_line_unique hp5 hr hi hj hab hl hlj]
    exact hαj
  · intro hα
    exact (mem_e8RootKernel_iff hp5 hr ab.1 ab.2 hi hα).2 hl

theorem e8RootKernel_eq_empty (hp5 : 5 < p) {r : ZMod p} (hr : peval phi5 r = 0)
    {ab : ZMod p × ZMod p} (hl : ∀ i < 12, ab ∉ e8F5Line r i) :
    e8RootKernel (e8F5Z r ab.1 ab.2) = ∅ := by
  ext α
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hα
  obtain ⟨j, hj, hαj⟩ := exists_classSet hα.1
  exact hl j hj ((mem_e8RootKernel_iff hp5 hr ab.1 ab.2 hj hαj).1 hα)

end Classes

end CFSG.RankThree.Lattice
