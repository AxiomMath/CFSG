module

public import CFSG.RankThree.Lattice.SteinbergBIDet

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial

variable {n : ℕ} {K : Type*} [CommRing K]

@[expose] def pair (x : Fin n → ℤ) (z : Fin n → K) : K := (fun i => (x i : K)) ⬝ᵥ z

theorem pair_add (x y : Fin n → ℤ) (z : Fin n → K) : pair (x + y) z = pair x z + pair y z := by
  simp only [pair, Pi.add_apply, Int.cast_add]
  rw [← add_dotProduct]
  rfl

theorem pair_neg (x : Fin n → ℤ) (z : Fin n → K) : pair (-x) z = -pair x z := by
  simp only [pair, Pi.neg_apply, Int.cast_neg]
  rw [← neg_dotProduct]
  rfl

theorem pair_smul (c : ℤ) (x : Fin n → ℤ) (z : Fin n → K) : pair (c • x) z = c * pair x z := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Int.cast_mul, dotProduct, Finset.mul_sum, mul_assoc]

theorem pair_zero (z : Fin n → K) : pair (0 : Fin n → ℤ) z = 0 := by
  simp [pair]

theorem pair_mulVec {w : Matrix (Fin n) (Fin n) ℤ} {z : Fin n → K} {a : K}
    (hz : (w.map (Int.cast : ℤ → K))ᵀ *ᵥ z = a • z) (x : Fin n → ℤ) :
    pair (w *ᵥ x) z = a * pair x z := by
  have h1 : (fun i => ((w *ᵥ x) i : K)) = w.map (Int.cast : ℤ → K) *ᵥ fun i => (x i : K) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [pair, h1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, hz, dotProduct_smul,
    smul_eq_mul]
  rfl

theorem pair_pow_mulVec {w : Matrix (Fin n) (Fin n) ℤ} {z : Fin n → K} {a : K}
    (hz : (w.map (Int.cast : ℤ → K))ᵀ *ᵥ z = a • z) (j : ℕ) (x : Fin n → ℤ) :
    pair ((w ^ j) *ᵥ x) z = a ^ j * pair x z := by
  induction j with
  | zero => rw [pow_zero, one_mulVec, pow_zero, one_mul]
  | succ j ih => rw [pow_succ', ← mulVec_mulVec, pair_mulVec hz, ih, pow_succ', mul_assoc]

theorem pair_eq_zero_of_fixed {F : Type*} [Field F] {w : Matrix (Fin n) (Fin n) ℤ}
    {z : Fin n → F} {a : F} (hz : (w.map (Int.cast : ℤ → F))ᵀ *ᵥ z = a • z) (ha : a ≠ 1)
    {x : Fin n → ℤ} (hx : w *ᵥ x = x) : pair x z = 0 := by
  have h := pair_mulVec hz x
  rw [hx] at h
  have h2 : (1 - a) * pair x z = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm ha))

@[expose] def peval (cs : List ℤ) (a : K) : K :=
  cs.foldr (fun (c : ℤ) (acc : K) => (c : K) + a * acc) 0

@[expose] def padd : List ℤ → List ℤ → List ℤ
  | [], g => g
  | f, [] => f
  | c :: f, d :: g => (c + d) :: padd f g

@[expose] def pscale (c : ℤ) (g : List ℤ) : List ℤ := g.map (c * ·)

@[expose] def pmul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | c :: f, g => padd (pscale c g) (0 :: pmul f g)

theorem peval_nil (a : K) : peval [] a = 0 := rfl

theorem peval_cons (c : ℤ) (cs : List ℤ) (a : K) : peval (c :: cs) a = c + a * peval cs a := rfl

theorem peval_padd (f g : List ℤ) (a : K) : peval (padd f g) a = peval f a + peval g a := by
  induction f generalizing g with
  | nil => simp [padd, peval_nil]
  | cons c f ih =>
    cases g with
    | nil => simp [padd, peval_nil]
    | cons d g =>
      rw [padd, peval_cons, peval_cons, peval_cons, ih, Int.cast_add]
      ring

theorem peval_pscale (c : ℤ) (g : List ℤ) (a : K) : peval (pscale c g) a = c * peval g a := by
  induction g with
  | nil => simp [pscale, peval_nil]
  | cons d g ih =>
    rw [pscale, List.map_cons, ← pscale, peval_cons, peval_cons, ih, Int.cast_mul]
    ring

theorem peval_pmul (f g : List ℤ) (a : K) : peval (pmul f g) a = peval f a * peval g a := by
  induction f with
  | nil => simp [pmul, peval_nil]
  | cons c f ih =>
    rw [pmul, peval_padd, peval_pscale, peval_cons, ih, peval_cons, Int.cast_zero]
    ring

theorem peval_append_zero (cs : List ℤ) (a : K) : peval (cs ++ [0]) a = peval cs a := by
  induction cs with
  | nil => simp [peval_cons, peval_nil]
  | cons c cs ih => rw [List.cons_append, peval_cons, peval_cons, ih]

@[expose] def pnorm (cs : List ℤ) : List ℤ := (cs.reverse.dropWhile (· == 0)).reverse

theorem peval_pnorm (cs : List ℤ) (a : K) : peval (pnorm cs) a = peval cs a := by
  rw [pnorm]
  conv_rhs => rw [← List.reverse_reverse cs]
  generalize cs.reverse = l
  induction l with
  | nil => rfl
  | cons c l ih =>
    by_cases hc : c = 0
    · subst hc
      rw [List.dropWhile_cons_of_pos (by simp), ih, List.reverse_cons, peval_append_zero]
    · rw [List.dropWhile_cons_of_neg (by simpa using hc)]

theorem peval_mul_eq_of_cong {f h q Φ : List ℤ} {d : ℤ}
    (hcong : pnorm (padd (pmul f h) [-d]) = pnorm (pmul q Φ)) {a : K} (ha : peval Φ a = 0) :
    peval f a * peval h a = d := by
  have h1 := congrArg (fun cs => peval cs a) hcong
  simp only [peval_pnorm, peval_padd, peval_pmul, ha, mul_zero, peval_cons, peval_nil,
    mul_zero, add_zero, Int.cast_neg] at h1
  linear_combination h1

@[expose] def lpolyVec (n : ℕ) (W : List (List ℤ)) : List ℤ → List ℤ → List ℤ
  | [], _ => vofFn n fun _ => 0
  | c :: f, x => vadd n (vsmul n c x) (lmulVec n W (lpolyVec n W f x))

theorem pair_lpolyVec {W : List (List ℤ)} {z : Fin n → K} {a : K}
    (hz : ((toMat n W).map (Int.cast : ℤ → K))ᵀ *ᵥ z = a • z) (f x : List ℤ) :
    pair (toVec n (lpolyVec n W f x)) z = peval f a * pair (toVec n x) z := by
  induction f with
  | nil =>
    rw [lpolyVec, toVec_vofFn, peval_nil, zero_mul]
    exact pair_zero z
  | cons c f ih =>
    rw [lpolyVec, toVec_vadd, toVec_vsmul, pair_add, pair_smul, toVec_lmulVec, pair_mulVec hz, ih,
      peval_cons]
    ring

theorem eq_zero_of_pair_cols_eq_zero [Nontrivial K] {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : IsUnit B.det) {z : Fin n → K} (h : ∀ j, pair (fun i => B i j) z = 0) : z = 0 := by
  have hdet : IsUnit ((B.map (Int.cast : ℤ → K))ᵀ).det := by
    rw [Matrix.det_transpose]
    have := hB.map (Int.castRingHom K)
    rwa [RingHom.map_det] at this
  have hmul : (B.map (Int.cast : ℤ → K))ᵀ *ᵥ z = 0 := by
    funext j
    have hj := h j
    simp only [pair, dotProduct] at hj
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, Pi.zero_apply]
    exact hj
  have hinv := hdet.invertible
  have := congrArg (fun v => ((B.map (Int.cast : ℤ → K))ᵀ)⁻¹ *ᵥ v) hmul
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet] using this

@[expose] def vneg (n : ℕ) (v : List ℤ) : List ℤ := vofFn n fun i => -vget v i

theorem toVec_vneg (v : List ℤ) : toVec n (vneg n v) = -toVec n v := by
  funext i
  simp only [vneg, toVec_vofFn, Pi.neg_apply]
  rfl

@[expose] def vcombo (n : ℕ) : List (List ℤ) → List ℤ → List ℤ
  | [], _ => vofFn n fun _ => 0
  | _ :: _, [] => vofFn n fun _ => 0
  | x :: F, c :: cs => vadd n (vsmul n c x) (vcombo n F cs)

theorem pair_vcombo_eq_zero {z : Fin n → K} (F : List (List ℤ)) (cs : List ℤ)
    (hF : ∀ x ∈ F, pair (toVec n x) z = 0) : pair (toVec n (vcombo n F cs)) z = 0 := by
  induction F generalizing cs with
  | nil =>
    rw [vcombo, toVec_vofFn]
    exact pair_zero z
  | cons x F ih =>
    cases cs with
    | nil =>
      rw [vcombo, toVec_vofFn]
      exact pair_zero z
    | cons c cs =>
      rw [vcombo, toVec_vadd, toVec_vsmul, pair_add, pair_smul,
        hF x List.mem_cons_self, ih cs fun y hy => hF y (List.mem_cons_of_mem x hy)]
      ring

structure KernelRow where
  rep : List ℤ
  fc : List ℤ
  f : List ℤ
  h : List ℤ
  d : ℤ
  q : List ℤ
  orbit : List (List ℤ)
  deriving Inhabited

@[expose] def lorbitSigned (n : ℕ) (W : List (List ℤ)) (x : List ℤ) (m : ℕ) (signed : Bool) :
    List (List ℤ) :=
  lorbit n W x m ++ if signed then (lorbit n W x m).map (vneg n) else []

@[expose] def KernelRow.check (n : ℕ) (W : List (List ℤ)) (F : List (List ℤ)) (β Φ : List ℤ)
    (m : ℕ) (signed : Bool) (r : KernelRow) : Bool :=
  decide (vadd n (vcombo n F r.fc) (lpolyVec n W r.f β) = r.rep) &&
    decide (pnorm (padd (pmul r.f r.h) [-r.d]) = pnorm (pmul r.q Φ)) &&
    decide (r.orbit = lorbitSigned n W r.rep m signed)

theorem pair_ne_zero_of_check {F' : Type*} [Field F'] {W : List (List ℤ)}
    {F : List (List ℤ)} {β Φ : List ℤ} {m : ℕ} {signed : Bool} {r : KernelRow}
    (hr : r.check n W F β Φ m signed = true) {z : Fin n → F'} {a : F'}
    (hz : ((toMat n W).map (Int.cast : ℤ → F'))ᵀ *ᵥ z = a • z) (ha : a ≠ 0)
    (hΦ : peval Φ a = 0) (hF : ∀ x ∈ F, pair (toVec n x) z = 0)
    (hβ : pair (toVec n β) z ≠ 0) (hd : (r.d : F') ≠ 0) :
    ∀ l ∈ r.orbit, pair (toVec n l) z ≠ 0 := by
  simp only [KernelRow.check, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨hrep, hcong⟩, horb⟩ := hr
  have hfa : peval r.f a ≠ 0 := by
    intro h0
    have := peval_mul_eq_of_cong hcong hΦ
    rw [h0, zero_mul] at this
    exact hd this.symm
  have hrep' : pair (toVec n r.rep) z ≠ 0 := by
    rw [← hrep, toVec_vadd, pair_add, pair_vcombo_eq_zero F r.fc hF, zero_add,
      pair_lpolyVec hz]
    exact mul_ne_zero hfa hβ
  have horbit : ∀ j : ℕ, pair (toVec n (lmulVec n (lpow n W j) r.rep)) z ≠ 0 := by
    intro j
    rw [toVec_lmulVec, toMat_lpow, pair_pow_mulVec hz]
    exact mul_ne_zero (pow_ne_zero j ha) hrep'
  intro l hl
  rw [horb, lorbitSigned, List.mem_append] at hl
  rcases hl with hl | hl
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hl
    exact horbit j
  · cases signed
    · simp at hl
    · simp only [↓reduceIte, List.mem_map] at hl
      obtain ⟨x, hx, rfl⟩ := hl
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      rw [toVec_vneg, pair_neg, neg_ne_zero]
      exact horbit j

theorem rootKernel_eq_of_rows {F' : Type*} [Field F'] {τ : Tag} {W : List (List ℤ)}
    {F : List (List ℤ)} {β Φ : List ℤ} {m : ℕ} {signed : Bool} (rows : List KernelRow)
    (S : List (List ℤ))
    (hrows : ∀ r ∈ rows, r.check τ.rank W F β Φ m signed = true)
    (hcover : ∀ l ∈ τ.artifactRoots, l ∈ S ∨ ∃ r ∈ rows, l ∈ r.orbit)
    (hS : ∀ l ∈ S, l ∈ τ.artifactRoots) {z : Fin τ.rank → F'} {a : F'}
    (hz : ((toMat τ.rank W).map (Int.cast : ℤ → F'))ᵀ *ᵥ z = a • z) (ha : a ≠ 0)
    (hΦ : peval Φ a = 0) (hF : ∀ x ∈ F, pair (toVec τ.rank x) z = 0)
    (hβ : pair (toVec τ.rank β) z ≠ 0) (hd : ∀ r ∈ rows, (r.d : F') ≠ 0)
    (hSz : ∀ l ∈ S, pair (toVec τ.rank l) z = 0) :
    {α | IsRoot τ α ∧ pair α z = 0} = {α | ∃ l ∈ S, α = toVec τ.rank l} := by
  ext α
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hα, h0⟩
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
    rcases hcover l hl with hS' | ⟨r, hr, hlr⟩
    · exact ⟨l, hS', rfl⟩
    · exact absurd h0 (pair_ne_zero_of_check (hrows r hr) hz ha hΦ hF hβ (hd r hr) l hlr)
  · rintro ⟨l, hl, rfl⟩
    exact ⟨isRoot_toVec (hS l hl), hSz l hl⟩

theorem intCast_zmod_ne_zero {p : ℕ} {d : ℤ} (h0 : 0 < d) (hd : d < p) : (d : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  have := Int.le_of_dvd h0 h
  omega

theorem fin_cons_toVec {k : ℕ} (a : List ℤ) (L : List (List ℤ)) :
    (Fin.cons (toVec n a) (fun j : Fin k => toVec n (L.getD j [])) : Fin (k + 1) → Fin n → ℤ) =
      fun j : Fin (k + 1) => toVec n ((a :: L).getD j []) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · rw [Fin.cons_succ]
    rfl

theorem orbit_fun_eq (W : List (List ℤ)) (β : List ℤ) (m : ℕ) :
    (fun j : Fin m => (toMat n W ^ (j : ℕ)) *ᵥ toVec n β) =
      fun j : Fin m => toVec n ((lorbit n W β m).getD j []) := by
  funext j
  rw [toVec_lorbit_getD j.isLt]

theorem of_cols_eq_toMat (cs : List (List ℤ)) :
    (Matrix.of fun i (j : Fin n) => toVec n (cs.getD j []) i) = toMat n (lcols n cs) := by
  rw [toMat_lcols]

theorem toMat_lsmul_neg_one (W : List (List ℤ)) : toMat n (lsmul n (-1) W) = -toMat n W := by
  rw [toMat_lsmul, neg_one_smul]

theorem neg_one_eq_toMat : (-1 : Matrix (Fin n) (Fin n) ℤ) = toMat n (lsmul n (-1) (lid n)) := by
  rw [toMat_lsmul_neg_one, toMat_lid]

theorem getD_cons_eq_ite (a : List ℤ) (L : List (List ℤ)) (j : ℕ) :
    (a :: L).getD j [] = if j = 0 then a else L.getD (j - 1) [] := by
  cases j with
  | zero => rfl
  | succ j => simp

theorem cols_ite_eq (W : List (List ℤ)) (x β : List ℤ) (m : ℕ) :
    (fun j : Fin (m + 1) => if (j : ℕ) = 0 then toVec n x else
      (toMat n W ^ ((j : ℕ) - 1)) *ᵥ toVec n β) =
      fun j : Fin (m + 1) => toVec n ((x :: lorbit n W β m).getD j []) := by
  funext j
  rw [getD_cons_eq_ite]
  split_ifs with h
  · rfl
  · rw [toVec_lorbit_getD (by omega)]

theorem cols_ite_two_eq (W : List (List ℤ)) (x y β : List ℤ) (m : ℕ) :
    (fun j : Fin (m + 2) => if (j : ℕ) = 0 then toVec n x else if (j : ℕ) = 1 then toVec n y else
      (toMat n W ^ ((j : ℕ) - 2)) *ᵥ toVec n β) =
      fun j : Fin (m + 2) => toVec n ((x :: y :: lorbit n W β m).getD j []) := by
  funext j
  rw [getD_cons_eq_ite, getD_cons_eq_ite]
  by_cases h : (j : ℕ) = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : (j : ℕ) = 1
    · rw [ite_eq_left h', ite_eq_left (by omega)]
    · rw [ite_eq_right h', ite_eq_right (by omega), toVec_lorbit_getD (by omega)]
      congr 2

theorem prod_map_toMat (L : List (List (List ℤ))) :
    (L.map (toMat n)).prod = toMat n (L.foldr (lmul n) (lid n)) := by
  induction L with
  | nil => rw [List.map_nil, List.prod_nil, List.foldr_nil, toMat_lid]
  | cons A L ih => rw [List.map_cons, List.prod_cons, ih, List.foldr_cons, toMat_lmul]

theorem prod_rootReflMat_eq (τ : Tag) {k : ℕ} (γs : List (List ℤ)) :
    (List.ofFn fun i : Fin k => rootReflMat τ (toVec τ.rank (γs.getD i []))) =
      (List.ofFn fun i : Fin k => lrootRefl τ.rank (cartanList τ) (γs.getD i [])).map
        (toMat τ.rank) := by
  rw [List.map_ofFn]
  congr 1
  funext i
  exact (toMat_lrootRefl τ (toMat_cartanList τ) _).symm

theorem charpoly_toMat_one_by_one (c : ℤ) : (toMat 1 [[c]]).charpoly = X - C c := by
  have h : toMat 1 [[c]] = Matrix.diagonal fun _ => c := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  rw [h, Matrix.charpoly_diagonal, Fin.prod_univ_one]

theorem charpoly_toMat_two_diag (c : ℤ) : (toMat 2 [[c, 0], [0, c]]).charpoly = (X - C c) ^ 2 := by
  have h : toMat 2 [[c, 0], [0, c]] = Matrix.diagonal fun _ => c := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.charpoly_diagonal, Fin.prod_univ_two, sq]

theorem polyOfList_cons (c : ℤ) (cs : List ℤ) : polyOfList (c :: cs) = C c + X * polyOfList cs :=
  rfl

theorem polyOfList_padd (f g : List ℤ) : polyOfList (padd f g) = polyOfList f + polyOfList g := by
  induction f generalizing g with
  | nil => simp [padd, polyOfList]
  | cons c f ih =>
    cases g with
    | nil => simp [padd, polyOfList]
    | cons d g =>
      rw [padd, polyOfList_cons, polyOfList_cons, polyOfList_cons, ih, C_add]
      ring

theorem polyOfList_pscale (c : ℤ) (g : List ℤ) : polyOfList (pscale c g) = C c * polyOfList g := by
  induction g with
  | nil => simp [pscale, polyOfList]
  | cons d g ih =>
    rw [pscale, List.map_cons, ← pscale, polyOfList_cons, polyOfList_cons, ih, C_mul]
    ring

theorem polyOfList_pmul (f g : List ℤ) : polyOfList (pmul f g) = polyOfList f * polyOfList g := by
  induction f with
  | nil => simp [pmul, polyOfList]
  | cons c f ih =>
    rw [pmul, polyOfList_padd, polyOfList_pscale, polyOfList_cons, ih, polyOfList_cons, C_0]
    ring

theorem polyOfList_append_zero (cs : List ℤ) : polyOfList (cs ++ [0]) = polyOfList cs := by
  induction cs with
  | nil => simp [polyOfList]
  | cons c cs ih => rw [List.cons_append, polyOfList_cons, polyOfList_cons, ih]

theorem polyOfList_pnorm (cs : List ℤ) : polyOfList (pnorm cs) = polyOfList cs := by
  rw [pnorm]
  conv_rhs => rw [← List.reverse_reverse cs]
  generalize cs.reverse = l
  induction l with
  | nil => rfl
  | cons c l ih =>
    by_cases hc : c = 0
    · subst hc
      rw [List.dropWhile_cons_of_pos (by simp), ih, List.reverse_cons, polyOfList_append_zero]
    · rw [List.dropWhile_cons_of_neg (by simpa using hc)]

theorem natDegree_polyOfList_lt {k : ℕ} (cs : List ℤ) (h : cs.length ≤ k) (hk : 0 < k) :
    (polyOfList cs).natDegree < k := by
  induction cs generalizing k with
  | nil => simp [polyOfList]; omega
  | cons c cs ih =>
    rw [polyOfList_cons]
    simp only [List.length_cons] at h
    rcases Nat.eq_zero_or_pos cs.length with h0 | h0
    · rw [List.length_eq_zero_iff.1 h0]
      simp [polyOfList]
      omega
    · have h1 := ih (k := k - 1) (by omega) (by omega)
      calc (C c + X * polyOfList cs).natDegree
          ≤ max (C c).natDegree (X * polyOfList cs).natDegree := natDegree_add_le _ _
        _ < k := by
          rw [natDegree_C]
          refine max_lt hk (lt_of_le_of_lt (natDegree_mul_le) ?_)
          rw [natDegree_X]
          omega

theorem dvd_of_cong {f h q Φ : List ℤ} {d : ℤ}
    (hcong : pnorm (padd (pmul f h) [-d]) = pnorm (pmul q Φ)) :
    polyOfList Φ ∣ polyOfList f * polyOfList h - C d := by
  have h1 := congrArg polyOfList hcong
  rw [polyOfList_pnorm, polyOfList_pnorm, polyOfList_padd, polyOfList_pmul, polyOfList_pmul] at h1
  simp only [polyOfList, mul_zero, add_zero, C_neg] at h1
  refine ⟨polyOfList q, ?_⟩
  rw [← sub_eq_add_neg] at h1
  rw [h1, mul_comm]

theorem toVec_lpolyVec (W : List (List ℤ)) (f x : List ℤ) :
    toVec n (lpolyVec n W f x) = (aeval (toMat n W) (polyOfList f)) *ᵥ toVec n x := by
  induction f with
  | nil =>
    rw [lpolyVec, toVec_vofFn, polyOfList, map_zero, Matrix.zero_mulVec]
    rfl
  | cons c f ih =>
    rw [lpolyVec, toVec_vadd, toVec_vsmul, toVec_lmulVec, ih, polyOfList_cons, map_add, map_mul,
      aeval_C, aeval_X, Matrix.add_mulVec, Matrix.mulVec_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.one_mulVec]

end CFSG.RankThree.Lattice
