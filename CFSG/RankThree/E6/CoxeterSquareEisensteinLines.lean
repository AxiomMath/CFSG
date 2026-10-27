module

public import CFSG.RankThree.E6.RootLatticeTools

public noncomputable section

namespace CFSG.RankThree.E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Polynomial

@[expose] def e6Coxeter : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd (e6Word [0, 1, 2, 3, 4, 5])

@[expose] def e6CoxeterSq : WeylGroup Tag.E6 := e6Coxeter ^ 2

@[expose] def e6CoxeterSqWord : List (Fin 6) := [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5]

theorem e6CoxeterSq_eq_wordProd :
    e6CoxeterSq = (coxeterSystem Tag.E6).wordProd (e6Word e6CoxeterSqWord) := by
  rw [e6CoxeterSq, e6Coxeter, sq, ← CoxeterSystem.wordProd_append]
  rfl

@[expose] def coxeterSqMatrix6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 0, 1, 0, -1, 0; 1, 1, 0, 0, -1, 0; 0, 1, 1, 0, -1, -1; 1, 1, 1, 0, -1, -1;
    0, 1, 1, 0, -1, 0; 0, 0, 0, 1, -1, 0]

@[expose] def coxeterSqMatrix : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := coxeterSqMatrix6

theorem foldr_coxeterSqWord_single : ∀ j : Fin 6,
    (e6Word e6CoxeterSqWord).foldr (reflect Tag.E6) (Pi.single (e6Index j) 1) =
      fun i => coxeterSqMatrix i (e6Index j) := by
  decide +kernel

theorem weylMatrix_e6CoxeterSq : weylMatrix e6CoxeterSq = coxeterSqMatrix := by
  rw [e6CoxeterSq_eq_wordProd]
  exact weylMatrix_wordProd_e6 foldr_coxeterSqWord_single

theorem coxeterSqMatrix_pow_six : coxeterSqMatrix ^ 6 = 1 := by decide +kernel

theorem e6CoxeterSq_pow_six : e6CoxeterSq ^ 6 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e6CoxeterSq, coxeterSqMatrix_pow_six, weylMatrix_one]

theorem det_scalar_sub_coxeterSqMatrix : ∀ n : Fin 7,
    detLaplace 6 ((Matrix.of fun i j : Fin 6 => if i = j then ((n : ℕ) : ℤ) else 0) -
      coxeterSqMatrix6) =
      (((n : ℕ) : ℤ) ^ 2 - (n : ℕ) + 1) ^ 2 * (((n : ℕ) : ℤ) ^ 2 + (n : ℕ) + 1) := by
  decide +kernel

theorem natDegree_eisensteinCharpoly :
    ((X ^ 2 - X + 1) ^ 2 * (X ^ 2 + X + 1) : ℤ[X]).natDegree ≤ 6 := by
  compute_degree

theorem charpoly_coxeterSqMatrix :
    coxeterSqMatrix.charpoly = (X ^ 2 - X + 1) ^ 2 * (X ^ 2 + X + 1) := by
  refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq
    ((Finset.range 7).image (fun n : ℕ => (n : ℤ))) ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range,
      Matrix.charpoly_degree_eq_dim]
    change ((6 : ℕ) : WithBot ℕ) < ((7 : ℕ) : WithBot ℕ)
    exact WithBot.coe_lt_coe.2 (by norm_num)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact lt_of_le_of_lt (degree_le_of_natDegree_le natDegree_eisensteinCharpoly)
      (WithBot.coe_lt_coe.2 (by norm_num))
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    rw [Matrix.eval_charpoly, ← detLaplace_eq_det]
    have h := det_scalar_sub_coxeterSqMatrix ⟨n, Finset.mem_range.1 hn⟩
    have e : Matrix.scalar (Fin Tag.E6.rank) (n : ℤ) - coxeterSqMatrix =
        (Matrix.of fun i j : Fin 6 => if i = j then (n : ℤ) else 0) - coxeterSqMatrix6 := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
      rfl
    rw [e]
    simp only [eval_mul, eval_pow, eval_add, eval_sub, eval_X, eval_one]
    exact h

variable {R : Type*} [CommRing R]

@[expose] def eisensteinColumn (r a b : R) : Fin Tag.E6.rank → R :=
  (![-a, -r * a + (r - 1) * b, -b, (1 - r) * b, a, b] : Fin 6 → R)

theorem eisensteinColumn_four (r a b : R) : eisensteinColumn r a b (e6Index 4) = a := rfl

theorem eisensteinColumn_five (r a b : R) : eisensteinColumn r a b (e6Index 5) = b := rfl

theorem dualMatrix_e6CoxeterSq : dualMatrix R e6CoxeterSq =
    ((coxeterSqMatrix.map (Int.cast : ℤ → R)).transpose) := by
  rw [dualMatrix, weylMatrix_e6CoxeterSq]

theorem dualMatrix_e6CoxeterSq_mulVec (z : Fin Tag.E6.rank → R) :
    (dualMatrix R e6CoxeterSq).mulVec z = (![z (e6Index 1) + z (e6Index 3),
      z (e6Index 1) + z (e6Index 2) + z (e6Index 3) + z (e6Index 4),
      z (e6Index 0) + z (e6Index 2) + z (e6Index 3) + z (e6Index 4), z (e6Index 5),
      -(z (e6Index 0) + z (e6Index 1) + z (e6Index 2) + z (e6Index 3) + z (e6Index 4) +
        z (e6Index 5)), -z (e6Index 2) - z (e6Index 3)] : Fin 6 → R) := by
  rw [dualMatrix_e6CoxeterSq]
  funext i
  revert i z
  change ∀ (z : Fin 6 → R) (i : Fin 6),
    ((coxeterSqMatrix6.map (Int.cast : ℤ → R)).transpose.mulVec z) i = _
  intro z i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, coxeterSqMatrix6, e6Index] <;>
    ring

theorem dualMatrix_e6CoxeterSq_mulVec_apply (z : Fin Tag.E6.rank → R) :
    (dualMatrix R e6CoxeterSq).mulVec z (e6Index 0) = z (e6Index 1) + z (e6Index 3) ∧
    (dualMatrix R e6CoxeterSq).mulVec z (e6Index 1) =
      z (e6Index 1) + z (e6Index 2) + z (e6Index 3) + z (e6Index 4) ∧
    (dualMatrix R e6CoxeterSq).mulVec z (e6Index 2) =
      z (e6Index 0) + z (e6Index 2) + z (e6Index 3) + z (e6Index 4) ∧
    (dualMatrix R e6CoxeterSq).mulVec z (e6Index 3) = z (e6Index 5) ∧
    (dualMatrix R e6CoxeterSq).mulVec z (e6Index 4) =
      -(z (e6Index 0) + z (e6Index 1) + z (e6Index 2) + z (e6Index 3) + z (e6Index 4) +
        z (e6Index 5)) ∧
    (dualMatrix R e6CoxeterSq).mulVec z (e6Index 5) = -z (e6Index 2) - z (e6Index 3) := by
  rw [dualMatrix_e6CoxeterSq_mulVec]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dualMatrix_mulVec_eisensteinColumn {r : R} (hr : r ^ 2 - r + 1 = 0) (a b : R) :
    (dualMatrix R e6CoxeterSq).mulVec (eisensteinColumn r a b) =
      r • eisensteinColumn r a b := by
  rw [dualMatrix_e6CoxeterSq_mulVec]
  funext i
  revert i
  change ∀ i : Fin 6, _ = r * (![-a, -r * a + (r - 1) * b, -b, (1 - r) * b, a, b] : Fin 6 → R) i
  intro i
  fin_cases i <;> simp [eisensteinColumn, e6Index]
  · ring
  · linear_combination (a - b) * hr
  · ring
  · linear_combination b * hr
  · ring
  · ring

theorem eq_eisensteinColumn_of_dualMatrix_mulVec {r : R} (hr : r ^ 2 - r + 1 = 0)
    {z : Fin Tag.E6.rank → R} (hz : (dualMatrix R e6CoxeterSq).mulVec z = r • z) :
    z = eisensteinColumn r (z (e6Index 4)) (z (e6Index 5)) := by
  obtain ⟨c0, -, c2, c3, -, c5⟩ := dualMatrix_e6CoxeterSq_mulVec_apply z
  have h0 := congrFun hz (e6Index 0)
  have h2 := congrFun hz (e6Index 2)
  have h3 := congrFun hz (e6Index 3)
  have h5 := congrFun hz (e6Index 5)
  rw [c0, Pi.smul_apply, smul_eq_mul] at h0
  rw [c2, Pi.smul_apply, smul_eq_mul] at h2
  rw [c3, Pi.smul_apply, smul_eq_mul] at h3
  rw [c5, Pi.smul_apply, smul_eq_mul] at h5
  have e3 : z (e6Index 3) = (1 - r) * z (e6Index 5) := by
    linear_combination (r - 1) * h3 + z (e6Index 3) * hr
  have e2 : z (e6Index 2) = -z (e6Index 5) := by linear_combination -h5 - e3
  have e0 : z (e6Index 0) = -z (e6Index 4) := by linear_combination h2 + (r - 1) * e2 - e3
  have e1 : z (e6Index 1) = -r * z (e6Index 4) + (r - 1) * z (e6Index 5) := by
    linear_combination h0 - e3 + r * e0
  funext i
  revert i
  change ∀ i : Fin 6, z (e6Index i) = eisensteinColumn r (z (e6Index 4)) (z (e6Index 5))
    (e6Index i)
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · rfl
  · rfl

@[expose] def eisMul (x y : ℤ × ℤ) : ℤ × ℤ :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

@[expose] def eisNorm (x : ℤ × ℤ) : ℤ := x.1 ^ 2 + x.1 * x.2 + x.2 ^ 2

@[expose] def eisConj (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + x.2, -x.2)

@[expose] def eisEval (r : R) (x : ℤ × ℤ) : R := x.1 + x.2 * r

theorem eisEval_mul {r : R} (hr : r ^ 2 - r + 1 = 0) (x y : ℤ × ℤ) :
    eisEval r (eisMul x y) = eisEval r x * eisEval r y := by
  simp only [eisEval, eisMul]
  push_cast
  linear_combination (-((x.2 : R) * y.2)) * hr

theorem eisEval_mul_conj {r : R} (hr : r ^ 2 - r + 1 = 0) (x : ℤ × ℤ) :
    eisEval r x * eisEval r (eisConj x) = eisNorm x := by
  simp only [eisEval, eisConj, eisNorm]
  push_cast
  linear_combination (-((x.2 : R) ^ 2)) * hr

@[expose] def eisUnits : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1), (-1, 1), (1, -1)]

theorem eisNorm_of_mem_eisUnits : ∀ u ∈ eisUnits, eisNorm u = 1 := by decide

@[expose] def eisLine : Fin 8 → (ℤ × ℤ) × (ℤ × ℤ) :=
  ![((0, 0), (1, 0)), ((1, 0), (0, 0)), ((1, 0), (1, 0)), ((1, 0), (1, -1)), ((1, 1), (1, 0)),
    ((1, 0), (2, -1)), ((1, 0), (0, 1)), ((1, 0), (0, -1))]

@[expose] def eisensteinLineForm (r a b : R) : Fin 8 → R :=
  ![b, a, a + b, a + (1 - r) * b, (1 + r) * a + b, a + (2 - r) * b, a + r * b, a - r * b]

theorem eisensteinLineForm_eq (r a b : R) (k : Fin 8) :
    eisensteinLineForm r a b k =
      eisEval r (eisLine k).1 * a + eisEval r (eisLine k).2 * b := by
  fin_cases k <;> simp [eisensteinLineForm, eisLine, eisEval] <;> ring

@[expose] def eisLineDet (k k' : Fin 8) : ℤ × ℤ :=
  eisMul (eisLine k).1 (eisLine k').2 - eisMul (eisLine k').1 (eisLine k).2

theorem eisNorm_eisLineDet : ∀ k k' : Fin 8, k ≠ k' →
    eisNorm (eisLineDet k k') = 1 ∨ eisNorm (eisLineDet k k') = 3 ∨
      eisNorm (eisLineDet k k') = 4 := by
  decide

theorem eisEval_sub (r : R) (x y : ℤ × ℤ) : eisEval r (x - y) = eisEval r x - eisEval r y := by
  simp only [eisEval, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

@[expose] def rootFormF (α : Fin Tag.E6.rank → ℤ) : ℤ × ℤ :=
  (-α (e6Index 0) + α (e6Index 4), -α (e6Index 1))

@[expose] def rootFormG (α : Fin Tag.E6.rank → ℤ) : ℤ × ℤ :=
  (-α (e6Index 1) - α (e6Index 2) + α (e6Index 3) + α (e6Index 5),
    α (e6Index 1) - α (e6Index 3))

theorem charVal_eisensteinColumn (r a b : R) (α : Fin Tag.E6.rank → ℤ) :
    charVal (eisensteinColumn r a b) α =
      eisEval r (rootFormF α) * a + eisEval r (rootFormG α) * b := by
  simp only [charVal]
  change ∑ i : Fin 6, _ = _
  simp only [Fin.sum_univ_six, eisensteinColumn, rootFormF, rootFormG, eisEval, e6Index]
  simp
  ring

@[expose] def OnEisLine (k : Fin 8) (α : Fin Tag.E6.rank → ℤ) : Prop :=
  ∃ u ∈ eisUnits, rootFormF α = eisMul u (eisLine k).1 ∧ rootFormG α = eisMul u (eisLine k).2

instance (k : Fin 8) (α : Fin Tag.E6.rank → ℤ) : Decidable (OnEisLine k α) :=
  inferInstanceAs (Decidable (∃ u ∈ eisUnits, _))

theorem exists_onEisLine : ∀ m : Fin 72, ∃ k : Fin 8, OnEisLine k (e6RootVec m) := by
  decide +kernel

theorem onEisLine_unique : ∀ m : Fin 72, ∀ k k' : Fin 8,
    OnEisLine k (e6RootVec m) → OnEisLine k' (e6RootVec m) → k = k' := by
  decide +kernel

theorem exists_e6RootVec_onEisLine : ∀ k : Fin 8, ∃ m : Fin 72, OnEisLine k (e6RootVec m) := by
  decide +kernel

section Field

variable {p : ℕ} [Fact p.Prime]

theorem natCast_ne_zero_of_lt {p : ℕ} [Fact p.Prime] (hp : 3 < p) {n : ℤ}
    (hn : n = 1 ∨ n = 3 ∨ n = 4) : (n : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hp' := (Fact.out : p.Prime)
  have hle : (p : ℤ) ≤ 4 := by
    rcases hn with rfl | rfl | rfl <;> exact (Int.le_of_dvd (by norm_num) h).trans (by norm_num)
  have h4 : p = 4 := by omega
  subst h4
  exact absurd hp' (by norm_num)

theorem eisEval_ne_zero_of_mem_eisUnits {r : ZMod p} (hr : r ^ 2 - r + 1 = 0)
    {u : ℤ × ℤ} (hu : u ∈ eisUnits) : eisEval r u ≠ 0 := by
  intro h
  have := eisEval_mul_conj hr u
  rw [h, zero_mul, eisNorm_of_mem_eisUnits u hu, Int.cast_one] at this
  exact zero_ne_one this

theorem charVal_eisensteinColumn_eq_zero_iff {r : ZMod p} (hr : r ^ 2 - r + 1 = 0) {k : Fin 8}
    {α : Fin Tag.E6.rank → ℤ} (hα : OnEisLine k α) (a b : ZMod p) :
    charVal (eisensteinColumn r a b) α = 0 ↔ eisensteinLineForm r a b k = 0 := by
  obtain ⟨u, hu, hf, hg⟩ := hα
  rw [charVal_eisensteinColumn, hf, hg, eisEval_mul hr, eisEval_mul hr, eisensteinLineForm_eq]
  rw [show eisEval r u * eisEval r (eisLine k).1 * a + eisEval r u * eisEval r (eisLine k).2 * b
    = eisEval r u * (eisEval r (eisLine k).1 * a + eisEval r (eisLine k).2 * b) by ring]
  exact ⟨fun h => (mul_eq_zero.1 h).resolve_left (eisEval_ne_zero_of_mem_eisUnits hr hu),
    fun h => by rw [h, mul_zero]⟩

theorem eq_of_eisensteinLineForm_eq_zero (hp : 3 < p) {r : ZMod p} (hr : r ^ 2 - r + 1 = 0)
    {a b : ZMod p} (hab : (a, b) ≠ 0) {k k' : Fin 8} (hk : eisensteinLineForm r a b k = 0)
    (hk' : eisensteinLineForm r a b k' = 0) : k = k' := by
  by_contra hne
  rw [eisensteinLineForm_eq] at hk hk'
  set c := eisEval r (eisLine k).1
  set d := eisEval r (eisLine k).2
  set c' := eisEval r (eisLine k').1
  set d' := eisEval r (eisLine k').2
  have hD : eisEval r (eisLineDet k k') = c * d' - c' * d := by
    rw [eisLineDet, eisEval_sub, eisEval_mul hr, eisEval_mul hr]
  have hD0 : c * d' - c' * d ≠ 0 := by
    rw [← hD]
    intro h0
    have := eisEval_mul_conj hr (eisLineDet k k')
    rw [h0, zero_mul] at this
    exact natCast_ne_zero_of_lt hp (eisNorm_eisLineDet k k' hne) this.symm
  have ha : (c * d' - c' * d) * a = 0 := by linear_combination d' * hk - d * hk'
  have hb : (c * d' - c' * d) * b = 0 := by linear_combination c * hk' - c' * hk
  have ha0 := (mul_eq_zero.1 ha).resolve_left hD0
  have hb0 := (mul_eq_zero.1 hb).resolve_left hD0
  exact hab (by rw [ha0, hb0]; rfl)

theorem rootKernel_eisensteinColumn (hp : 3 < p) {r : ZMod p} (hr : r ^ 2 - r + 1 = 0)
    {a b : ZMod p} (hab : (a, b) ≠ 0) {k : Fin 8} (hk : eisensteinLineForm r a b k = 0) :
    rootKernel (eisensteinColumn r a b) = {α | IsRoot Tag.E6 α ∧ OnEisLine k α} := by
  ext α
  rw [mem_rootKernel, Set.mem_ofPred_eq]
  refine and_congr_right fun hα => ?_
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
  obtain ⟨k₀, h₀⟩ := exists_onEisLine m
  rw [charVal_eisensteinColumn_eq_zero_iff hr h₀]
  constructor
  · intro h
    rwa [eq_of_eisensteinLineForm_eq_zero hp hr hab h hk] at h₀
  · intro h
    rw [onEisLine_unique m k₀ k h₀ h]
    exact hk

@[expose] def eisLinePoint (r : R) (k : Fin 8) : R × R :=
  (eisEval r (eisLine k).2, -eisEval r (eisLine k).1)

theorem eisensteinLineForm_eisLinePoint (r : R) (k : Fin 8) :
    eisensteinLineForm r (eisLinePoint r k).1 (eisLinePoint r k).2 k = 0 := by
  rw [eisensteinLineForm_eq, eisLinePoint]
  ring

theorem eisLinePoint_ne_zero (r : ZMod p) (k : Fin 8) : eisLinePoint r k ≠ 0 := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [eisLinePoint, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h1 h2
  fin_cases k <;> simp [eisLine, eisEval] at h1 h2

end Field

@[expose] def supportA2A2 : Set (Fin Tag.E6.rank) :=
  {e6Index 0, e6Index 2, e6Index 4, e6Index 5}

theorem mem_supportA2A2 (i : Fin Tag.E6.rank) :
    i ∈ supportA2A2 ↔ (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) := by
  simp only [supportA2A2, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem ncard_parabolicRoots_supportA2A2 : (parabolicRoots Tag.E6 supportA2A2).ncard = 12 :=
  ncard_parabolicRoots_eq mem_supportA2A2 (by decide +kernel)

theorem ncard_parabolicRoots_support13 : (parabolicRoots Tag.E6 support13).ncard = 6 :=
  ncard_parabolicRoots_eq mem_support13 (by decide +kernel)

@[expose] def eisTransporter : Fin 8 → List (Fin 6) :=
  ![[3, 2, 0], [3, 4, 5, 1], [3, 2, 1, 3, 4, 5, 3, 2, 1, 3, 0], [3, 2, 1, 3, 4, 3, 0, 2],
    [3, 4, 5, 1, 3, 4, 2, 3, 1], [3, 4, 5, 2, 1, 3, 4, 2, 1, 3, 2], [3, 4, 5, 2, 1, 3],
    [3, 2, 1, 3, 4, 0]]

@[expose] def eisTransporterElt (k : Fin 8) : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd (e6Word (eisTransporter k))

theorem image_wordProd_onEisLine_eq {k : Fin 8} {ω : List (Fin 6)} {J : Set (Fin Tag.E6.rank)}
    {P : Fin Tag.E6.rank → Prop} (hJ : ∀ i, i ∈ J ↔ P i)
    (h₁ : ∀ m : Fin 72, OnEisLine k (e6RootVec m) →
      ∀ i, ¬P i → (e6Word ω).foldr (reflect Tag.E6) (e6RootVec m) i = 0)
    (h₂ : ∀ m : Fin 72, (∀ i, ¬P i → e6RootVec m i = 0) →
      ∃ m' : Fin 72, OnEisLine k (e6RootVec m') ∧
        (e6Word ω).foldr (reflect Tag.E6) (e6RootVec m') = e6RootVec m) :
    ((coxeterSystem Tag.E6).wordProd (e6Word ω) • ·) '' {α | IsRoot Tag.E6 α ∧ OnEisLine k α} =
      parabolicRoots Tag.E6 J := by
  ext β
  simp only [Set.mem_image, parabolicRoots, Set.mem_ofPred_eq, hJ]
  constructor
  · rintro ⟨α, ⟨hα, hk⟩, rfl⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
    refine ⟨IsRoot.smul hα _, fun i hi => ?_⟩
    rw [wordProd_e6Word_smul]
    exact h₁ m hk i hi
  · rintro ⟨hβ, hsupp⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hβ
    obtain ⟨m', hm', he⟩ := h₂ m hsupp
    exact ⟨e6RootVec m', ⟨isRoot_e6RootVec m', hm'⟩, by rw [wordProd_e6Word_smul]; exact he⟩

theorem image_eisTransporter_A2A2 : ∀ k : Fin 8, k.val < 4 →
    (eisTransporterElt k • ·) '' {α | IsRoot Tag.E6 α ∧ OnEisLine k α} =
      parabolicRoots Tag.E6 supportA2A2 := by
  intro k hk
  fin_cases k <;> simp at hk <;>
    exact image_wordProd_onEisLine_eq mem_supportA2A2 (by decide +kernel) (by decide +kernel)

theorem image_eisTransporter_A2 : ∀ k : Fin 8, 4 ≤ k.val →
    (eisTransporterElt k • ·) '' {α | IsRoot Tag.E6 α ∧ OnEisLine k α} =
      parabolicRoots Tag.E6 support13 := by
  intro k hk
  fin_cases k <;> simp at hk <;>
    exact image_wordProd_onEisLine_eq mem_support13 (by decide +kernel) (by decide +kernel)

@[expose] def eisTransported (k : Fin 8) : WeylGroup Tag.E6 :=
  eisTransporterElt k * e6CoxeterSq * (eisTransporterElt k)⁻¹

theorem eisTransported_eq (k : Fin 8) :
    eisTransported k = (coxeterSystem Tag.E6).wordProd
      (e6Word (eisTransporter k ++ e6CoxeterSqWord ++ (eisTransporter k).reverse)) := by
  rw [eisTransported, eisTransporterElt, e6CoxeterSq_eq_wordProd, wordProd_conj_e6]

theorem eisTransported_smul (k : Fin 8) (v : Fin Tag.E6.rank → ℤ) :
    eisTransported k • v = (e6Word (eisTransporter k ++ e6CoxeterSqWord ++
      (eisTransporter k).reverse)).foldr (reflect Tag.E6) v := by
  rw [eisTransported_eq, wordProd_e6Word_smul]

theorem eisTransported_exchanges : ∀ k : Fin 8, k.val < 4 →
    (eisTransported k • ·) '' parabolicRoots Tag.E6 support13 =
        parabolicRoots Tag.E6 support56 ∧
      (eisTransported k • ·) '' parabolicRoots Tag.E6 support56 =
        parabolicRoots Tag.E6 support13 := by
  intro k hk
  rw [eisTransported_eq]
  fin_cases k <;> simp at hk <;>
    exact ⟨image_wordProd_parabolicRoots_eq mem_support13 mem_support56 (by decide +kernel)
      (by decide +kernel), image_wordProd_parabolicRoots_eq mem_support56 mem_support13
      (by decide +kernel) (by decide +kernel)⟩

theorem eisTransported_preserves : ∀ k : Fin 8, 4 ≤ k.val →
    (eisTransported k • ·) '' parabolicRoots Tag.E6 support13 =
      parabolicRoots Tag.E6 support13 := by
  intro k hk
  rw [eisTransported_eq]
  fin_cases k <;> simp at hk <;>
    exact image_wordProd_parabolicRoots_eq mem_support13 mem_support13 (by decide +kernel)
      (by decide +kernel)

@[expose] def perm120 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def perm201 : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1

theorem eisTransported_positive : ∀ k : Fin 8, k.val < 4 →
    IsPositiveTransition (eisTransported k • ·) chain13 chain56 ∧
      IsPositiveTransition (eisTransported k • ·) chain56 chain13 := by
  intro k hk
  simp only [IsPositiveTransition, eisTransported_smul]
  fin_cases k <;> simp at hk
  · exact ⟨⟨1, by decide +kernel⟩, ⟨perm120, by decide +kernel⟩⟩
  · exact ⟨⟨1, by decide +kernel⟩, ⟨perm120, by decide +kernel⟩⟩
  · exact ⟨⟨1, by decide +kernel⟩, ⟨perm201, by decide +kernel⟩⟩
  · exact ⟨⟨Equiv.swap 0 1, by decide +kernel⟩, ⟨Equiv.swap 1 2, by decide +kernel⟩⟩

theorem eisTransported_negative : ∀ k : Fin 8, 4 ≤ k.val →
    IsNegativeTransition (eisTransported k • ·) chain13 chain13 := by
  intro k hk
  simp only [IsNegativeTransition, eisTransported_smul]
  fin_cases k <;> simp at hk
  · exact ⟨perm201, by decide +kernel⟩
  · exact ⟨perm201, by decide +kernel⟩
  · exact ⟨perm201, by decide +kernel⟩
  · exact ⟨perm120, by decide +kernel⟩

theorem restrictMatrix₂_eisTransported : ∀ k : Fin 8, 4 ≤ k.val →
    (restrictMatrix₂ (eisTransported k) (e6Index 0) (e6Index 2)).trace = 1 ∧
      (restrictMatrix₂ (eisTransported k) (e6Index 0) (e6Index 2)).det = 1 := by
  intro k hk
  simp only [restrictMatrix₂, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    weylMatrix_apply, eisTransported_smul]
  fin_cases k <;> simp at hk <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem charpoly_restrictMatrix₂_eisTransported (k : Fin 8) (hk : 4 ≤ k.val) :
    (restrictMatrix₂ (eisTransported k) (e6Index 0) (e6Index 2)).charpoly = X ^ 2 - X + 1 := by
  obtain ⟨htr, hdet⟩ := restrictMatrix₂_eisTransported k hk
  rw [Matrix.charpoly_fin_two, htr, hdet, map_one, one_mul]

theorem eisensteinColumn_zero (r : R) : eisensteinColumn r 0 0 = 0 := by
  funext i
  revert i
  change ∀ i : Fin 6, (![-0, -r * 0 + (r - 1) * 0, -0, (1 - r) * 0, 0, 0] : Fin 6 → R) i = 0
  intro i
  fin_cases i <;> simp

theorem ncard_rootKernel_of_image {z : Fin Tag.E6.rank → R} {w : WeylGroup Tag.E6}
    {J : Set (Fin Tag.E6.rank)} (h : (w • ·) '' rootKernel z = parabolicRoots Tag.E6 J) :
    (rootKernel z).ncard = (parabolicRoots Tag.E6 J).ncard := by
  rw [← h, Set.ncard_image_of_injective _ (MulAction.injective w)]

theorem E6_Coxeter_square_eight_Eisenstein_root_kernel_lines :
    weylMatrix e6CoxeterSq = coxeterSqMatrix ∧ e6CoxeterSq ^ 6 = 1 ∧
    weylMatrix e6CoxeterSq ^ 6 = 1 ∧
    (weylMatrix e6CoxeterSq).charpoly = (X ^ 2 - X + 1) ^ 2 * (X ^ 2 + X + 1) ∧
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ r : ZMod p, r ^ 2 - r + 1 = 0 →
      (∀ a b : ZMod p, (a, b) ≠ 0 → eisensteinColumn r a b ≠ 0 ∧
        (dualMatrix (ZMod p) e6CoxeterSq).mulVec (eisensteinColumn r a b) =
          r • eisensteinColumn r a b) ∧
      (∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
        (dualMatrix (ZMod p) e6CoxeterSq).mulVec z = r • z →
          ∃! ab : ZMod p × ZMod p, ab ≠ 0 ∧ z = eisensteinColumn r ab.1 ab.2) ∧
      (∀ k k' : Fin 8, k ≠ k' → ∀ a b : ZMod p, (a, b) ≠ 0 →
        ¬(eisensteinLineForm r a b k = 0 ∧ eisensteinLineForm r a b k' = 0)) ∧
      (∀ a b : ZMod p, (a, b) ≠ 0 →
        ((rootKernel (eisensteinColumn r a b)).Nonempty ↔
          ∃ k : Fin 8, eisensteinLineForm r a b k = 0)) ∧
      (∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α → ∃! k : Fin 8, ∀ a b : ZMod p,
        (a, b) ≠ 0 → eisensteinLineForm r a b k = 0 → α ∈ rootKernel (eisensteinColumn r a b)) ∧
      (∀ k : Fin 8, k.val < 4 → ∃ w : WeylGroup Tag.E6,
        (∀ a b : ZMod p, (a, b) ≠ 0 → eisensteinLineForm r a b k = 0 →
          (w • ·) '' rootKernel (eisensteinColumn r a b) = parabolicRoots Tag.E6 supportA2A2 ∧
          (rootKernel (eisensteinColumn r a b)).ncard = 12) ∧
        ((w * e6CoxeterSq * w⁻¹) • ·) '' parabolicRoots Tag.E6 support13 =
          parabolicRoots Tag.E6 support56 ∧
        ((w * e6CoxeterSq * w⁻¹) • ·) '' parabolicRoots Tag.E6 support56 =
          parabolicRoots Tag.E6 support13 ∧
        IsPositiveTransition ((w * e6CoxeterSq * w⁻¹) • ·) chain13 chain56 ∧
        IsPositiveTransition ((w * e6CoxeterSq * w⁻¹) • ·) chain56 chain13) ∧
      (∀ k : Fin 8, 4 ≤ k.val → ∃ w : WeylGroup Tag.E6,
        (∀ a b : ZMod p, (a, b) ≠ 0 → eisensteinLineForm r a b k = 0 →
          (w • ·) '' rootKernel (eisensteinColumn r a b) = parabolicRoots Tag.E6 support13 ∧
          (rootKernel (eisensteinColumn r a b)).ncard = 6) ∧
        ((w * e6CoxeterSq * w⁻¹) • ·) '' parabolicRoots Tag.E6 support13 =
          parabolicRoots Tag.E6 support13 ∧
        (restrictMatrix₂ (w * e6CoxeterSq * w⁻¹) (e6Index 0) (e6Index 2)).charpoly =
          X ^ 2 - X + 1 ∧
        IsNegativeTransition ((w * e6CoxeterSq * w⁻¹) • ·) chain13 chain13) := by
  refine ⟨weylMatrix_e6CoxeterSq, e6CoxeterSq_pow_six,
    by rw [weylMatrix_e6CoxeterSq, coxeterSqMatrix_pow_six],
    by rw [weylMatrix_e6CoxeterSq, charpoly_coxeterSqMatrix], ?_⟩
  intro p _ hp r hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a b hab
    refine ⟨fun h => hab ?_, dualMatrix_mulVec_eisensteinColumn hr a b⟩
    have h4 := congrFun h (e6Index 4)
    have h5 := congrFun h (e6Index 5)
    rw [eisensteinColumn_four] at h4
    rw [eisensteinColumn_five] at h5
    rw [h4, h5]
    rfl
  ·
    intro z hz hu
    have hz' := eq_eisensteinColumn_of_dualMatrix_mulVec hr hu
    refine ⟨(z (e6Index 4), z (e6Index 5)), ⟨fun h0 => hz ?_, hz'⟩, ?_⟩
    · rw [hz', show z (e6Index 4) = 0 from congrArg Prod.fst h0,
        show z (e6Index 5) = 0 from congrArg Prod.snd h0, eisensteinColumn_zero]
    · rintro ⟨a, b⟩ ⟨-, hab⟩
      rw [hab]
      rfl
  ·
    intro k k' hne a b hab h
    exact hne (eq_of_eisensteinLineForm_eq_zero hp hr hab h.1 h.2)
  ·
    intro a b hab
    constructor
    · rintro ⟨α, hα, hα0⟩
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
      obtain ⟨k, hk⟩ := exists_onEisLine m
      exact ⟨k, (charVal_eisensteinColumn_eq_zero_iff hr hk a b).1 hα0⟩
    · rintro ⟨k, hk⟩
      obtain ⟨m, hm⟩ := exists_e6RootVec_onEisLine k
      exact ⟨e6RootVec m, isRoot_e6RootVec m, (charVal_eisensteinColumn_eq_zero_iff hr hm a b).2 hk⟩
  ·
    intro α hα
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
    obtain ⟨k, hk⟩ := exists_onEisLine m
    refine ⟨k, fun a b _ h0 =>
      ⟨isRoot_e6RootVec m, (charVal_eisensteinColumn_eq_zero_iff hr hk a b).2 h0⟩,
      fun k' hk' => ?_⟩
    have hP := eisLinePoint_ne_zero r k'
    have hP' : ((eisLinePoint r k').1, (eisLinePoint r k').2) ≠ 0 := hP
    have h := hk' _ _ hP' (eisensteinLineForm_eisLinePoint r k')
    exact eq_of_eisensteinLineForm_eq_zero hp hr hP' (eisensteinLineForm_eisLinePoint r k')
      ((charVal_eisensteinColumn_eq_zero_iff hr hk _ _).1 h.2)
  ·
    intro k hk
    refine ⟨eisTransporterElt k, fun a b hab h0 => ?_, (eisTransported_exchanges k hk).1,
      (eisTransported_exchanges k hk).2, (eisTransported_positive k hk).1,
      (eisTransported_positive k hk).2⟩
    have himg : (eisTransporterElt k • ·) '' rootKernel (eisensteinColumn r a b) =
        parabolicRoots Tag.E6 supportA2A2 := by
      rw [rootKernel_eisensteinColumn hp hr hab h0]
      exact image_eisTransporter_A2A2 k hk
    exact ⟨himg, by rw [ncard_rootKernel_of_image himg, ncard_parabolicRoots_supportA2A2]⟩
  ·
    intro k hk
    refine ⟨eisTransporterElt k, fun a b hab h0 => ?_, eisTransported_preserves k hk,
      charpoly_restrictMatrix₂_eisTransported k hk, eisTransported_negative k hk⟩
    have himg : (eisTransporterElt k • ·) '' rootKernel (eisensteinColumn r a b) =
        parabolicRoots Tag.E6 support13 := by
      rw [rootKernel_eisensteinColumn hp hr hab h0]
      exact image_eisTransporter_A2 k hk
    exact ⟨himg, by rw [ncard_rootKernel_of_image himg, ncard_parabolicRoots_support13]⟩

end CFSG.RankThree.E6
