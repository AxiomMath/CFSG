module

public import CFSG.Monster.AxisCount.DenseFlat
public import CFSG.Monster.Griess.TrialityMatrix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B.Rep4371 Matrix

@[expose] def tauL (p : ℕ) : List (ℕ × ℤ) := Native.tauT (Native.mkCtx ()).tau p

@[expose] noncomputable def tauImg (p : ℕ) : SpaceB :=
  ((tauL p).map fun t => (t.2 : ℚ) • fbasis t.1).sum

@[expose] def TauBasis : Prop :=
  ∀ p, p < 196884 → tauB (fbasis p) = (1 / 8 : ℚ) • tauImg p

theorem tauL_lt (p : ℕ) (hp : p < 196884) : ∀ t ∈ tauL p, t.1 < 196884 := by
  intro t ht
  unfold tauL Native.tauT at ht
  split_ifs at ht with h1 h2 h3 h4 h5 h6 h7
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp only <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp only <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp only <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    simp only
    omega
  · rw [List.mem_map] at ht
    obtain ⟨q', hq', rfl⟩ := ht
    have := List.mem_range.1 hq'
    simp only
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    simp only
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    simp only
    omega

theorem scatter_list {M : Type*} [AddCommGroup M] [Module ℚ M] (n : ℕ) (c : ℚ) (F : ℕ → M)
    (L : List (ℕ × ℤ)) (hL : ∀ t ∈ L, t.1 < n) :
    ∑ q ∈ Finset.range n, (L.map fun t => if t.1 = q then (t.2 : ℚ) * c else 0).sum • F q =
      c • (L.map fun t => (t.2 : ℚ) • F t.1).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have ht : t.1 < n := hL t List.mem_cons_self
    have ih' := ih fun t' ht' => hL t' (List.mem_cons_of_mem _ ht')
    simp only [List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib, ih', smul_add]
    congr 1
    rw [Finset.sum_eq_single t.1]
    · rw [ite_eq_left rfl, smul_smul, mul_comm]
    · intro q _ hq
      rw [ite_eq_right (fun e => hq e.symm), zero_smul]
    · intro h
      exact absurd (Finset.mem_range.2 ht) h

theorem scatter_vec {M : Type*} [AddCommGroup M] [Module ℚ M] (n : ℕ) (c : ℕ → ℚ) (F : ℕ → M)
    (T : ℕ → List (ℕ × ℤ)) (hT : ∀ p, p < n → ∀ t ∈ T p, t.1 < n) :
    ∑ q ∈ Finset.range n, (∑ p ∈ Finset.range n,
        ((T p).map fun t => if t.1 = q then (t.2 : ℚ) * c p else 0).sum) • F q =
      ∑ p ∈ Finset.range n, c p • ((T p).map fun t => (t.2 : ℚ) • F t.1).sum := by
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact scatter_list n (c p) F (T p) (hT p (Finset.mem_range.1 hp))

@[expose] def cf8 (v : Native.DVec) (k : ℕ) : ℚ := cf v k / 8

theorem cast_list_scatter (q : ℕ) (x : ℤ) (s y : ℚ) (hxs : (x : ℚ) * s = y) (L : List (ℕ × ℤ)) :
    (((L.map fun t => if t.1 = q then t.2 * x else 0).sum : ℤ) : ℚ) * s =
      (L.map fun t => if t.1 = q then (t.2 : ℚ) * y else 0).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, add_mul, ih]
    refine congrArg₂ (· + ·) ?_ rfl
    by_cases h : t.1 = q
    · rw [ite_eq_left h, ite_eq_left h]
      push_cast
      rw [mul_assoc, hxs]
    · rw [ite_eq_right h, ite_eq_right h]
      simp

theorem applyTau_D (c : Native.Ctx) (v : Native.DVec) :
    (Native.applyTau c v).D = Native.scatterAt 0 196884 (Native.tauT c.tau) v.D := by
  simp only [Native.applyTau]

theorem applyTau_e (c : Native.Ctx) (v : Native.DVec) : (Native.applyTau c v).e = v.e + 3 := by
  simp only [Native.applyTau]

theorem cf_applyTau (v : Native.DVec) (q : ℕ) (hq : q < 196884) :
    cf (Native.applyTau (Native.mkCtx ()) v) q =
      ∑ p ∈ Finset.range 196884,
        ((tauL p).map fun t => if t.1 = q then (t.2 : ℚ) * cf8 v p else 0).sum := by
  have hD : (Native.applyTau (Native.mkCtx ()) v).D.getD q 0 =
      ∑ p ∈ Finset.range 196884,
        ((tauL p).map fun t => if t.1 = q then t.2 * v.D.getD p 0 else 0).sum := by
    rw [applyTau_D, Native.scatterAt_getD _ _ _ _ _ hq]
    exact Finset.sum_congr rfl fun p _ => by rw [zero_add]; rfl
  unfold cf
  rw [hD, applyTau_e, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [div_eq_mul_inv]
  have hxs : ((v.D.getD p 0 : ℤ) : ℚ) * ((2 : ℚ) ^ (v.e + 3))⁻¹ = cf8 v p := by
    unfold cf8 cf
    rw [pow_add]
    field_simp
    norm_num
  exact cast_list_scatter q (v.D.getD p 0) _ _ hxs (tauL p)

theorem interp_applyTau_of (h : TauBasis) (v : Native.DVec) :
    interp (Native.applyTau (Native.mkCtx ()) v) = tauB (interp v) := by
  have hsc := scatter_vec 196884 (cf8 v) fbasis tauL (fun p hp => tauL_lt p hp)
  have e1 : interp (Native.applyTau (Native.mkCtx ()) v) =
      ∑ q ∈ Finset.range 196884, tm (cf (Native.applyTau (Native.mkCtx ()) v)) q :=
    interp_eq_sum _
  have e2 : ∑ q ∈ Finset.range 196884, tm (cf (Native.applyTau (Native.mkCtx ()) v)) q =
      ∑ q ∈ Finset.range 196884, (∑ p ∈ Finset.range 196884,
        ((tauL p).map fun t => if t.1 = q then (t.2 : ℚ) * cf8 v p else 0).sum) • fbasis q :=
    Finset.sum_congr rfl fun q hq => by
      rw [tm, cf_applyTau v q (Finset.mem_range.1 hq)]
  have e3 : tauB (interp v) = ∑ p ∈ Finset.range 196884, cf8 v p • tauImg p := by
    rw [interp_eq_sum v, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [tm, map_smul, h p (Finset.mem_range.1 hp), smul_smul, cf8,
      show cf v p * (1 / 8) = cf v p / 8 by ring]
  rw [e1, e2, hsc, e3]
  exact Finset.sum_congr rfl fun p _ => rfl

end CFSG.Monster.AxisCount
