module

public import CFSG.Monster.Griess.TrialityMatrix
public import CFSG.Monster.Griess.Trilinear

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix

namespace DiagonalInvariance

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem gmul_inA_inA (A A' : symMat) :
    gmul (inA A) (inA A') = (⟨gmulA (inA A) (inA A'), gmulA_symm _ _⟩, 0, 0) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext c
    change gmulX (inA A) (inA A') c = 0
    simp [gmulX, qf_zero]
  · change gmulWHalf (inA A) (inA A') + gmulWHalf (inA A') (inA A) = 0
    simp [gmulWHalf]

theorem gmulA_inA_inA (A A' : symMat) :
    gmulA (inA A) (inA A') = (2 : ℚ) • ((A : Matrix (Fin 24) (Fin 24) ℚ) * A' +
      (A' : Matrix (Fin 24) (Fin 24) ℚ) * A) := by
  simp [gmulA]

theorem gmul_inA_inX (A : symMat) (x : SpaceX) :
    gmul (inA A) (inX x) = inX (fun c => qf c A / 8 * x c) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · change gmulA (inA A) (inX x) = ((0 : symMat) : Matrix (Fin 24) (Fin 24) ℚ)
    simp [gmulA]
  · funext c
    change gmulX (inA A) (inX x) c = qf c A / 8 * x c
    simp [gmulX, qf_zero]
    ring
  · change gmulWHalf (inA A) (inX x) + gmulWHalf (inX x) (inA A) = 0
    simp [gmulWHalf]

theorem gmul_inA_inW (A : symMat) (N : SpaceW) :
    gmul (inA A) (inW N) =
      inW ((trace (A : Matrix (Fin 24) (Fin 24) ℚ) / 8) • N +
        N * (A : Matrix (Fin 24) (Fin 24) ℚ)) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · change gmulA (inA A) (inW N) = ((0 : symMat) : Matrix (Fin 24) (Fin 24) ℚ)
    simp [gmulA]
  · funext c
    change gmulX (inA A) (inW N) c = 0
    simp [gmulX, qf_zero]
  · change gmulWHalf (inA A) (inW N) + gmulWHalf (inW N) (inA A) = _
    simp [gmulWHalf]

theorem T_cycle2 (x y z : SpaceB) : T x y z = T z x y := (T_cycle x y z).trans (T_cycle y z x)

theorem smul_inX (t : ℚ) (x : SpaceX) : inX (t • x) = t • inX x := by
  simp [Prod.smul_mk]

theorem smul_inW (t : ℚ) (N : SpaceW) : inW (t • N) = t • inW N := by
  simp [Prod.smul_mk]

theorem fun_mul_eq_smul {x : SpaceX} {f : ShortIdx → ℚ} {t : ℚ} (h : ∀ c, x c ≠ 0 → f c = t) :
    (fun c => f c * x c) = t • x := by
  funext c
  by_cases hx : x c = 0
  · simp [hx]
  · rw [h c hx, Pi.smul_apply, smul_eq_mul]

theorem gmul_inA_inX_eq_smul (A : symMat) {x : SpaceX} {t : ℚ}
    (h : ∀ c, x c ≠ 0 → qf c A / 8 = t) : gmul (inA A) (inX x) = t • inX x := by
  rw [gmul_inA_inX, fun_mul_eq_smul h, smul_inX]

theorem coe_basisA_diag (k : Fin 24) :
    (basisA s(k, k) : Matrix (Fin 24) (Fin 24) ℚ) = Matrix.single k k 1 := by
  rw [coe_basisA, ite_eq_left rfl]

theorem coe_basisA_ltPair (p : LtPair) :
    (basisA s(p.1.1, p.1.2) : Matrix (Fin 24) (Fin 24) ℚ) =
      Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1 := by
  rw [coe_basisA, ite_eq_right p.2.ne]

theorem qf_single (c : ShortIdx) (i j : Fin 24) :
    qf c (Matrix.single i j 1) = uQ c i * uQ c j := by
  rw [qf, single_mulVec_eq, dotProduct_smul, dotProduct_single, smul_eq_mul]
  ring

theorem labelVec_eq_uvec (l : ShortLabel) :
    labelVec l = uvec (labelIdx l) ∨ labelVec l = -uvec (labelIdx l) :=
  (classOf_eq_iff (uvec_mem (labelIdx l)) (labelVec_mem l)).1
    ((classOf_uvec (labelIdx l)).trans (phi0_labelElt l))

theorem uQ_mul_uQ_labelIdx (l : ShortLabel) (i j : Fin 24) :
    uQ (labelIdx l) i * uQ (labelIdx l) j = ((labelVec l i * labelVec l j : ℤ) : ℚ) := by
  unfold uQ
  rcases labelVec_eq_uvec l with h | h
  · rw [h]
    push_cast
    ring
  · rw [h]
    push_cast [Pi.neg_apply]
    ring

theorem qf_labelIdx_Ekk (l : ShortLabel) (k : Fin 24) :
    qf (labelIdx l) (basisA s(k, k)) = ((labelVec l k * labelVec l k : ℤ) : ℚ) := by
  rw [coe_basisA_diag, qf_single, uQ_mul_uQ_labelIdx]

theorem vMinus_apply (a b k : Fin 24) :
    vMinus a b k = 4 * (if k = a then 1 else 0) - 4 * (if k = b then 1 else 0) := by
  simp [vMinus, eℤ, Pi.single_apply]

theorem vPlus_apply (a b k : Fin 24) :
    vPlus a b k = 4 * (if k = a then 1 else 0) + 4 * (if k = b then 1 else 0) := by
  simp [vPlus, eℤ, Pi.single_apply]

theorem vMinus_mul_self {a b : Fin 24} (hab : a ≠ b) (k : Fin 24) :
    vMinus a b k * vMinus a b k =
      16 * ((if a = k then 1 else 0) + (if b = k then 1 else 0)) := by
  rw [vMinus_apply]
  by_cases ha : a = k
  · have hb : b ≠ k := fun hb => hab (ha.trans hb.symm)
    simp [ha, hb, Ne.symm hb]
  · by_cases hb : b = k
    · simp [ha, hb, Ne.symm ha]
    · simp [ha, hb, Ne.symm ha, Ne.symm hb]

theorem vPlus_mul_self {a b : Fin 24} (hab : a ≠ b) (k : Fin 24) :
    vPlus a b k * vPlus a b k =
      16 * ((if a = k then 1 else 0) + (if b = k then 1 else 0)) := by
  rw [vPlus_apply]
  by_cases ha : a = k
  · have hb : b ≠ k := fun hb => hab (ha.trans hb.symm)
    simp [ha, hb, Ne.symm hb]
  · by_cases hb : b = k
    · simp [ha, hb, Ne.symm ha]
    · simp [ha, hb, Ne.symm ha, Ne.symm hb]

theorem oddMin_mul_self (i : Fin 24) (d : Fin 24 → ZMod 2) (k : Fin 24) :
    oddMin i d k * oddMin i d k = 1 + 8 * (if i = k then 1 else 0) := by
  have hs : ((-1 : ℤ) ^ (d k).val) * ((-1) ^ (d k).val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have e : oddMin i d k * oddMin i d k = ((-1 : ℤ) ^ (d k).val * (-1) ^ (d k).val) *
      ((1 - 4 * if k = i then 1 else 0) * (1 - 4 * if k = i then 1 else 0)) := by
    unfold oddMin
    ring
  rw [e, hs, one_mul]
  by_cases h : k = i
  · simp only [h, ite_true]
    norm_num
  · simp [h, Ne.symm h]

theorem vOct_mul_self {d : Fin 24 → ZMod 2} {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d)
    (k : Fin 24) : vOct d δ k * vOct d δ k = if k ∈ supp d then 4 else 0 := by
  have e : vOct d δ k = 2 * bitLift (d k) - 4 * bitLift (Octad.ind δ k) := by
    simp only [vOct, liftℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  rcases zmod2_cases (d k) with h | h
  · have hk : k ∉ supp d := fun hk => (mem_supp_iff.1 hk) h
    have hkδ : k ∉ δ := fun h' => hk (hδ h')
    simp only [ite_eq_right hk, h, Octad.ind, ite_eq_right hkδ]
    rfl
  · have hk : k ∈ supp d := mem_supp_iff.2 (by rw [h]; decide)
    by_cases hkδ : k ∈ δ
    · simp only [ite_eq_left hk, h, Octad.ind, ite_eq_left hkδ]
      rfl
    · simp only [ite_eq_left hk, h, Octad.ind, ite_eq_right hkδ]
      rfl

theorem qf_rMinus_Ekk (p : LtPair) (k : Fin 24) :
    qf (labelIdx (.inl p)) (basisA s(k, k)) =
      16 * ((if p.1.1 = k then 1 else 0) + (if p.1.2 = k then 1 else 0)) := by
  rw [qf_labelIdx_Ekk]
  change ((vMinus p.1.1 p.1.2 k * vMinus p.1.1 p.1.2 k : ℤ) : ℚ) = _
  rw [vMinus_mul_self p.2.ne]
  push_cast
  ring

theorem qf_rPlus_Ekk (p : LtPair) (k : Fin 24) :
    qf (labelIdx (.inr (.inl p))) (basisA s(k, k)) =
      16 * ((if p.1.1 = k then 1 else 0) + (if p.1.2 = k then 1 else 0)) := by
  rw [qf_labelIdx_Ekk]
  change ((vPlus p.1.1 p.1.2 k * vPlus p.1.1 p.1.2 k : ℤ) : ℚ) = _
  rw [vPlus_mul_self p.2.ne]
  push_cast
  ring

theorem qf_rOdd_Ekk (c : C₀) (i k : Fin 24) :
    qf (labelIdx (.inr (.inr (.inl (c, i))))) (basisA s(k, k)) =
      1 + 8 * (if i = k then 1 else 0) := by
  rw [qf_labelIdx_Ekk]
  change ((oddMin i ((c : C) : Fin 24 → ZMod 2) k * oddMin i ((c : C) : Fin 24 → ZMod 2) k : ℤ) :
    ℚ) = _
  rw [oddMin_mul_self]
  push_cast
  ring

theorem qf_rOct_Ekk (o : OctIdx) (k : Fin 24) :
    qf (labelIdx (.inr (.inr (.inr o)))) (basisA s(k, k)) =
      if k ∈ octSupp o.1 then 4 else 0 := by
  rw [qf_labelIdx_Ekk]
  change ((vOct ((o.1 : C) : Fin 24 → ZMod 2) (octRep o.1 o.2) k *
    vOct ((o.1 : C) : Fin 24 → ZMod 2) (octRep o.1 o.2) k : ℤ) : ℚ) = _
  rw [vOct_mul_self (octRep_spec o.1 o.2).1]
  push_cast
  rfl

theorem single_vecMul_single_diag (i k : Fin 24) :
    (Pi.single i (1 : ℚ) : Fin 24 → ℚ) ᵥ* Matrix.single k k 1 =
      if i = k then Pi.single i 1 else 0 := by
  funext j
  rw [single_vecMul, one_smul]
  by_cases h : i = k
  · subst h
    simp [Matrix.single_apply, Pi.single_apply, eq_comm]
  · simp [h, Ne.symm h]

theorem tensor_mul_Ekk (q : SpinIdx → ℚ) (i k : Fin 24) :
    tensor q (Pi.single i 1) * Matrix.single k k (1 : ℚ) =
      (if i = k then (1 : ℚ) else 0) • tensor q (Pi.single i 1) := by
  rw [tensor, vecMulVec_mul, single_vecMul_single_diag]
  by_cases h : i = k
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right h, zero_smul]
    ext a b
    simp [vecMulVec_apply]

theorem gmul_Ekk_inW (k i : Fin 24) (s : ℚ) (q : SpinIdx → ℚ) :
    gmul (inA (basisA s(k, k))) (inW (s • tensor q (Pi.single i 1))) =
      ((8 : ℚ)⁻¹ + if i = k then 1 else 0) • inW (s • tensor q (Pi.single i 1)) := by
  rw [gmul_inA_inW, coe_basisA_diag, trace_single_eq_same, Matrix.smul_mul, tensor_mul_Ekk,
    ← smul_inW]
  congr 1
  rw [smul_comm s (if i = k then (1 : ℚ) else 0), add_smul, one_div]

end DiagonalInvariance

open DiagonalInvariance

@[expose] def diagEig (k : Fin 24) : TIdx → ℚ
  | .inl i => if i = k then 4 else 0
  | .inr (.inl (p, _)) => 2 * ((if p.1.1 = k then 1 else 0) + (if p.1.2 = k then 1 else 0))
  | .inr (.inr (.inl (_, i, _))) => (8 : ℚ)⁻¹ + if i = k then 1 else 0
  | .inr (.inr (.inr o)) => if k ∈ octSupp o.1 then (2 : ℚ)⁻¹ else 0

theorem gmul_Ekk_tbasis_diag (k i : Fin 24) :
    gmul (inA (basisA s(k, k))) (tbasis (.inl i)) =
      (if i = k then (4 : ℚ) else 0) • tbasis (.inl i) := by
  rw [tbasis_diag]
  change gmul (inA (basisA s(k, k))) (inA (basisA s(i, i))) = _
  rw [gmul_inA_inA]
  refine Prod.ext (Subtype.ext ?_) ?_
  · change gmulA (inA (basisA s(k, k))) (inA (basisA s(i, i))) =
      (if i = k then (4 : ℚ) else 0) • (basisA s(i, i) : Matrix (Fin 24) (Fin 24) ℚ)
    rw [gmulA_inA_inA, coe_basisA_diag, coe_basisA_diag]
    by_cases h : i = k
    · subst h
      rw [ite_eq_left rfl, single_mul_single_same, one_mul, ← two_smul ℚ, smul_smul]
      norm_num
    · rw [ite_eq_right h]
      simp [h, Ne.symm h]
  · exact (smul_zero _).symm

theorem DiagonalInvariance.Ekk_mul_add (k : Fin 24) (p : LtPair) :
    (2 : ℚ) • (Matrix.single k k (1 : ℚ) * (Matrix.single p.1.1 p.1.2 1 +
        Matrix.single p.1.2 p.1.1 1) +
      (Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1) * Matrix.single k k 1) =
      (2 * ((if p.1.1 = k then (1 : ℚ) else 0) + (if p.1.2 = k then 1 else 0))) •
        (Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1) := by
  have hne : p.1.1 ≠ p.1.2 := p.2.ne
  by_cases h1 : p.1.1 = k
  · have h2 : p.1.2 ≠ k := fun h2 => hne (h1.trans h2.symm)
    rw [← h1]
    simp [Matrix.mul_add, Matrix.add_mul, hne, Ne.symm hne]
  · by_cases h2 : p.1.2 = k
    · rw [← h2]
      simp [Matrix.mul_add, Matrix.add_mul, hne, Ne.symm hne]
      module
    · simp [Matrix.mul_add, Matrix.add_mul, h1, h2, Ne.symm h1, Ne.symm h2]

theorem gmul_Ekk_tbasis_pair (k : Fin 24) (p : LtPair) (m : Fin 3) :
    gmul (inA (basisA s(k, k))) (tbasis (.inr (.inl (p, m)))) =
      (2 * ((if p.1.1 = k then (1 : ℚ) else 0) + (if p.1.2 = k then 1 else 0))) •
        tbasis (.inr (.inl (p, m))) := by
  have hq0 := qf_rMinus_Ekk p k
  have hq1 := qf_rPlus_Ekk p k
  have hXm : Xlift (rMinus p.1.1 p.1.2) = Pi.single (labelIdx (.inl p)) 1 :=
    Xlift_labelElt (.inl p)
  have hXp : Xlift (rPlus p.1.1 p.1.2) = Pi.single (labelIdx (.inr (.inl p))) 1 :=
    Xlift_labelElt (.inr (.inl p))
  have key : ∀ c : ShortIdx, c = labelIdx (.inl p) ∨ c = labelIdx (.inr (.inl p)) →
      qf c (basisA s(k, k)) / 8 =
        2 * ((if p.1.1 = k then (1 : ℚ) else 0) + (if p.1.2 = k then 1 else 0)) := by
    rintro c (rfl | rfl)
    · rw [hq0]; ring
    · rw [hq1]; ring
  rcases m with ⟨_ | _ | _ | m, hm⟩
  · rw [show (⟨0, hm⟩ : Fin 3) = 0 from rfl, tbasis_pair_zero]
    change gmul (inA (basisA s(k, k))) (inA (basisA s(p.1.1, p.1.2))) = _
    rw [gmul_inA_inA]
    refine Prod.ext (Subtype.ext ?_) ?_
    · change gmulA (inA (basisA s(k, k))) (inA (basisA s(p.1.1, p.1.2))) =
        (2 * ((if p.1.1 = k then (1 : ℚ) else 0) + (if p.1.2 = k then 1 else 0))) •
          (basisA s(p.1.1, p.1.2) : Matrix (Fin 24) (Fin 24) ℚ)
      rw [gmulA_inA_inA, coe_basisA_diag, coe_basisA_ltPair]
      exact Ekk_mul_add k p
    · exact (smul_zero _).symm
  · rw [show (⟨0 + 1, hm⟩ : Fin 3) = 1 from rfl, tbasis_pair_one]
    refine gmul_inA_inX_eq_smul _ fun c hc => key c ?_
    by_contra h
    apply hc
    rw [hXm, hXp, Pi.sub_apply, Pi.single_eq_of_ne (not_or.1 h).1,
      Pi.single_eq_of_ne (not_or.1 h).2, sub_zero]
  · rw [show (⟨0 + 1 + 1, hm⟩ : Fin 3) = 2 from rfl, tbasis_pair_two]
    refine gmul_inA_inX_eq_smul _ fun c hc => key c ?_
    by_contra h
    apply hc
    rw [hXm, hXp, Pi.add_apply, Pi.single_eq_of_ne (not_or.1 h).1,
      Pi.single_eq_of_ne (not_or.1 h).2, add_zero]
  · omega

theorem gmul_Ekk_tbasis_odd (k : Fin 24) (c : C₀) (i : Fin 24) (m : Fin 3) :
    gmul (inA (basisA s(k, k))) (tbasis (.inr (.inr (.inl (c, i, m))))) =
      ((8 : ℚ)⁻¹ + if i = k then 1 else 0) • tbasis (.inr (.inr (.inl (c, i, m)))) := by
  rcases m with ⟨_ | _ | _ | m, hm⟩
  · rw [show (⟨0, hm⟩ : Fin 3) = 0 from rfl, tbasis_odd_zero]
    have hX : Xlift (rOdd c i) = Pi.single (labelIdx (.inr (.inr (.inl (c, i))))) 1 :=
      Xlift_labelElt (.inr (.inr (.inl (c, i))))
    refine gmul_inA_inX_eq_smul _ fun c' hc' => ?_
    have hc'' : c' = labelIdx (.inr (.inr (.inl (c, i)))) := by
      by_contra h
      apply hc'
      rw [hX, Pi.single_eq_of_ne h]
    rw [hc'', qf_rOdd_Ekk]
    by_cases h : i = k
    · simp only [h, ite_true]
      norm_num
    · simp [h]
  · rw [show (⟨0 + 1, hm⟩ : Fin 3) = 1 from rfl, tbasis_odd_one]
    exact gmul_Ekk_inW k i _ _
  · rw [show (⟨0 + 1 + 1, hm⟩ : Fin 3) = 2 from rfl, tbasis_odd_two]
    exact gmul_Ekk_inW k i _ _
  · omega

theorem gmul_Ekk_tbasis_oct (k : Fin 24) (o : OctIdx) :
    gmul (inA (basisA s(k, k))) (tbasis (.inr (.inr (.inr o)))) =
      (if k ∈ octSupp o.1 then (2 : ℚ)⁻¹ else 0) • tbasis (.inr (.inr (.inr o))) := by
  rw [tbasis_oct]
  have hX : Xlift (rOctQ o.1 o.2) = Pi.single (labelIdx (.inr (.inr (.inr o)))) 1 :=
    Xlift_labelElt (.inr (.inr (.inr o)))
  refine gmul_inA_inX_eq_smul _ fun c' hc' => ?_
  have hc'' : c' = labelIdx (.inr (.inr (.inr o))) := by
    by_contra h
    apply hc'
    rw [hX, Pi.single_eq_of_ne h]
  rw [hc'', qf_rOct_Ekk]
  split_ifs <;> norm_num

theorem gmul_Ekk_tbasis (k : Fin 24) (x : TIdx) :
    gmul (inA (basisA s(k, k))) (tbasis x) = diagEig k x • tbasis x := by
  rcases x with i | ⟨p, m⟩ | ⟨c, i, m⟩ | o
  · exact gmul_Ekk_tbasis_diag k i
  · exact gmul_Ekk_tbasis_pair k p m
  · exact gmul_Ekk_tbasis_odd k c i m
  · exact gmul_Ekk_tbasis_oct k o

theorem gmul_Ekk_tauB_tbasis (k : Fin 24) (x : TIdx) :
    gmul (inA (basisA s(k, k))) (tauB (tbasis x)) =
      tauB (gmul (inA (basisA s(k, k))) (tbasis x)) := by
  rw [gmul_Ekk_tbasis k x, map_smul]
  rcases x with i | ⟨p, m⟩ | ⟨c, i, m⟩ | ⟨d, v⟩
  · rw [tauB_diag, gmul_Ekk_tbasis]
  · rw [tauB_pair, gmul_Ekk_tbasis]
    rfl
  · rw [tauB_odd, gmul_Ekk_tbasis]
    rfl
  · rw [tauB_oct, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, gmul_Ekk_tbasis, smul_comm]
    rfl

theorem gmul_Ekk_tauB (k : Fin 24) (u : SpaceB) :
    gmul (inA (basisA s(k, k))) (tauB u) = tauB (gmul (inA (basisA s(k, k))) u) := by
  have h : (gmul (inA (basisA s(k, k)))).comp (tauB : SpaceB →ₗ[ℚ] SpaceB) =
      (tauB : SpaceB →ₗ[ℚ] SpaceB).comp (gmul (inA (basisA s(k, k)))) :=
    tbasis.ext fun x => gmul_Ekk_tauB_tbasis k x
  exact LinearMap.congr_fun h u

theorem inA_eq_sum_of_diagonal {a : Fin 24 → ℚ} {A : symMat}
    (hA : (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a) :
    inA A = ∑ k, a k • inA (basisA s(k, k)) := by
  refine Prod.ext (Subtype.ext ?_) ?_
  · rw [Prod.fst_sum, Submodule.coe_sum, hA, ← sum_single_eq_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Prod.smul_fst, Submodule.coe_smul, coe_basisA_diag, smul_single, smul_eq_mul, mul_one]
  · rw [Prod.snd_sum]
    simp

theorem gmul_inA_tauB_of_diagonal {a : Fin 24 → ℚ} {A : symMat}
    (hA : (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a) (u : SpaceB) :
    gmul (inA A) (tauB u) = tauB (gmul (inA A) u) := by
  rw [inA_eq_sum_of_diagonal hA, map_sum, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, gmul_Ekk_tauB, map_smul]

theorem tauB_inA_of_diagonal {a : Fin 24 → ℚ} {A : symMat}
    (hA : (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a) : tauB (inA A) = inA A := by
  rw [inA_eq_sum_of_diagonal hA, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : inA (basisA s(k, k)) = tbasis (.inl k) := (tbasis_diag k).symm
  rw [map_smul, e, tauB_diag]

theorem tauB_symm_inA_of_diagonal {a : Fin 24 → ℚ} {A : symMat}
    (hA : (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a) : tauB.symm (inA A) = inA A := by
  rw [LinearEquiv.symm_apply_eq, tauB_inA_of_diagonal hA]

theorem T_inA_tauB_of_diagonal {a : Fin 24 → ℚ} {A : symMat}
    (hA : (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a) (u v : SpaceB) :
    T (inA A) (tauB u) (tauB v) = T (inA A) u v :=
  calc T (inA A) (tauB u) (tauB v) = bform (gmul (inA A) (tauB u)) (tauB v) := rfl
    _ = bform (tauB (gmul (inA A) u)) (tauB v) := by rw [gmul_inA_tauB_of_diagonal hA]
    _ = bform (gmul (inA A) u) v := bform_tauB _ _
    _ = T (inA A) u v := rfl

theorem T_inA_tauB_symm_of_diagonal {a : Fin 24 → ℚ} {A : symMat}
    (hA : (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a) (u v : SpaceB) :
    T (inA A) (tauB.symm u) (tauB.symm v) = T (inA A) u v := by
  have h := T_inA_tauB_of_diagonal hA (tauB.symm u) (tauB.symm v)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem T_tauB_of_diagonal {a : Fin 24 → ℚ} {A : symMat}
    (hA : (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a) (u v : SpaceB) :
    T (tauB (inA A)) (tauB u) (tauB v) = T (inA A) u v ∧
      T (tauB u) (tauB (inA A)) (tauB v) = T u (inA A) v ∧
      T (tauB u) (tauB v) (tauB (inA A)) = T u v (inA A) := by
  rw [tauB_inA_of_diagonal hA]
  refine ⟨T_inA_tauB_of_diagonal hA u v, ?_, ?_⟩
  · calc T (tauB u) (inA A) (tauB v) = T (inA A) (tauB u) (tauB v) := T_swap12 _ _ _
      _ = T (inA A) u v := T_inA_tauB_of_diagonal hA u v
      _ = T u (inA A) v := T_swap12 _ _ _
  · calc T (tauB u) (tauB v) (inA A) = T (inA A) (tauB u) (tauB v) := T_cycle2 _ _ _
      _ = T (inA A) u v := T_inA_tauB_of_diagonal hA u v
      _ = T u v (inA A) := (T_cycle2 _ _ _).symm

theorem T_tauB_symm_of_diagonal {a : Fin 24 → ℚ} {A : symMat}
    (hA : (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a) (u v : SpaceB) :
    T (tauB.symm (inA A)) (tauB.symm u) (tauB.symm v) = T (inA A) u v ∧
      T (tauB.symm u) (tauB.symm (inA A)) (tauB.symm v) = T u (inA A) v ∧
      T (tauB.symm u) (tauB.symm v) (tauB.symm (inA A)) = T u v (inA A) := by
  rw [tauB_symm_inA_of_diagonal hA]
  refine ⟨T_inA_tauB_symm_of_diagonal hA u v, ?_, ?_⟩
  · calc T (tauB.symm u) (inA A) (tauB.symm v) = T (inA A) (tauB.symm u) (tauB.symm v) :=
          T_swap12 _ _ _
      _ = T (inA A) u v := T_inA_tauB_symm_of_diagonal hA u v
      _ = T u (inA A) v := T_swap12 _ _ _
  · calc T (tauB.symm u) (tauB.symm v) (inA A) = T (inA A) (tauB.symm u) (tauB.symm v) :=
          T_cycle2 _ _ _
      _ = T (inA A) u v := T_inA_tauB_symm_of_diagonal hA u v
      _ = T u v (inA A) := (T_cycle2 _ _ _).symm

theorem triality_Griess_diagonal_invariance :
    (∀ (a : Fin 24 → ℚ) (A : symMat), (A : Matrix (Fin 24) (Fin 24) ℚ) = diagonal a →
      tauB (inA A) = inA A ∧ tauB.symm (inA A) = inA A ∧
      (∀ u v : SpaceB, T (inA A) (tauB u) (tauB v) = T (inA A) u v) ∧
      (∀ u v : SpaceB, T (inA A) (tauB.symm u) (tauB.symm v) = T (inA A) u v) ∧
      (∀ u v : SpaceB, T (tauB (inA A)) (tauB u) (tauB v) = T (inA A) u v ∧
        T (tauB u) (tauB (inA A)) (tauB v) = T u (inA A) v ∧
        T (tauB u) (tauB v) (tauB (inA A)) = T u v (inA A)) ∧
      (∀ u v : SpaceB, T (tauB.symm (inA A)) (tauB.symm u) (tauB.symm v) = T (inA A) u v ∧
        T (tauB.symm u) (tauB.symm (inA A)) (tauB.symm v) = T u (inA A) v ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm (inA A)) = T u v (inA A))) ∧
    (∀ k i : Fin 24, gmul (inA (basisA s(k, k))) (tbasis (.inl i)) =
      (if i = k then (4 : ℚ) else 0) • tbasis (.inl i)) ∧
    (∀ (k : Fin 24) (p : LtPair) (m : Fin 3),
      gmul (inA (basisA s(k, k))) (tbasis (.inr (.inl (p, m)))) =
        (2 * ((if p.1.1 = k then (1 : ℚ) else 0) + (if p.1.2 = k then 1 else 0))) •
          tbasis (.inr (.inl (p, m)))) ∧
    (∀ (k : Fin 24) (c : C₀) (i : Fin 24) (m : Fin 3),
      gmul (inA (basisA s(k, k))) (tbasis (.inr (.inr (.inl (c, i, m))))) =
        ((8 : ℚ)⁻¹ + if i = k then 1 else 0) • tbasis (.inr (.inr (.inl (c, i, m))))) ∧
    (∀ (k : Fin 24) (o : OctIdx),
      gmul (inA (basisA s(k, k))) (tbasis (.inr (.inr (.inr o)))) =
        (if k ∈ octSupp o.1 then (2 : ℚ)⁻¹ else 0) • tbasis (.inr (.inr (.inr o)))) :=
  ⟨fun _ _ hA => ⟨tauB_inA_of_diagonal hA, tauB_symm_inA_of_diagonal hA,
      T_inA_tauB_of_diagonal hA, T_inA_tauB_symm_of_diagonal hA, T_tauB_of_diagonal hA,
      T_tauB_symm_of_diagonal hA⟩,
    gmul_Ekk_tbasis_diag, gmul_Ekk_tbasis_pair, gmul_Ekk_tbasis_odd, gmul_Ekk_tbasis_oct⟩

end CFSG.Monster.Griess
