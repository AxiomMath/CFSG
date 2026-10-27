module

public import CFSG.Monster.B.Cbar.TraceBlocks
public import CFSG.Monster.B.Cbar.Octads
public import CFSG.Monster.Griess.TrialityBasis.Classes
public import CFSG.Monster.Spin.FourierPauli

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Parity Matrix

theorem hrStar : IsShortCoord (coordOf (rMinus 0 1)) :=
  isShortCoord_labelElt (.inl ⟨(0, 1), by decide⟩)

@[expose] noncomputable def outerZ (w : Fin 24 → ℤ) : Matrix (Fin 24) (Fin 24) ℚ :=
  vecMulVec (ratVec w) (ratVec w)

theorem outerZ_neg (w : Fin 24 → ℤ) : outerZ (-w) = outerZ w := by
  rw [outerZ, outerZ, ratVec_neg, neg_vecMulVec, vecMulVec_neg, neg_neg]

theorem outerZ_apply (w : Fin 24 → ℤ) (j k : Fin 24) :
    outerZ w j k = ratVec w j * ratVec w k := rfl

theorem pair_deltaPair_zero_one (a : C) :
    pair a (deltaPair 0 1) = (a : Fin 24 → ZMod 2) 0 + (a : Fin 24 → ZMod 2) 1 := by
  rw [deltaPair, pair_mk, dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]

theorem sgn_alphaS_cStar (d : ShortIdx) :
    sgn ((alphaS (shortCls hrStar) d : ℤ) : ZMod 2) =
      sgn ((d.1.1 : Fin 24 → ZMod 2) 0 + (d.1.1 : Fin 24 → ZMod 2) 1) := by
  rw [← pair_add_pair_eq_alphaS]
  change sgn (pair d.1.1 (coordOf (rMinus 0 1)).2 + pair (coordOf (rMinus 0 1)).1 d.1.2) = _
  rw [coordOf_rMinus, pair_zero_left, add_zero, pair_deltaPair_zero_one]

theorem Umat_labelIdx (l : ShortLabel) : Umat (labelIdx l) = outerZ (labelVec l) := by
  have hcl : classOf (labelVec l) = classOf (uvec (labelIdx l)) :=
    (phi0_labelElt l).symm.trans (classOf_uvec (labelIdx l)).symm
  rcases (classOf_eq_iff (labelVec_mem l) (uvec_mem _)).1 hcl with h | h
  · rw [Umat, uQ_eq_ratVec, h]
    rfl
  · rw [Umat, uQ_eq_ratVec, h]
    exact outerZ_neg _

noncomputable abbrev labelCode (l : ShortLabel) : C := (coordOf (labelElt l)).1

theorem signedU_eq_sum_labels :
    signedU hrStar = ∑ l : ShortLabel,
      sgn ((labelCode l : Fin 24 → ZMod 2) 0 + (labelCode l : Fin 24 → ZMod 2) 1) •
        outerZ (labelVec l) := by
  rw [signedU, ← Equiv.sum_comp labelEquiv]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [labelEquiv_apply, sgn_alphaS_cStar, Umat_labelIdx]
  rfl

theorem labelCode_minus (p : LtPair) : labelCode (.inl p) = 0 := by
  change (coordOf (rMinus p.1.1 p.1.2)).1 = 0
  rw [coordOf_rMinus]

theorem labelCode_plus (p : LtPair) : labelCode (.inr (.inl p)) = ΩC := by
  change (coordOf (rPlus p.1.1 p.1.2)).1 = ΩC
  rw [coordOf_rPlus]

theorem vecMulVec_single_single (i j : Fin 24) (a b : ℚ) :
    vecMulVec (Pi.single i a) (Pi.single j b) = Matrix.single i j (a * b) := by
  ext k l
  rw [vecMulVec_apply, Matrix.single_apply, Pi.single_apply, Pi.single_apply]
  by_cases hk : k = i
  · subst hk
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl, Ne.symm hl]
  · simp [hk, Ne.symm hk]

theorem outerZ_vMinus_add_vPlus (i j : Fin 24) :
    outerZ (vMinus i j) + outerZ (vPlus i j) =
      (32 : ℚ) • (Matrix.single i i 1 + Matrix.single j j 1) := by
  have hm : ratVec (vMinus i j) = (4 : ℚ) • Pi.single i 1 - (4 : ℚ) • Pi.single j 1 := by
    funext k
    simp only [ratVec, vMinus, eℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> norm_num
  have hp : ratVec (vPlus i j) = (4 : ℚ) • Pi.single i 1 + (4 : ℚ) • Pi.single j 1 := by
    funext k
    simp only [ratVec, vPlus, eℤ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> norm_num
  rw [outerZ, outerZ, hm, hp]
  simp only [vecMulVec_add, add_vecMulVec, vecMulVec_sub, sub_vecMulVec, smul_vecMulVec,
    vecMulVec_smul, vecMulVec_single_single, smul_add, mul_one]
  module

private theorem card_pairs_through : ∀ k : Fin 24,
    (Finset.univ.filter fun p : LtPair => p.1.1 = k).card +
      (Finset.univ.filter fun p : LtPair => p.1.2 = k).card = 23 := by
  decide

theorem sum_single_diag_pairs :
    ∑ p : LtPair, (Matrix.single p.1.1 p.1.1 (1 : ℚ) + Matrix.single p.1.2 p.1.2 1) =
      (23 : ℚ) • 1 := by
  ext k l
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hkl : k = l
  · subst hkl
    simp only [and_self, mul_one, ite_true]
    rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
    exact_mod_cast card_pairs_through k
  · simp only [hkl, mul_zero, ite_false]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ite_eq_right (fun h => hkl (h.1.symm.trans h.2)),
      ite_eq_right (fun h => hkl (h.1.symm.trans h.2)), add_zero]

theorem sum_pair_labels :
    (∑ p : LtPair, sgn ((labelCode (.inl p) : Fin 24 → ZMod 2) 0 +
        (labelCode (.inl p) : Fin 24 → ZMod 2) 1) • outerZ (labelVec (.inl p))) +
      (∑ p : LtPair, sgn ((labelCode (.inr (.inl p)) : Fin 24 → ZMod 2) 0 +
        (labelCode (.inr (.inl p)) : Fin 24 → ZMod 2) 1) • outerZ (labelVec (.inr (.inl p)))) =
      (736 : ℚ) • 1 := by
  have h1 : ∀ p : LtPair, sgn ((labelCode (.inl p) : Fin 24 → ZMod 2) 0 +
      (labelCode (.inl p) : Fin 24 → ZMod 2) 1) = 1 := by
    intro p
    rw [labelCode_minus]
    rfl
  have h2 : ∀ p : LtPair, sgn ((labelCode (.inr (.inl p)) : Fin 24 → ZMod 2) 0 +
      (labelCode (.inr (.inl p)) : Fin 24 → ZMod 2) 1) = 1 := by
    intro p
    rw [labelCode_plus]
    rfl
  simp only [h1, h2, one_smul]
  rw [← Finset.sum_add_distrib]
  change ∑ p : LtPair, (outerZ (vMinus p.1.1 p.1.2) + outerZ (vPlus p.1.1 p.1.2)) = _
  simp only [outerZ_vMinus_add_vPlus]
  rw [← Finset.smul_sum, sum_single_diag_pairs, smul_smul]
  norm_num

theorem labelCode_odd (q : C₀ × Fin 24) : labelCode (.inr (.inr (.inl q))) = aOdd q.1 q.2 := by
  change (coordOf (rOdd q.1 q.2)).1 = aOdd q.1 q.2
  rw [coordOf_rOdd]

private theorem two_eq_zero_zmod : (2 : ZMod 2) = 0 := rfl

theorem aOdd_apply (c : C₀) (i j : Fin 24) :
    ((aOdd c i : C) : Fin 24 → ZMod 2) j = ((c : C) : Fin 24 → ZMod 2) j + mOdd c i := by
  rw [aOdd, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change _ + mOdd c i * 1 = _
  rw [mul_one]

theorem sgn_labelCode_odd (q : C₀ × Fin 24) :
    sgn ((labelCode (.inr (.inr (.inl q))) : Fin 24 → ZMod 2) 0 +
      (labelCode (.inr (.inr (.inl q))) : Fin 24 → ZMod 2) 1) =
      sgn (((q.1 : C) : Fin 24 → ZMod 2) 0 + ((q.1 : C) : Fin 24 → ZMod 2) 1) := by
  rw [labelCode_odd, aOdd_apply, aOdd_apply]
  congr 1
  linear_combination mOdd q.1 q.2 * two_eq_zero_zmod

theorem sgn_eq_neg_one_pow (t : ZMod 2) : sgn t = (-1 : ℚ) ^ t.val := by
  have : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases this t with rfl | rfl <;> rfl

theorem ratVec_oddMin (i : Fin 24) (d : Fin 24 → ZMod 2) (j : Fin 24) :
    ratVec (oddMin i d) j = sgn (d j) * (1 - 4 * if j = i then 1 else 0) := by
  rw [ratVec, oddMin, sgn_eq_neg_one_pow]
  push_cast
  split_ifs <;> simp

theorem sum_odd_weights (j k : Fin 24) :
    ∑ i : Fin 24, (1 - 4 * (if j = i then (1 : ℚ) else 0)) * (1 - 4 * if k = i then 1 else 0) =
      16 + 16 * if j = k then 1 else 0 := by
  have e : ∀ i : Fin 24, (1 - 4 * (if j = i then (1 : ℚ) else 0)) * (1 - 4 * if k = i then 1 else 0) =
      1 - 4 * (if j = i then 1 else 0) - 4 * (if k = i then 1 else 0) +
        16 * (if j = i then (if k = i then 1 else 0) else 0) := by
    intro i
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  by_cases hjk : j = k
  · subst hjk
    simp
    norm_num
  · simp [hjk, Ne.symm hjk]
    norm_num

theorem sum_single_zmod_apply (x : Fin 24 → ZMod 2) (a : C) :
    (a : Fin 24 → ZMod 2) ⬝ᵥ x = ∑ i, (a : Fin 24 → ZMod 2) i * x i := rfl

theorem not_forall_pair_C₀ {x : Fin 24 → ZMod 2} (hx0 : x ≠ 0) (hw : hammingNorm x < 8)
    (hΩ : pair ΩC (Submodule.Quotient.mk x) = 0) :
    ¬ ∀ c : C₀, pair (c : C) (Submodule.Quotient.mk x) = 0 := by
  intro h
  have hC : x ∈ C := by
    rw [mem_C_iff_forall_dotProduct]
    intro y hy
    obtain ⟨p, hp, -⟩ := existsUnique_add_smul_ΩC ⟨y, hy⟩
    have hpair : pair (⟨y, hy⟩ : C) (Submodule.Quotient.mk x) = 0 := by
      rw [hp, pair_add_left, pair_smul_left, h p.1, hΩ, mul_zero, add_zero]
    rw [pair_mk] at hpair
    rw [dotProduct_comm]
    exact hpair
  have := eight_le_wt hC hx0
  omega

theorem pair_mk_four (a : C) (j k : Fin 24) :
    pair a (Submodule.Quotient.mk (Pi.single 0 1 + Pi.single 1 1 + Pi.single j 1 + Pi.single k 1)) =
      (a : Fin 24 → ZMod 2) 0 + (a : Fin 24 → ZMod 2) 1 + (a : Fin 24 → ZMod 2) j +
        (a : Fin 24 → ZMod 2) k := by
  rw [pair_mk]
  simp only [dotProduct_add, dotProduct_single, mul_one]

theorem hammingNorm_four_lt (j k : Fin 24) :
    hammingNorm (Pi.single 0 1 + Pi.single 1 1 + Pi.single j 1 + Pi.single k 1 :
      Fin 24 → ZMod 2) < 8 := by
  have hsub : (Finset.univ.filter fun i => (Pi.single 0 1 + Pi.single 1 1 + Pi.single j 1 +
      Pi.single k 1 : Fin 24 → ZMod 2) i ≠ 0) ⊆ {0, 1, j, k} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.single_apply] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hne
    push Not at hne
    apply hi
    rw [ite_eq_right hne.1, ite_eq_right hne.2.1, ite_eq_right hne.2.2.1, ite_eq_right hne.2.2.2]
    rfl
  have h4 : ({0, 1, j, k} : Finset (Fin 24)).card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  have := Finset.card_le_card hsub
  rw [hammingNorm]
  omega

theorem four_singles_ne_zero (j k : Fin 24) (hjk : ¬((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0))) :
    (Pi.single 0 1 + Pi.single 1 1 + Pi.single j 1 + Pi.single k 1 : Fin 24 → ZMod 2) ≠ 0 := by
  intro h0
  by_cases hjk' : j = k
  · subst hjk'
    have h := congrFun h0 0
    simp only [Pi.add_apply, Pi.single_apply, Pi.zero_apply] at h
    by_cases hj : (0 : Fin 24) = j
    · subst hj
      revert h
      decide
    · simp [hj] at h
  · by_cases hj : j = 0 ∨ j = 1
    · have hk : ¬(k = 0 ∨ k = 1) := by
        rintro (rfl | rfl) <;> rcases hj with rfl | rfl <;> simp_all
      have h := congrFun h0 k
      simp only [Pi.add_apply, Pi.single_apply, Pi.zero_apply] at h
      push Not at hk
      simp [hk.1, hk.2, Ne.symm hjk'] at h
    · have h := congrFun h0 j
      simp only [Pi.add_apply, Pi.single_apply, Pi.zero_apply] at h
      push Not at hj
      simp [hj.1, hj.2, hjk'] at h

theorem sum_sgn_C₀_four (j k : Fin 24) :
    ∑ c : C₀, sgn (((c : C) : Fin 24 → ZMod 2) 0 + ((c : C) : Fin 24 → ZMod 2) 1 +
      ((c : C) : Fin 24 → ZMod 2) j + ((c : C) : Fin 24 → ZMod 2) k) =
      if (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) then 2048 else 0 := by
  have h := sum_sgnR_pair (two_ne_zero : (2 : ℚ) ≠ 0)
    (Submodule.Quotient.mk (Pi.single 0 1 + Pi.single 1 1 + Pi.single j 1 + Pi.single k 1))
  simp only [sgnR_rat, pair_mk_four] at h
  rw [h]
  by_cases hjk : (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)
  · rw [ite_eq_left hjk, ite_eq_left]
    intro c
    rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring_nf <;>
      linear_combination (((c : C) : Fin 24 → ZMod 2) 0 + ((c : C) : Fin 24 → ZMod 2) 1) *
        two_eq_zero_zmod
  · rw [ite_eq_right hjk, ite_eq_right]
    intro hall
    refine not_forall_pair_C₀ ?_ (hammingNorm_four_lt j k) ?_ (fun c => by
      rw [pair_mk_four]; exact hall c)
    · exact four_singles_ne_zero j k hjk
    · rw [pair_mk]
      simp only [dotProduct_add, dotProduct_single, mul_one]
      change (1 : ZMod 2) + 1 + 1 + 1 = 0
      rfl

theorem sum_odd_labels :
    ∑ q : C₀ × Fin 24, sgn ((labelCode (.inr (.inr (.inl q))) : Fin 24 → ZMod 2) 0 +
        (labelCode (.inr (.inr (.inl q))) : Fin 24 → ZMod 2) 1) •
        outerZ (labelVec (.inr (.inr (.inl q)))) =
      (32768 : ℚ) • (Matrix.single 0 1 1 + Matrix.single 1 0 1) := by
  simp only [sgn_labelCode_odd]
  ext j k
  rw [Matrix.sum_apply]
  change ∑ q : C₀ × Fin 24, sgn (((q.1 : C) : Fin 24 → ZMod 2) 0 + ((q.1 : C) : Fin 24 → ZMod 2) 1) *
      (ratVec (oddMin q.2 ((q.1 : C) : Fin 24 → ZMod 2)) j *
        ratVec (oddMin q.2 ((q.1 : C) : Fin 24 → ZMod 2)) k) = _
  simp only [ratVec_oddMin]
  have e : ∀ q : C₀ × Fin 24,
      sgn (((q.1 : C) : Fin 24 → ZMod 2) 0 + ((q.1 : C) : Fin 24 → ZMod 2) 1) *
        (sgn (((q.1 : C) : Fin 24 → ZMod 2) j) * (1 - 4 * if j = q.2 then 1 else 0) *
          (sgn (((q.1 : C) : Fin 24 → ZMod 2) k) * (1 - 4 * if k = q.2 then 1 else 0))) =
      sgn (((q.1 : C) : Fin 24 → ZMod 2) 0 + ((q.1 : C) : Fin 24 → ZMod 2) 1 +
        ((q.1 : C) : Fin 24 → ZMod 2) j + ((q.1 : C) : Fin 24 → ZMod 2) k) *
        ((1 - 4 * if j = q.2 then 1 else 0) * (1 - 4 * if k = q.2 then 1 else 0)) := by
    intro q
    simp only [sgn_add]
    ring
  rw [Finset.sum_congr rfl fun q _ => e q, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, sum_odd_weights]
  rw [← Finset.sum_mul, sum_sgn_C₀_four]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h01 : (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)
  · rw [ite_eq_left h01]
    rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  · rw [ite_eq_right h01, zero_mul]
    have h1 : ¬((0 : Fin 24) = j ∧ (1 : Fin 24) = k) := fun h => h01 (Or.inl ⟨h.1.symm, h.2.symm⟩)
    have h2 : ¬((1 : Fin 24) = j ∧ (0 : Fin 24) = k) := fun h => h01 (Or.inr ⟨h.1.symm, h.2.symm⟩)
    rw [ite_eq_right h1, ite_eq_right h2]
    norm_num

theorem labelCode_oct (o : OctIdx) :
    labelCode (.inr (.inr (.inr o))) = aOct o.1 (octRep o.1 o.2) := by
  change (coordOf (rOctQ o.1 o.2)).1 = _
  rw [rOctQ, coordOf_rOct]

theorem aOct_apply (d : C) (δ : Finset (Fin 24)) (j : Fin 24) :
    ((aOct d δ : C) : Fin 24 → ZMod 2) j = (d : Fin 24 → ZMod 2) j + nOct δ := by
  rw [aOct, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change _ + nOct δ * 1 = _
  rw [mul_one]

theorem sgn_labelCode_oct (o : OctIdx) :
    sgn ((labelCode (.inr (.inr (.inr o))) : Fin 24 → ZMod 2) 0 +
      (labelCode (.inr (.inr (.inr o))) : Fin 24 → ZMod 2) 1) =
      sgn (((o.1 : C) : Fin 24 → ZMod 2) 0 + ((o.1 : C) : Fin 24 → ZMod 2) 1) := by
  rw [labelCode_oct, aOct_apply, aOct_apply]
  congr 1
  linear_combination nOct (octRep o.1 o.2) * two_eq_zero_zmod

theorem val_cast_zmod2 (x : ZMod 2) : ((x.val : ℤ) : ℚ) = if x = 0 then 0 else 1 := by
  have : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases this x with rfl | rfl <;> rfl

theorem ratVec_vOct (d : Fin 24 → ZMod 2) (δ : Finset (Fin 24)) (j : Fin 24) :
    ratVec (vOct d δ) j = 2 * (if d j = 0 then 0 else 1) - 4 * (if j ∈ δ then 1 else 0) := by
  rw [ratVec, vOct, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  push_cast
  rw [liftℤ, liftℤ, bitLift, bitLift, val_cast_zmod2, val_cast_zmod2, Octad.ind_apply]
  split_ifs <;> simp_all

theorem sum_sgn_linear_eq_zero {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Fintype E]
    (f : E →ₗ[ZMod 2] ZMod 2) {e₀ : E} (he : f e₀ ≠ 0) : ∑ e, sgn (f e) = 0 := by
  have h1 : f e₀ = 1 := by
    have : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
    exact this _ he
  have hshift : ∑ e, sgn (f e) = ∑ e, sgn (f (e + e₀)) :=
    (Fintype.sum_equiv (Equiv.addRight e₀) _ _ fun e => rfl).symm
  simp only [map_add, sgn_add, h1, show sgn (1 : ZMod 2) = -1 from rfl, mul_neg, mul_one,
    Finset.sum_neg_distrib] at hshift
  linarith

theorem card_inter_pair (δ : Finset (Fin 24)) {j k : Fin 24} (hjk : j ≠ k) :
    (δ ∩ {j, k}).card = (if j ∈ δ then 1 else 0) + (if k ∈ δ then 1 else 0) := by
  by_cases hj : j ∈ δ <;> by_cases hk : k ∈ δ
  · rw [Finset.inter_insert_of_mem hj, Finset.inter_singleton_of_mem hk,
      Finset.card_pair hjk, ite_eq_left hj, ite_eq_left hk]
  · rw [Finset.inter_insert_of_mem hj, Finset.inter_singleton_of_notMem hk,
      ite_eq_left hj, ite_eq_right hk]
    simp
  · rw [Finset.inter_insert_of_notMem hj, Finset.inter_singleton_of_mem hk,
      ite_eq_right hj, ite_eq_left hk]
    simp
  · rw [Finset.inter_insert_of_notMem hj, Finset.inter_singleton_of_notMem hk,
      ite_eq_right hj, ite_eq_right hk]
    simp

theorem cls_pair_ne_zero (d : OctadWord) {j k : Fin 24} (hj : j ∈ octSupp d) (hk : k ∈ octSupp d)
    (hjk : j ≠ k) : Octad.cls (octSupp d) {j, k} ≠ 0 := by
  have hsub : ({j, k} : Finset (Fin 24)) ⊆ octSupp d := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hj
    · exact hk
  have heven : Even ({j, k} : Finset (Fin 24)).card := by
    rw [Finset.card_pair hjk]
    decide
  rw [Octad.cls_eq hsub heven, Ne, Octad.mk_eq_zero_iff, Octad.mem_complSpan_iff]
  rintro (h | h)
  · have := congrFun h j
    simp [Octad.ind] at this
  · have hlt : ({j, k} : Finset (Fin 24)).card < (octSupp d).card := by
      rw [Finset.card_pair hjk, card_octSupp]
      norm_num
    obtain ⟨l, hl, hl'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have := congrFun h l
    simp only [Octad.ind_apply] at this
    rw [ite_eq_right hl', ite_eq_left hl] at this
    exact zero_ne_one this

theorem sum_outer_vOct (d : OctadWord) :
    ∑ q : Octad.EvenQuot (octSupp d), outerZ (vOct ((d : C) : Fin 24 → ZMod 2) (octRep d q)) =
      (256 : ℚ) • Matrix.diagonal (fun j => if j ∈ octSupp d then 1 else 0) := by
  ext j k
  rw [Matrix.sum_apply]
  simp only [outerZ_apply, ratVec_vOct, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  have hmem : ∀ i : Fin 24, i ∈ octSupp d ↔ ((d : C) : Fin 24 → ZMod 2) i ≠ 0 := fun i => by
    simp [octSupp, supp]
  have hsubset : ∀ q : Octad.EvenQuot (octSupp d), octRep d q ⊆ octSupp d :=
    fun q => (octRep_spec d q).1
  by_cases hj : j ∈ octSupp d
  · by_cases hk : k ∈ octSupp d
    · have hj' : ((d : C) : Fin 24 → ZMod 2) j ≠ 0 := (hmem j).1 hj
      have hk' : ((d : C) : Fin 24 → ZMod 2) k ≠ 0 := (hmem k).1 hk
      simp only [hj', hk', ite_false]
      by_cases hjk : j = k
      · subst hjk
        simp only [ite_true, hj, mul_one]
        have e : ∀ q : Octad.EvenQuot (octSupp d), (2 - 4 * (if j ∈ octRep d q then (1 : ℚ) else 0)) *
            (2 - 4 * if j ∈ octRep d q then 1 else 0) = 4 := by
          intro q
          split_ifs <;> norm_num
        rw [Finset.sum_congr rfl fun q _ => e q, Finset.sum_const, Finset.card_univ,
          Octad.card_evenQuot (card_octSupp d)]
        norm_num
      · simp only [hjk, ite_false, mul_zero]
        have h4 : 4 ∣ (octSupp d).card := by rw [card_octSupp]; norm_num
        have hsub : ({j, k} : Finset (Fin 24)) ⊆ octSupp d := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hj
          · exact hk
        have heven : Even ({j, k} : Finset (Fin 24)).card := by
          rw [Finset.card_pair hjk]
          decide
        set w := Octad.cls (octSupp d) {j, k} with hw
        have e : ∀ q : Octad.EvenQuot (octSupp d),
            (2 * 1 - 4 * (if j ∈ octRep d q then (1 : ℚ) else 0)) *
              (2 * 1 - 4 * if k ∈ octRep d q then 1 else 0) =
            4 * sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) w q) := by
          intro q
          obtain ⟨hq1, hq2, hq3⟩ := octRep_spec d q
          have hb := Octad.polarBilin_quadForm_cls h4 hsub heven hq1 hq2
          rw [hq3, Finset.inter_comm, card_inter_pair _ hjk] at hb
          rw [hb]
          split_ifs <;> (norm_num [sgn]; try rfl)
        rw [Finset.sum_congr rfl fun q _ => e q, ← Finset.mul_sum]
        have hne : ∃ e₀, QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) w e₀ ≠ 0 := by
          by_contra hall
          push Not at hall
          exact cls_pair_ne_zero d hj hk hjk
            (Octad.polarBilin_quadForm_separatingLeft h4 ⟨j, hj⟩ w hall)
        obtain ⟨e₀, he₀⟩ := hne
        rw [sum_sgn_linear_eq_zero (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) w) he₀,
          mul_zero]
    · have hk' : ((d : C) : Fin 24 → ZMod 2) k = 0 := by
        by_contra h
        exact hk ((hmem k).2 h)
      have e : ∀ q : Octad.EvenQuot (octSupp d), k ∉ octRep d q := fun q h => hk (hsubset q h)
      simp only [hk', e, ite_true, ite_false, mul_zero, sub_zero, Finset.sum_const_zero]
      split_ifs with h <;> simp_all
  · have hj' : ((d : C) : Fin 24 → ZMod 2) j = 0 := by
      by_contra h
      exact hj ((hmem j).2 h)
    have e : ∀ q : Octad.EvenQuot (octSupp d), j ∉ octRep d q := fun q h => hj (hsubset q h)
    simp only [hj', e, ite_true, ite_false, mul_zero, sub_zero, zero_mul, Finset.sum_const_zero]
    split_ifs <;> simp

theorem sum_octadWord (g : Finset (Fin 24) → ℚ) :
    ∑ d : OctadWord, g (octSupp d) = ∑ O ∈ octads, g O := by
  rw [octads, Finset.sum_image suppFin_injective.injOn]
  refine Finset.sum_bij (fun d _ => ((d : C) : Fin 24 → ZMod 2)) ?_ ?_ ?_ ?_
  · intro d _
    exact mem_octFin.2 ⟨d.1.2, d.2⟩
  · intro d _ d' _ h
    exact Subtype.ext (Subtype.ext h)
  · intro x hx
    obtain ⟨hC, hw⟩ := mem_octFin.1 hx
    exact ⟨⟨⟨x, hC⟩, hw⟩, Finset.mem_univ _, rfl⟩
  · intro d _
    rfl

@[expose] def octSign (O : Finset (Fin 24)) : ℚ :=
  (if (0 : Fin 24) ∈ O then -1 else 1) * (if (1 : Fin 24) ∈ O then -1 else 1)

theorem sgn_eq_octSign (d : OctadWord) :
    sgn (((d : C) : Fin 24 → ZMod 2) 0 + ((d : C) : Fin 24 → ZMod 2) 1) = octSign (octSupp d) := by
  have hmem : ∀ i : Fin 24, i ∈ octSupp d ↔ ((d : C) : Fin 24 → ZMod 2) i ≠ 0 := fun i => by
    simp [octSupp, supp]
  have h : ∀ i : Fin 24, sgn (((d : C) : Fin 24 → ZMod 2) i) = if i ∈ octSupp d then -1 else 1 := by
    intro i
    have : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases this (((d : C) : Fin 24 → ZMod 2) i) with h0 | h1
    · rw [h0, ite_eq_right (fun h => (hmem i).1 h h0)]
      rfl
    · rw [h1, ite_eq_left ((hmem i).2 (by rw [h1]; exact one_ne_zero))]
      rfl
  rw [sgn_add, h, h, octSign]

theorem sum_octSign (j : Fin 24) :
    ∑ O ∈ octads, (if j ∈ O then octSign O else 0) = if j = 0 ∨ j = 1 then -99 else 29 := by
  have e : ∀ O : Finset (Fin 24), (if j ∈ O then octSign O else 0) =
      (if {j} ⊆ O then (1 : ℚ) else 0) - 2 * (if {j, 0} ⊆ O then 1 else 0) -
        2 * (if {j, 1} ⊆ O then 1 else 0) + 4 * (if {j, 0, 1} ⊆ O then 1 else 0) := by
    intro O
    simp only [octSign, Finset.singleton_subset_iff, Finset.insert_subset_iff]
    by_cases hj : j ∈ O <;> by_cases h0 : (0 : Fin 24) ∈ O <;> by_cases h1 : (1 : Fin 24) ∈ O <;>
      simp [hj, h0, h1] <;> norm_num
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  obtain ⟨-, -, -, h1, h2, h3⟩ := octads_steiner_five_design
  by_cases hj0 : j = 0
  · subst hj0
    have e1 : ({0, 0} : Finset (Fin 24)) = {0} := by simp
    have e2 : ({0, 0, 1} : Finset (Fin 24)) = {0, 1} := by simp
    rw [e1, e2, h1 {0} (by simp), h2 {0, 1} (by decide)]
    norm_num
  · by_cases hj1 : j = 1
    · subst hj1
      have e1 : ({1, 1} : Finset (Fin 24)) = {1} := by simp
      have e2 : ({1, 0, 1} : Finset (Fin 24)) = {1, 0} := by
        ext x; simp; tauto
      rw [e1, e2, h1 {1} (by simp), h2 {1, 0} (by decide)]
      norm_num
    · rw [h1 {j} (by simp), h2 {j, 0} (Finset.card_pair hj0), h2 {j, 1} (Finset.card_pair hj1),
        h3 {j, 0, 1} (by
          rw [Finset.card_insert_of_notMem (by simp [hj0, hj1]), Finset.card_pair (by decide)])]
      rw [ite_eq_right (by tauto)]
      norm_num

theorem sum_oct_labels :
    ∑ o : OctIdx, sgn ((labelCode (.inr (.inr (.inr o))) : Fin 24 → ZMod 2) 0 +
        (labelCode (.inr (.inr (.inr o))) : Fin 24 → ZMod 2) 1) •
        outerZ (labelVec (.inr (.inr (.inr o)))) =
      Matrix.diagonal (fun j => if j = 0 ∨ j = 1 then (-25344 : ℚ) else 7424) := by
  simp only [sgn_labelCode_oct]
  rw [Fintype.sum_sigma]
  change ∑ d : OctadWord, ∑ q : Octad.EvenQuot (octSupp d),
      sgn (((d : C) : Fin 24 → ZMod 2) 0 + ((d : C) : Fin 24 → ZMod 2) 1) •
        outerZ (vOct ((d : C) : Fin 24 → ZMod 2) (octRep d q)) = _
  simp only [← Finset.smul_sum, sum_outer_vOct, sgn_eq_octSign]
  ext j k
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hjk : j = k
  · subst hjk
    simp only [ite_true]
    have e : ∀ d : OctadWord, octSign (octSupp d) * (256 * if j ∈ octSupp d then 1 else 0) =
        256 * (if j ∈ octSupp d then octSign (octSupp d) else 0) := by
      intro d
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun d _ => e d, ← Finset.mul_sum,
      sum_octadWord (fun O => if j ∈ O then octSign O else 0), sum_octSign]
    split_ifs <;> norm_num
  · simp [hjk]

theorem outerZ_vMinus_zero_one :
    outerZ (vMinus 0 1) = (16 : ℚ) • (Matrix.single 0 0 1 + Matrix.single 1 1 1 -
      Matrix.single 0 1 1 - Matrix.single 1 0 1) := by
  have hm : ratVec (vMinus 0 1) = (4 : ℚ) • Pi.single 0 1 - (4 : ℚ) • Pi.single 1 1 := by
    funext k
    simp only [ratVec, vMinus, eℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> norm_num
  rw [outerZ, hm]
  simp only [vecMulVec_sub, sub_vecMulVec, smul_vecMulVec, vecMulVec_smul,
    vecMulVec_single_single, mul_one]
  module

theorem Umat_cStar : Umat (shortCls hrStar) = outerZ (vMinus 0 1) :=
  Umat_labelIdx (.inl ⟨(0, 1), by decide⟩)

theorem signedU_rStar :
    signedU hrStar = (8160 : ℚ) • 1 - (2048 : ℚ) • Umat (shortCls hrStar) := by
  rw [signedU_eq_sum_labels, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← add_assoc, sum_pair_labels, sum_odd_labels, sum_oct_labels, Umat_cStar,
    outerZ_vMinus_zero_one]
  ext j k
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply,
    Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul, eq_comm (a := (0 : Fin 24)) (b := j),
    eq_comm (a := (1 : Fin 24)) (b := j), eq_comm (a := (0 : Fin 24)) (b := k),
    eq_comm (a := (1 : Fin 24)) (b := k)]
  by_cases hj0 : j = 0 <;> by_cases hj1 : j = 1 <;> by_cases hk0 : k = 0 <;>
    by_cases hk1 : k = 1 <;> by_cases hjk : j = k <;> simp_all <;> norm_num

end CFSG.Monster.B
