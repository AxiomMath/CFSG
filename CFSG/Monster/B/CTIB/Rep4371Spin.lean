module

public import CFSG.Monster.B.CTIB.Rep4371Lines

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.SpinLattice CFSG.Monster.Spin CFSG.Monster.ScalarKernel CFSG.Monster.B
  CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371 Matrix
open CFSG.Monster.B.Co2 (v0)

abbrev IsPlus (i : SpinIdx) : Prop :=
  ((i.2 : C) : Fin 24 → ZMod 2) 0 = ((i.2 : C) : Fin 24 → ZMod 2) 1

@[expose] noncomputable def spinIdx (t : Fin 2048) : SpinIdx :=
  (if 1024 ≤ (t : ℕ) then 1 else 0, oddC ((t : ℕ) % 1024))

@[expose] def tIdx (t : Fin 2048) : Fin 4371 := ⟨2323 + t, by omega⟩

theorem tIdx_injective : Function.Injective tIdx := fun t t' h =>
  Fin.ext (by have := congrArg Fin.val h; simp only [tIdx] at this; omega)

theorem coe_Rbasis_tIdx (t : Fin 2048) :
    (Rbasis (tIdx t) : SpaceB) = rawSpin (spinIdx t).1 (spinIdx t).2 := by
  rw [coe_Rbasis, show ((tIdx t : Fin 4371) : ℕ) = 2323 + t from rfl, Rraw_spin_eq (by omega),
    show (2323 + (t : ℕ) - 2323) % 1024 = (t : ℕ) % 1024 by omega]
  congr 1
  by_cases h : 1024 ≤ (t : ℕ)
  · rw [ite_eq_left (by omega : 3347 ≤ 2323 + (t : ℕ)), spinIdx, ite_eq_left h]
  · rw [ite_eq_right (by omega : ¬ 3347 ≤ 2323 + (t : ℕ)), spinIdx, ite_eq_right h]

theorem isPlus_spinIdx (t : Fin 2048) : IsPlus (spinIdx t) :=
  oddC_bits _ (Nat.mod_lt _ (by norm_num))

theorem spinIdx_injective : Function.Injective spinIdx := by
  intro t t' h
  have h1 := congrArg Prod.fst h
  have h2 := oddC_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (congrArg Prod.snd h)
  simp only [spinIdx] at h1
  apply Fin.ext
  have ht := t.2
  have ht' := t'.2
  by_cases a : 1024 ≤ (t : ℕ) <;> by_cases b : 1024 ≤ (t' : ℕ)
  · omega
  · rw [ite_eq_left a, ite_eq_right b] at h1; exact absurd h1 (by decide)
  · rw [ite_eq_right a, ite_eq_left b] at h1; exact absurd h1 (by decide)
  · omega

theorem exists_spinIdx {i : SpinIdx} (hi : IsPlus i) : ∃ t, spinIdx t = i := by
  obtain ⟨t₀, ht₀, hc⟩ := exists_oddC i.2 hi
  rcases zmod2_cases i.1 with h | h
  · refine ⟨⟨t₀, by omega⟩, Prod.ext ?_ ?_⟩
    · show (if 1024 ≤ t₀ then (1 : ZMod 2) else 0) = i.1
      rw [ite_eq_right (by omega), h]
    · show oddC (t₀ % 1024) = i.2
      rw [Nat.mod_eq_of_lt ht₀, hc]
  · refine ⟨⟨1024 + t₀, by omega⟩, Prod.ext ?_ ?_⟩
    · show (if 1024 ≤ 1024 + t₀ then (1 : ZMod 2) else 0) = i.1
      rw [ite_eq_left (by omega), h]
    · show oddC ((1024 + t₀) % 1024) = i.2
      rw [show (1024 + t₀) % 1024 = t₀ by omega, hc]

abbrev Rq (q : Q) : Matrix SpinIdx SpinIdx ℚ := ((q : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)

@[expose] noncomputable def qPi (q : Q) : SpinIdx → SpinIdx :=
  qPerm (spinEquiv.symm q).a (spinEquiv.symm q).δ

@[expose] noncomputable def qSg (q : Q) (i : SpinIdx) : ℚ :=
  sgnR ℚ (qSign (spinEquiv.symm q).s (spinEquiv.symm q).a (spinEquiv.symm q).δ i)

theorem Rq_eq (q : Q) :
    Rq q = qmatR ℚ (spinEquiv.symm q).s (spinEquiv.symm q).a (spinEquiv.symm q).δ := by
  conv_lhs => rw [← spinEquiv.apply_symm_apply q]
  rfl

theorem Rq_apply (q : Q) (i j : SpinIdx) : Rq q i j = if j = qPi q i then qSg q i else 0 := by
  rw [Rq_eq, qmatR_apply]
  rfl

theorem single_vecMul_Rq (q : Q) (i : SpinIdx) :
    Pi.single i 1 ᵥ* Rq q = qSg q i • Pi.single (qPi q i) 1 := by
  rw [single_one_vecMul]
  funext j
  rw [Matrix.row_apply, Rq_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

theorem qSg_ne_zero (q : Q) (i : SpinIdx) : qSg q i ≠ 0 := by
  rw [qSg, sgnR]
  split_ifs <;> norm_num

theorem isPlus_qPi {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) {i : SpinIdx}
    (hi : IsPlus i) : IsPlus (qPi q i) := by
  have hc : Rq q * Rq rStar = Rq rStar * Rq q := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 hq
    have h' := congrArg (fun g : Q => ((g : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ)) h
    simp only [Subgroup.coe_mul, Units.val_mul] at h'
    exact h'
  have h1 := congrFun (congrArg (fun M => M i) hc) (qPi q i)
  rw [Matrix.mul_apply, Matrix.mul_apply] at h1
  simp_rw [rStar_mat_apply] at h1
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h1
  rw [Rq_apply, ite_eq_left rfl] at h1
  have hs := qSg_ne_zero q i
  have hsgn : sgn ((((qPi q i).2 : C) : Fin 24 → ZMod 2) 0 +
      (((qPi q i).2 : C) : Fin 24 → ZMod 2) 1) =
      sgn (((i.2 : C) : Fin 24 → ZMod 2) 0 + ((i.2 : C) : Fin 24 → ZMod 2) 1) := by
    have := mul_left_cancel₀ hs (h1.trans (mul_comm _ _))
    exact this
  rw [show ((i.2 : C) : Fin 24 → ZMod 2) 0 + ((i.2 : C) : Fin 24 → ZMod 2) 1 = 0 by
    rw [hi, ZModModule.add_self]] at hsgn
  have h0 := sgn_zmod_injective (hsgn.trans sgn_zero.symm)
  show (((qPi q i).2 : C) : Fin 24 → ZMod 2) 0 = (((qPi q i).2 : C) : Fin 24 → ZMod 2) 1
  rw [← sub_eq_zero, sub_eq_add_neg, ZModModule.neg_eq_self]
  exact h0

theorem E_eq_single (i : SpinIdx) : E i.1 i.2 = Pi.single i 1 := rfl

theorem theta_rhoPair_rawSpin (q : Q) (i : SpinIdx) :
    theta (rhoPair q) (rawSpin i.1 i.2) = qSg q i • rawSpin (qPi q i).1 (qPi q i).2 := by
  have h1 : theta (rhoPair q) (0, 0, tensor (E i.1 i.2) wvec) =
      (0, 0, tensor (E i.1 i.2 ᵥ* Rq q) (wvec ᵥ* mat 1)) := theta_tensor (rhoPair q) _ _
  have h2 : E i.1 i.2 ᵥ* Rq q = qSg q i • E (qPi q i).1 (qPi q i).2 := by
    rw [E_eq_single, single_vecMul_Rq, E_eq_single]
  rw [mat_one, vecMul_one, h2, tensor_smul_left] at h1
  show theta (rhoPair q) (0, 0, tensor (E i.1 i.2) wvec) =
    qSg q i • ((0, 0, tensor (E (qPi q i).1 (qPi q i).2) wvec) : SpaceB)
  rw [h1]
  refine Prod.ext (by simp) (Prod.ext (by simp) rfl)

@[expose] noncomputable def shatQ (q : Q) (hq : q ∈ Subgroup.centralizer {rStar}) : Shat :=
  cbarEquiv (kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩)

theorem shatQ_mem_Ehat {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) :
    (shatQ q hq : Dfull) ∈ Ehat :=
  ⟨_, kappa_rho_mem_Ebar hq, rfl⟩

theorem rhoV_shatQ_spin
    {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) {t t' : Fin 2048}
    (ht' : spinIdx t' = qPi q (spinIdx t)) :
    rhoV (shatQ q hq) (Rbasis (tIdx t)) = qSg q (spinIdx t) • Rbasis (tIdx t') := by
  apply Subtype.ext
  rw [shatQ, rhoV_kappa_apply, Submodule.coe_smul, coe_Rbasis_tIdx, coe_Rbasis_tIdx, ht']
  exact theta_rhoPair_rawSpin q (spinIdx t)

@[expose] noncomputable def blkM
    (h : Shat) : Matrix (Fin 2048) (Fin 2048) ℚ :=
  fun s t => Rbasis.repr (rhoV h (Rbasis (tIdx t))) (tIdx s)

theorem blkM_shatQ
    {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) (s t : Fin 2048) :
    blkM (shatQ q hq) s t = Rq q (spinIdx t) (spinIdx s) := by
  obtain ⟨t', ht'⟩ := exists_spinIdx (isPlus_qPi hq (isPlus_spinIdx t))
  rw [blkM, rhoV_shatQ_spin hq ht', repr_smul, Module.Basis.repr_self, Finsupp.single_apply,
    Rq_apply]
  by_cases h : s = t'
  · subst h
    rw [ite_eq_left rfl, mul_one, ite_eq_left ht']
  · rw [ite_eq_right (fun h' => h (tIdx_injective h').symm), mul_zero,
      ite_eq_right (fun h' => h (spinIdx_injective (h'.trans ht'.symm)))]

theorem Rr_apply (i j : SpinIdx) : Rq rStar i j =
    if i = j then sgn (((i.2 : C) : Fin 24 → ZMod 2) 0 + ((i.2 : C) : Fin 24 → ZMod 2) 1)
    else 0 := rStar_mat_apply i j

theorem sum_spinIdx (f : SpinIdx → ℚ) :
    ∑ t : Fin 2048, f (spinIdx t) = ∑ i, if IsPlus i then f i else 0 := by
  rw [← Finset.sum_filter]
  have hmap : (Finset.univ : Finset (Fin 2048)).map ⟨spinIdx, spinIdx_injective⟩ =
      Finset.univ.filter IsPlus := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      exact isPlus_spinIdx t
    · exact exists_spinIdx
  rw [← hmap, Finset.sum_map]
  rfl

theorem trace_blkM_shatQ
    {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) :
    Matrix.trace (blkM (shatQ q hq)) =
      (Matrix.trace (Rq q) + Matrix.trace (Rq q * Rq rStar)) / 2 := by
  have h1 : Matrix.trace (blkM (shatQ q hq)) = ∑ t : Fin 2048, Rq q (spinIdx t) (spinIdx t) := by
    rw [Matrix.trace]
    exact Finset.sum_congr rfl fun t _ => blkM_shatQ hq t t
  have h2 : Matrix.trace (Rq q * Rq rStar) = ∑ i, Rq q i i *
      sgn (((i.2 : C) : Fin 24 → ZMod 2) 0 + ((i.2 : C) : Fin 24 → ZMod 2) 1) := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    simp_rw [Rr_apply, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ _)]
  rw [h1, sum_spinIdx (fun i => Rq q i i), h2, Matrix.trace, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply]
  by_cases hi : IsPlus i
  · rw [ite_eq_left hi, show ((i.2 : C) : Fin 24 → ZMod 2) 0 + ((i.2 : C) : Fin 24 → ZMod 2) 1 = 0
      by rw [hi, ZModModule.add_self], sgn_zero]
    ring
  · rw [ite_eq_right hi, show ((i.2 : C) : Fin 24 → ZMod 2) 0 + ((i.2 : C) : Fin 24 → ZMod 2) 1 = 1
      by
        have h2 : ∀ x y : ZMod 2, x ≠ y → x + y = 1 := by decide
        exact h2 _ _ hi]
    simp [sgn]

theorem trace_Rq (q : Q) :
    Matrix.trace (Rq q) = if coordOf q = 0 then sgn (centralCoord q) * 4096 else 0 := by
  rw [Rq_eq, trace_qmatR two_ne_zero]
  have e : ((spinEquiv.symm q).a = 0 ∧ (spinEquiv.symm q).δ = 0) ↔ coordOf q = 0 := by
    rw [coordOf, Prod.mk_eq_zero]
  by_cases h : coordOf q = 0
  · rw [ite_eq_left (e.2 h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (fun h' => h (e.1 h')), ite_eq_right h]

theorem Rq_mul (q q' : Q) : Rq q * Rq q' = Rq (q * q') := by
  rw [Rq, Rq, Rq, Subgroup.coe_mul, Units.val_mul]

theorem trace_blkM_shatQ_eq_zero
    {q : Q} (hq : q ∈ Subgroup.centralizer {rStar})
    (h1 : coordOf q ≠ 0) (h2 : coordOf q ≠ coordOf rStar) :
    Matrix.trace (blkM (shatQ q hq)) = 0 := by
  have h2' : coordOf (q * rStar) ≠ 0 := by
    rw [coordOf_mul]
    intro h
    apply h2
    rw [← sub_eq_zero, sub_eq_add_neg, ZModModule.neg_eq_self]
    exact h
  rw [trace_blkM_shatQ, Rq_mul, trace_Rq, trace_Rq, ite_eq_right h1, ite_eq_right h2', add_zero,
    zero_div]

theorem Tplus_span_Vst
    {v : Vst} (hv : (v : SpaceB) ∈ Tplus isShortCoord_rStar) :
    v ∈ Submodule.span ℚ (Set.range fun t => Rbasis (tIdx t)) := by
  rw [Tplus_eq_span] at hv
  have hmap : Submodule.span ℚ (Set.range fun t : Fin 2048 => Rraw (2323 + t)) =
      (Submodule.span ℚ (Set.range fun t => Rbasis (tIdx t))).map Vst.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, Submodule.subtype_apply]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [coe_Rbasis]; rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [coe_Rbasis]; rfl⟩
  rw [hmap] at hv
  obtain ⟨w, hw, hwv⟩ := hv
  rw [← Subtype.ext hwv]
  exact hw

theorem Rbasis_tIdx_mem
    (t : Fin 2048) : (Rbasis (tIdx t) : SpaceB) ∈ Tplus isShortCoord_rStar := by
  rw [coe_Rbasis]
  exact Rraw_mem_Tplus (by simp [tIdx])

theorem repr_rhoV_blk_span
    (h : Shat) {v : Vst}
    (hv : v ∈ Submodule.span ℚ (Set.range fun t => Rbasis (tIdx t))) (s : Fin 2048) :
    Rbasis.repr (rhoV h v) (tIdx s) = ∑ u, blkM h s u * Rbasis.repr v (tIdx u) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    simp_rw [Module.Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single t (fun u _ hu => by
      rw [ite_eq_right (fun h' => hu (tIdx_injective h').symm), mul_zero])
      (fun h' => absurd (Finset.mem_univ t) h'), ite_eq_left rfl, mul_one]
    rfl
  | zero =>
    rw [map_zero (rhoV h), repr_zero']
    exact (Finset.sum_eq_zero fun u _ => by rw [repr_zero', mul_zero]).symm
  | add x y _ _ hx hy =>
    rw [map_add (rhoV h) x y, repr_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [repr_add, mul_add]
  | smul c x _ hx =>
    rw [map_smul (rhoV h) c x, repr_smul, hx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [repr_smul]; ring

theorem repr_rhoV_blk
    (h : Shat) {v : Vst} (hv : (v : SpaceB) ∈ Tplus isShortCoord_rStar)
    (s : Fin 2048) :
    Rbasis.repr (rhoV h v) (tIdx s) = ∑ u, blkM h s u * Rbasis.repr v (tIdx u) :=
  repr_rhoV_blk_span h (Tplus_span_Vst hv) s

theorem blkM_mul (h h' : Shat)
    (hh' : ∀ v : Vst, (v : SpaceB) ∈ Tplus isShortCoord_rStar →
      (rhoV h' v : SpaceB) ∈ Tplus isShortCoord_rStar) :
    blkM (h * h') = blkM h * blkM h' := by
  ext s t
  rw [Matrix.mul_apply, blkM, map_mul, LinearEquiv.mul_apply,
    repr_rhoV_blk h (hh' _ (Rbasis_tIdx_mem t))]
  rfl

theorem blkM_one : blkM 1 = 1 := by
  ext s t
  rw [blkM, map_one, LinearEquiv.coe_one, id_eq, Module.Basis.repr_self, Finsupp.single_apply,
    Matrix.one_apply]
  by_cases h : t = s
  · rw [ite_eq_left (congrArg tIdx h), ite_eq_left h.symm]
  · rw [ite_eq_right (fun h' => h (tIdx_injective h')), ite_eq_right (fun h' => h h'.symm)]

end CFSG.Monster.B.CTIB
