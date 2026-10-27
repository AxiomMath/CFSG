module

public import CFSG.Monster.Schur.H1Nvis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.VisCert
  CFSG.Monster.Visible

@[expose] def xorTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => xorTo f n ^^^ f n

@[expose] def fixMask (g c : ℕ) : ℕ :=
  xorTo (fun i => if (frameMatrices[g]!)[i]!.testBit c ^^ (i == c) then 1 <<< i else 0) 24

@[expose] def fixEqs : List ℕ :=
  (List.range 14).flatMap fun j => (List.range 24).map fun c => fixMask (j + 1) c

@[expose] def fixCertOK : Bool :=
  (List.range 24).all fun i =>
    i == 0 || (xorSelL fixEqs (fixSel.getD i 0) == (1 <<< i) ^^^ (if i < 6 then 1 else 0))

theorem fixCertOK_eq_true : fixCertOK = true := by decide +kernel


theorem bitZ_xorTo (f : ℕ → ℕ) (i : ℕ) :
    ∀ n, bitZ (xorTo f n) i = ∑ t ∈ Finset.range n, bitZ (f t) i
  | 0 => by simp [xorTo, bitZ_zero]
  | n + 1 => by rw [xorTo, bitZ_xor, bitZ_xorTo f i n, Finset.sum_range_succ]

theorem bitZ_fixMask {g c i : ℕ} (hi : i < 24) :
    bitZ (fixMask g c) i = bitZ ((frameMatrices[g]!)[i]!) c + (if i = c then 1 else 0) := by
  rw [fixMask, bitZ_xorTo]
  have h1 : ∀ t ∈ Finset.range 24, bitZ (if (frameMatrices[g]!)[t]!.testBit c ^^ (t == c)
      then 1 <<< t else 0) i = if t = i then
        (if (frameMatrices[g]!)[t]!.testBit c ^^ (t == c) then 1 else 0) else 0 := by
    intro t _
    by_cases hc : ((frameMatrices[g]!)[t]!.testBit c ^^ (t == c)) = true
    · simp [hc, bitZ_pow, eq_comm]
    · simp [hc, bitZ_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Finset.range 24) i]
  simp only [Finset.mem_range, hi, ↓reduceIte]
  unfold bitZ
  generalize (frameMatrices[g]!)[i]!.testBit c = b
  by_cases h3 : i = c
  · cases b
    · simp [h3]
    · subst h3
      simp
      decide
  · cases b <;> simp [h3]


noncomputable def coordVec (v : L2) (i : ℕ) : ZMod 2 :=
  if h : i < 24 then ellBasis.repr v ⟨i, h⟩ else 0

theorem repr_dec (x : ℕ) (c : Fin 24) : ellBasis.repr (dec x) c = bitZ x c := by
  rw [dec_eq_ellBasis, Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self]
  rfl

theorem repr_apply_eq (T : L2 →ₗ[ZMod 2] L2) (v : L2) (c : Fin 24) :
    ellBasis.repr (T v) c = ∑ i : Fin 24, ellBasis.repr v i * ellBasis.repr (T (ellCls i)) c := by
  conv_lhs => rw [← ellBasis.sum_repr v]
  simp [map_sum, map_smul, ellBasis_apply]

theorem fix_equation (v : L2) {g : ℕ} (hg1 : 1 ≤ g) (hg : g ≤ 14) (hv : kGenN g • v = v)
    (c : ℕ) (hc : c < 24) : maskDot 24 (coordVec v) (fixMask g c) = 0 := by
  have h1 : ellBasis.repr (((kGenN g : GLV) : L2 →ₗ[ZMod 2] L2) v) ⟨c, hc⟩ =
      ellBasis.repr v ⟨c, hc⟩ := congrArg (fun w => ellBasis.repr w ⟨c, hc⟩) hv
  rw [repr_apply_eq] at h1
  have h2 : ∀ i : Fin 24, ellBasis.repr (((kGenN g : GLV) : L2 →ₗ[ZMod 2] L2) (ellCls i))
      ⟨c, hc⟩ = bitZ ((frameMatrices[g]!)[(i : ℕ)]!) c := by
    intro i
    have : ((kGenN g : GLV) : L2 →ₗ[ZMod 2] L2) (ellCls i) =
        dec ((frameMatrices[g]!)[(i : ℕ)]!) := by
      rw [kGenN_eq (by omega)]
      exact kGen_smul_ellCls ⟨g, by omega⟩ i
    rw [this, repr_dec]
  simp only [h2] at h1
  unfold maskDot
  rw [← Fin.sum_univ_eq_sum_range (fun s => coordVec v s * bitZ (fixMask g c) s) 24]
  have h3 : ∀ i : Fin 24, coordVec v i * bitZ (fixMask g c) i =
      ellBasis.repr v i * bitZ ((frameMatrices[g]!)[(i : ℕ)]!) c +
        ellBasis.repr v i * (if (i : ℕ) = c then 1 else 0) := by
    intro i
    rw [bitZ_fixMask i.2, mul_add]
    simp only [coordVec, i.2, ↓reduceDIte, Fin.eta]
  rw [Finset.sum_congr rfl fun i _ => h3 i, Finset.sum_add_distrib, h1]
  have h4 : ∑ i : Fin 24, ellBasis.repr v i * (if (i : ℕ) = c then 1 else 0) =
      ellBasis.repr v ⟨c, hc⟩ := by
    rw [Finset.sum_eq_single ⟨c, hc⟩]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ c := fun h => hi (Fin.ext h)
      simp [this]
    · simp
  rw [h4]
  exact CharTwo.add_self_eq_zero _


theorem bvec_63 : ∀ i : Fin 24, bvec 24 63 i = if (i : ℕ) < 6 then 1 else 0 := by decide

theorem fixed_Nvis_L2 (v : L2) (hv : ∀ g ∈ Nvis, (g : GLV) • v = v) : v = 0 ∨ v = twoΩCls := by
  have hfix : ∀ g : ℕ, 1 ≤ g → g ≤ 14 → kGenN g • v = v := fun g h1 h2 =>
    hv _ (kGenN_mem_Nvis h1 (by omega))
  have hzero : ∀ t ∈ fixEqs, maskDot 24 (coordVec v) t = 0 := by
    intro t ht
    obtain ⟨j, hj, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ht
    exact fix_equation v (by omega) (by have := List.mem_range.1 hj; omega)
      (hfix _ (by omega) (by have := List.mem_range.1 hj; omega)) c (List.mem_range.1 hc)
  have hcoord : ∀ i : ℕ, 1 ≤ i → i < 24 →
      coordVec v i = if i < 6 then coordVec v 0 else 0 := by
    intro i hi1 hi
    have h := fixCertOK_eq_true
    simp only [fixCertOK, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    have h2 := (h i (List.mem_range.2 hi)).resolve_left (by omega)
    have h3 := congrArg (maskDot 24 (coordVec v)) h2
    rw [maskDot_xorSelL, selSum_eq_zero (fun w hw => ?_), maskDot_xor, maskDot_pow hi] at h3
    · have h4 : maskDot 24 (coordVec v) (if i < 6 then 1 else 0) =
          if i < 6 then coordVec v 0 else 0 := by
        by_cases h5 : i < 6
        · simp only [h5, ↓reduceIte]
          rw [show (1 : ℕ) = 1 <<< 0 from rfl, maskDot_pow (by norm_num)]
        · simp [h5, maskDot_zero]
      rw [h4] at h3
      rw [eq_neg_of_add_eq_zero_left h3.symm, ZMod.neg_eq_self_mod_two]
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hw
      exact hzero t ht
  have hv_eq : v = coordVec v 0 • dec 63 := by
    refine ellBasis.ext_elem fun i => ?_
    rw [map_smul, Finsupp.smul_apply, repr_dec, smul_eq_mul]
    have h63 : bitZ 63 i = if (i : ℕ) < 6 then 1 else 0 := bvec_63 i
    rw [h63]
    by_cases h0 : (i : ℕ) = 0
    · have : coordVec v i = ellBasis.repr v i := by
        simp [coordVec, i.2, Fin.eta]
      rw [← this, h0]
      simp
    · have h1 := hcoord i (by omega) i.2
      have : coordVec v i = ellBasis.repr v i := by
        simp [coordVec, i.2, Fin.eta]
      rw [← this, h1]
      split_ifs <;> simp
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (coordVec v 0) with h | h
  · left
    rw [hv_eq, h, zero_smul]
  · right
    rw [hv_eq, h, one_smul, dec_seed]

end CFSG.Monster.Schur
