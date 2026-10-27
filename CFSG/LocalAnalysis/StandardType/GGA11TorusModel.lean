module

public import CFSG.LocalAnalysis.StandardType.GGA11FrameDefs
public import CFSG.LocalAnalysis.StandardType.GGA11GraphAut

public section

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.A8Coord Matrix
open Module

namespace CFSG.StandardType.A11

noncomputable section

private def a11tm_good (u : (GaloisField 2 3)ˣ) : Prop :=
  (u : GaloisField 2 3) ^ 3 = (u : GaloisField 2 3) + 1

private def a11tm_e2 : F2 ≃+* ZMod 2 := (GaloisField.equivZmodP (p := 2)).toRingEquiv

private theorem a11tm_two : (2 : GaloisField 2 3) = 0 := CharP.cast_eq_zero _ _

private theorem a11tm_three : (3 : GaloisField 2 3) = 1 := by
  rw [show (3 : GaloisField 2 3) = 2 + 1 by norm_num, a11tm_two, zero_add]

private theorem a11tm_good_or : a11tm_good ggSL9Zeta ∨ a11tm_good ggSL9Zeta⁻¹ := by
  let x : GaloisField 2 3 := ggSL9Zeta
  have h7 : x ^ 7 = 1 := by
    have h := ggSL9_units_pow_seven ggSL9Zeta
    have := congrArg (fun w : (GaloisField 2 3)ˣ => (w : GaloisField 2 3)) h
    simpa [x, Units.val_pow_eq_pow_val] using this
  have hne : x ≠ 1 := by
    intro h1
    have hord : orderOf ggSL9Zeta = 1 := orderOf_eq_one_iff.mpr (Units.ext (by simpa [x] using h1))
    rw [orderOf_ggSL9Zeta] at hord
    omega
  have hsum : x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 = 0 := by
    have hmul : (x + 1) * (x^6 + x^5 + x^4 + x^3 + x^2 + x + 1) = 0 := by
      have hexp : (x + 1) * (x^6 + x^5 + x^4 + x^3 + x^2 + x + 1) = x^7 + 1 := by
        ring_nf
        simp only [a11tm_two, a11tm_three, mul_zero, mul_one, add_zero, zero_add]
      rw [hexp, h7]
      exact CharTwo.add_self_eq_zero 1
    exact (mul_eq_zero.mp hmul).resolve_left (by
      intro hc
      have hneg : (-1 : GaloisField 2 3) = 1 := by
        rw [neg_eq_iff_add_eq_zero]; exact CharTwo.add_self_eq_zero 1
      have : x = -1 := eq_neg_of_add_eq_zero_left hc
      rw [hneg] at this
      exact hne this)
  have hprod : (x^3 + x + 1) * (x^3 + x^2 + 1) = 0 := by
    have hp : (x^3 + x + 1) * (x^3 + x^2 + 1) = x^6 + x^5 + x^4 + x^3 + x^2 + x + 1 := by
      ring_nf
      simp only [a11tm_two, a11tm_three, mul_zero, mul_one, add_zero, zero_add]
    rw [hp, hsum]
  rcases mul_eq_zero.mp hprod with h | h
  · left
    rw [a11tm_good]
    show x ^ 3 = x + 1
    linear_combination h - CharTwo.add_self_eq_zero (x + 1)
  · right
    rw [a11tm_good]
    show ((ggSL9Zeta⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3) ^ 3 =
      ((ggSL9Zeta⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3) + 1
    have hval : ((ggSL9Zeta⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3) = x⁻¹ := by
      rw [Units.val_inv_eq_inv_val]
    rw [hval]
    have hx : x^3 = x^2 + 1 := by
      linear_combination h - CharTwo.add_self_eq_zero (x^2 + 1)
    have hxne : x ≠ 0 := by
      intro h0; rw [h0] at hx; simp at hx
    field_simp
    ring_nf
    rw [hx, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem a11tm_zpowers_eq_top (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) :
    Subgroup.zpowers u = ⊤ := by
  have h7 : u ^ 7 = 1 := ggSL9_units_pow_seven u
  have hne : u ≠ 1 := by
    intro h1
    have h2 : (u : GaloisField 2 3) ^ 3 = (u : GaloisField 2 3) + 1 := h
    rw [h1] at h2
    simp only [Units.val_one, one_pow] at h2
    rw [CharTwo.add_self_eq_zero] at h2
    exact one_ne_zero h2
  have hdvd : orderOf u ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr h7
  have hord : orderOf u = 7 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_seven _ hdvd with h1 | h7'
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h7'
  exact Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, card_units_ggSL9])

private theorem a11tm_adjoin_eq_top (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) :
    Algebra.adjoin (ZMod 2) ({(u : GaloisField 2 3)} : Set (GaloisField 2 3)) = ⊤ := by
  haveI : Algebra.IsAlgebraic (ZMod 2) (GaloisField 2 3) := Algebra.IsAlgebraic.of_finite _ _
  rw [← IntermediateField.adjoin_eq_top_iff]
  apply IntermediateField.ext
  intro y
  constructor
  · intro _; trivial
  · intro _
    by_cases hy : y = 0
    · rw [hy]; exact (IntermediateField.adjoin (ZMod 2) _).zero_mem
    · let uy : (GaloisField 2 3)ˣ := Units.mk0 y hy
      have hu : uy ∈ Subgroup.zpowers u := by
        rw [a11tm_zpowers_eq_top u h]; exact Subgroup.mem_top uy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu
      have hyu : y = (u : GaloisField 2 3) ^ n := by
        have hcoe := congrArg (fun w : (GaloisField 2 3)ˣ => (w : GaloisField 2 3)) hn
        rw [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hcoe
        exact hcoe.symm
      rw [hyu]
      exact (IntermediateField.adjoin (ZMod 2) _).pow_mem
        (IntermediateField.subset_adjoin (ZMod 2) _ (by simp)) n

private noncomputable def a11tm_pb (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) :
    PowerBasis (ZMod 2) (GaloisField 2 3) :=
  PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite (ZMod 2) (u : GaloisField 2 3))
    (a11tm_adjoin_eq_top u h)

private theorem a11tm_pb_dim (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) :
    (a11tm_pb u h).dim = 3 := by
  have h1 := (a11tm_pb u h).finrank
  rw [GaloisField.finrank 2 (by norm_num : (3 : ℕ) ≠ 0)] at h1
  exact h1.symm

private noncomputable def a11tm_bF (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) :
    Basis (Fin 3) (ZMod 2) (GaloisField 2 3) :=
  (a11tm_pb u h).basis.reindex (finCongr (a11tm_pb_dim u h))

private theorem a11tm_bF_apply (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (i : Fin 3) :
    a11tm_bF u h i = (u : GaloisField 2 3) ^ (i : ℕ) := by
  rw [a11tm_bF, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp only [a11tm_pb, PowerBasis.ofAdjoinEqTop_gen]
  congr 1 <;> simp [finCongr]


private def a11tm_blk3 (p : Fin 9) : Fin 3 :=
  ⟨(blk (Fin.castLE (by omega) p)).val, by fin_cases p <;> decide⟩

private def a11tm_idx3 (p : Fin 9) : Fin 3 := idxIn (Fin.castLE (by omega) p)

private noncomputable def a11tm_e9 : Fin 9 ≃ Fin 3 × Fin 3 :=
  Equiv.ofBijective (fun p => (a11tm_blk3 p, a11tm_idx3 p)) (by decide)

private noncomputable def a11tm_bV (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) :
    Basis (Fin 9) (ZMod 2) GGSL9V :=
  ((Pi.basis (fun _ : Fin 3 => a11tm_bF u h)).reindex
    (Equiv.sigmaEquivProd (Fin 3) (Fin 3))).reindex a11tm_e9.symm

private theorem a11tm_bV_repr (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (x : GGSL9V)
    (p : Fin 9) :
    (a11tm_bV u h).repr x p =
      (a11tm_bF u h).repr (x (a11tm_blk3 p)) (a11tm_idx3 p) := by
  rw [a11tm_bV, Basis.repr_reindex_apply, Equiv.symm_symm]
  simp only [a11tm_e9, Equiv.ofBijective_apply]
  rw [Basis.repr_reindex_apply, Pi.basis_repr]
  rfl

private theorem a11tm_bV_apply (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (p : Fin 9) :
    a11tm_bV u h p = Pi.single (a11tm_blk3 p) (a11tm_bF u h (a11tm_idx3 p)) := by
  rw [a11tm_bV, Basis.reindex_apply, Equiv.symm_symm]
  simp only [a11tm_e9, Equiv.ofBijective_apply]
  rw [Basis.reindex_apply, Pi.basis_apply]
  rfl

private noncomputable def a11tm_mulCoord (u : (GaloisField 2 3)ˣ) (i : Fin 3) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  ggSL9Diag (Function.update (1 : Fin 3 → (GaloisField 2 3)ˣ) i u)

private theorem a11tm_mulCoord_apply (u : (GaloisField 2 3)ˣ) (i : Fin 3) (v : GGSL9V)
    (l : Fin 3) :
    a11tm_mulCoord u i v l =
      ((Function.update (1 : Fin 3 → (GaloisField 2 3)ˣ) i u) l : GaloisField 2 3) * v l := by
  rw [a11tm_mulCoord, ggSL9Diag_apply]

private theorem a11tm_bF_repr_mul (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (a b : Fin 3) :
    (a11tm_bF u h).repr ((u : GaloisField 2 3) * a11tm_bF u h b) a =
      a11tm_e2 (Om a b) := by
  have h0 : (a11tm_bF u h) 0 = 1 := by rw [a11tm_bF_apply]; simp
  have h1 : (a11tm_bF u h) 1 = (u : GaloisField 2 3) := by rw [a11tm_bF_apply]; simp
  have h2 : (a11tm_bF u h) 2 = (u : GaloisField 2 3) ^ 2 := by rw [a11tm_bF_apply]; simp
  have h3 : (u : GaloisField 2 3) ^ 3 = (u : GaloisField 2 3) + 1 := h
  have e0 : a11tm_e2 (0 : F2) = 0 := map_zero a11tm_e2
  have e1 : a11tm_e2 (1 : F2) = 1 := map_one a11tm_e2
  have hb0 : (u : GaloisField 2 3) * a11tm_bF u h 0 = a11tm_bF u h 1 := by
    rw [h0, h1, mul_one]
  have hb1 : (u : GaloisField 2 3) * a11tm_bF u h 1 = a11tm_bF u h 2 := by
    rw [h1, h2, ← pow_two]
  have hb2 : (u : GaloisField 2 3) * a11tm_bF u h 2 = a11tm_bF u h 1 + a11tm_bF u h 0 := by
    rw [h2, h1, h0, ← pow_succ', h3]
  fin_cases b
  · show (a11tm_bF u h).repr ((u : GaloisField 2 3) * a11tm_bF u h 0) a =
      a11tm_e2 (Om a 0)
    rw [hb0]
    fin_cases a <;>
      simp [Om, e0, e1, Basis.repr_self, Finsupp.single_apply, Matrix.cons_val]
  · show (a11tm_bF u h).repr ((u : GaloisField 2 3) * a11tm_bF u h 1) a =
      a11tm_e2 (Om a 1)
    rw [hb1]
    fin_cases a <;>
      simp [Om, e0, e1, Basis.repr_self, Finsupp.single_apply, Matrix.cons_val]
  · show (a11tm_bF u h).repr ((u : GaloisField 2 3) * a11tm_bF u h 2) a =
      a11tm_e2 (Om a 2)
    rw [hb2]
    fin_cases a <;>
      simp [Om, e0, e1, Basis.repr_self, Finsupp.single_apply, Matrix.cons_val, map_add]


private theorem a11tm_bV_repr_single (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (i : Fin 3)
    (x : GaloisField 2 3) (p : Fin 9) :
    (a11tm_bV u h).repr (Pi.single i x) p =
      if a11tm_blk3 p = i then (a11tm_bF u h).repr x (a11tm_idx3 p) else 0 := by
  rw [a11tm_bV_repr]
  by_cases hp : a11tm_blk3 p = i
  · rw [if_pos hp, hp, Pi.single_eq_same]
  · rw [if_neg hp, Pi.single_eq_of_ne hp, map_zero]
    rfl

private theorem a11tm_mulCoord_bV (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (i : Fin 3)
    (q : Fin 9) :
    a11tm_mulCoord u i (a11tm_bV u h q) =
      if a11tm_blk3 q = i then Pi.single i ((u : GaloisField 2 3) * a11tm_bF u h (a11tm_idx3 q))
      else Pi.single (a11tm_blk3 q) (a11tm_bF u h (a11tm_idx3 q)) := by
  rw [a11tm_bV_apply]
  by_cases hq : a11tm_blk3 q = i
  · rw [if_pos hq, hq]
    funext l
    rw [a11tm_mulCoord_apply]
    by_cases hl : l = i
    · subst hl; simp [Function.update, Pi.single_eq_same]
    · simp [Function.update, hl, Pi.single_eq_of_ne]
  · rw [if_neg hq]
    funext l
    rw [a11tm_mulCoord_apply]
    by_cases hl : l = i
    · subst hl; simp [Function.update, Pi.single_eq_of_ne (Ne.symm hq)]
    · simp [Function.update, hl]

private theorem a11tm_blk3_iff (p : Fin 9) (i : Fin 3) :
    blk (Fin.castLE (by omega) p) = i.castSucc ↔ a11tm_blk3 p = i := by
  constructor
  · intro h; exact Fin.ext (by simpa [a11tm_blk3] using congrArg Fin.val h)
  · intro h; exact Fin.ext (by simpa [a11tm_blk3] using congrArg Fin.val h)

private theorem a11tm_T9mat_apply (i : Fin 3) (p q : Fin 9) :
    T9mat i p q =
      if a11tm_blk3 p = i ∧ a11tm_blk3 q = i then Om (a11tm_idx3 p) (a11tm_idx3 q)
      else if p = q then 1 else 0 := by
  simp only [T9mat, Matrix.of_apply, a11tm_blk3_iff, a11tm_idx3]

private theorem a11tm_e9_injective : Function.Injective a11tm_e9 := a11tm_e9.injective

private theorem a11tm_toMatrix_mulCoord (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (i : Fin 3) :
    LinearMap.toMatrix (a11tm_bV u h) (a11tm_bV u h) (a11tm_mulCoord u i) =
      a11tm_e2.mapMatrix (T9mat i) := by
  ext p q
  rw [LinearMap.toMatrix_apply, RingEquiv.mapMatrix_apply, Matrix.map_apply]
  change (a11tm_bV u h).repr (a11tm_mulCoord u i (a11tm_bV u h q)) p =
    a11tm_e2 (T9mat i p q)
  rw [a11tm_mulCoord_bV, a11tm_T9mat_apply]
  by_cases hq : a11tm_blk3 q = i
  · rw [if_pos hq, a11tm_bV_repr_single]
    by_cases hp : a11tm_blk3 p = i
    · rw [if_pos hp, if_pos (show a11tm_blk3 p = i ∧ a11tm_blk3 q = i from ⟨hp, hq⟩)]
      exact a11tm_bF_repr_mul u h (a11tm_idx3 p) (a11tm_idx3 q)
    · rw [if_neg hp,
        if_neg (show ¬ (a11tm_blk3 p = i ∧ a11tm_blk3 q = i) from fun hc => hp hc.1),
        if_neg (show ¬ p = q from fun hpq => hp (hpq ▸ hq))]
      exact (map_zero a11tm_e2).symm
  · rw [if_neg hq, a11tm_bV_repr_single,
      if_neg (show ¬ (a11tm_blk3 p = i ∧ a11tm_blk3 q = i) from fun hc => hq hc.2)]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, if_pos rfl, Basis.repr_self, Finsupp.single_eq_same, map_one]
    · rw [if_neg hpq]
      by_cases hblk : a11tm_blk3 p = a11tm_blk3 q
      · rw [if_pos hblk, Basis.repr_self,
          Finsupp.single_eq_of_ne (show a11tm_idx3 p ≠ a11tm_idx3 q from fun hidx => hpq (by
            apply a11tm_e9_injective
            simp only [a11tm_e9, Equiv.ofBijective_apply, Prod.mk.injEq]
            exact ⟨hblk, hidx⟩))]
        exact (map_zero a11tm_e2).symm
      · rw [if_neg hblk]
        exact (map_zero a11tm_e2).symm


private theorem a11tm_toLin_T9 (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (i : Fin 3) :
    Matrix.toLin (a11tm_bV u h) (a11tm_bV u h) (a11tm_e2.mapMatrix (T9mat i)) =
      a11tm_mulCoord u i := by
  apply (LinearMap.toMatrix (a11tm_bV u h) (a11tm_bV u h)).injective
  rw [LinearMap.toMatrix_toLin, a11tm_toMatrix_mulCoord]

private theorem a11tm_mulCoord_zeta (i : Fin 3) :
    a11tm_mulCoord ggSL9Zeta i =
      ggSL9TorusCoord (Multiplicative.ofAdd (Pi.single i 1)) := by
  ext v l
  rw [a11tm_mulCoord_apply, ggSL9TorusCoord_apply]
  by_cases hl : l = i
  · subst hl
    rw [Function.update_self, Pi.single_eq_same,
      show (1 : ZMod 7).val = 1 by decide, pow_one]
  · rw [Function.update_of_ne hl, Pi.single_eq_of_ne hl]
    simp

private theorem a11tm_mulCoord_zeta_inv (i : Fin 3) :
    a11tm_mulCoord ggSL9Zeta⁻¹ i =
      ggSL9TorusCoord (Multiplicative.ofAdd (-(Pi.single i 1))) := by
  have h6 : ggSL9Zeta ^ 6 = ggSL9Zeta⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, show (6 + 1 : ℕ) = 7 by norm_num,
      ggSL9_units_pow_seven]
  ext v l
  rw [a11tm_mulCoord_apply, ggSL9TorusCoord_apply]
  by_cases hl : l = i
  · subst hl
    rw [Function.update_self, Pi.neg_apply, Pi.single_eq_same]
    rw [show ((-1 : ZMod 7)).val = 6 by decide, h6]
  · rw [Function.update_of_ne hl, Pi.neg_apply, Pi.single_eq_of_ne hl]
    simp [_root_.neg_zero]

private noncomputable def a11tm_slMap :
    SL 9 ≃* Matrix.SpecialLinearGroup (Fin 9) (ZMod 2) where
  toFun := Matrix.SpecialLinearGroup.map a11tm_e2.toRingHom
  invFun := Matrix.SpecialLinearGroup.map a11tm_e2.symm.toRingHom
  left_inv x := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change a11tm_e2.symm (a11tm_e2 (x i j)) = x i j
    simp
  right_inv y := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change a11tm_e2 (a11tm_e2.symm (y i j)) = y i j
    simp
  map_mul' := map_mul _

private noncomputable def a11tm_slToGLV :
    _root_.SpecialLinearGroup (ZMod 2) GGSL9V ≃* GLV :=
  MulEquiv.ofBijective _root_.SpecialLinearGroup.toLinearEquiv (by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact Subtype.ext hxy
    · intro u
      exact ⟨⟨u, Subsingleton.elim _ _⟩, rfl⟩)

private noncomputable def a11tm_theta (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) :
    SL 9 ≃* GLV :=
  a11tm_slMap.trans
    ((Matrix.SpecialLinearGroup.toLin_equiv (a11tm_bV u h)).trans a11tm_slToGLV)

private theorem a11tm_slMap_T9 (i : Fin 3) :
    (a11tm_slMap (T9 i) : Matrix (Fin 9) (Fin 9) (ZMod 2)) =
      a11tm_e2.mapMatrix (T9mat i) := by
  rw [a11tm_slMap]
  rfl

private theorem a11tm_theta_toLinearMap (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (g : SL 9) :
    (a11tm_theta u h g : GGSL9V →ₗ[ZMod 2] GGSL9V) =
      Matrix.toLin (a11tm_bV u h) (a11tm_bV u h)
        (a11tm_slMap g : Matrix (Fin 9) (Fin 9) (ZMod 2)) := by
  rw [a11tm_theta, MulEquiv.trans_apply, MulEquiv.trans_apply]
  change (↑↑((Matrix.SpecialLinearGroup.toLin_equiv (a11tm_bV u h)) (a11tm_slMap g)) :
      GGSL9V →ₗ[ZMod 2] GGSL9V) = _
  rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]

private theorem a11tm_theta_T9 (u : (GaloisField 2 3)ˣ) (h : a11tm_good u) (i : Fin 3) :
    a11tm_theta u h (T9 i) = a11tm_mulCoord u i := by
  apply LinearEquiv.toLinearMap_injective
  rw [a11tm_theta_toLinearMap, a11tm_slMap_T9, a11tm_toLin_T9]

theorem a11TorusModelInput_holds : A11TorusModelInput := by
  rcases a11tm_good_or with hζ | hζinv
  · exact ⟨a11tm_theta ggSL9Zeta hζ, fun i => by
      rw [a11tm_theta_T9, a11tm_mulCoord_zeta]⟩
  · obtain ⟨γ, hγ⟩ := a11GraphAutInput_holds
    refine ⟨(a11tm_theta ggSL9Zeta⁻¹ hζinv).trans γ, fun i => ?_⟩
    rw [MulEquiv.trans_apply, a11tm_theta_T9, a11tm_mulCoord_zeta_inv]
    rw [show ggSL9TorusCoord (Multiplicative.ofAdd (-(Pi.single i 1))) =
      tC (-(Pi.single i 1)) from rfl]
    rw [hγ]
    congr 1
    rw [_root_.neg_neg]

end

end CFSG.StandardType.A11

end
