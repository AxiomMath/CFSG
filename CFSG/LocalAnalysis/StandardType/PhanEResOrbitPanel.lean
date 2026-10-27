module

public import CFSG.LocalAnalysis.StandardType.PhanEResSeam
public import CFSG.LocalAnalysis.StandardType.PhanEResPsiAct
import CFSG.LieType.Universal.SpecialLinearRoots.SignedPerm
public import CFSG.LocalAnalysis.StandardType.PhanELocalGate

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix Module CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Universal.SpecialLinear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} {d : List ℕ}

private theorem plo_Vsub_succ (j : Fin (m + 1)) :
    Vsub (K := K) (m + 1) (j.val + 1) = Vsub (K := K) (m + 1) j.val ⊔
      Submodule.span K {(Pi.single j (1 : K) : Fin (m + 1) → K)} := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · refine sup_le (Vsub_mono (Nat.le_succ j.val)) (Submodule.span_le.mpr ?_)
    rintro _ rfl i hi
    rw [Pi.single_apply, if_neg (by intro h; rw [h] at hi; omega)]
  · have huV : (Pi.single j (1 : K) : Fin (m + 1) → K) ∉ Vsub (K := K) (m + 1) j.val := by
      intro h
      have h1 := h j (le_refl j.val)
      rw [Pi.single_eq_same] at h1
      exact one_ne_zero h1
    rw [Submodule.finrank_sup_span_singleton huV,
      finrank_Vsub (K := K) (n := m + 1) (by omega),
      finrank_Vsub (K := K) (n := m + 1) (by omega)]

private theorem plo_span_singleton_smul_eq {r : K} (hr : r ≠ 0) (x : Fin (m + 1) → K) :
    Submodule.span K {r • x} = Submodule.span K {x} := by
  simpa using Submodule.span_singleton_smul_eq (R := K) (M := Fin (m + 1) → K)
    (isUnit_iff_ne_zero.mpr hr) x

private theorem plo_tv_glLin (i : Fin m) (c : K) (v : Fin (m + 1) → K) :
    glLin (SpecialLinearGroup.toGL (tv K i.succ i.castSucc c)) v =
      v + (c * v i.castSucc) • (Pi.single i.succ (1 : K) : Fin (m + 1) → K) := by
  have hpq : i.succ ≠ i.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  rw [glLin_apply]
  change (tv K i.succ i.castSucc c : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ v = _
  rw [tv_of_ne hpq, SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]

private theorem plo_tv_stab (i : Fin m) (c : K) {j : ℕ} (hj : j ≠ i.val + 1) :
    (Vsub (K := K) (m + 1) j).map
        (glLin (SpecialLinearGroup.toGL (tv K i.succ i.castSucc c))).toLinearMap =
      Vsub (K := K) (m + 1) j := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rw [Submodule.map_le_iff_le_comap]
  intro v hv r hr
  change (glLin (SpecialLinearGroup.toGL (tv K i.succ i.castSucc c)) v) r = 0
  rw [plo_tv_glLin i c v]
  simp only [Pi.add_apply, hv r hr, zero_add, Pi.smul_apply, smul_eq_mul]
  by_cases hrq : r = i.succ
  · subst hrq
    have hvp : v i.castSucc = 0 := by
      apply hv
      by_contra h
      rw [not_le] at h
      have hle : j ≤ i.val + 1 := by simpa [Fin.val_succ] using hr
      have hlt : i.val < j := by simpa only [Fin.val_castSucc] using h
      omega
    simp [hvp]
  · rw [Pi.single_eq_of_ne (i := i.succ) (i' := r) hrq, mul_zero]

private theorem plo_tv_map_succ (i : Fin m) (c : K) :
    (Vsub (K := K) (m + 1) (i.val + 1)).map
        (glLin (SpecialLinearGroup.toGL (tv K i.succ i.castSucc c))).toLinearMap =
      Vsub (K := K) (m + 1) i.val ⊔ Submodule.span K
        {(Pi.single i.castSucc (1 : K) : Fin (m + 1) → K) +
          c • (Pi.single i.succ (1 : K) : Fin (m + 1) → K)} := by
  have himg : (glLin (SpecialLinearGroup.toGL (tv K i.succ i.castSucc c))).toLinearMap ''
      {(Pi.single i.castSucc (1 : K) : Fin (m + 1) → K)} =
      {(Pi.single i.castSucc (1 : K) : Fin (m + 1) → K) +
        c • (Pi.single i.succ (1 : K) : Fin (m + 1) → K)} := by
    rw [Set.image_singleton]
    congr 1
    change glLin (SpecialLinearGroup.toGL (tv K i.succ i.castSucc c))
      (Pi.single i.castSucc (1 : K) : Fin (m + 1) → K) = _
    rw [plo_tv_glLin i c]
    simp
  have hVs : Vsub (K := K) (m + 1) (i.val + 1) = Vsub (K := K) (m + 1) i.val ⊔
      Submodule.span K {(Pi.single i.castSucc (1 : K) : Fin (m + 1) → K)} := by
    simpa only [Fin.val_castSucc] using plo_Vsub_succ (K := K) i.castSucc
  rw [hVs, Submodule.map_sup,
    plo_tv_stab i c (j := i.val) (by omega), Submodule.map_span, himg]

private noncomputable def plo_swap (i : Fin m) : SpecialLinearGroup (Fin (m + 1)) K :=
  tv K i.castSucc i.succ 1 * tv K i.succ i.castSucc 1 * tv K i.castSucc i.succ 1

private theorem plo_swap_mem (i : Fin m) :
    plo_swap (K := K) i ∈ Subgroup.closure {A : SpecialLinearGroup (Fin (m + 1)) K |
        ∃ c : K, A = tv K i.castSucc i.succ c ∨ A = tv K i.succ i.castSucc c} := by
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact Subgroup.subset_closure ⟨1, Or.inl rfl⟩
  · exact Subgroup.subset_closure ⟨1, Or.inr rfl⟩
  · exact Subgroup.subset_closure ⟨1, Or.inl rfl⟩

private theorem plo_swap_matrix (i : Fin m) :
    (plo_swap (K := K) i : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      weylMatrix (R := K) i.castSucc i.succ := by
  have hpq : i.castSucc ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  change ((tv K i.castSucc i.succ 1 * tv K i.succ i.castSucc 1 * tv K i.castSucc i.succ 1 :
    SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
    weylMatrix (R := K) i.castSucc i.succ
  rw [tv_of_ne hpq, tv_of_ne hpq.symm]
  simpa only [CharTwo.neg_eq] using
    (coe_transvection_mul_transvection_mul_transvection (R := K) (a := i.castSucc)
      (b := i.succ) hpq)

private theorem plo_weylSign_eq_one (s t : Fin (m + 1)) : weylSign (R := K) s t = 1 := by
  have h : weylSign (R := K) s t * weylSign (R := K) s t = 1 := weylSign_mul_self s t
  rcases (mul_self_eq_one_iff.mp h) with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

private theorem plo_signedPerm_mulVec (π : Equiv.Perm (Fin (m + 1))) (ε : Fin (m + 1) → K)
    (v : Fin (m + 1) → K) :
    (signedPerm π ε) *ᵥ v = fun r => ε (π.symm r) * v (π.symm r) := by
  funext r
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π.symm r)]
  · rw [signedPerm_apply, Equiv.apply_symm_apply, if_pos rfl]
  · intro s _ hs
    rw [signedPerm_apply, if_neg (fun h => hs (by rw [h, Equiv.symm_apply_apply]))]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem plo_weylMatrix_mulVec (a b : Fin (m + 1)) (v : Fin (m + 1) → K) :
    (weylMatrix (R := K) a b) *ᵥ v = fun r => v (Equiv.swap a b r) := by
  rw [weylMatrix, plo_signedPerm_mulVec]
  funext r
  have hsymm : (Equiv.swap a b).symm = Equiv.swap a b := rfl
  rw [hsymm, plo_weylSign_eq_one, one_mul]

private theorem plo_swap_glLin (i : Fin m) (v : Fin (m + 1) → K) :
    glLin (SpecialLinearGroup.toGL (plo_swap (K := K) i)) v =
      fun r => v (Equiv.swap i.castSucc i.succ r) := by
  rw [glLin_apply]
  change (plo_swap (K := K) i : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *ᵥ v = _
  rw [plo_swap_matrix, plo_weylMatrix_mulVec]

private theorem plo_swap_stab (i : Fin m) {j : ℕ} (hj : j ≠ i.val + 1) :
    (Vsub (K := K) (m + 1) j).map
        (glLin (SpecialLinearGroup.toGL (plo_swap (K := K) i))).toLinearMap =
      Vsub (K := K) (m + 1) j := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq _ _)
  rw [Submodule.map_le_iff_le_comap]
  intro v hv r hr
  change (glLin (SpecialLinearGroup.toGL (plo_swap (K := K) i)) v) r = 0
  rw [plo_swap_glLin i v]
  apply hv
  by_cases hrp : r = i.castSucc
  · subst hrp
    have hle : j ≤ i.val := by simpa only [Fin.val_castSucc] using hr
    simp only [Equiv.swap_apply_left, Fin.val_succ]
    omega
  · by_cases hrq : r = i.succ
    · subst hrq
      simp only [Equiv.swap_apply_right, Fin.val_castSucc]
      have hle : j ≤ i.val + 1 := by simpa only [Fin.val_succ] using hr
      by_contra h
      rw [not_le] at h
      omega
    · rwa [Equiv.swap_apply_of_ne_of_ne hrp hrq]

private theorem plo_swap_map_succ (i : Fin m) :
    (Vsub (K := K) (m + 1) (i.val + 1)).map
        (glLin (SpecialLinearGroup.toGL (plo_swap (K := K) i))).toLinearMap =
      Vsub (K := K) (m + 1) i.val ⊔
        Submodule.span K {(Pi.single i.succ (1 : K) : Fin (m + 1) → K)} := by
  have himg : (glLin (SpecialLinearGroup.toGL (plo_swap (K := K) i))).toLinearMap ''
      {(Pi.single i.castSucc (1 : K) : Fin (m + 1) → K)} =
      {(Pi.single i.succ (1 : K) : Fin (m + 1) → K)} := by
    rw [Set.image_singleton]
    congr 1
    change glLin (SpecialLinearGroup.toGL (plo_swap (K := K) i))
      (Pi.single i.castSucc (1 : K) : Fin (m + 1) → K) = _
    rw [plo_swap_glLin i]
    funext r
    by_cases hr : r = i.succ
    · subst hr
      simp
    · have hne : Equiv.swap i.castSucc i.succ r ≠ i.castSucc := by
        intro h
        apply hr
        have h2 := congrArg (Equiv.swap i.castSucc i.succ) h
        simpa [Equiv.swap_apply_self] using h2
      rw [Pi.single_eq_of_ne (i := i.castSucc) (i' := Equiv.swap i.castSucc i.succ r) hne,
        Pi.single_eq_of_ne (i := i.succ) (i' := r) hr]
  have hVs : Vsub (K := K) (m + 1) (i.val + 1) = Vsub (K := K) (m + 1) i.val ⊔
      Submodule.span K {(Pi.single i.castSucc (1 : K) : Fin (m + 1) → K)} := by
    simpa only [Fin.val_castSucc] using plo_Vsub_succ (K := K) i.castSucc
  rw [hVs, Submodule.map_sup,
    plo_swap_stab i (j := i.val) (by omega), Submodule.map_span, himg]

private theorem plo_flagAct_std_E (g : GL (Fin (m + 1)) K) (j : ℕ) :
    (flagAct g (stdFlag K (m + 1))).E j = (Vsub (K := K) (m + 1) j).map (glLin g).toLinearMap := by
  rw [flagAct, flagMap_E]
  rfl

theorem exists_sl2_of_adj (i : Fin m) {y : FlagK K (m + 1)}
    (h : (flagSys K m).adj i (stdFlag K (m + 1)) y) :
    ∃ B ∈ Subgroup.closure {A : SpecialLinearGroup (Fin (m + 1)) K |
        ∃ c : K, A = tv K i.castSucc i.succ c ∨ A = tv K i.succ i.castSucc c},
      y = flagAct (SpecialLinearGroup.toGL B) (stdFlag K (m + 1)) := by
  have hE : ∀ j, j ≠ i.val + 1 → y.E j = Vsub (K := K) (m + 1) j := by
    intro j hj
    exact (h j hj).symm
  have hWle : y.E (i.val + 1) ≤ Vsub (K := K) (m + 1) (i.val + 2) := by
    rw [← hE (i.val + 2) (by omega)]
    exact y.mono (by omega)
  have hVle : Vsub (K := K) (m + 1) i.val ≤ y.E (i.val + 1) := by
    rw [← hE i.val (by omega)]
    exact y.mono (by omega)
  have hdim : finrank K (y.E (i.val + 1)) = i.val + 1 := y.dim _ (by omega)
  by_cases hstd : y.E (i.val + 1) = Vsub (K := K) (m + 1) (i.val + 1)
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [map_one, flagAct_one]
    apply FlagK.ext
    intro j
    by_cases hj : j = i.val + 1
    · subst hj; exact hstd
    · exact hE j hj
  · have hnot : ¬ (y.E (i.val + 1) ≤ Vsub (K := K) (m + 1) i.val) := by
      intro hle
      have heq : y.E (i.val + 1) = Vsub (K := K) (m + 1) i.val := le_antisymm hle hVle
      have h2 := congrArg (fun (U : Submodule K (Fin (m + 1) → K)) => finrank K U) heq
      rw [hdim, finrank_Vsub (K := K) (n := m + 1) (by omega)] at h2
      omega
    obtain ⟨u, huW, huV⟩ := Set.not_subset.mp hnot
    set a : K := u i.castSucc with ha
    set b : K := u i.succ with hb
    set w : Fin (m + 1) → K := a • (Pi.single i.castSucc (1 : K) : Fin (m + 1) → K) +
      b • (Pi.single i.succ (1 : K) : Fin (m + 1) → K) with hw
    have hpq : i.castSucc ≠ i.succ := by
      intro hh
      have := congrArg Fin.val hh
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    have hw_c : w i.castSucc = a := by
      simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        Pi.single_eq_of_ne (i := i.succ) (i' := i.castSucc) hpq, mul_one, mul_zero, add_zero]
    have hw_s : w i.succ = b := by
      simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        Pi.single_eq_of_ne (i := i.castSucc) (i' := i.succ) hpq.symm, mul_one, mul_zero, zero_add]
    have hdiff : u - w ∈ Vsub (K := K) (m + 1) i.val := by
      intro j hj
      rw [Pi.sub_apply]
      by_cases hjc : j = i.castSucc
      · subst hjc
        rw [hw_c, ← ha]
        exact sub_self a
      · by_cases hjs : j = i.succ
        · subst hjs
          rw [hw_s, ← hb]
          exact sub_self b
        · have hge : i.val + 2 ≤ j.val := by
            have h1 : j.val ≠ i.val := fun h => hjc (Fin.ext (by simpa using h))
            have h2 : j.val ≠ i.val + 1 :=
              fun h => hjs (Fin.ext (by simpa [Fin.val_succ] using h))
            omega
          have hu0 : u j = 0 := hWle huW j hge
          have hw0 : w j = 0 := by
            simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
              Pi.single_eq_of_ne (i := i.castSucc) (i' := j) hjc,
              Pi.single_eq_of_ne (i := i.succ) (i' := j) hjs, mul_zero, add_zero]
          rw [hu0, hw0, sub_zero]
    have hspan_u : y.E (i.val + 1) = Vsub (K := K) (m + 1) i.val ⊔ Submodule.span K {u} := by
      symm
      refine Submodule.eq_of_le_of_finrank_eq (sup_le hVle ?_) ?_
      · rw [Submodule.span_le, Set.singleton_subset_iff]; exact huW
      · rw [Submodule.finrank_sup_span_singleton huV,
          finrank_Vsub (K := K) (n := m + 1) (by omega), hdim]
    have hspan_le1 : Submodule.span K {u} ≤
        Vsub (K := K) (m + 1) i.val ⊔ Submodule.span K {w} := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      have huw : u = (u - w) + w := by abel
      rw [huw]
      exact Submodule.mem_sup.mpr ⟨u - w, hdiff, w, Submodule.subset_span rfl, rfl⟩
    have hspan_le2 : Submodule.span K {w} ≤
        Vsub (K := K) (m + 1) i.val ⊔ Submodule.span K {u} := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      have hwu : w = u - (u - w) := by abel
      rw [hwu]
      exact Submodule.mem_sup.mpr ⟨-(u - w),
        (Vsub (K := K) (m + 1) i.val).neg_mem hdiff, u, Submodule.subset_span rfl, by abel⟩
    have hspan_w : y.E (i.val + 1) = Vsub (K := K) (m + 1) i.val ⊔ Submodule.span K {w} := by
      rw [hspan_u]
      exact le_antisymm (sup_le le_sup_left hspan_le1) (sup_le le_sup_left hspan_le2)
    have hab : (a, b) ≠ (0, 0) := by
      rintro h0
      apply huV
      have hw0 : w = 0 := by
        have h1 : a = 0 := (Prod.ext_iff.mp h0).1
        have h2 : b = 0 := (Prod.ext_iff.mp h0).2
        rw [hw, h1, h2, zero_smul, zero_smul, add_zero]
      have hd0 : u ∈ Vsub (K := K) (m + 1) i.val := by simpa [hw0] using hdiff
      exact hd0
    by_cases ha0 : a = 0
    · have hb0 : b ≠ 0 := by
        intro hb0
        exact hab (by simp [ha0, hb0])
      have hw_eq : w = b • (Pi.single i.succ (1 : K) : Fin (m + 1) → K) := by
        rw [hw]; simp [ha0]
      have hspan_e : Submodule.span K {w} =
          Submodule.span K {(Pi.single i.succ (1 : K) : Fin (m + 1) → K)} := by
        rw [hw_eq, plo_span_singleton_smul_eq hb0]
      refine ⟨plo_swap (K := K) i, plo_swap_mem (K := K) i, ?_⟩
      apply FlagK.ext
      intro j
      rw [plo_flagAct_std_E]
      by_cases hj : j = i.val + 1
      · subst hj
        rw [plo_swap_map_succ, hspan_w, hspan_e]
      · rw [plo_swap_stab (K := K) i hj, hE j hj]
    · have hw_eq : w = a • ((Pi.single i.castSucc (1 : K) : Fin (m + 1) → K) +
          (b / a) • (Pi.single i.succ (1 : K) : Fin (m + 1) → K)) := by
        rw [hw]
        simp only [smul_add, smul_smul, div_eq_mul_inv]
        rw [show a * (b * a⁻¹) = b from by
          rw [mul_comm b a⁻¹, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]]
      have hspan_e : Submodule.span K {w} = Submodule.span K
          {(Pi.single i.castSucc (1 : K) : Fin (m + 1) → K) +
            (b / a) • (Pi.single i.succ (1 : K) : Fin (m + 1) → K)} := by
        rw [hw_eq, plo_span_singleton_smul_eq ha0]
      refine ⟨tv K i.succ i.castSucc (b / a),
        Subgroup.subset_closure ⟨b / a, Or.inr rfl⟩, ?_⟩
      apply FlagK.ext
      intro j
      rw [plo_flagAct_std_E]
      by_cases hj : j = i.val + 1
      · subst hj
        rw [plo_tv_map_succ, hspan_w, hspan_e]
      · rw [plo_tv_stab (K := K) i (b / a) hj, hE j hj]

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
