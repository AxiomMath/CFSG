module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepModel9mAux
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallModel

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pk5_main {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (h : Fin 8 → V)
    (α : Fin 8 → Module.Dual (ZMod 3) V) (x : V) (u : Fin 8 → ZMod 3)
    (C : NineDepChart 9 h α x u) (hfix : ∀ v : V, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod 3) {x})
    (ha : V) (αa : Module.Dual (ZMod 3) V) (hha : αa ha = 2)
    (hx : αa x ≠ 0) (hM : C.e ha 8 = 0) (s : ℕ) (hs : s ≤ 2) (o : ℕ × ℕ × ℕ) (ho : o ∈ kopts ())
    (hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3))
    (hA : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod 3)) :
    ∃ (nF : ℕ) (gens : List Refl) (x' : Vec) (b : ℕ),
      (⟨3, 9, nF, gens, x', b⟩ : Pt) ∈ pts9m () ∧
      ∃ e : V ≃ₗ[ZMod 3] (Fin 9 → ZMod 3), (⟨3, 9, nF, gens, x', b⟩ : Pt).Models e h α x ha αa := by
  let E := C.e
  have hdu : (∑ k : Fin 8, pk5_d k * u k) ≠ 0 := by
    intro h0
    have hvw : pk5_vOf (pk5_tail u) = u := pk5_hvw u h0
    let w0 : V := E.symm ((Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3) - pk5_mvW (pk5_tail u))
    have hker : ∀ i, α i w0 = 0 := by
      intro i
      have hk := pk5_ker_zeroW (pk5_tail u) i
      rw [hvw] at hk
      rw [C.α_eq i w0, show E w0 = (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3)
        - pk5_mvW (pk5_tail u) from LinearEquiv.apply_symm_apply E _]
      exact hk
    have hspan := hfix w0 hker
    obtain ⟨a, ha_eq⟩ := Submodule.mem_span_singleton.mp hspan
    have hEw0 : E w0 8 = 1 := by
      rw [show E w0 = (Pi.single (8 : Fin 9) (1 : ZMod 3) : Fin 9 → ZMod 3)
        - pk5_mvW (pk5_tail u) from LinearEquiv.apply_symm_apply E _]
      simp [pk5_mvW]
    have hEx8 : E x 8 = 0 := by
      rw [C.x_eq]
      decide
    rw [← ha_eq] at hEw0
    rw [map_smul, Pi.smul_apply, hEx8, smul_eq_mul, mul_zero] at hEw0
    exact one_ne_zero hEw0.symm
  let du : ZMod 3 := ∑ k : Fin 8, pk5_d k * u k
  have hdu' : du ≠ 0 := hdu
  let c : ZMod 3 := du⁻¹
  have hcd : c * du = 1 := by
    dsimp only [c]; exact inv_mul_cancel₀ hdu'
  have hdc : du * c = 1 := by
    dsimp only [c]; exact mul_inv_cancel₀ hdu'
  let v2 : Fin 8 → ZMod 3 := fun k => (if (k : ℕ) = 0 then (1 : ZMod 3) else 0) - c * u k
  have hv2 : ∑ k : Fin 8, pk5_d k * v2 k = 0 := by
    have h1 : ∑ k : Fin 8, pk5_d k * (if (k : ℕ) = 0 then (1 : ZMod 3) else 0) = 1 := by
      rw [Finset.sum_eq_single (0 : Fin 8)]
      · simp [pk5_d]
      · intro b _ hb
        have hbval : (b : ℕ) ≠ 0 := fun hh => hb (Fin.ext (by simpa using hh))
        rw [if_neg hbval, mul_zero]
      · intro hh; exact absurd (Finset.mem_univ 0) hh
    have h2 : ∑ k : Fin 8, pk5_d k * (c * u k) = c * du := by
      rw [show du = ∑ k : Fin 8, pk5_d k * u k from rfl, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp only [v2, mul_sub]
    rw [Finset.sum_sub_distrib, h1, h2, hcd, sub_self]
  let w2 : Fin 7 → ZMod 3 := pk5_tail v2
  let m : Fin 8 → ZMod 3 := pk5_mFunW w2
  have hvw2 : pk5_vOf w2 = v2 := pk5_hvw v2 hv2
  have hm : ∀ k : Fin 8, ∑ j : Fin 8, ((cl k.val j.val : ℕ) : ZMod 3) * m j = v2 k := by
    intro k
    have hh := pk5_mFunW_spec w2 k
    rw [hvw2] at hh
    exact hh
  have hm7 : m 7 = 0 := by simp [m, pk5_mFunW]
  let s7 : Fin 9 → ZMod 3 := Pi.single (7 : Fin 9) (1 : ZMod 3)
  let s8 : Fin 9 → ZMod 3 := Pi.single (8 : Fin 9) (1 : ZMod 3)
  let mv : Fin 9 → ZMod 3 := pk5_mvW w2
  let e8 : V := E.symm s8
  let μ : ZMod 3 := -(c * αa e8 + αa (E.symm mv)) * (αa x)⁻¹
  let mvT : Fin 9 → ZMod 3 := fun j => if h : (j : ℕ) < 7 then m ⟨j.val, by omega⟩ else if (j : ℕ) = 7 then μ else 0
  have hmvT8 : mvT 8 = 0 := by simp [mvT]
  let T : (Fin 9 → ZMod 3) ≃ₗ[ZMod 3] (Fin 9 → ZMod 3) :=
    { toFun := pk5_Tfun du mvT
      invFun := pk5_Tinv c mvT
      left_inv := pk5_T_left du c mvT hmvT8 hcd
      right_inv := pk5_T_right du c mvT hmvT8 hdc
      map_add' := pk5_Tfun_add du mvT
      map_smul' := pk5_Tfun_smul du mvT }
  have hT : ∀ w, T w = pk5_Tfun du mvT w := fun w => rfl
  let E' : V ≃ₗ[ZMod 3] (Fin 9 → ZMod 3) := E.trans T
  have hE' : ∀ v, E' v = pk5_Tfun du mvT (E v) := by
    intro v
    show T (E v) = pk5_Tfun du mvT (E v)
    exact hT (E v)
  have hE'symm : ∀ w, E'.symm w = E.symm (T.symm w) := by
    intro w
    change (E.trans T).symm w = E.symm (T.symm w)
    rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  have hTinv_s8 : pk5_Tinv c mvT s8 = mvT + c • s8 := by
    funext j
    by_cases hj : j = 8
    · subst hj
      simp only [pk5_Tinv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same, hmvT8]
      ring
    · have hs : s8 j = 0 := by simp [s8, Pi.single_apply, hj]
      have h8 : s8 8 = 1 := by simp [s8, Pi.single_apply]
      change s8 j + s8 8 * mvT j + (c - 1) * s8 8 * s8 j = mvT j + c * s8 j
      rw [hs, h8]
      ring
  have hT_mvT : T (mvT + c • s8) = s8 := by
    rw [← hTinv_s8, hT]
    exact pk5_T_right du c mvT hmvT8 hdc s8
  have hTsymm_s : T.symm s8 = mvT + c • s8 := by
    conv_lhs => rw [← hT_mvT]
    rw [LinearEquiv.symm_apply_apply]
  have hTsymm_j : ∀ j : Fin 8, T.symm (Pi.single (Fin.castSucc j) (1 : ZMod 3)) = Pi.single (Fin.castSucc j) (1 : ZMod 3) := by
    intro j
    have hfix : T (Pi.single (Fin.castSucc j) (1 : ZMod 3) : Fin 9 → ZMod 3)
        = (Pi.single (Fin.castSucc j) (1 : ZMod 3) : Fin 9 → ZMod 3) := by
      rw [hT]
      apply pk5_T_fix
      fin_cases j <;> simp [Pi.single_apply]
    conv_lhs => rw [← hfix]
    rw [LinearEquiv.symm_apply_apply]
  have hmvT_decomp : mvT = mv + μ • s7 := by
    funext j
    fin_cases j <;> simp [mvT, mv, m, w2, pk5_mvW, s7, Pi.single_apply]
  have hEx : E x = s7 := by
    funext j
    fin_cases j <;> (rw [C.x_eq]; decide)
  have hEsymm_s7 : E.symm s7 = x := by
    rw [LinearEquiv.symm_apply_eq]
    exact hEx.symm
  have hαa_mvT : αa (E.symm mvT) = αa (E.symm mv) + μ * αa x := by
    rw [hmvT_decomp, map_add, map_smul, map_add, map_smul, smul_eq_mul, hEsymm_s7]
  have hμ : μ * αa x = -(c * αa e8 + αa (E.symm mv)) := by
    simp only [μ]
    rw [mul_assoc, inv_mul_cancel₀ hx, mul_one]
  have hαa_e0 : αa (E'.symm s8) = 0 := by
    rw [hE'symm, hTsymm_s, map_add, map_smul, map_add, map_smul, smul_eq_mul]
    rw [show E.symm s8 = e8 from rfl, hαa_mvT, hμ]
    ring
  have hα_basis (i : Fin 8) (j : Fin 8) :
      α i (E'.symm (Pi.single (Fin.castSucc j) (1 : ZMod 3))) = (((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3) := by
    rw [hE'symm, hTsymm_j j, pk5_alpha_chart C i]
    rw [Finset.sum_eq_single (Fin.castSucc j)
      (by intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero])
      (by intro hh; exact absurd (Finset.mem_univ _) hh)]
    have h8 : j.val ≠ 8 := by omega
    simp only [Pi.single_eq_same, mul_one, Fin.val_castSucc]
    rw [if_neg h8, add_zero]
  have hα8_getD7 : ∀ i : Fin 8, (alpha8 i.val)[7]?.getD 0 = 0 := by
    decide +kernel
  have hα_e0 (i : Fin 8) :
      α i (E'.symm s8) = (if (i : ℕ) = 0 then (1 : ZMod 3) else 0) := by
    have hdecomp : mvT + c • s8 = mv + μ • s7 + c • s8 := by rw [hmvT_decomp]
    rw [hE'symm, hTsymm_s, pk5_alpha_chart C i, hdecomp]
    have hsum_mv : ∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
        + (if j.val = 8 then u i else 0)) * mv j = ∑ j : Fin 8, ((cl i.val j.val : ℕ) : ZMod 3) * m j := by
      have hmv8 : mv 8 = 0 := by simp [mv, pk5_mvW]
      have hmv7 : mv 7 = 0 := by simp [mv, pk5_mvW]
      rw [pk5_sum9_split, hmv8, mul_zero, add_zero, pk5_sum8_split,
        show mv (Fin.castSucc 7) = 0 from by simpa using hmv7, mul_zero, add_zero,
        pk5_sum8_split, hm7, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      have hj7 : j.val < 7 := j.isLt
      have hg : ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
          + (if j.val = 8 then u i else 0)) = ((cl i.val j.val : ℕ) : ZMod 3) := by
        rw [if_neg (by omega), add_zero, pk5_alpha8_getD i.val j.val hj7]
      have hmv : mv (Fin.castSucc (Fin.castSucc j)) = m (Fin.castSucc j) := by
        show pk5_mvW w2 (Fin.castSucc (Fin.castSucc j)) = pk5_mFunW w2 (Fin.castSucc j)
        simp only [pk5_mvW, Fin.val_castSucc, dif_pos hj7]
        rfl
      simp only [Fin.val_castSucc]
      rw [hg, hmv]
    have hsum_s7 : ∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
        + (if j.val = 8 then u i else 0)) * s7 j = 0 := by
      rw [Finset.sum_eq_single (7 : Fin 9)
        (by intro b _ hb; simp [s7, Pi.single_apply, hb])
        (by intro hh; exact absurd (Finset.mem_univ 7) hh)]
      simp [s7, Pi.single_apply, hα8_getD7 i]
    have hsum_s8 : ∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
        + (if j.val = 8 then u i else 0)) * s8 j = u i := by
      rw [Finset.sum_eq_single (8 : Fin 9)
        (by intro b _ hb; simp [s8, Pi.single_apply, hb])
        (by intro hh; exact absurd (Finset.mem_univ 8) hh)]
      simp [s8, Pi.single_apply, alpha8]
    have hsplit_sum : ∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
        + (if j.val = 8 then u i else 0)) * (mv + μ • s7 + c • s8) j
        = (∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
            + (if j.val = 8 then u i else 0)) * mv j)
          + μ * (∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
            + (if j.val = 8 then u i else 0)) * s7 j)
          + c * (∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
            + (if j.val = 8 then u i else 0)) * s8 j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit_sum, hsum_mv, hsum_s7, hsum_s8]
    simp only [mul_zero, add_zero]
    rw [hm i]
    simp only [v2]
    ring
  let hb : Vec := List.ofFn (fun j : Fin 8 => (E ha (Fin.castSucc j)).val)
  let fa : Vec := List.ofFn (fun j : Fin 8 => (αa (E'.symm (Pi.single (Fin.castSucc j) (1 : ZMod 3)))).val)
  let P : Pt := ⟨3, 9, 8, frame9m () ++ [⟨fa ++ [0], hb ++ [0]⟩], [0, 0, 0, 0, 0, 0, 0, 1, 0], bound9⟩
  have hb_len : hb.length = 8 := by simp [hb]
  have fa_len : fa.length = 8 := by simp [fa]
  have hb_mem : hb ∈ allVecs 8 := pk5_ofFn_mem_allVecs 8 _ (fun j => ZMod.val_lt _)
  have fa_mem : fa ∈ allVecs 8 := pk5_ofFn_mem_allVecs 8 _ (fun j => ZMod.val_lt _)
  have hb_getD (j : Fin 8) : hb.getD j.val 0 = (E ha (Fin.castSucc j)).val := by
    simp only [hb]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have fa_getD (j : Fin 8) : fa.getD j.val 0 = (αa (E'.symm (Pi.single (Fin.castSucc j) (1 : ZMod 3)))).val := by
    simp only [fa]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hPvec8 (v : Vec) (hv : v.length = 8) (a : ℕ) (k : Fin 8) :
      P.vec (v ++ [a]) (Fin.castSucc k) = ((v.getD k.val 0 : ℕ) : ZMod 3) := by
    simp only [Pt.vec, Fin.val_castSucc]
    rw [List.getD_append v [a] 0 k.val (by simpa [hv] using k.isLt)]
  have hPvec_last (v : Vec) (hv : v.length = 8) (a : ℕ) :
      P.vec (v ++ [a]) (Fin.last 8) = (a : ZMod 3) := by
    simp only [Pt.vec, Fin.val_last]
    rw [List.getD_append_right v [a] 0 8 (by simp [hv])]
    simp [hv]
  have hPg (i : Fin 8) : P.gens.getD i.val ⟨[], []⟩ =
      ⟨alpha8 i.val ++ [if i.val = 0 then 1 else 0], hvec8 i.val ++ [0]⟩ :=
    pk5_gens_getD fa hb i
  have hPg8 : P.gens.getD 8 ⟨[], []⟩ = ⟨fa ++ [0], hb ++ [0]⟩ :=
    pk5_gens_getD8 fa hb
  have hE'ha : E' ha = P.vec (hb ++ [0]) := by
    rw [hE', pk5_T_fix du mvT (E ha) hM]
    funext j
    revert j
    refine Fin.lastCases ?_ ?_
    · rw [hPvec_last hb hb_len 0]
      exact hM
    · intro k
      rw [hPvec8 hb hb_len 0 k, hb_getD k, ZMod.natCast_zmod_val]
  have hPx : P.vec P.x = s7 := by
    change P.vec [0, 0, 0, 0, 0, 0, 0, 1, 0] = s7
    funext j
    fin_cases j <;> rfl
  have hE'x : E' x = P.vec P.x := by
    rw [hE', pk5_T_fix du mvT (E x) (by rw [hEx]; simp [s7]), hEx, hPx]
  have hE'h (i : Fin 8) : E' (h i) = P.vec (hvec8 i.val ++ [0]) := by
    rw [hE']
    have hi8 : E (h i) 8 = 0 := by
      rw [C.h_eq i 8, List.getD_eq_default (hvec8 i) 0 (by simp [pk5_hvec8_length])]
      simp
    rw [pk5_T_fix du mvT (E (h i)) hi8]
    funext j
    revert j
    refine Fin.lastCases ?_ ?_
    · rw [hPvec_last (hvec8 i.val) (pk5_hvec8_length i.val) 0]
      exact hi8
    · intro k
      rw [hPvec8 (hvec8 i.val) (pk5_hvec8_length i.val) 0 k, C.h_eq i (Fin.castSucc k)]
      rfl
  have hα_f (i : Fin 8) : ∀ j : Fin 9, α i (E'.symm (Pi.single j (1 : ZMod 3)))
      = P.vec (alpha8 i.val ++ [if i.val = 0 then 1 else 0]) j := by
    intro j
    revert j
    refine Fin.lastCases ?_ ?_
    · rw [show (Pi.single (Fin.last 8) (1 : ZMod 3) : Fin 9 → ZMod 3) = s8 from rfl, hα_e0 i,
        hPvec_last (alpha8 i.val) (pk5_alpha8_length i.val) (if i.val = 0 then 1 else 0)]
      simp
    · intro k
      rw [hα_basis i k, hPvec8 (alpha8 i.val) (pk5_alpha8_length i.val) (if i.val = 0 then 1 else 0) k]
  have hαa_f : ∀ j : Fin 9, αa (E'.symm (Pi.single j (1 : ZMod 3)))
      = P.vec (fa ++ [0]) j := by
    intro j
    revert j
    refine Fin.lastCases ?_ ?_
    · rw [show (Pi.single (Fin.last 8) (1 : ZMod 3) : Fin 9 → ZMod 3) = s8 from rfl, hαa_e0]
      rw [hPvec_last fa fa_len 0]
      rfl
    · intro k
      rw [hPvec8 fa fa_len 0 k, fa_getD k, ZMod.natCast_zmod_val]
  have ho1 : o.2.1 < 3 := by
    have hmem := ho
    simp only [kopts, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨c, _, rfl⟩ | (rfl | rfl | rfl | rfl) <;> norm_num
  have ho2 : o.2.2 < 3 := by
    have hmem := ho
    simp only [kopts, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨c, _, rfl⟩ | (rfl | rfl | rfl | rfl) <;> norm_num
  have hmem : (fa, hb) ∈ addPairs8 s o := by
    apply pk5_mem_addPairs8 s o fa hb hb_mem fa_mem
    · intro jj hjj
      obtain ⟨hj2lt, hj1eq⟩ := List.mem_zipIdx' hjj
      have hj2lt6 : jj.2 < 6 := by simpa [embJ] using hj2lt
      have hj1 : jj.1 = jj.2 + s := by
        rw [hj1eq]
        simp only [embJ, List.getElem_map, List.getElem_range]
      have hle : s ≤ jj.1 := by omega
      have hlt : jj.1 < s + 6 := by omega
      have hj1lt8 : jj.1 < 8 := by omega
      have hsub : jj.1 - s = jj.2 := by omega
      apply pk5_natCast3_inj
      · rw [dotv]; exact Nat.mod_lt _ (by norm_num)
      · split
        · exact ho1
        · norm_num
      · have hsum_dot : ∑ i : Fin 9, ((alpha8 jj.1).getD i.val 0 : ZMod 3) * (hb.getD i.val 0 : ZMod 3)
            = P.dot (P.vec (alpha8 jj.1 ++ [if jj.1 = 0 then 1 else 0])) (E' ha) := by
          rw [hE'ha]
          simp only [Pt.dot, Pt.vec]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i.val < 8
          · rw [List.getD_append (alpha8 jj.1) [if jj.1 = 0 then 1 else 0] 0 i.val
                (by simpa [pk5_alpha8_length] using hi),
              List.getD_append hb [0] 0 i.val (by simpa [hb_len] using hi)]
          · have hi8 : i.val = 8 := by
              have h9 : i.val < 9 := i.isLt
              omega
            rw [hi8, List.getD_eq_default (alpha8 jj.1) 0 (by simp [pk5_alpha8_length]),
              List.getD_eq_default hb 0 (by simp [hb_len]),
              List.getD_append_right (alpha8 jj.1) [if jj.1 = 0 then 1 else 0] 0 8 (by simp [pk5_alpha8_length]),
              List.getD_append_right hb [0] 0 8 (by simp [hb_len])]
            simp
        rw [pk5_dotv_cast (alpha8 jj.1) hb (pk5_alpha8_length jj.1) hb_len, hsum_dot,
          ← hsub, ← hH ⟨jj.1, hj1lt8⟩ hle hlt]
        exact (pk5_dual_expand E' (α ⟨jj.1, hj1lt8⟩)
          (P.vec (alpha8 jj.1 ++ [if jj.1 = 0 then 1 else 0])) (hα_f ⟨jj.1, hj1lt8⟩) ha).symm
    · intro jj hjj
      obtain ⟨hj2lt, hj1eq⟩ := List.mem_zipIdx' hjj
      have hj2lt6 : jj.2 < 6 := by simpa [embJ] using hj2lt
      have hj1 : jj.1 = jj.2 + s := by
        rw [hj1eq]
        simp only [embJ, List.getElem_map, List.getElem_range]
      have hle : s ≤ jj.1 := by omega
      have hlt : jj.1 < s + 6 := by omega
      have hj1lt8 : jj.1 < 8 := by omega
      have hsub : jj.1 - s = jj.2 := by omega
      apply pk5_natCast3_inj
      · rw [dotv]; exact Nat.mod_lt _ (by norm_num)
      · split
        · exact ho2
        · norm_num
      · have hsum_dot : ∑ i : Fin 9, (fa.getD i.val 0 : ZMod 3) * ((hvec8 jj.1).getD i.val 0 : ZMod 3)
            = P.dot (P.vec (fa ++ [0])) (E' (h ⟨jj.1, hj1lt8⟩)) := by
          rw [hE'h ⟨jj.1, hj1lt8⟩]
          simp only [Pt.dot, Pt.vec]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i.val < 8
          · rw [List.getD_append fa [0] 0 i.val (by simpa [fa_len] using hi),
              List.getD_append (hvec8 jj.1) [0] 0 i.val (by simpa [pk5_hvec8_length] using hi)]
          · have hi8 : i.val = 8 := by
              have h9 : i.val < 9 := i.isLt
              omega
            rw [hi8, List.getD_eq_default fa 0 (by simp [fa_len]),
              List.getD_eq_default (hvec8 jj.1) 0 (by simp [pk5_hvec8_length]),
              List.getD_append_right fa [0] 0 8 (by simp [fa_len]),
              List.getD_append_right (hvec8 jj.1) [0] 0 8 (by simp [pk5_hvec8_length])]
            simp
        rw [pk5_dotv_cast fa (hvec8 jj.1) fa_len (pk5_hvec8_length jj.1), hsum_dot,
          ← hsub, ← hA ⟨jj.1, hj1lt8⟩ hle hlt]
        exact (pk5_dual_expand E' αa (P.vec (fa ++ [0])) hαa_f (h ⟨jj.1, hj1lt8⟩)).symm
    · intro hcontra
      have hEx7 : E' x = s7 := by rw [hE'x, hPx]
      have hEsymm7 : E'.symm s7 = x := by
        rw [LinearEquiv.symm_apply_eq]
        exact hEx7.symm
      have h7val : fa.getD 7 0 = (αa x).val := by
        rw [show (7 : ℕ) = ((7 : Fin 8).val) from rfl, fa_getD (7 : Fin 8)]
        congr 1
        rw [show (Pi.single (Fin.castSucc (7 : Fin 8)) (1 : ZMod 3) : Fin 9 → ZMod 3) = s7 from rfl,
          hEsymm7]
      rw [h7val] at hcontra
      apply hx
      rw [← ZMod.natCast_zmod_val (αa x), hcontra]
      simp
    · apply pk5_natCast3_inj
      · rw [dotv]; exact Nat.mod_lt _ (by norm_num)
      · norm_num
      · rw [pk5_dotv_cast fa hb fa_len hb_len]
        have hdot : P.dot (P.vec (fa ++ [0])) (P.vec (hb ++ [0]))
            = ∑ j : Fin 9, (fa.getD j.val 0 : ZMod 3) * (hb.getD j.val 0 : ZMod 3) := by
          simp only [Pt.dot, Pt.vec]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i.val < 8
          · rw [List.getD_append fa [0] 0 i.val (by simpa [fa_len] using hi),
              List.getD_append hb [0] 0 i.val (by simpa [hb_len] using hi)]
          · have hi8 : i.val = 8 := by
              have h9 : i.val < 9 := i.isLt
              omega
            rw [hi8, List.getD_eq_default fa 0 (by simp [fa_len]),
              List.getD_eq_default hb 0 (by simp [hb_len]),
              List.getD_append_right fa [0] 0 8 (by simp [fa_len]),
              List.getD_append_right hb [0] 0 8 (by simp [hb_len])]
            simp
        rw [← hdot, ← hE'ha]
        rw [show P.dot (P.vec (fa ++ [0])) (E' ha)
            = ∑ j : Fin 9, (P.vec (fa ++ [0])) j * E' ha j from rfl]
        rw [← pk5_dual_expand E' αa (P.vec (fa ++ [0])) hαa_f ha]
        exact hha
  refine ⟨8, frame9m () ++ [(⟨fa ++ [0], hb ++ [0]⟩ : Refl)], [0, 0, 0, 0, 0, 0, 0, 1, 0], bound9, ?_, E', ?_⟩
  · exact pk5_pts9m_mem s o hs ho fa hb hmem
  · refine ⟨rfl, ?_, hE'x, ?_, ?_, ?_⟩
    · show (frame9m () ++ [(⟨fa ++ [0], hb ++ [0]⟩ : Refl)]).length = 8 + 1
      simp [frame9m]
    · intro i
      refine ⟨?_, ?_⟩
      · rw [hPg i]; exact hE'h i
      · intro w
        rw [hPg i]
        exact pk5_dual_expand E' (α i) (P.vec (alpha8 i.val ++ [if i.val = 0 then 1 else 0])) (hα_f i) w
    · rw [hPg8]; exact hE'ha
    · intro w
      rw [hPg8]
      exact pk5_dual_expand E' αa (P.vec (fa ++ [0])) hαa_f w

theorem ninedep_model_9m {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (h : Fin 8 → V)
    (α : Fin 8 → Module.Dual (ZMod 3) V) (x : V) (u : Fin 8 → ZMod 3)
    (C : NineDepChart 9 h α x u) (hfix : ∀ v : V, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod 3) {x})
    (ha : V) (αa : Module.Dual (ZMod 3) V) (hha : αa ha = 2)
    (hx : αa x ≠ 0) (hM : C.e ha 8 = 0) (s : ℕ) (hs : s ≤ 2) (o : ℕ × ℕ × ℕ) (ho : o ∈ kopts ())
    (hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3))
    (hA : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod 3)) :
    ∃ (nF : ℕ) (gens : List Refl) (x' : Vec) (b : ℕ),
      (⟨3, 9, nF, gens, x', b⟩ : Pt) ∈ pts9m () ∧
      ∃ e : V ≃ₗ[ZMod 3] (Fin 9 → ZMod 3), (⟨3, 9, nF, gens, x', b⟩ : Pt).Models e h α x ha αa :=
  pk5_main h α x u C hfix ha αa hha hx hM s hs o ho hH hA

end CFSG.TwoNodeSmall
