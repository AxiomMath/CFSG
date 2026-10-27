module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepModel9mAux

public section

namespace CFSG.NineAll

open CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ninedep_chart_norm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (h : Fin 8 → V)
    (α : Fin 8 → Module.Dual (ZMod 3) V) (x : V) (u : Fin 8 → ZMod 3)
    (C : NineDepChart 9 h α x u)
    (hfix : ∀ v : V, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod 3) ({x} : Set V)) :
    Nonempty (NineDepChart 9 h α x (fun i : Fin 8 => if (i : ℕ) = 0 then (1 : ZMod 3) else 0)) := by
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
  have hmv8 : mv 8 = 0 := by simp [mv, pk5_mvW]
  have hmv7 : mv 7 = 0 := by simp [mv, pk5_mvW]
  let T : (Fin 9 → ZMod 3) ≃ₗ[ZMod 3] (Fin 9 → ZMod 3) :=
    { toFun := pk5_Tfun du mv
      invFun := pk5_Tinv c mv
      left_inv := pk5_T_left du c mv hmv8 hcd
      right_inv := pk5_T_right du c mv hmv8 hdc
      map_add' := pk5_Tfun_add du mv
      map_smul' := pk5_Tfun_smul du mv }
  have hT : ∀ w, T w = pk5_Tfun du mv w := fun w => rfl
  let E' : V ≃ₗ[ZMod 3] (Fin 9 → ZMod 3) := E.trans T
  have hE' : ∀ v, E' v = pk5_Tfun du mv (E v) := by
    intro v
    show T (E v) = pk5_Tfun du mv (E v)
    exact hT (E v)
  have hE'symm : ∀ w, E'.symm w = E.symm (T.symm w) := by
    intro w
    change (E.trans T).symm w = E.symm (T.symm w)
    rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  have hTinv_s8 : pk5_Tinv c mv s8 = mv + c • s8 := by
    funext j
    by_cases hj : j = 8
    · subst hj
      simp only [pk5_Tinv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same, hmv8]
      ring
    · have hs : s8 j = 0 := by simp [s8, Pi.single_apply, hj]
      have h8 : s8 8 = 1 := by simp [s8, Pi.single_apply]
      change s8 j + s8 8 * mv j + (c - 1) * s8 8 * s8 j = mv j + c * s8 j
      rw [hs, h8]
      ring
  have hT_mv : T (mv + c • s8) = s8 := by
    rw [← hTinv_s8, hT]
    exact pk5_T_right du c mv hmv8 hdc s8
  have hTsymm_s : T.symm s8 = mv + c • s8 := by
    conv_lhs => rw [← hT_mv]
    rw [LinearEquiv.symm_apply_apply]
  have hTsymm_j : ∀ j : Fin 8, T.symm (Pi.single (Fin.castSucc j) (1 : ZMod 3)) =
      Pi.single (Fin.castSucc j) (1 : ZMod 3) := by
    intro j
    have hfix' : T (Pi.single (Fin.castSucc j) (1 : ZMod 3) : Fin 9 → ZMod 3)
        = (Pi.single (Fin.castSucc j) (1 : ZMod 3) : Fin 9 → ZMod 3) := by
      rw [hT]
      apply pk5_T_fix
      fin_cases j <;> simp [Pi.single_apply]
    conv_lhs => rw [← hfix']
    rw [LinearEquiv.symm_apply_apply]
  have hα_basis (i : Fin 8) (j : Fin 8) :
      α i (E'.symm (Pi.single (Fin.castSucc j) (1 : ZMod 3))) =
        (((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3) := by
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
    rw [hE'symm, hTsymm_s, pk5_alpha_chart C i]
    have hsum_mv : ∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
        + (if j.val = 8 then u i else 0)) * mv j = ∑ j : Fin 8, ((cl i.val j.val : ℕ) : ZMod 3) * m j := by
      rw [pk5_sum9_split, hmv8, mul_zero, add_zero, pk5_sum8_split,
        show mv (Fin.castSucc 7) = 0 from by simpa using hmv7, mul_zero, add_zero,
        pk5_sum8_split, hm7, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      have hj7 : j.val < 7 := j.isLt
      have hg : ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
          + (if j.val = 8 then u i else 0)) = ((cl i.val j.val : ℕ) : ZMod 3) := by
        rw [if_neg (by omega), add_zero, pk5_alpha8_getD i.val j.val hj7]
      have hmvj : mv (Fin.castSucc (Fin.castSucc j)) = m (Fin.castSucc j) := by
        show pk5_mvW w2 (Fin.castSucc (Fin.castSucc j)) = pk5_mFunW w2 (Fin.castSucc j)
        simp only [pk5_mvW, Fin.val_castSucc, dif_pos hj7]
        rfl
      simp only [Fin.val_castSucc]
      rw [hg, hmvj]
    have hsum_s8 : ∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
        + (if j.val = 8 then u i else 0)) * s8 j = u i := by
      rw [Finset.sum_eq_single (8 : Fin 9)
        (by intro b _ hb; simp [s8, Pi.single_apply, hb])
        (by intro hh; exact absurd (Finset.mem_univ 8) hh)]
      simp [s8, Pi.single_apply, alpha8]
    have hsplit_sum : ∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
        + (if j.val = 8 then u i else 0)) * (mv + c • s8) j
        = (∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
            + (if j.val = 8 then u i else 0)) * mv j)
          + c * (∑ j : Fin 9, ((((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3)
            + (if j.val = 8 then u i else 0)) * s8 j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit_sum, hsum_mv, hsum_s8, hm i]
    simp only [v2]
    ring
  refine ⟨{ e := E', h_eq := ?_, x_eq := ?_, α_eq := ?_ }⟩
  · intro i j
    have hi8 : E (h i) 8 = 0 := by
      rw [C.h_eq i 8, List.getD_eq_default (hvec8 i) 0 (by simp [pk5_hvec8_length])]
      simp
    rw [hE', pk5_T_fix du mv (E (h i)) hi8]
    exact C.h_eq i j
  · intro j
    have hx8 : E x 8 = 0 := by
      rw [C.x_eq]
      decide
    rw [hE', pk5_T_fix du mv (E x) hx8]
    exact C.x_eq j
  · intro i w
    refine pk5_dual_expand E' (α i)
      (fun j : Fin 9 => (((alpha8 i.val).getD j.val 0 : ℕ) : ZMod 3) +
        (if j.val = 8 then (if (i : ℕ) = 0 then (1 : ZMod 3) else 0) else 0)) ?_ w
    intro j
    revert j
    refine Fin.lastCases ?_ ?_
    · have h8 : (alpha8 i.val).getD 8 0 = 0 :=
        List.getD_eq_default (alpha8 i.val) 0 (by simp [pk5_alpha8_length])
      show α i (E'.symm s8) = (((alpha8 i.val).getD (Fin.last 8).val 0 : ℕ) : ZMod 3) +
        (if (Fin.last 8).val = 8 then (if (i : ℕ) = 0 then (1 : ZMod 3) else 0) else 0)
      rw [hα_e0 i, Fin.val_last, h8, if_pos rfl]
      simp
    · intro k
      rw [hα_basis i k]
      show _ = (((alpha8 i.val).getD (Fin.castSucc k).val 0 : ℕ) : ZMod 3) +
        (if (Fin.castSucc k).val = 8 then (if (i : ℕ) = 0 then (1 : ZMod 3) else 0) else 0)
      have hk8 : (Fin.castSucc k).val ≠ 8 := by
        simp only [Fin.val_castSucc]
        omega
      rw [if_neg hk8, add_zero, Fin.val_castSucc]

end CFSG.NineAll

end
