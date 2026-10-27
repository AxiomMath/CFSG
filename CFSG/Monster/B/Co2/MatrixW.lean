
module


public import CFSG.Monster.B.Co2.MatrixAction

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv

theorem alpha_mem_Kv
    (i : Fin 24) : alpha i ∈ Kstab v0 := vShort_eq_v0 ▸ alpha_mem_Kstab i

theorem kOp_alpha_dec
    (i : Fin 24) (x : ℕ) :
    kOp (alpha i) (dec x) = dec (VisCert.actRows (genMatrix i) x) :=
  smul_dec_alpha i x

theorem wAct_alpha_qbW
    (i : Fin 24) (t : Fin 22) :
    wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ (qbW t) = decW (genQuotMatrix i)[(t : ℕ)]! := by
  obtain ⟨hm, he⟩ := decW_eq_mk (genQuotMatrix i)[(t : ℕ)]!
  rw [he, qbW, wAct_mk, Submodule.Quotient.eq, vLineInL, Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.coe_sub, mem_vLineL]
  change kOp (alpha i) (dec (quotBasis t)) - dec (Native.actD 22 Native.quotientBasis
    (genQuotMatrix i)[(t : ℕ)]!) = 0 ∨ kOp (alpha i) (dec (quotBasis t)) -
    dec (Native.actD 22 Native.quotientBasis (genQuotMatrix i)[(t : ℕ)]!) = v0
  have hk : kOp (alpha i) (dec (quotBasis t)) = (actQ (alpha i)).unop • dec (quotBasis t) := rfl
  rw [hk]
  rcases smul_quotBasis i t with h | h
  · left
    rw [h, sub_self]
  · right
    rw [h, ← vShort_eq_v0, add_sub_cancel_left]

theorem wAct_alpha_decW
    (i : Fin 24) (c : ℕ) :
    wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ (decW c) = decW (Native.actD 22 (genQuotMatrix i) c) := by
  rw [Native.actD, xorHom_actGo decW decW_xor, decW_zero, zero_add, decW, map_sum]
  simp only [map_smul, wAct_alpha_qbW]
  rw [Finset.sum_range (fun s => if c.testBit s then decW (genQuotMatrix i)[s]! else 0)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp

theorem wvec_injective : Function.Injective wvec := fun i j h =>
  shortVec_injective (decW_injective (shortVec_lt i) (shortVec_lt j) h)

theorem span_wvec :
    Submodule.span (ZMod 2) (Set.range wvec) = ⊤ := by
  have hf : wvec = (qbWBasis.equivFun.symm.toLinearMap : (Fin 22 → ZMod 2) →ₗ[ZMod 2] Wv v0) ∘
      fun j : Ω => bvec 22 (shortVec j) :=
    funext fun j => decW_eq_equivFun _
  rw [hf, Set.range_comp, Submodule.span_image, span_shortVec, Submodule.map_top,
    LinearMap.range_eq_top.2 qbWBasis.equivFun.symm.surjective]

theorem wAct_alpha_wvec
    (i : Fin 24) (j : Ω) :
    wAct v0 ⟨alpha i, alpha_mem_Kv i⟩ (wvec j) = wvec (pPerm i j) := by
  rw [wvec, wAct_alpha_decW, actD_genQuotMatrix, wvec]

theorem alphaN_mem
    (j : ℕ) : alphaN j ∈ Kstab v0 := by
  unfold alphaN
  split_ifs
  · exact alpha_mem_Kv _
  · exact one_mem _

theorem alphaLetter_mem
    (l : ℤ) : alphaLetter l ∈ Kstab v0 := by
  unfold alphaLetter
  split_ifs
  · exact alphaN_mem _
  · exact inv_mem (alphaN_mem _)

theorem alphaWord_mem :
    ∀ w : List ℤ, alphaWord w ∈ Kstab v0
  | [] => one_mem _
  | l :: w => by
    rw [alphaWord_cons]
    exact mul_mem (alphaLetter_mem l) (alphaWord_mem w)

theorem A0_mem :
    A0 ∈ Kstab v0 := alphaWord_mem _

theorem A1_mem :
    A1 ∈ Kstab v0 := alphaWord_mem _

theorem Agrp_le :
    Agrp ≤ Kstab v0 := by
  rw [Agrp, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact A0_mem
  · exact A1_mem

theorem wAct_alphaN_wvec
    {j : ℕ} (hj : j < 24) (x : Ω) :
    wAct v0 ⟨alphaN j, alphaN_mem j⟩ (wvec x) = wvec (pLetter.pPermN j x) := by
  have e : (⟨alphaN j, alphaN_mem j⟩ : Kstab v0) = ⟨alpha ⟨j, hj⟩, alpha_mem_Kv _⟩ := by
    apply Subtype.ext
    simp [alphaN, hj]
  rw [e, wAct_alpha_wvec]
  simp [pLetter.pPermN, hj]

theorem wAct_alphaLetter_wvec
    {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ 24) (x : Ω) :
    wAct v0 ⟨alphaLetter l, alphaLetter_mem l⟩ (wvec x) = wvec (pLetter l x) := by
  have hi : l.natAbs - 1 < 24 := by omega
  unfold pLetter
  by_cases hpos : 0 < l
  · have e : (⟨alphaLetter l, alphaLetter_mem l⟩ : Kstab v0) = ⟨alphaN (l.natAbs - 1), alphaN_mem _⟩ :=
      Subtype.ext (by simp [alphaLetter, hpos])
    rw [e, wAct_alphaN_wvec hi, ite_eq_left hpos]
  · have e : (⟨alphaLetter l, alphaLetter_mem l⟩ : Kstab v0) =
        (⟨alphaN (l.natAbs - 1), alphaN_mem _⟩ : Kstab v0)⁻¹ :=
      Subtype.ext (by simp [alphaLetter, hpos])
    rw [e, ite_eq_right hpos]
    set p := pLetter.pPermN (l.natAbs - 1)
    have h1 := wAct_alphaN_wvec hi (p⁻¹ x)
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at h1
    rw [← h1, wAct_inv_apply]

theorem wAct_alphaWord_wvec :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 24) → ∀ x : Ω,
    wAct v0 ⟨alphaWord w, alphaWord_mem w⟩ (wvec x) = wvec (pairWordPerm w x)
  | [], _, x => by
    have e : (⟨alphaWord [], alphaWord_mem []⟩ : Kstab v0) = 1 := rfl
    rw [e, wAct_one]
    rfl
  | l :: w, hw, x => by
    have e : (⟨alphaWord (l :: w), alphaWord_mem (l :: w)⟩ : Kstab v0) =
        ⟨alphaLetter l, alphaLetter_mem l⟩ * ⟨alphaWord w, alphaWord_mem w⟩ := rfl
    rw [e, wAct_mul, Module.End.mul_apply, wAct_alphaLetter_wvec (hw l List.mem_cons_self),
      wAct_alphaWord_wvec w (fun l' h => hw l' (List.mem_cons_of_mem _ h)), pairWordPerm,
      Equiv.Perm.mul_apply]

theorem wAct_A0_wvec
    (x : Ω) : wAct v0 ⟨A0, A0_mem⟩ (wvec x) = wvec (pa x) := by
  rw [pa_eq]
  exact wAct_alphaWord_wvec _ (dataCheck_parts.2.2.2.2.2.2 0 (by norm_num)) x

theorem wAct_A1_wvec
    (x : Ω) : wAct v0 ⟨A1, A1_mem⟩ (wvec x) = wvec (pb x) := by
  rw [pb_eq]
  exact wAct_alphaWord_wvec _ (dataCheck_parts.2.2.2.2.2.2 1 (by norm_num)) x

end CFSG.Monster.B.Co2
