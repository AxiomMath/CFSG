
module

public import CFSG.Monster.Existence.TwoPoint.GammaExclDefBase

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short

theorem gx_fix_of_commute {y g : SpaceB ≃ₗ[ℚ] SpaceB} (hy : y ∈ Gmat) (hg : g ∈ Gmat)
    (h : g * (y * tStar * y⁻¹) = (y * tStar * y⁻¹) * g) : g (y aStar) = y aStar := by
  have hmem : y⁻¹ * g * y ∈ Gmat := Gmat.mul_mem (Gmat.mul_mem (Gmat.inv_mem hy) hg) hy
  have hc : y⁻¹ * g * y * tStar = tStar * (y⁻¹ * g * y) := by
    calc y⁻¹ * g * y * tStar = y⁻¹ * (g * (y * tStar * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * tStar * y⁻¹) * g) * y := by rw [h]
      _ = tStar * (y⁻¹ * g * y) := by group
  have h2 : y⁻¹ (g (y aStar)) = aStar := (mul_tStar_comm_iff hmem).1 hc
  calc g (y aStar) = y (y⁻¹ (g (y aStar))) := (y.apply_symm_apply _).symm
    _ = y aStar := by rw [h2]

noncomputable def GmatM : Subgroup MGriess := Gmat.comap AutO.subtype

theorem fiMkW_mem_GmatM (w : List Native.Gen) : fiMkW w ∈ GmatM := wordLin_mem_Gmat w

theorem gxElem_mem_GmatM (k : ℕ) : gxElem k ∈ GmatM := by
  rw [← fiMkW_gxElemWord]
  exact fiMkW_mem_GmatM _

noncomputable def gxD : MGriess := fiMkW fiCAlpha

noncomputable def gxAxis (j : ℕ) : SpaceB := (xHat j * gxD).1 aStar

def gxDiffAt (k : ℕ) (u w : Native.DVec) : Bool :=
  decide (u.D.getD k 0 * 2 ^ w.e ≠ w.D.getD k 0 * 2 ^ u.e)

def gxDiffScan (u w : Native.DVec) : Bool :=
  (List.range 98280).any (fun k => gxDiffAt (300 + k) u w) ||
    (List.range 98304).any fun k => gxDiffAt (98580 + k) u w

theorem gx_coord_eq {u w : Native.DVec} {k : ℕ}
    (h : (u.D.getD k 0 : ℚ) / 2 ^ u.e = (w.D.getD k 0 : ℚ) / 2 ^ w.e) :
    ¬ gxDiffAt k u w = true := by
  unfold gxDiffAt
  rw [decide_eq_true_eq, not_not]
  have h2 : ((u.D.getD k 0 : ℤ) : ℚ) * 2 ^ w.e = ((w.D.getD k 0 : ℤ) : ℚ) * 2 ^ u.e := by
    field_simp at h
    linarith
  exact_mod_cast h2

theorem gx_interp_ne_of_diffScan
    {u w : Native.DVec} (h : gxDiffScan u w = true) :
    interp u ≠ interp w := by
  unfold gxDiffScan at h
  rw [Bool.or_eq_true] at h
  intro heq
  rcases h with h | h
  · obtain ⟨k, hk, hk'⟩ := List.any_eq_true.1 h
    have hk98 : k < 98280 := List.mem_range.1 hk
    have h1 := congrFun (congrArg (fun x : SpaceB => x.2.1) heq) (shortOf ⟨k, hk98⟩)
    simp only [interp, interpX, posOf_shortOf] at h1
    exact gx_coord_eq h1 hk'
  · obtain ⟨k, hk, hk'⟩ := List.any_eq_true.1 h
    have hk98 : k < 98304 := List.mem_range.1 hk
    have hr : k / 24 < 4096 := by omega
    have hj : k % 24 < 24 := Nat.mod_lt _ (by norm_num)
    have h1 := congrFun (congrFun (congrArg (fun x : SpaceB => x.2.2) heq)
      (spinOfRow (k / 24))) ⟨k % 24, hj⟩
    simp only [interp, interpW, Matrix.of_apply, rowOf_spinOfRow hr] at h1
    have e : 98580 + 24 * (k / 24) + k % 24 = 98580 + k := by omega
    rw [e] at h1
    exact gx_coord_eq h1 hk'

@[noinline] def gxNodeCheck (j : ℕ) : Bool :=
  (fiWAlpha ++ fiWBeta ++ fiCAlpha ++ gxProdWord (gxXList j)).all Native.Gen.validB &&
    (let u := Native.evalPrep HS.hsCtx (fiPCAlpha ++ gxProdP (gxXList j)) HS.axisP
     (j == 9 || gxDiffScan (Native.evalPrep HS.hsCtx fiPAlpha u) u) &&
       gxDiffScan (Native.evalPrep HS.hsCtx (fiPAlpha ++ fiPBeta ++ fiPAlpha) u) u)

theorem fiMkW_wordBetaPrime : fiMkW (fiWAlpha ++ fiWBeta ++ fiWAlpha) = betaPrime := by
  rw [fiMkW_append, fiMkW_append]
  show fiAlpha * (fiBeta * fiAlpha) = fiAlpha * fiBeta * fiAlpha
  rw [mul_assoc]

def gxYWord (j : ℕ) : List Native.Gen := fiCAlpha ++ gxProdWord (gxXList j)

def gxBPWord : List Native.Gen := fiWAlpha ++ fiWBeta ++ fiWAlpha

def gxNodeNe (j : ℕ) : Prop :=
  (j ≠ 9 → wordLin (gxYWord j ++ fiWAlpha) aStar ≠ wordLin (gxYWord j) aStar) ∧
    wordLin (gxYWord j ++ gxBPWord) aStar ≠ wordLin (gxYWord j) aStar

theorem gxNodeNe_of {j : ℕ}
    (h : wordLin (gxYWord j ++ fiWAlpha) aStar ≠ wordLin (gxYWord j) aStar ∧
      wordLin (gxYWord j ++ gxBPWord) aStar ≠ wordLin (gxYWord j) aStar) : gxNodeNe j :=
  ⟨fun _ => h.1, h.2⟩

end CFSG.Monster.Existence
