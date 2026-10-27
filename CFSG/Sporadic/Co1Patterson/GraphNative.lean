module

public import CFSG.Sporadic.Co1Patterson.GraphInputs
public import CFSG.Sporadic.Co1Patterson.NativeSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)

@[expose] def NRep (R : Rows) (x : NativeSporadic.Co1) : Prop := matHom x = rowsMatrix 24 R

namespace NRep

variable {R S Ri : Rows} {x y : NativeSporadic.Co1}

theorem mul (hx : NRep R x) (hy : NRep S y) : NRep (Native.mul R S) (x * y) := by
  unfold NRep Native.mul
  rw [map_mul, hx, hy, rowsMatrix_mulRows]

theorem one' : NRep Native.one (1 : NativeSporadic.Co1) := by
  unfold NRep Native.one
  rw [map_one, rowsMatrix_idRows]

theorem inv (hx : NRep R x) (h : Native.mul R Ri = Native.one) : NRep Ri x⁻¹ := by
  unfold NRep
  refine matHom_inv_eq ?_
  rw [hx, ← rowsMatrix_mulRows]
  exact (congrArg (rowsMatrix 24) h).trans (rowsMatrix_idRows 24)

theorem unique (hx : NRep R x) (hy : NRep R y) : x = y :=
  matHom_injective (hx.trans hy.symm)

theorem rows_eq (hR : NRep R x) (hS : NRep S x) (hRv : validRows R = true)
    (hSv : validRows S = true) : R = S :=
  rowsMatrix_injective_of_valid hRv hSv (hR.symm.trans hS)

end NRep

theorem validRows_mul {X Y : Rows} (hX : validRows X = true) (hY : validRows Y = true) :
    validRows (Native.mul X Y) = true := by
  have hXs := validRows_size hX
  have hYlt : ∀ j : ℕ, Y[j]?.getD 0 < 2 ^ 24 := by
    intro j
    rcases Nat.lt_or_ge j Y.size with hj | hj
    · rw [Array.getElem?_eq_getElem hj, Option.getD_some]
      exact validRows_lt hY (Array.getElem_mem_toList hj)
    · rw [Array.getElem?_eq_none hj, Option.getD_none]
      exact Nat.two_pow_pos 24
  unfold validRows Native.mul mulRows
  rw [Bool.and_eq_true, Array.all_eq_true]
  refine ⟨by rw [Array.size_map, hXs]; rfl, fun i hi => ?_⟩
  rw [Array.getElem_map]
  exact decide_eq_true (vecMulN_lt Y hYlt _)

noncomputable abbrev brayGL : List GL24 := brayEltsG aG twoAD1 twoABray

@[expose] noncomputable def brayNC (l : ℕ) : NativeSporadic.Co1 :=
  co1MatEquiv.symm ⟨brayGL.getD l 1, getD_mem_of_forall (brayElts_mem_GA iotaA_mem_GA) l⟩

theorem matHom_eq_nativeEmb (x : NativeSporadic.Co1) :
    matHom x = ((nativeEmb x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
  (co1MatEquiv_val x).symm

theorem nativeEmb_brayNC (l : ℕ) : nativeEmb (brayNC l) = brayGL.getD l 1 := by
  rw [nativeEmb_apply, brayNC, MulEquiv.apply_symm_apply]

theorem nrep_of_mrep {R : Rows} {x : NativeSporadic.Co1} (h : MRep R (nativeEmb x)) :
    NRep R x := by
  unfold NRep
  rw [matHom_eq_nativeEmb]
  exact h.symm

theorem nrep_brayNC
    (l : ℕ) : NRep (brayG.getD l Native.one) (brayNC l) := by
  refine nrep_of_mrep ?_
  rw [nativeEmb_brayNC]
  exact getD_rep (rep_brayElts rep_iotaA (centCheck_parts twoA_cent_check).1) MRep.one l

theorem brayG_length :
    brayG.length = 8 := by
  have h := (rep_brayElts (bidx := twoABray) rep_iotaA (centCheck_parts twoA_cent_check).1)
  unfold brayG
  rw [h.length_eq]
  simp [brayEltsG, twoABray]

theorem nrep_brayArr
    (l : ℕ) (hl : l < brayArr.size) :
    NRep brayArr[l]! (brayNC l) := by
  have : brayArr[l]! = brayG.getD l Native.one := by
    rw [getElem!_pos brayArr l hl]
    simp [brayArr, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa [brayArr] using hl)]
  rw [this]
  exact nrep_brayNC l

theorem brayArr_size :
    brayArr.size = 8 := by
  simp [brayArr, brayG_length]

theorem map_centralizer_aNC :
    (centralizer ({aNC} : Set NativeSporadic.Co1)).map nativeEmb = GA ⊓ centralizer {aG} := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_inf.2 ⟨nativeEmb_mem x, mem_centralizer_aNC_iff.1 hx⟩
  · intro hg
    obtain ⟨x, rfl⟩ := exists_nativeEmb_eq (mem_inf.1 hg).1
    exact ⟨x, mem_centralizer_aNC_iff.2 (mem_inf.1 hg).2, rfl⟩

theorem closure_brayNC :
    Subgroup.closure (brayNC '' {l | l < 8}) = centralizer ({aNC} : Set NativeSporadic.Co1) := by
  apply Subgroup.map_injective nativeEmb_injective
  rw [MonoidHom.map_closure, map_centralizer_aNC, ← twoAE_eq]
  show _ = brayE aG twoAD1 twoABray
  unfold brayE
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  have hlen : (brayEltsG aG twoAD1 twoABray).length = 8 := by simp [brayEltsG, twoABray]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    rw [nativeEmb_brayNC, List.getD_eq_getElem _ _ (by rw [hlen]; exact hl)]
    exact List.getElem_mem _
  · intro hg
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
    rw [hlen] at hl
    refine ⟨brayNC l, ⟨l, hl, rfl⟩, ?_⟩
    rw [nativeEmb_brayNC, List.getD_eq_getElem]

noncomputable abbrev gBaseGL : List GL24 :=
  [A₁, A₂, aG] ++ (List.range 8).map twoAQg ++ brayGL

theorem rep_gBase :
    List.Forall₂ MRep gBase gBaseGL := by
  show List.Forall₂ MRep ([CFSG.Sporadic.Co1Schreier.Native.aR, CFSG.Sporadic.Co1Schreier.Native.bR,
    iotaARows] ++ twoAQRows ++ brayG) ([A₁, A₂, aG] ++ (List.range 8).map twoAQg ++ brayGL)
  refine List.rel_append (List.rel_append ?_ ?_) ?_
  · exact .cons rep_A₁ (.cons rep_A₂ (.cons rep_iotaA .nil))
  · unfold twoAQRows
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun k _ => rep_iotaQ k
  · exact rep_brayElts rep_iotaA (centCheck_parts twoA_cent_check).1

theorem gBaseGL_mem : ∀ g ∈ gBaseGL, g ∈ GA := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · rcases List.mem_cons.1 hg with h | hg
      · exact h ▸ A₁_mem
      rcases List.mem_cons.1 hg with h | hg
      · exact h ▸ A₂_mem
      rcases List.mem_cons.1 hg with h | hg
      · exact h ▸ iotaA_mem_GA
      exact absurd hg List.not_mem_nil
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
      exact iotaQ_mem_GA k
  · exact brayElts_mem_GA iotaA_mem_GA g hg

@[expose] noncomputable def gElt (j : ℕ) : NativeSporadic.Co1 :=
  co1MatEquiv.symm ⟨(dagG gBaseGL gWords).getD (j - 1) 1,
    getD_mem_of_forall (dagG_mem gBaseGL_mem gWords) _⟩

theorem nativeEmb_gElt (j : ℕ) : nativeEmb (gElt j) = (dagG gBaseGL gWords).getD (j - 1) 1 := by
  rw [nativeEmb_apply, gElt, MulEquiv.apply_symm_apply]

theorem nrep_gEl
    (h : gDag.2.2 = true) (j : ℕ) : NRep (gEl j) (gElt j) := by
  refine nrep_of_mrep ?_
  rw [nativeEmb_gElt]
  exact getD_rep (dag_rep rep_gBase gWords h) MRep.one (j - 1)

theorem dagOK_parts (h : dagOK = true) :
    gDag.2.2 = true ∧ ∀ j, 1 ≤ j → j ≤ 190 → validRows (gEl j) = true ∧
      validRows (gElInv j) = true ∧ Native.mul (gEl j) (gElInv j) = Native.one := by
  unfold dagOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  refine ⟨h1, fun j hj1 hj2 => ?_⟩
  obtain ⟨⟨h4, h5⟩, h6⟩ := h3 (j - 1) (by omega)
  rw [Nat.sub_add_cancel hj1] at h4 h5 h6
  exact ⟨h4, h5, h6⟩

theorem nrep_gElInv
    (h : dagOK = true) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 190) :
    NRep (gElInv j) (gElt j)⁻¹ :=
  (nrep_gEl (dagOK_parts h).1 j).inv ((dagOK_parts h).2 j hj1 hj2).2.2

end CFSG.Sporadic.Co1Patterson
