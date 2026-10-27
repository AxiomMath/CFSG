module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeFrameShared
public import CFSG.LocalAnalysis.StandardType.GGResXDatumLFrame
public import CFSG.LocalAnalysis.StandardType.GGLargeRowShared
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLargeRowFrame_of_pieces (hK : GGLargeRowKDatum) (hX : GGResXDichotomyInput)
    (hFix : GGTBFixInput) (hNoSeven : GGLargeRowNoSevenAtL) (hC : GGLargeRowCard)
    (hDim : GGTwoNodeRowDimKnown) (hWA : GGTBFixNbrXInput) : GGLargeRowFrameInput := by
  intro G _ _ p _ B Bs x L D J y K N hH hrow hx
  obtain ⟨hN11, hpN, hKd⟩ := hK G p B Bs x L D J y K N hH hrow
  have hrow_keep : GGResRowAt (ggRowLargeN N) p J K := hrow
  obtain ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRow2, _, hNrank⟩ := hrow
  have hrow' : GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N)
      p J K :=
    ⟨labJ, labX, hJΛ, hXΛ, hJlab, hXlab, hRow2, hNrank⟩
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hN5 : 5 ≤ N := by omega
  have hLd : GGResXDatum p Bs L :=
    (hX G p B Bs x L D J y K hH).1.resolve_right
      (hNoSeven G p B Bs x L D J y K N hH hrow_keep)
  obtain ⟨V, iA, iM, ι, h, α, r, T, hT, s, hdim, hpair, hrefl, hclosr, hsrefl, hconn, hclos_s,
    hfix, hx0, hxnot, hnt, _⟩ :=
      ggTwoNodeFrame_of_datums hFix hWA hDim hH hrow' hp2 hN5 hpN hKd hLd hx
  let := iA
  let := iM
  have hlin : GGLargeLinHyp p N h α r s (ι (Additive.ofMul ⟨x, hx⟩)) :=
    { p_ne_two := hp2
      N_ge := hN11
      p_dvd := hpN
      dim_le := hdim
      pair := hpair
      refl_form := hrefl
      finT := hT
      s_refl := hsrefl
      conn := hconn
      x_ne := hx0
      fix_s := hfix
      x_not_fix := hxnot
      no_transv := hnt }
  refine ⟨V, iA, iM, ι, h, α, r, T, s, hlin, hclosr, ?_⟩
  intro _
  have hgrp : ggLargeGrp r s =
      (ggAutomizer K Bs ⊔ ggAutomizer L Bs).map (ggLin (p := p) ι) := by
    unfold ggLargeGrp
    rw [Subgroup.closure_union, hclosr, hclos_s]
    exact (Subgroup.map_sup (ggAutomizer K Bs) (ggAutomizer L Bs) (ggLin (p := p) ι)).symm
  have hcard : Nat.card ↥((ggAutomizer K Bs ⊔ ggAutomizer L Bs).map (ggLin (p := p) ι)) =
      Nat.card ↥(ggAutomizer K Bs ⊔ ggAutomizer L Bs) :=
    Nat.card_congr (Subgroup.equivMapOfInjective
      (ggAutomizer K Bs ⊔ ggAutomizer L Bs) (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv.symm
  rw [hgrp, hcard]
  exact hC G p B Bs x L D J y K N hH hrow_keep

end CFSG.StandardType

end
