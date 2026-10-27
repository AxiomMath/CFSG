module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632WeylDatum
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1632Weyl
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableAHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableBHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTableCHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCompanion1625Pieces

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.E6Centralizer1585
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma ltrb1g6_stabOmega_eq_filter
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (hE6 : ρ.row.T = GGKacType.E6) :
    ρ.row.D.stabΩ =
      ((k0DiagOf (GGKacType.E6)).omega.filter
        (fun w => decide (k0pAct w ρ.row.s = ρ.row.s))).length := by
  rw [ρ.row.D_eq, hE6]
  rfl

private lemma ltrb1g6_stabOmega_fst
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (hE6 : ρ.row.T = GGKacType.E6) (hs : ρ.row.s = [0, 1, 0, 0, 0, 0, 2]) :
    ρ.row.D.stabΩ = 1 := by
  rw [ltrb1g6_stabOmega_eq_filter ρ hE6, hs]
  decide

private lemma ltrb1g6_stabOmega_snd
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (hE6 : ρ.row.T = GGKacType.E6) (hs : ρ.row.s = [0, 2, 0, 0, 0, 0, 1]) :
    ρ.row.D.stabΩ = 1 := by
  rw [ltrb1g6_stabOmega_eq_filter ρ hE6, hs]
  decide

private lemma ltrb1g6_stabOmega_r3
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (hE6 : ρ.row.T = GGKacType.E6) (hs : ρ.row.s = [0, 0, 0, 0, 1, 0, 0]) :
    ρ.row.D.stabΩ = 3 := by
  rw [ltrb1g6_stabOmega_eq_filter ρ hE6, hs]
  decide

private lemma ltrb1g6_stabOmega_r4
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (hE6 : ρ.row.T = GGKacType.E6) (hs : ρ.row.s = [0, 0, 0, 0, 0, 1, 1]) :
    ρ.row.D.stabΩ = 1 := by
  rw [ltrb1g6_stabOmega_eq_filter ρ hE6, hs]
  decide

private lemma ltrb1g6_stabOmega_r16
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (hE6 : ρ.row.T = GGKacType.E6) (hs : ρ.row.s = [1, 1, 0, 0, 0, 0, 1]) :
    ρ.row.D.stabΩ = 3 := by
  rw [ltrb1g6_stabOmega_eq_filter ρ hE6, hs]
  decide

theorem geomIndexByDatumAt_e6
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi) (hE6 : ρ.row.T = GGKacType.E6) :
    GeomIndexByDatumAt ρ := by
  show (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = ρ.row.D.stabΩ
  exact (weylIndexAt_holds ρ).trans (weylIndexByDatumAt_e6 ρ hE6)

theorem b1GeomOn_r1_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1GeomOn Omega CFSG.StandardType.GGE6ThreeR1Labels1585 1 := by
  intro lab R _ I phi ρ j hΛ hj hqs hrow
  obtain ⟨hT, hs⟩ := e6RowTableR1_holds lab R I phi ρ j hΛ hj hqs hrow
  simp only [E6RowDataR1] at hs
  obtain ⟨hs, -⟩ := hs
  have hG : (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = ρ.row.D.stabΩ :=
    geomIndexByDatumAt_e6 ρ hT
  rw [hG]
  rcases hs with hs | hs
  · exact ltrb1g6_stabOmega_fst ρ hT hs
  · exact ltrb1g6_stabOmega_snd ρ hT hs

theorem b1GeomOn_r3_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1GeomOn Omega CFSG.StandardType.GGE6ThreeR3Labels1585 3 := by
  intro lab R _ I phi ρ j hΛ hj hqs hrow
  obtain ⟨hT, hs⟩ := e6RowTableR3_holds lab R I phi ρ j hΛ hj hqs hrow
  simp only [E6RowDataR3] at hs
  obtain ⟨hs, -⟩ := hs
  have hG : (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = ρ.row.D.stabΩ :=
    geomIndexByDatumAt_e6 ρ hT
  rw [hG]
  exact ltrb1g6_stabOmega_r3 ρ hT hs

theorem b1GeomOn_r4_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1GeomOn Omega CFSG.StandardType.GGE6ThreeR4Labels1585 1 := by
  intro lab R _ I phi ρ j hΛ hj hqs hrow
  obtain ⟨hT, hs⟩ := e6RowTableR4_holds lab R I phi ρ j hΛ hj hqs hrow
  simp only [E6RowDataR4] at hs
  obtain ⟨hs, -⟩ := hs
  have hG : (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = ρ.row.D.stabΩ :=
    geomIndexByDatumAt_e6 ρ hT
  rw [hG]
  exact ltrb1g6_stabOmega_r4 ρ hT hs

theorem b1GeomOn_r16_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1GeomOn Omega CFSG.StandardType.GGE6ThreeR16Labels1585 3 := by
  intro lab R _ I phi ρ j hΛ hj hqs hrow
  obtain ⟨hT, hs⟩ := e6RowTableR16_holds lab R I phi ρ j hΛ hj hqs hrow
  simp only [E6RowDataR16] at hs
  obtain ⟨hs, -⟩ := hs
  have hG : (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = ρ.row.D.stabΩ :=
    geomIndexByDatumAt_e6 ρ hT
  rw [hG]
  exact ltrb1g6_stabOmega_r16 ρ hT hs

theorem b1GeomOn_r4Opp_holds
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2] :
    B1GeomOn Omega CFSG.StandardType.GGE6ThreeR4OppLabels1585 1 := by
  intro lab R _ I phi ρ j hΛ hj hqs hrow
  obtain ⟨hT, hs⟩ := e6RowTableR4Opp_holds lab R I phi ρ j hΛ hj hqs hrow
  simp only [E6RowDataR4Opp] at hs
  obtain ⟨hs, -⟩ := hs
  have hG : (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = ρ.row.D.stabΩ :=
    geomIndexByDatumAt_e6 ρ hT
  rw [hG]
  exact ltrb1g6_stabOmega_r4 ρ hT hs

end CFSG.StandardType.S2MathAs1E6Companion1625

end
