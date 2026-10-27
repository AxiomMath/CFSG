module

public import CFSG.Quasithin.Background.F918J0
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB45
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

section Rows

theorem insp5a_rows (h45 : AsB45)
    (hF : Vol2.Ch10.SecA.Facts10_1) (hX : Insp5aNonShape) {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) {X K : Subgroup (MulAut U)} {C : Subgroup U}
    (hQ : InternalSec.QSec X K C) (hS : SQTKGroup ↥K)
    (hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)) (hA : A38Types ↥K) [IsSimpleGroup ↥K] :
    Vol2.Ch10.SecA.IsShapeGroup ↥K ∧
      (((∃ n, 2 ≤ n ∧ BinaryNaturalSL K ⊤ C 2 n) ∨ BinaryNaturalSL K ⊤ C 3 1 ∨
          AlternatingNatural K ⊤ C 5) ∨
        ((∃ m, 1 ≤ m ∧ BinaryOrthogonalFour K ⊤ C m) ∨ (∃ f, BinaryNaturalSz K ⊤ C f))) := by
  have hb4 := hQ.b4Hyp hU hS
  have hsv : ∀ v : Sec (⊤ : Subgroup U) C, v ^ 2 = 1 := sec_sq_eq_one hU ⊤ C
  have hqsec : qhatOf (autSec X ⊤ C) ≤ ((2 : ℚ) : WithTop ℚ) :=
    (hQ.qhatOf_autSec_le hU).trans hq
  have hKC : K ≤ stabSub C := hQ.stabKC
  have hf : K ⊓ centSec ⊤ C = ⊥ := hQ.faithful
  let e : ↥K ≃* ↥(autSec K ⊤ C) := B5.secEquiv K (InternalSec.le_stabSub_top K) hKC hf
  by_cases hsh : Vol2.Ch10.SecA.IsShapeGroup ↥(autSec K ⊤ C)
  · have : IsSimpleGroup ↥(autSec K ⊤ C) := e.symm.isSimpleGroup
    refine ⟨hsh.of_mulEquiv e, ?_⟩
    rcases h45 _ hsv _ _ hb4 hqsec with ⟨-, ⟨A, hA'⟩, hall⟩ | ⟨-, ht⟩ | h3
    · rcases Vol2.Ch10.SecA.b42_of_isShapeGroup hF hsv hb4 hA' (hall A hA') hsh with
        ⟨m, hm, hnat⟩ | hnat3 | halt
      · exact Or.inl (Or.inl ⟨m, hm, InternalSec.binaryNaturalSL_of_autSec hKC hf hnat⟩)
      · exact Or.inl (Or.inr (Or.inl (InternalSec.binaryNaturalSL_of_autSec hKC hf hnat3)))
      · exact Or.inl (Or.inr (Or.inr (InternalSec.alternatingNatural_of_autSec hKC hf halt)))
    · rcases Vol2.Ch10.SecA.table_of_isShapeGroup hF hb4 ht hsh with ⟨m, hm, horth⟩ | ⟨f, hsz⟩
      · exact Or.inr (Or.inl ⟨m, hm, InternalSec.binaryOrthogonalFour_of_autSec hKC hf horth⟩)
      · exact Or.inr (Or.inr ⟨f, InternalSec.binaryNaturalSz_of_autSec hKC hf hsz⟩)
    · exact (Vol2.Ch10.SecA.not_part3_of_isShapeGroup hF h3 hsh).elim
  · exfalso
    have hA'' : A38Types ↥(autSec K ⊤ C) := a38Types_congr e hA
    obtain ⟨hB42, hTab, hP3⟩ := hX _ _ _ hb4 hA'' hsh
    rcases h45 _ hsv _ _ hb4 hqsec with ⟨-, ⟨A, hA'⟩, hall⟩ | ⟨-, ht⟩ | h3
    · exact hB42 A hA' (hall A hA')
    · exact hTab ht
    · exact hP3 h3

end Rows

end CFSG.Quasithin
