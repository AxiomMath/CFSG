module

public import CFSG.LocalAnalysis.StandardType.GGForkClassify
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A3
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A4
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A5
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A6
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.A7
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B3
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B4
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B5
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B6
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.B7
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C3
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C4
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C5
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C6
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.C7
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D4
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D5
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D6
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.D7
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.E6
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.E7
public import CFSG.LocalAnalysis.StandardType.GGResIDisp.F4

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResI_F₄_rev (i j : Fin 4) : CartanMatrix.F₄ j.rev i.rev = CartanMatrix.F₄ i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem ggResILinInput_holds : GGResILinInput := by
  intro p _ Λ _ _ b ML CL MK CK V _ _ _ _ g h α x hp2 h3 h8 hWL hCL hWK hCK hconn hnf hg hL hK hind
    hspan hxL hfix hx0
  have H : GGResIHyp p b ML CL MK CK g h α x :=
    ⟨hp2, hWL, hCL, hWK, hCK, hconn, hnf, hg, hL, hK, hind, hspan, hxL, hfix, hx0⟩
  show GGResILinConcl p b CL CK g h α x
  have hcard : ∀ {m : ℕ} (e : Fin m ≃ Λ), m = Fintype.card Λ := fun e => by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  rcases ggIntCartan_models hWL hCL with ⟨n, e, hn, hA | ⟨hn2, hB | hC⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ |
    ⟨e, hE7⟩ | ⟨e, hE8⟩ | ⟨e, hF | hFt⟩ | ⟨e, hG | hGt⟩
  · have := hcard e
    have h3' : 3 ≤ n := by omega
    have h8' : n < 8 := by omega
    interval_cases n
    · exact GGResIDisp.A3.ggResI_type_A3 H e hA
    · exact GGResIDisp.A4.ggResI_type_A4 H e hA
    · exact GGResIDisp.A5.ggResI_type_A5 H e hA
    · exact GGResIDisp.A6.ggResI_type_A6 H e hA
    · exact GGResIDisp.A7.ggResI_type_A7 H e hA
  · have := hcard e
    have h3' : 3 ≤ n := by omega
    have h8' : n < 8 := by omega
    interval_cases n
    · exact GGResIDisp.B3.ggResI_type_B3 H e hB
    · exact GGResIDisp.B4.ggResI_type_B4 H e hB
    · exact GGResIDisp.B5.ggResI_type_B5 H e hB
    · exact GGResIDisp.B6.ggResI_type_B6 H e hB
    · exact GGResIDisp.B7.ggResI_type_B7 H e hB
  · have := hcard e
    have h3' : 3 ≤ n := by omega
    have h8' : n < 8 := by omega
    interval_cases n
    · exact GGResIDisp.C3.ggResI_type_C3 H e hC
    · exact GGResIDisp.C4.ggResI_type_C4 H e hC
    · exact GGResIDisp.C5.ggResI_type_C5 H e hC
    · exact GGResIDisp.C6.ggResI_type_C6 H e hC
    · exact GGResIDisp.C7.ggResI_type_C7 H e hC
  · have := hcard e
    have h8' : n < 8 := by omega
    interval_cases n
    · exact GGResIDisp.D4.ggResI_type_D4 H e hD
    · exact GGResIDisp.D5.ggResI_type_D5 H e hD
    · exact GGResIDisp.D6.ggResI_type_D6 H e hD
    · exact GGResIDisp.D7.ggResI_type_D7 H e hD
  · exact GGResIDisp.E6.ggResI_type_E6 H e hE6
  · exact GGResIDisp.E7.ggResI_type_E7 H e hE7
  · have := hcard e
    omega
  · exact GGResIDisp.F4.ggResI_type_F4 H e hF
  · refine GGResIDisp.F4.ggResI_type_F4 H (Fin.revPerm.trans e) fun i j => ?_
    simp only [Equiv.trans_apply, Fin.revPerm_apply]
    rw [hFt, ggResI_F₄_rev]
  · have := hcard e
    omega
  · have := hcard e
    omega

end CFSG.StandardType
