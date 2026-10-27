module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenProof
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortClauses
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusCent
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.D1Frontier
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.RestOrth
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusCent
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusFinal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput (orthPlusLeviOb orthPlusCentOb
  orthMinusLeviOb lieInputRest_of_orth_nodes)

variable {G : Type} [Group G] [Finite G]

section Certificates


variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G}
  {r : ℕ} {Y N Dsub H S : Subgroup G}

theorem p19_16_of_nineThreeFour (h85 : CFSG.AGLEmbedding.Asc81bEightFive)
    (hC : K_19_16_census) (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h15 : R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (h4 : CFSG.AGLEmbedding.NineThreeFour H S Dsub) : P19_16 D Dsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := ctx19_14_isKGroup h
  have hhyp := ctx19_14_asc81bHyp h h11
  have hK := ctx19_14_isWeakSBlock h h11
  obtain ⟨-, hZ, ⟨e⟩, -, -⟩ := h4
  have hcl : CFSG.AGLEmbedding.IsClassicalTwoOrG2
      (↥(CFSG.AGLEmbedding.barM H Dsub) ⧸
        Subgroup.center ↥(CFSG.AGLEmbedding.barM H Dsub)) :=
    Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl), ⟨e⟩⟩)
  have h89 := CFSG.HardMathSupport.Cooperstein.StructureLie.eightNine_of_nonParabolic
    (CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.eightNineNonParabolic_of_lieInputRest
      (lieInputRest_of_orth_nodes orthPlusLeviOb orthPlusCentOb orthMinusLeviOb
        CFSG.HardMathSupport.Cooperstein.StructureLie.orthMinusCentOb_proved))
  rcases h89 G H S Dsub hX hhyp hK hcl with h2 | hx | hstar
  · exact p19_16_of_nineThreeTwo h85 hC h h11 h15 h2
  · exact (ctx19_14_not_inClassXBlock h h15 hx).elim
  · have ht := CFSG.HardMathSupport.Cooperstein.StructureLie.eightEightTransvection
      G H S Dsub hX hhyp hK hcl hstar
    have hQV := CFSG.HardMathSupport.Cooperstein.StructureLie.commutator_pCore_le_blockV
      hX hhyp hK ht
    exact (CFSG.HardMathSupport.Cooperstein.StructureLie.card_center_barM_ne_three
      hX hhyp hK ht hQV hZ).elim

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
