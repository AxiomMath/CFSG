module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaFork
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6ThreeAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggTorusFork_of_e6ThreeModel {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGE6ThreeModelSCr R I) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup 3 5 R I L' ψ A → GGTorusFork 3 A := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, h5, -, hsc⟩ := hA
  obtain ⟨Φ, T, w, hd⟩ := (h L' ψ hψ hker hperf A hAe hAI h5 hsc).exists_data
  obtain ⟨x31, hx31, hn31⟩ := ggNE3_move_31
  obtain ⟨x32, hx32, hn32⟩ := ggNE3_move_32
  obtain ⟨x34, hx34, hn34⟩ := ggNE3_move_34
  obtain ⟨x12, hx12, hn12⟩ := ggNE3_move_12
  obtain ⟨x14, hx14, hn14⟩ := ggNE3_move_14
  obtain ⟨x24, hx24, hn24⟩ := ggNE3_move_24
  refine ⟨hd.conjAut (3 : Fin 6), hd.conjAut_mem_ggTorusReflSet (3 : Fin 6),
    hd.conjAut (1 : Fin 6), hd.conjAut_mem_ggTorusReflSet (1 : Fin 6),
    hd.conjAut (2 : Fin 6), hd.conjAut_mem_ggTorusReflSet (2 : Fin 6),
    hd.conjAut (4 : Fin 6), hd.conjAut_mem_ggTorusReflSet (4 : Fin 6), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact orderOf_eq_prime (p := 3) (ggNE3_pair_pow_eq_one hd 3 1 3 ggNE3_cube_31)
      (ggNE3_pair_ne_one hd 3 1 x31 hx31 hn31)
  · exact orderOf_eq_prime (p := 3) (ggNE3_pair_pow_eq_one hd 3 2 3 ggNE3_cube_32)
      (ggNE3_pair_ne_one hd 3 2 x32 hx32 hn32)
  · exact orderOf_eq_prime (p := 3) (ggNE3_pair_pow_eq_one hd 3 4 3 ggNE3_cube_34)
      (ggNE3_pair_ne_one hd 3 4 x34 hx34 hn34)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 1 2 2 ggNE3_sq_12)
      (ggNE3_pair_ne_one hd 1 2 x12 hx12 hn12)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 1 4 2 ggNE3_sq_14)
      (ggNE3_pair_ne_one hd 1 4 x14 hx14 hn14)
  · exact orderOf_eq_prime (p := 2) (ggNE3_pair_pow_eq_one hd 2 4 2 ggNE3_sq_24)
      (ggNE3_pair_ne_one hd 2 4 x24 hx24 hn24)

theorem ggRowForkAt_ETwE6_three
    : GGRowForkAt (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) 5 := by
  intro p hp hp2 lab hlab hS
  obtain ⟨hrow, rfl⟩ := hS
  refine TwE6Delta.labelAll hrow.1 fun K _ _ hK => ?_
  exact ggTorusFork_of_e6ThreeModel (E6ThreeModel.e6ThreeModel_holds.2 K lab.n hlab.1 hK hrow.2)

end CFSG.StandardType

end
