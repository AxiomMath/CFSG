module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Parabolic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Line
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Om6mBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer mem_isoStabilizer
  overgroupCuts unitary_Borel_overgroups normalizer_hypUnitriangular)
open CFSG.AGLEmbedding.LeviBlock (orthParab)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.UniquenessCase.UC22.OmegaMinus6Tail

theorem su4_eq_flagStabilizer_two_or_eq_top {a : ℕ} {K : Type} [Field K]
    (hF : UnitaryFieldData 2 a K) {P : Subgroup ↥(hypSU hF 2 0)}
    (hP : IsParabolicTwo ↥(hypSU hF 2 0) P) (hU : hypUnitriangular hF 2 0 ≤ P)
    (hnot : ¬ P ≤ parP hF) : P = flagStabilizer hF 2 0 {2} ∨ P = ⊤ := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' hF
  obtain ⟨U, hUeq⟩ := KAdjE.su4_exists_sylow_hypUnitriangular hF
  have hUP : (U : Subgroup ↥(hypSU hF 2 0)) ≤ P := by
    rw [hUeq]
    exact hU
  have hBP : hypBorel hF 2 0 ≤ P := by
    rw [← normalizer_hypUnitriangular hF (by norm_num) (by norm_num), ← hUeq]
    exact hP.normalizer_le U hUP
  obtain ⟨hI, hPI, -, -⟩ :=
    unitary_Borel_overgroups hF (by norm_num) (by norm_num) hc hc0 P hBP
  have h1I : (1 : ℕ) ∉ overgroupCuts 0 hF c hc P := by
    intro h1
    apply hnot
    rw [hPI]
    intro g hg
    exact mem_isoStabilizer.mpr ((UnitaryHigher.mem_flagStabilizer.mp hg) 1 h1)
  have hI2 : overgroupCuts 0 hF c hc P ⊆ {2} := by
    intro i hi
    have hine : i ≠ 1 := fun e => h1I (e ▸ hi)
    obtain ⟨hi1, hi2⟩ := hI hi
    rw [Set.mem_singleton_iff]
    omega
  rcases Set.subset_singleton_iff_eq.mp hI2 with h0 | h2
  · right
    rw [hPI, h0, eq_top_iff]
    intro g _
    rw [UnitaryHigher.mem_flagStabilizer]
    intro i hi
    exact absurd hi (Set.notMem_empty i)
  · left
    rw [hPI, h2]

theorem om6m_eq_orthParab_two_or_eq_top {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P : Subgroup ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hP : IsParabolicTwo ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) P)
    (hU : (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 2 (minusTailForm K b c))) ≤ P)
    (hnot : ¬ P ≤ orthParab 2 (minusTailForm K b c) ![0, 1]) :
    P = orthParab 2 (minusTailForm K b c) ![0, 2] ∨ P = ⊤ := by
  by_cases htop : P = ⊤
  · exact Or.inr htop
  · left
    have hB : T2B K b c ≤ P := by
      rw [T2B_eq_normalizer K b c hirr, ← t2Sylow_coe K b c hirr]
      exact hP.normalizer_le (t2Sylow K b c hirr) hU
    have hnot' : ¬ P ≤ T2Pℓ0 K b c := by
      simpa [KAdjE.om6m_orthParab_one_eq_T2Pℓ0] using hnot
    rw [KAdjE.om6m_orthParab_two_eq_T2P0 hirr]
    exact T2P0_eq_of_borel_le_of_ne_top_of_not_le_point K b c hirr hB htop hnot'

variable {W : Type} [CommGroup W] [Finite W]

theorem nParam_eq_of_natSU4 {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : ∃ a : ℕ, k = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a) (hk : 2 ≤ k)
    (hperf : ⁅H, H⁆ = H) (hS : IsSylowIn 2 S H)
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hnat : IsNaturalClassicalModule H k :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  obtain ⟨-, -, -, -, -, hSU4, -⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  have hline := hSU4 h
  obtain ⟨a, hka, hSU, K, _, _, hK, hreal⟩ := h
  have hF : UnitaryFieldData 2 a K := unitaryFieldDataOfCard hK
  obtain ⟨φ, hφU, hφP, Q, hparQ, hUQ, hQnot, hPQ⟩ :=
    exists_model_parabolic hS (KAdjE.su4_exists_mulEquiv_pointStab hF hreal) hBP hPH hPnot
  rcases su4_eq_flagStabilizer_two_or_eq_top hF hparQ hUQ hQnot with rfl | rfl
  · obtain ⟨hpar, hSQ, hnot, hleast⟩ := KAdjE.leastParabolic_map φ hφU
      (KAdjE.su4_isParabolicTwo_flagStabilizer_two hF)
      (KAdjE.su4_hypUnitriangular_le_flagStabilizer_two hF)
      (KAdjE.su4_not_flagStabilizer_two_le_parP hF)
      (fun P' hP' hU' hnot' => KAdjE.su4_flagStabilizer_two_le_of_parabolic hF hP' hU' hnot')
    rw [← hPQ] at hpar hSQ hnot hleast
    rw [← hφP] at hnot hleast
    exact nParam_eq_of_least hS hPH hN hk hpar hSQ hnot hleast hline
  · exfalso
    have hPeq : P = H := by
      refine le_antisymm hPH ?_
      rw [Subgroup.map_top_of_surjective _ φ.surjective] at hPQ
      exact Subgroup.subgroupOf_eq_top.mp hPQ
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf (KOrdNat.kOrd_pCore_eq_bot hnat)
    obtain ⟨K', hK'f, hK'fin, hK', ⟨e⟩⟩ := hSU
    exact not_nParam_of_isSUn_four ⟨K', hK'f, hK'fin, hK', ⟨χ.trans e⟩⟩ (by omega) hN

theorem nParam_eq_of_natOmegaMinusSix {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsOmegaMinus ↥H 6 k ∧ NatOmegaMinus H ⊤ ⊥ 6 k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hnat : IsNaturalClassicalModule H k :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  obtain ⟨-, -, -, -, -, -, hO6m, -⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  have hline := hO6m h
  obtain ⟨-, K, _, _, b, c, hK, hirr, hreal⟩ := h.2
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show (6 : ℕ) / 2 = 3 by norm_num] at hreal
  obtain ⟨φ, hφU, hφP, Q, hparQ, hUQ, hQnot, hPQ⟩ :=
    exists_model_parabolic hS (KAdjE.om6m_exists_mulEquiv_pointStab hirr hreal) hBP hPH hPnot
  rcases om6m_eq_orthParab_two_or_eq_top hirr hparQ hUQ hQnot with rfl | rfl
  · obtain ⟨hpar, hSQ, hnot, hleast⟩ := KAdjE.leastParabolic_map φ hφU
      (KAdjE.om6m_isParabolicTwo_orthParab_two hirr)
      ((KAdjE.om6m_tailUnipotent_le_orthParab hirr).trans inf_le_right)
      (KAdjE.om6m_not_orthParab_two_le_one hirr)
      (fun _ hP' hU' hnot' => KAdjE.om6m_orthParab_two_le_of_parabolic hirr hP' hU' hnot')
    rw [← hPQ] at hpar hSQ hnot hleast
    rw [← hφP] at hnot hleast
    exact nParam_eq_of_least hS hPH hN hk hpar hSQ hnot hleast hline
  · exfalso
    have hPeq : P = H := by
      refine le_antisymm hPH ?_
      rw [Subgroup.map_top_of_surjective _ φ.surjective] at hPQ
      exact Subgroup.subgroupOf_eq_top.mp hPQ
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf (KOrdNat.kOrd_pCore_eq_bot hnat)
    obtain ⟨he, K', hK'f, hK'fin, b', c', hK', hirr', ⟨e⟩⟩ := h.1
    exact not_nParam_of_isOmegaMinus_six ⟨he, K', hK'f, hK'fin, b', c', hK', hirr', ⟨χ.trans e⟩⟩
      (by omega) hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
