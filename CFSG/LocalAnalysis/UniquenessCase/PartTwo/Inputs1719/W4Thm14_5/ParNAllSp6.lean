module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankThreeBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.LocalAnalysis.ComponentInitial

variable {W : Type} [CommGroup W] [Finite W]

theorem nParam_eq_of_natSp6 {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsSpn ↥H 6 k ∧ NatSpn H ⊤ ⊥ 6 k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hnat : IsNaturalClassicalModule H k :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  obtain ⟨-, -, -, -, -, -, -, -, -, hSp6, -⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  obtain ⟨-, K, _, _, hK, hreal⟩ := h.2
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [show (6 : ℕ) / 2 = 1 + 2 by norm_num] at hreal
  have hmodel : ∀ S' : Sylow 2 ↥H, ∃ φ : ↥(StatedSp (1 + 2) K) ≃* ↥H,
      (SymplecticFlag.unipotent (1 + 2) K).map φ.toMonoidHom = (S' : Subgroup ↥H) ∧
        KTabD.pointStab H S' =
          (KTabD.lineStab (StatedSp (1 + 2) K) (Pi.single (Sum.inl 0) 1)).map φ.toMonoidHom := by
    intro S'
    obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (1 + 2)
    have hUle : (U : Subgroup ↥(StatedSp (1 + 2) K)) ≤
        KTabD.lineStab (StatedSp (1 + 2) K) (Pi.single (Sum.inl 0) 1) := by
      rw [hU]
      exact KAdjE.unipotent_le_lineStab 1 K
    obtain ⟨φ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
      (KTabD.sylowFixedLine_statedSp (K := K) (1 + 2)) U hUle S'
    exact ⟨φ, hU ▸ h1, h2⟩
  obtain ⟨φ, hφU, hφP, Q, hparQ, hUQ, hQnot, hPQ⟩ :=
    exists_model_parabolic hS hmodel hBP hPH hPnot
  obtain ⟨I, hI, rfl⟩ := sp_eq_flagStabilizer_of_parabolic 1 hparQ hUQ hQnot
  have hI23 : Set.Icc 2 (1 + 2) = ({2, 3} : Set ℕ) := by
    ext i
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hres : Nonempty (Bar2 (Hinf P) ≃* Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K I))) :=
    nonempty_bar2_hinf_equiv_of_subgroupOf_eq_map hPH φ hPQ
  rw [hI23] at hI
  rcases Set.subset_pair_iff_eq.mp hI with rfl | rfl | rfl | rfl
  ·
    exfalso
    have htop : SymplecticHigher.flagStabilizer (1 + 2) K ∅ = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      rw [SymplecticHigher.mem_flagStabilizer]
      intro i hi
      exact absurd hi (Set.notMem_empty i)
    rw [htop, Subgroup.map_top_of_surjective _ φ.surjective] at hPQ
    have hPeq : P = H := le_antisymm hPH (Subgroup.subgroupOf_eq_top.mp hPQ)
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf (KOrdNat.kOrd_pCore_eq_bot hnat)
    obtain ⟨he, K', hK'f, hK'fin, hK', ⟨e⟩⟩ := h.1
    exact not_nParam_of_isSpn_six ⟨he, K', hK'f, hK'fin, hK', ⟨χ.trans e⟩⟩ hk hN
  ·
    obtain ⟨χ⟩ := hres
    obtain ⟨e⟩ := nonempty_bar2_hinf_spFlagStab_three_two hK4
    exact nParam_eq_of_mulEquiv_sl2_prod hk hK hN (χ.trans e)
  ·
    obtain ⟨χ⟩ := hres
    obtain ⟨e⟩ := nonempty_bar2_hinf_spFlagStab_three_three (K := K)
    exact nParam_eq_of_mulEquiv_sl3 hk hK hN (χ.trans e)
  ·
    have hα : SymplecticHigher.flagStabilizer (1 + 2) K {2, 3} =
        SymplecticHigher.flagStabilizer (1 + 2) K (Set.Icc 2 (1 + 2)) := by
      rw [hI23]
    obtain ⟨hpar, hSQ, hnot, hleast⟩ := KAdjE.leastParabolic_map φ hφU
      (KAdjE.isParabolicTwo_flagStabilizer_alpha 1 K) (KAdjE.unipotent_le_flagStabilizer_alpha 1 K)
      (KAdjE.not_flagStabilizer_alpha_le_lineStab 1 K)
      (fun P' hP' hU' hnot' => KAdjE.flagStabilizer_alpha_le_of_parabolic 1 hP' hU' hnot')
    rw [← hα, ← hPQ] at hpar hSQ hnot hleast
    rw [← hφP] at hnot hleast
    exact nParam_eq_of_least hS hPH hN hk hpar hSQ hnot hleast (hSp6 h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
