module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankThreeBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W] [Finite W]

theorem nParam_eq_of_natSL4 {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsSLn ↥H 4 k ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 4 k) (hk : 2 ≤ k)
    (hperf : ⁅H, H⁆ = H) (hS : IsSylowIn 2 S H)
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hnat : IsNaturalClassicalModule H k :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  obtain ⟨-, -, -, -, -, -, -, hSL4, -⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  obtain ⟨K, _, _, hK, hreal⟩ := h.2
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hmodel : ∀ S' : Sylow 2 ↥H, ∃ φ : ↥(StatedSL 4 K) ≃* ↥H,
      (KAdjE.slU 4 K).map φ.toMonoidHom = (S' : Subgroup ↥H) ∧
        KTabD.pointStab H S' = (KAdjE.slQZero 4 K).map φ.toMonoidHom := by
    intro S'
    obtain ⟨U, hU⟩ := KAdjE.exists_sylow_slU (k := 4) (K := K) (by norm_num)
    obtain ⟨φ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
      (KTabD.sylowFixedLine_statedSL (K := K) (d := 4) (by norm_num)) U
      (hU ▸ KAdjE.slU_le_slQZero) S'
    exact ⟨φ, hU ▸ h1, h2⟩
  obtain ⟨φ, hφU, hφP, Q, hparQ, hUQ, hQnot, hPQ⟩ :=
    exists_model_parabolic hS hmodel hBP hPH hPnot
  obtain ⟨I, hI, rfl⟩ := sl_eq_map_flagStabilizer_of_parabolic (by norm_num) hparQ hUQ hQnot
  have hcuts : KAdjE.slAlphaCuts 4 = {2, 3} := by
    ext i
    simp only [KAdjE.slAlphaCuts, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hres : Nonempty (Bar2 (Hinf P) ≃* Bar2 (Hinf (LinearFlag.flagStabilizer 4 K I))) := by
    obtain ⟨χ₁⟩ := nonempty_bar2_hinf_equiv_of_subgroupOf_eq_map hPH φ hPQ
    obtain ⟨χ₂⟩ := nonempty_bar2_hinf_map_mulEquiv (specialLinearGroupEquivStatedSL 4 K)
      (LinearFlag.flagStabilizer 4 K I)
    exact ⟨χ₁.trans χ₂⟩
  rw [hcuts] at hI
  rcases Set.subset_pair_iff_eq.mp hI with rfl | rfl | rfl | rfl
  ·
    exfalso
    have htop : (LinearFlag.flagStabilizer 4 K ∅).map
        (specialLinearGroupEquivStatedSL 4 K).toMonoidHom = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      exact ⟨(specialLinearGroupEquivStatedSL 4 K).symm x,
        LinearFlag.mem_flagStabilizer.mpr fun i hi => absurd hi (Set.notMem_empty i), by simp⟩
    rw [htop, Subgroup.map_top_of_surjective _ φ.surjective] at hPQ
    have hPeq : P = H := le_antisymm hPH (Subgroup.subgroupOf_eq_top.mp hPQ)
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf (KOrdNat.kOrd_pCore_eq_bot hnat)
    obtain ⟨K', hK'f, hK'fin, hK', ⟨e⟩⟩ := h.1
    exact not_nParam_of_isSLn_four ⟨K', hK'f, hK'fin, hK', ⟨χ.trans e⟩⟩ hk hN
  ·
    obtain ⟨χ⟩ := hres
    obtain ⟨e⟩ := nonempty_bar2_hinf_slFlagStab_four_two hK4
    exact nParam_eq_of_mulEquiv_sl2_prod hk hK hN (χ.trans e)
  ·
    obtain ⟨χ⟩ := hres
    obtain ⟨e⟩ := nonempty_bar2_hinf_slFlagStab_four_three (K := K)
    exact nParam_eq_of_mulEquiv_sl3 hk hK hN (χ.trans e)
  ·
    have hα : (LinearFlag.flagStabilizer 4 K {2, 3}).map
        (specialLinearGroupEquivStatedSL 4 K).toMonoidHom = KAdjE.slQAlpha 4 K := by
      unfold KAdjE.slQAlpha
      rw [hcuts]
    rw [hα] at hPQ
    obtain ⟨hpar, hSQ, hnot, hleast⟩ := KAdjE.leastParabolic_map φ hφU
      (KAdjE.isParabolicTwo_slQAlpha (by norm_num)) (KAdjE.slU_le_slQAlpha 4 K)
      (KAdjE.not_slQAlpha_le_slQZero (by norm_num))
      (fun P' hP' hU' hnot' => KAdjE.slQAlpha_le_of_parabolic (by norm_num) hP' hU' hnot')
    rw [← hPQ] at hpar hSQ hnot hleast
    rw [← hφP] at hnot hleast
    exact nParam_eq_of_least hS hPH hN hk hpar hSQ hnot hleast (hSL4 h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
