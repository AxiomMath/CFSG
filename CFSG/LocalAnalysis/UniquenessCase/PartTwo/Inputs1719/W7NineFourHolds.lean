module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W7NineOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W7NineFourOrbit
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFiveRel
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem w7_9_4_commutator_le {M I X L : Subgroup G} (hIM : I ≤ M)
    (hIn : (I.subgroupOf M).Normal) (hXI : S17.oUpperTwo X ≤ I) :
    ⁅Opp 2 (M ⊓ L), S17.oUpperTwo X⁆ ≤ I := by
  have hMn : M ≤ normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIM).mp hIn
  rw [Subgroup.commutator_le]
  intro k hk i hi
  have hkM : k ∈ M := ((F09.opp_le_self 2 (M ⊓ L)).trans inf_le_left) hk
  have hki : k * i * k⁻¹ ∈ I :=
    ((Subgroup.mem_normalizer_iff.mp (hMn hkM)) i).mp (hXI hi)
  exact I.mul_mem hki (I.inv_mem (hXI hi))

theorem w7_9_le_normalizer_of_asc81bHyp {X S L : Subgroup G}
    (hK : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L) :
    S ≤ normalizer (L : Set G) :=
  hL.le_normalizer
    (asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved G X S hK hA _
      hL.component)
    hA.twoRadical.1

theorem w7_9_4_ne_top {M H : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hHM : ¬ H ≤ M) (hHne : pCoreOf 2 H ≠ ⊥) : H ≠ ⊤ := by
  intro hHtop
  have hcore : pCoreOf 2 (⊤ : Subgroup G) ≠ ⊥ := by rwa [← hHtop]
  have hloc : IsTwoLocal (⊤ : Subgroup G) :=
    ⟨pCoreOf 2 ⊤, hcore, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤,
      (top_le_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤)).symm⟩
  have htop : (⊤ : Subgroup G) = M := hM.2 ⊤ hloc le_top
  exact hHM (by simpa [hHtop] using htop.le)

theorem w7_9_4c_holds : W7_9_4c := by
  intro G _ _ hsimple hchar hKp M I X Y L H hM hIM hIn hXM hXI heta hYM hY hYne hYcal hmax
    hYH hHM hHne hHLY hLc hc hnb
  refine ⟨?_, w7_9_4_commutator_le hIM hIn hXI⟩
  intro hcomm
  have hL : IsTwoPrimeComponent H L := isTwoPrimeComponent_of_perfectCore hLc hc
  have hLM : ¬ L ≤ M := by
    intro hLM
    exact hHM (hHLY ▸ sup_le hLM hYM)
  have hHtop : H ≠ ⊤ := w7_9_4_ne_top hM hHM hHne
  have hKH : CFSG.Open.IsKGroup ↥H := hKp.isKGroup H hHtop
  obtain ⟨hA, hinf⟩ :=
    w7_asc81bHyp hchar hIM hIn hXM heta hYM hY hYne hmax hYH hHM hHne
  have hS2 : IsPGroup 2 (pCoreOf 2 (H ⊓ M)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
  have hO2S : pCoreOf 2 H ≤ pCoreOf 2 (H ⊓ M) := hA.twoCore_le
  have hSN : H ⊓ M ≤ normalizer (pCoreOf 2 (H ⊓ M) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  have hYS : Y ≤ normalizer (pCoreOf 2 (H ⊓ M) : Set G) :=
    (le_inf hYH hYM).trans hSN
  have hN : normalizer (pCoreOf 2 Y : Set G) ≤ M :=
    w7_9_1_4_normalizer_pCore_le hIM hIn hXM heta hYM hY hYne hmax
  have hSleO2Y : pCoreOf 2 (H ⊓ M) ≤ pCoreOf 2 Y :=
    w7_9_1_4_le_pCore hYM hY hYne hN hmax hYH hHM hHne hA.twoRadical.1 hS2 hYS
  have hSL : pCoreOf 2 (H ⊓ M) ≤ normalizer (L : Set G) :=
    w7_9_le_normalizer_of_asc81bHyp hKH hA hL
  obtain ⟨P₁, hP₁syl, hP₁L, hP₁st⟩ := w7_9_exists_sylow_fixed hYM hY hYH hL hcomm
  have hP₁p : IsPGroup 2 P₁ := hP₁syl.2.1
  obtain ⟨W, hP₁W, hO2W, hW2, hWH, hYW, hWL⟩ :=
    w7_9_exists_orbit_pGroup hL hYH hP₁p hP₁L hP₁st
  have hO2YY : pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hWleO2Y : W ≤ pCoreOf 2 Y :=
    w7_9_1_4_le_pCore hYM hY hYne hN hmax hYH hHM hHne hWH hW2 hYW
  set U : Subgroup G := pCoreOf 2 (H ⊓ M) ⊔ W with hUdef
  have hUM : U ≤ M := by
    rw [hUdef]
    exact sup_le (hSleO2Y.trans (hO2YY.trans hYM))
      (hWleO2Y.trans (hO2YY.trans hYM))
  have hUH : U ≤ H := by rw [hUdef]; exact sup_le hA.twoRadical.1 hWH
  have hU2 : IsPGroup 2 U := by
    rw [hUdef]
    exact IsPGroup.to_sup_of_normal_right' hS2 hW2 (hSleO2Y.trans (hO2YY.trans hYW))
  have hYU : Y ≤ normalizer (U : Set G) := by
    rw [hUdef]
    exact (le_inf hYS hYW).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hO2HU : pCoreOf 2 H ≤ U := by rw [hUdef]; exact le_sup_of_le_left hO2S
  have hP₁U : P₁ ≤ U := hP₁W.trans le_sup_right
  have hU1 : U ≠ ⊥ := fun hbot => hHne (le_bot_iff.mp (hbot ▸ hO2HU))
  have hUL : U ≤ normalizer (L : Set G) := by rw [hUdef]; exact sup_le hSL hWL
  have hcalU : CFSG.LocalAnalysis.UniquenessCase.UC6.calCGS U ≤ M :=
    w7_9_1_5 hIM hIn hXM heta hYM hY hYne hmax hYH (by rw [hUdef]; exact le_sup_left)
      hUM hU2 hYU
  have hNC : ∀ C : Subgroup G, C ≤ U → C ≠ ⊥ → (C.subgroupOf U).Characteristic →
      normalizer (C : Set G) ≤ M := fun C hCU hC1 hCc =>
    (le_iSup_of_le C (le_iSup_of_le hC1 (le_iSup_of_le hCU
      (le_iSup (fun _ => normalizer (C : Set G)) hCc)))).trans hcalU
  have hNU : normalizer (U : Set G) ≤ M :=
    hNC U le_rfl hU1 (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hsyl : IsSylowTwoOf (U ⊓ L) L :=
    isSylowTwoOf_inf_of_normalizer_le hU2 hUL hNU hP₁syl hP₁U
  have hinX : CFSG.RankThree.PartOne.InClassX ↥L :=
    AscEightFive.inClassX_of_rel (M := M)
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
      hKH hA.charTwo hL hU2 hUH hO2HU hU1 hsyl hUM hLM hNC
  exact hnb ((CFSG.CGT.PushingUpLit.isBlockInX_subgroupOf_iff hL.le).mpr
    ⟨hL.le, hL.isSubnormal_subgroupOf, hinX⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
