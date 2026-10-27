module

public import CFSG.RankThree.PartTwo.Sec15.Item15More
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.GF2n.QTwo
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS

theorem exists_maximal_twoLocal {G : Type} [Group G] [Finite G] (hG : TheoremFourHyp G)
    (hchar : CFSG.Assembly.IsCharTwoType G) {A N : Subgroup G}
    (hN : CFSG.Assembly.IsTwoLocal N) (hAN : A ≤ N) :
    ∃ M : Subgroup G, N ≤ M ∧ CFSG.IsMaximalTwoLocal M ∧ M ∈ scriptY2 A ∧
      generalizedFitting ↥M = CFSG.pCore 2 ↥M := by
  haveI : IsSimpleGroup G := hG.isSimpleGroup
  have hN' : CFSG.IsPLocal 2 N := hN
  obtain ⟨M, hNM, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hN'
  have hM1 : CFSG.IsPLocal 2 M := hM.1
  have hchar' : CFSG.IsCharacteristicPType G 2 := fun H hH =>
    CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hchar hH
  have hne : M ≠ ⊤ := CFSG.CGT.PushingUp.ne_top_of_isPLocal hG.nonabelian hM1
  have hpc : CFSG.Open.pCoreOf 2 M ≠ ⊥ := by
    intro h
    apply CFSG.CGT.PushingUp.pCore_ne_bot_of_isPLocal hM1
    unfold CFSG.Open.pCoreOf at h
    exact ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
  have hAM : A ≤ Subgroup.normalizer (M : Set G) :=
    (hAN.trans hNM).trans Subgroup.le_normalizer
  exact ⟨M, hNM, hM, ⟨⟨hne, hAM⟩, hpc⟩,
    CFSG.RankThree.GF2n.generalizedFitting_eq_pCore hchar' hM1⟩

theorem delta_le_normalizer_of_twoLocal {G : Type} [Group G] [Finite G] (hG : TheoremFourHyp G)
    (hchar : CFSG.Assembly.IsCharTwoType G) {A Y₀ X N : Subgroup G}
    (h152 : Item152 A (lB A)) (h155 : Item155 A (lB A)) (hY0 : scriptY0Star A (lB A) = {Y₀})
    (hX4 : X ∈ scriptY4 A (lB A)) (hXY : X ≤ Y₀) (hcov : Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hN : CFSG.Assembly.IsTwoLocal N) (hAN : A ≤ N) (hXN : X ≤ N) :
    delta A (lB A) N ≤ Subgroup.normalizer (Y₀ : Set G) := by
  obtain ⟨M, hNM, hMmax, hM2, hFstar⟩ := exists_maximal_twoLocal hG hchar hN hAN
  obtain ⟨X'', hX''L, hXX'', hX''0⟩ := h152 X hX4 M hM2 (hXN.trans hNM) hFstar
  have hX''M : X'' ≤ M := by
    obtain ⟨L, -, rfl⟩ := hX''L
    exact Subgroup.map_subtype_le L
  obtain ⟨Y', hX''Y', hY'max⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hX''0
  have hY'star : Y' ∈ scriptY0Star A (lB A) := hY'max
  rw [hY0] at hY'star
  have hY'eq : Y' = Y₀ := hY'star
  have hX''Y₀ : X'' ≤ Y₀ := hY'eq ▸ hX''Y'
  have hMY₀star : Y₀ ∈ scriptY0Star A (lB A) := by rw [hY0]; rfl
  have hres : oPrimeResidualOf 3 X'' = X'' := hX''0.1.2.1.symm
  have hX''3 : X'' ∈ scriptY3 A (lB A) := ⟨hX''0.2, hX''0.1.2.2.1⟩
  have h4 : oPrimeResidualOf 3 X'' ∈ scriptY4 A (lB A) := by rw [hres]; exact hX''0.1
  have hYeq : X'' = oPrimeResidualOf 3 X'' ⊔ CFSG.Open.pCoreOf 2 X'' := by
    rw [hres]
    exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 X'')).symm
  have hK : Y₀ ∈ gam155 A (lB A) X'' (oPrimeResidualOf 3 X'') :=
    ⟨hMY₀star, by rw [hres]; exact hX''Y₀, hX''Y₀.trans Subgroup.le_normalizer⟩
  have hKeq : Y₀ = oPrimeResidualOf 3 X'' ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    rw [hres]
    refine le_antisymm ?_ (sup_le hX''Y₀ (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀))
    calc Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀ := hcov
      _ ≤ X'' ⊔ CFSG.Open.pCoreOf 2 Y₀ := sup_le_sup_right hXX'' _
  have hMmem : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ X'' : Subgroup G) : Set G) :=
    ⟨hMmax, fun g hg => by
      have : A ⊔ X'' ≤ M := sup_le (hAN.trans hNM) hX''M
      exact this hg⟩
  exact (delta_mono hNM).trans
    ((h155 X'' hX''3 h4 hYeq).2 Y₀ hK (Or.inr hKeq) M hMmem)

end CFSG.RankThree.PartTwo.Sec17.PropU
