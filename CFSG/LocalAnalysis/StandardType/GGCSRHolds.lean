module

public import CFSG.Assembly.GL83StatedBridge
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.RankPSL
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGCSRBasic
public import CFSG.LocalAnalysis.StandardType.GGCSRLabels
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.LinCover
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Linear
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggSmallThreeRank_of_labels :
    GGSmallThreeRank := by
  intro lab hlab htag
  refine ggCSR_of_lib ?_
  rcases htag with ht | ht | ht | ht | ht | ht | ht
  · exact ggCSR_G2 hlab ht
  · exact ggCSR_triD4 hlab ht
  · exact ggCSR_twB2 hlab ht
  · exact ggCSR_twF4 hlab ht
  · exact ggCSR_B2der hlab ht
  · exact ggCSR_G2der hlab ht
  · exact ggCSR_twF4der hlab ht

section Certificates


theorem ggSmallThreeRank_not_small_of_elemAbelian
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (H ⧸ Subgroup.center H))
    {E : Subgroup (H ⧸ Subgroup.center H)} (hEa : IsElemAbelian 3 E)
    (hcard : 27 ≤ Nat.card E) :
    ¬ (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) := by
  intro htag
  have hAll := ggSmallThreeRank_of_labels lab hlab htag
  have hraw : LargeEvenRawDatum lab
      (fun R _ I F => Nonempty (H ⧸ Subgroup.center H ≃* R) ∧ LargeEvenInnSet R ⊆ I) :=
    largeEvenRawDatum_inn_all hhas
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  obtain ⟨he, hInn⟩ := hQ.1
  have hBound := hQ.2
  obtain ⟨e⟩ := he
  let ρ : H ⧸ Subgroup.center H →* MulAut R :=
    (MulAut.conj : R →* MulAut R).comp e.toMonoidHom
  have hZR : Subgroup.center R = ⊥ := by
    rw [← Subgroup.map_center_eq e, Group.IsPerfect.center_quotient_center_eq_bot H,
      Subgroup.map_bot]
  have hconj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    exact (MonoidHom.ker_eq_bot_iff _).mp (by
      rw [CFSG.GroupTheory.ker_conj_eq_center, hZR])
  have hρ : Function.Injective ρ := by
    intro x y hxy
    exact e.injective (hconj (show MulAut.conj (e x) = MulAut.conj (e y) from hxy))
  have hcardA : Nat.card (E.map ρ) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) (f := ρ) hρ
  have hAI : ∀ a ∈ E.map ρ, a ∈ I := by
    rintro _ ⟨x, -, rfl⟩
    exact hInn ⟨e x, rfl⟩
  have hAea : IsElemAbelian 3 (E.map ρ) := hEa.map ρ
  have hle := hBound (E.map ρ) hAI hAea
  rw [hcardA] at hle
  norm_num at hcard hle
  omega

end Certificates

theorem not_ggHasLabel_of_elemAbelian_of_labelAll_bound
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {lab : LargeEvenLabel} (hhas : GGHasLabel lab (H ⧸ Subgroup.center H))
    {p : ℕ}
    (hall : LargeEvenLabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E < p ^ 3)
    {E : Subgroup (H ⧸ Subgroup.center H)} (hEa : IsElemAbelian p E)
    (hcard : p ^ 3 ≤ Nat.card E) : False := by
  have hraw : LargeEvenRawDatum lab
      (fun R _ I F => Nonempty (H ⧸ Subgroup.center H ≃* R) ∧ LargeEvenInnSet R ⊆ I) :=
    largeEvenRawDatum_inn_all hhas
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists (hall _ hraw)
  obtain ⟨he, hInn⟩ := hQ.1
  have hBound := hQ.2
  obtain ⟨e⟩ := he
  let ρ : H ⧸ Subgroup.center H →* MulAut R :=
    (MulAut.conj : R →* MulAut R).comp e.toMonoidHom
  have hZR : Subgroup.center R = ⊥ := by
    rw [← Subgroup.map_center_eq e, Group.IsPerfect.center_quotient_center_eq_bot H,
      Subgroup.map_bot]
  have hconj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    exact (MonoidHom.ker_eq_bot_iff _).mp (by
      rw [CFSG.GroupTheory.ker_conj_eq_center, hZR])
  have hρ : Function.Injective ρ := by
    intro x y hxy
    exact e.injective (hconj (show MulAut.conj (e x) = MulAut.conj (e y) from hxy))
  have hcardA : Nat.card (E.map ρ) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) (f := ρ) hρ
  have hAI : ∀ a ∈ E.map ρ, a ∈ I := by
    rintro _ ⟨x, -, rfl⟩
    exact hInn ⟨e x, rfl⟩
  have hAea : IsElemAbelian p (E.map ρ) := hEa.map ρ
  have hle := hBound (E.map ρ) hAI hAea
  rw [hcardA] at hle
  exact absurd hle (not_lt.mpr hcard)

section LinearLowRank

open CFSG.Open
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem ggSmallThreeRank_linear_rank_three_of_elemAbelian
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (H ⧸ Subgroup.center H))
    {E : Subgroup (H ⧸ Subgroup.center H)} (hEa : IsElemAbelian 3 E)
    (hcard : 27 ≤ Nat.card E)
    (htag : lab.tag = .A ∨ lab.tag = .twA) : 3 ≤ lab.rank := by
  obtain ⟨t, l, n⟩ := lab
  by_contra hle
  change ¬ 3 ≤ l at hle
  have hl2 : l ≤ 2 := by omega
  change t = .A ∨ t = .twA at htag
  rcases htag with hA | htwA
  · subst hA
    dsimp only [LargeEvenInLambda2] at hlab
    dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
    obtain ⟨K, _, _, hK, hQ⟩ := hhas
    obtain ⟨e⟩ := hQ
    haveI : Fintype K := Fintype.ofFinite K
    have hcardK : Fintype.card K = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) hcardK
    have h3K : ((3 : ℕ) : K) ≠ 0 := by
      intro hzero
      have h2dvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp hzero
      norm_num at h2dvd
    have eR : LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) K) ≃*
        StatedProj (StatedSL (l + 1) K) := by
      rw [largeEvenSLGroup_eq_statedSL]
    let e' : H ⧸ Subgroup.center H ≃* StatedProj (StatedSL (l + 1) K) := e.trans eR
    have hEa' : IsElemAbelian 3 (E.map e'.toMonoidHom) := hEa.map e'.toMonoidHom
    have hbound := CFSG.HardMathSupport.Malle.E27Lie.card_le_of_statedProj_SL
      (F := K) (n := l + 1) h3K (by omega) (E.map e'.toMonoidHom) hEa'
    have hcardmap : Nat.card (E.map e'.toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (K := E) (f := e'.toMonoidHom) e'.injective
    rw [hcardmap] at hbound
    have hpow : 3 ^ (l + 1 - 1) ≤ 3 ^ 2 := by
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h9 : Nat.card E ≤ 9 := le_trans hbound (by simpa using hpow)
    omega
  · subst htwA
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, hl_lower, hn2⟩ := hlab
    have hl : l = 2 := by omega
    subst hl
    have hn2' : 2 ≤ n := hn2 rfl
    dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
    obtain ⟨K, _, _, hK, hQ⟩ := hhas
    obtain ⟨e⟩ := hQ
    have hU : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK (by omega)
    haveI : CharP K 2 := hU.charP
    have h3K : ((3 : ℕ) : K) ≠ 0 := by
      intro hzero
      have h2dvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff K 2 3).mp hzero
      norm_num at h2dvd
    let eU : H ⧸ Subgroup.center H ≃* StatedProj (StatedSU 3 (2 ^ n) K) := e
    let e' : H ⧸ Subgroup.center H ≃* unitaryPSU hU 3 :=
      eU.trans (unitaryPSUEquiv hU (by norm_num : 1 ≤ 3)).symm
    let A : Subgroup (unitaryPSU hU 3) := E.map e'.toMonoidHom
    have hA : IsElemAbelian 3 A := hEa.map e'.toMonoidHom
    let F : Subgroup (MulAut (unitaryPSU hU 3)) :=
      A.map (MulAut.conj : unitaryPSU hU 3 →* MulAut (unitaryPSU hU 3))
    have hF : IsElemAbelian 3 F := hA.map _
    have hFi : F ≤ (MulAut.conj : unitaryPSU hU 3 →* MulAut (unitaryPSU hU 3)).range := by
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
    have hq : 2 < 2 ^ n := by
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2'
      norm_num at h4
      omega
    have hZ : Subgroup.center (unitaryPSU hU 3) = ⊥ :=
      CFSG.RankThree.PartTwo.KFacts.center_unitaryPSU_three_eq_bot hU hq
    have hconj : Function.Injective
        (MulAut.conj : unitaryPSU hU 3 →* MulAut (unitaryPSU hU 3)) := by
      exact (MonoidHom.ker_eq_bot_iff _).mp (by
        rw [CFSG.GroupTheory.ker_conj_eq_center, hZ])
    have hcardF : Nat.card F = Nat.card E := by
      rw [show Nat.card F = Nat.card A from Subgroup.card_map_of_injective
        (K := A) (f := (MulAut.conj : unitaryPSU hU 3 →* MulAut (unitaryPSU hU 3))) hconj]
      exact Subgroup.card_map_of_injective (K := E) (f := e'.toMonoidHom) e'.injective
    have hbound := CFSG.RankThree.PartTwo.Sec21.Item223CensusProof.card_le_nine_inner_unitaryPSU
      (h := hU) h3K F hF hFi
    rw [hcardF] at hbound
    omega

end LinearLowRank

end CFSG.StandardType

end
