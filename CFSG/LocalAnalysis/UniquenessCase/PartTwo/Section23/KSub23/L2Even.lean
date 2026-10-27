module

import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal
import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsSL
import CFSG.Walter.FinalNative
import CFSG.GH74.Uniqueness.Bender.Dickson
import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
import CFSG.Quasithin.Recognition.St84.L2Group
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
import CFSG.Adapters.StatedPSLTwo
import CFSG.Quasithin.Vol2.Ch7Bridge326
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open CFSG.BenderSuzuki.MatrixGroups

private theorem card_galoisField_two_le_three_of_le_one {m : ℕ} (hm : m ≤ 1) :
    Nat.card (GaloisField 2 m) ≤ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  interval_cases m
  · rw [CFSG.CGT.PushingUpLit.BHS.natCard_galoisField_two_zero]
    norm_num
  · rw [GaloisField.card 2 1 one_ne_zero, pow_one]
    norm_num

private theorem nonsolvable_alt_or_isL2 {F : Type} [Field F]
    [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ a) (H : Subgroup (PSL2MatrixGroup F))
    (hns : ¬ Group.IsSolvable ↥H) :
    Nonempty (↥H ≃* alternatingGroup (Fin 5)) ∨
      ∃ b : ℕ, 2 ≤ b ∧ b ∣ a ∧ IsL2 ↥H b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.GH74.GLS.IVK.Lifted.psl2_subgroup_dichotomy (p := 2) (f := a) hF H with
    hs | hA5 | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · exact absurd hs hns
  · exact Or.inl hA5
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · haveI : Group.IsSolvable (PSL2MatrixGroup (GaloisField 2 m)) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_psl2_of_card_le_three
          (card_galoisField_two_le_three_of_le_one (by omega))
      exact absurd (CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_mulEquiv_lifted e) hns
    · refine Or.inr ⟨m, hm2, hm, ?_⟩
      exact CFSG.Walter.blueprintLieModel_psl_two_of_mulEquiv 2 m (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2) e
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · haveI : Group.IsSolvable (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_pgl2_of_card_le_three
          (card_galoisField_two_le_three_of_le_one (by omega))
      exact absurd (CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_mulEquiv_lifted e) hns
    · obtain ⟨ePGL⟩ := CFSG.GH74.Uniqueness.Bender.nonempty_pgl2_mulEquiv_psl2 m (by omega)
      have hm_dvd : m ∣ a := by
        obtain ⟨c, hc⟩ := hm
        exact ⟨2 * c, by rw [hc]; ring⟩
      refine Or.inr ⟨m, hm2, hm_dvd, ?_⟩
      exact CFSG.Walter.blueprintLieModel_psl_two_of_mulEquiv 2 m (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2) (e.trans ePGL)

theorem isAlt_or_isL2_of_isL2 {S : Type} [Group S] [Finite S]
    {a : ℕ} (hS : IsL2 S a) (Y : Subgroup S) (hY : ⁅Y, Y⁆ = Y) (hne : Y ≠ ⊥) :
    IsAlt ↥Y 5 ∨ ∃ b : ℕ, b ∣ a ∧ IsL2 ↥Y b := by
  obtain ⟨eS⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel hS
  obtain ⟨ha1, -⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23.card_isL2 hS
  have hF : Nat.card (GaloisField 2 a) = 2 ^ a := GaloisField.card 2 a (by omega)
  let H : Subgroup (PSL2MatrixGroup (GaloisField 2 a)) := Y.map eS.toMonoidHom
  have hHns : ¬ Group.IsSolvable ↥H := by
    intro hs
    have hYsolv : Group.IsSolvable ↥Y :=
      @Group.isSolvable_of_surjective ↥(Y.map eS.toMonoidHom) ↥Y _ _
        (eS.subgroupMap Y).symm.toMonoidHom (eS.subgroupMap Y).symm.surjective hs
    haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hne
    haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
    exact Group.IsPerfect.not_isSolvable ↥Y hYsolv
  rcases nonsolvable_alt_or_isL2 hF H hHns with hA5 | ⟨b, -, hba, hL2⟩
  · left
    obtain ⟨e5⟩ := hA5
    exact ⟨(eS.subgroupMap Y).trans e5⟩
  · right
    refine ⟨b, hba, ?_⟩
    have hL2' : CFSG.Blueprint.LieModel ↥H .PSL 2 2 b := hL2
    exact CFSG.Blueprint.LieModel.of_mulEquiv (eS.subgroupMap Y).symm hL2'

theorem eq_bot_or_isSimpleGroup_of_isL2 {S : Type} [Group S]
    [Finite S] {a : ℕ} (hS : IsL2 S a) (Y : Subgroup S) (hY : ⁅Y, Y⁆ = Y) :
    Y = ⊥ ∨ IsSimpleGroup ↥Y := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  · right
    rcases isAlt_or_isL2_of_isL2 hS Y hY hbot with hA5 | ⟨b, hba, hL2⟩
    · change Nonempty (↥Y ≃* alternatingGroup (Fin 5)) at hA5
      obtain ⟨e5⟩ := hA5
      haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup_five
      exact e5.isSimpleGroup
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2

private theorem eq_top_of_isAlt_of_card_dvd {F : Type} [Field F]
    [Finite F] {a : ℕ} (ha2 : 2 ≤ a) (H : Subgroup (PSL2MatrixGroup F))
    (hA5 : Nonempty (↥H ≃* alternatingGroup (Fin 5)))
    (hdiv : 2 ^ a ∣ Nat.card ↥H)
    (hMcard : Nat.card (PSL2MatrixGroup F) = 2 ^ a * ((2 ^ a) ^ 2 - 1)) :
    H = ⊤ := by
  obtain ⟨e5⟩ := hA5
  have hH60 : Nat.card ↥H = 60 := by
    rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have hdvd60 : 2 ^ a ∣ 60 := by
    rw [hH60] at hdiv
    exact hdiv
  have hale : a ≤ 2 := by
    have hodd : Odd (15 : ℕ) := by norm_num
    have hcop : Nat.Coprime (2 ^ a) 15 := (Nat.coprime_two_left.mpr hodd).pow_left a
    have h2 : 2 ^ a ∣ 2 ^ 2 := by
      have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
      rw [h60] at hdvd60
      exact hcop.dvd_of_dvd_mul_right hdvd60
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2
  have haeq : a = 2 := by omega
  have hM60 : Nat.card (PSL2MatrixGroup F) = 60 := by
    rw [hMcard, haeq]
    norm_num
  exact Subgroup.eq_top_of_card_eq H (by rw [hH60, hM60])

private theorem eq_top_of_isL2_of_card_dvd {F : Type} [Field F]
    [Finite F] {a : ℕ} (ha1 : 1 ≤ a) (H : Subgroup (PSL2MatrixGroup F)) {b : ℕ}
    (hb2 : 2 ≤ b) (hba : b ∣ a) (hL2 : IsL2 ↥H b) (hdiv : 2 ^ a ∣ Nat.card ↥H)
    (hMcard : Nat.card (PSL2MatrixGroup F) = 2 ^ a * ((2 ^ a) ^ 2 - 1)) :
    H = ⊤ := by
  have hHcard : Nat.card ↥H = 2 ^ b * ((2 ^ b) ^ 2 - 1) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23.card_isL2 hL2).2
  have hodd : Odd ((2 ^ b) ^ 2 - 1) := by
    simpa using CFSG.Timmesfeld.Orders.odd_pow_sub_one (f := b) (a := 2)
      (by omega) (by norm_num)
  have hcop : Nat.Coprime (2 ^ a) ((2 ^ b) ^ 2 - 1) :=
    (Nat.coprime_two_left.mpr hodd).pow_left a
  have hdvd : 2 ^ a ∣ 2 ^ b * ((2 ^ b) ^ 2 - 1) := by
    rw [← hHcard]
    exact hdiv
  have hab : a ≤ b :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hcop.dvd_of_dvd_mul_right hdvd)
  have hba' : b ≤ a := Nat.le_of_dvd (by omega) hba
  have hbeq : b = a := le_antisymm hba' hab
  have hMcard' : Nat.card (PSL2MatrixGroup F) = 2 ^ b * ((2 ^ b) ^ 2 - 1) := by
    rw [hMcard, hbeq]
  exact Subgroup.eq_top_of_card_eq H (by rw [hHcard, hMcard'])

private theorem eq_top_of_nonsolvable {F : Type} [Field F]
    [Finite F] {a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 ≤ a) (hF : Nat.card F = 2 ^ a)
    (H : Subgroup (PSL2MatrixGroup F)) (hns : ¬ Group.IsSolvable ↥H)
    (hdiv : 2 ^ a ∣ Nat.card ↥H)
    (hMcard : Nat.card (PSL2MatrixGroup F) = 2 ^ a * ((2 ^ a) ^ 2 - 1)) :
    H = ⊤ := by
  rcases nonsolvable_alt_or_isL2 hF H hns with hA5 | ⟨b, hb2, hba, hL2⟩
  · exact eq_top_of_isAlt_of_card_dvd ha2 H hA5 hdiv hMcard
  · exact eq_top_of_isL2_of_card_dvd ha1 H hb2 hba hL2 hdiv hMcard

theorem eq_top_of_sylow_le_normalizer_of_isL2 {S : Type} [Group S]
    [Finite S] {a : ℕ} (hS : IsL2 S a) (Y : Subgroup S) (hY : ⁅Y, Y⁆ = Y) (hne : Y ≠ ⊥)
    (T : Sylow 2 S) (hT : ∀ t : T, (t : S) ∈ normalizer (Y : Set S)) : Y = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eS⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel hS
  obtain ⟨ha1, hScard⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23.card_isL2 hS
  have hF : Nat.card (GaloisField 2 a) = 2 ^ a := GaloisField.card 2 a (by omega)
  let H : Subgroup S := Y ⊔ (T : Subgroup S)
  have hYleH : Y ≤ H := le_sup_left
  have hTleH : (T : Subgroup S) ≤ H := le_sup_right
  have hHleNorm : H ≤ Subgroup.normalizer (Y : Set S) := by
    refine sup_le Subgroup.le_normalizer ?_
    intro t ht
    exact hT ⟨t, ht⟩
  have hHns : ¬ Group.IsSolvable ↥H := by
    intro hs
    haveI : Group.IsSolvable ↥H := hs
    have hYsolv : Group.IsSolvable ↥Y :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion hYleH) (Subgroup.inclusion_injective hYleH)
    haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hne
    haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
    exact Group.IsPerfect.not_isSolvable ↥Y hYsolv
  let Hbar : Subgroup (PSL2MatrixGroup (GaloisField 2 a)) := H.map eS.toMonoidHom
  have hHbarCard : Nat.card ↥H = Nat.card ↥Hbar :=
    Nat.card_congr (eS.subgroupMap H).toEquiv
  have hHbarNs : ¬ Group.IsSolvable ↥Hbar := by
    intro hs
    exact hHns (@Group.isSolvable_of_isSolvable_injective ↥H
      ↥(H.map eS.toMonoidHom) _ _ (eS.subgroupMap H).toMonoidHom
      (eS.subgroupMap H).injective hs)
  have hTcard : Nat.card (T : Subgroup S) = 2 ^ a := by
    let T' : Sylow 2 (PSL2MatrixGroup (GaloisField 2 a)) :=
      Sylow.mapSurjective (f := eS.toMonoidHom) eS.surjective T
    have hT' : (T' : Subgroup (PSL2MatrixGroup (GaloisField 2 a))) =
        (T : Subgroup S).map eS.toMonoidHom :=
      Sylow.coe_mapSurjective (f := eS.toMonoidHom) eS.surjective T
    rw [Nat.card_congr (eS.subgroupMap (T : Subgroup S)).toEquiv]
    exact hT' ▸ CFSG.Quasithin.St84.psl2_sylow_two_card (by omega) T'
  have hdiv : 2 ^ a ∣ Nat.card ↥Hbar := by
    rw [← hHbarCard, ← hTcard]
    exact Subgroup.card_dvd_of_le hTleH
  have hMcard : Nat.card (PSL2MatrixGroup (GaloisField 2 a)) =
      2 ^ a * ((2 ^ a) ^ 2 - 1) := by
    rw [← Nat.card_congr eS.toEquiv, hScard]
  have hHbarTop : Hbar = ⊤ :=
    eq_top_of_nonsolvable ha1 (CFSG.Quasithin.H13.two_le_of_lieModel_psl_two hS)
      hF Hbar hHbarNs hdiv hMcard
  have hHtop : H = ⊤ := by
    apply Subgroup.map_injective (f := eS.toMonoidHom) eS.injective
    rw [Subgroup.map_top]
    simpa [Hbar] using hHbarTop
  have hnorm : Subgroup.normalizer (Y : Set S) = ⊤ :=
    le_antisymm le_top (hHtop ▸ hHleNorm)
  haveI : Y.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  haveI : IsSimpleGroup S := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with h | h
  · exact absurd h hne
  · exact h

end CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

end
