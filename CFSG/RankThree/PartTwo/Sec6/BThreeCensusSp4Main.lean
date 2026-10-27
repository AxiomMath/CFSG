module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LieType.Universal.Symplectic
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.IVK (fixedField)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {F : Type} [Field F] [CharP F 2]

noncomputable def sp4EquivProj : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
  MulEquiv.ofBijective (proj 2 F) ⟨proj_injective_of_charTwo, proj_surjective⟩

omit [CharP F 2] in
theorem center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hq : e.symm x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hx (e w)
  rw [h, Subgroup.mem_bot] at hq
  rw [Subgroup.mem_bot]
  have := congrArg e hq
  rwa [MulEquiv.apply_symm_apply, map_one] at this

theorem center_statedSp_two_eq_bot : Subgroup.center (StatedSp 2 F) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq]
  exact spScalars_eq_bot

theorem center_statedProj_sp4_eq_bot : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ :=
  center_eq_bot_of_mulEquiv sp4EquivProj center_statedSp_two_eq_bot

omit [CharP F 2] in
theorem card_statedSp_two_of_card_two [CharP F 2] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (StatedSp 2 F) = 720 := by
  rw [Nat.card_congr (sp4EquivProj (F := F)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hF]
  decide

omit [CharP F 2] in
theorem not_suzukiOrder_dvd_720 {a : ℕ} (ha : 1 ≤ a) : ¬ suzukiOrder a ∣ 720 := by
  intro h
  have haB := le_of_suzukiOrder_dvd (M := 720) (B := 1) (by norm_num) (by norm_num) h
  obtain rfl : a = 1 := by omega
  exact absurd h (by decide)

variable [Finite F]

theorem threePrimeB3_statedProj_sp4
    (hF : 4 ≤ Nat.card F) : ThreePrimeB3 (StatedProj (StatedSp 2 F)) := by
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr hF))
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs hsz
  by_cases hD : β ∈ (conjAut 2 F).range
  ·
    obtain ⟨A, rfl⟩ := hD
    obtain ⟨x, hx⟩ := conjAut_mem_inner_of_charTwo A
    rw [← hx] at hβ hC
    have hx3 : x ^ 3 = 1 := by
      have h1 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hβ
      have h2 : x ^ 3 ∈ Subgroup.center (StatedProj (StatedSp 2 F)) := by
        rw [Subgroup.mem_center_iff]
        intro z
        have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ z) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc z * x ^ 3 = x ^ 3 * z * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
          _ = x ^ 3 * z := by group
      rw [center_statedProj_sp4_eq_bot, Subgroup.mem_bot] at h2
      exact h2
    by_cases hx1 : x = 1
    · subst hx1
      have hCtop : C = ⊤ := by
        ext z
        simp [hC z]
      have hsimp : IsSimpleGroup C :=
        ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
      exact commutator_eq_bot_of_isSimpleGroup_or_isSolvable (Or.inl hsimp) hYC hsn hYp hRY hRn
        hRs
    · suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
      set e : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) := sp4EquivProj with he
      set g : StatedSp 2 F := e.symm x with hg
      have hg3 : (g : GL V₄ F) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hg, ← map_pow, hx3, map_one, Subgroup.coe_one]
      have hg1 : (g : GL V₄ F) ≠ 1 := by
        intro h1
        apply hx1
        have : g = 1 := Subtype.ext h1
        rw [hg] at this
        have := congrArg e this
        rwa [MulEquiv.apply_symm_apply, map_one] at this
      set Y₀ : Subgroup (StatedSp 2 F) := Y.map e.symm.toMonoidHom with hY₀
      have hY₀p : Group.IsPerfect Y₀ := by
        have := hYp
        exact Group.IsPerfect.map _
      have hY₀card : Nat.card Y₀ = Nat.card Y := Subgroup.card_map_of_injective e.symm.injective
      set Y₁ : Subgroup (GL V₄ F) := Y₀.map (StatedSp 2 F).subtype with hY₁
      have hY₁ : Y₁ = ⊥ := by
        refine eq_bot_of_commute_of_mem_statedSp three_ne_zero_of_charTwo g.2 hg3 hg1 Y₁ ?_ ?_ ?_
        · rintro _ ⟨q, ⟨y, hy, rfl⟩, rfl⟩
          have hyC := (hC y).mp (hYC hy)
          rw [MulAut.conj_apply] at hyC
          have h1 : e.symm y * g = g * e.symm y := by
            rw [hg, ← map_mul, ← map_mul]
            congr 1
            calc y * x = x * y * x⁻¹ * x := by rw [hyC]
              _ = x * y := by group
          exact congrArg Subtype.val h1
        · have := hY₀p
          exact Group.IsPerfect.map _
        · rwa [Subgroup.card_map_of_injective (StatedSp 2 F).subtype_injective, hY₀card]
      have hY₀ : Y₀ = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective Y₀ (StatedSp 2 F).subtype_injective).mp hY₁
      exact (Subgroup.map_eq_bot_iff_of_injective Y e.symm.injective).mp hY₀
  ·
    obtain ⟨σ, hσ3, H, hβH⟩ := sp4_even_order_three_field_descent β hβ hD
    set ι : StatedSp 2 (fixedField σ) →* StatedProj (StatedSp 2 F) :=
      (conjAut 2 F H : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F)).toMonoidHom.comp
        ((proj 2 F).comp (spIncl σ)) with hι
    have hιinj : Function.Injective ι :=
      (conjAut 2 F H).injective.comp (proj_spIncl_injective σ)
    have hCι : C = ι.range := by
      ext z
      rw [hC z, hβH]
      exact (mem_range_conj_comp_iff _ _ _ (mem_range_proj_spIncl_iff σ) z).symm
    have eC : C ≃* StatedSp 2 (fixedField σ) :=
      (MulEquiv.subgroupCongr hCι).trans (MonoidHom.ofInjective hιinj).symm
    have : CharP (fixedField σ) 2 := RingHom.charP _ (fixedField σ).subtype_injective 2
    have : Finite (fixedField σ) := Subtype.finite
    have hcard := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ3] at hcard
    by_cases h4 : 4 ≤ Nat.card (fixedField σ)
    · have : IsSimpleGroup (StatedProj (StatedSp 2 (fixedField σ))) :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp _ 2 (by norm_num)
          (Or.inl (Or.inr h4))
      have hsimp : IsSimpleGroup C := (eC.trans sp4EquivProj).isSimpleGroup
      exact commutator_eq_bot_of_isSimpleGroup_or_isSolvable (Or.inl hsimp) hYC hsn hYp hRY hRn
        hRs
    · exfalso
      have h2 : Nat.card (fixedField σ) = 2 := by
        have : Fintype (fixedField σ) := Fintype.ofFinite _
        have hdvd : 2 ∣ Nat.card (fixedField σ) := by
          rw [Nat.card_eq_fintype_card]
          exact (CharP.cast_eq_zero_iff (fixedField σ) 2 _).mp (FiniteField.cast_card_eq_zero _)
        have hpos : 0 < Nat.card (fixedField σ) := Nat.card_pos
        omega
      have hC720 : Nat.card C = 720 := by
        rw [Nat.card_congr eC.toEquiv, card_statedSp_two_of_card_two h2]
      obtain ⟨f, hf⟩ := hsz
      obtain ⟨a, ha, hcardY⟩ := card_eq_suzukiOrder hf
      apply not_suzukiOrder_dvd_720 ha
      rw [← hcardY, ← hC720]
      exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hYC)

open CFSG.Assembly.RankThreeEven (projSp)

theorem threePrimeB3_projSp_two_charTwo
    {n : ℕ} (hn : 1 ≤ n) :
    ThreePrimeB3 (projSp 2 (GaloisField 2 n)) := by
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  let e : projSp 2 (GaloisField 2 n) ≃* StatedProj (StatedSp 2 (GaloisField 2 n)) :=
    (statedSpEquivProjSpOfCharTwo (GaloisField 2 n)).symm.trans sp4EquivProj
  by_cases h4 : 4 ≤ 2 ^ n
  · exact threePrimeB3_of_mulEquiv e (threePrimeB3_statedProj_sp4 (by rw [hF]; exact h4))
  · have hn1 : n = 1 := by
      by_contra hne
      exact h4 (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega))
    subst hn1
    have hcard : Nat.card (projSp 2 (GaloisField 2 1)) = 720 := by
      rw [← Nat.card_congr (statedSpEquivProjSpOfCharTwo (GaloisField 2 1)).toEquiv,
        card_statedSp_two_of_card_two (by rw [hF]; norm_num)]
    have : Finite (projSp 2 (GaloisField 2 1)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    exact threePrimeB3_of_suzukiOrder_not_dvd fun a ha hdvd =>
      not_suzukiOrder_dvd_720 ha (hcard ▸ hdvd)

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
