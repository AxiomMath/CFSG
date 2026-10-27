module

import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoO2Ky
import CFSG.Adapters.StatedPSLTwo
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem normal_inf_N :
    ((t.Ky ⊓ t.d.N).subgroupOf t.Ky).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  have hKyM : t.Ky ≤ c.S.M := (t.Ky_le.trans inf_le_left).trans c.hyp81.1
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    simpa [t.hdM] using SylowThreeData.N_normal t.d
  exact (le_inf t.Ky.le_normalizer (hKyM.trans hMN)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem inf_N_ne_top : t.Ky ⊓ t.d.N ≠ t.Ky := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZN : t.Z ≤ t.d.N := by
    intro z hz
    have hz' : z ∈ t.Ky ⊓ t.d.N := by
      rw [h]
      exact t.Z_le_Ky hz
    exact hz'.2
  have hN2 : IsPGroup 2 ↥t.d.N := SylowThreeData.N_isPGroup t.d
  have hZ2 : IsPGroup 2 ↥t.Z := hN2.to_le hZN
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  rw [t.card_Z] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    norm_num at hk
  have hdvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
  rw [← hk] at hdvd
  norm_num at hdvd

private theorem inf_N_eq_top_of_subgroupOf_eq_top
    (h : (t.Ky ⊓ t.d.N).subgroupOf t.Ky = ⊤) : t.Ky ⊓ t.d.N = t.Ky := by
  refine le_antisymm inf_le_left ?_
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥t.Ky) ∈ (t.Ky ⊓ t.d.N).subgroupOf t.Ky := by
    rw [h]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hx'

private theorem inf_N_eq_bot_of_subgroupOf_eq_bot
    (h : (t.Ky ⊓ t.d.N).subgroupOf t.Ky = ⊥) : t.Ky ⊓ t.d.N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx.1⟩ : ↥t.Ky) ∈ (t.Ky ⊓ t.d.N).subgroupOf t.Ky :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [h] at hx'
  simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hx')

private theorem subgroupOf_inf_N_ne_top :
    ((t.Ky ⊓ t.d.N).subgroupOf t.Ky) ≠ ⊤ := by
  intro h
  exact t.inf_N_ne_top (t.inf_N_eq_top_of_subgroupOf_eq_top h)

private theorem commutator_eq_bot_of_le_center
    (h : (t.Ky ⊓ t.d.N).subgroupOf t.Ky ≤ Subgroup.center ↥t.Ky) :
    ⁅t.Ky ⊓ t.d.N, t.Z⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hmem : (⟨a, ha.1⟩ : ↥t.Ky) ∈ (t.Ky ⊓ t.d.N).subgroupOf t.Ky :=
    Subgroup.mem_subgroupOf.mpr ha
  exact congrArg Subtype.val
    (Subgroup.mem_center_iff.mp (h hmem) ⟨z, t.Z_le_Ky hz⟩)

private theorem card_Ky_ge_sixty : 60 ≤ Nat.card ↥t.Ky := by
  haveI hperf : Group.IsPerfect ↥t.Ky := Subgroup.isPerfect_iff.mpr t.commutator_Ky
  have h3 : 3 ≤ Nat.card ↥t.Ky := by
    have h := Nat.card_le_card_of_injective
      (f := fun z : ↥t.Z => (⟨(z : G), t.Z_le_Ky z.2⟩ : ↥t.Ky)) (by
        intro a b hab
        exact Subtype.ext (congrArg (fun x : ↥t.Ky => (x : G)) hab))
    rwa [t.card_Z] at h
  haveI : Nontrivial ↥t.Ky := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  by_contra h60
  exact (Group.IsPerfect.not_isSolvable ↥t.Ky)
    (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))

theorem not_nonempty_mulEquiv_SL2 :
    ¬ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nonempty (↥t.Ky ≃* SL(2, F)) := by
  rintro ⟨F, hF, hFin, ⟨e⟩⟩
  letI : Field F := hF
  letI : Finite F := hFin
  let N₀ : Subgroup ↥t.Ky := (t.Ky ⊓ t.d.N).subgroupOf t.Ky
  haveI hN₀normal : N₀.Normal := t.normal_inf_N
  have hN₀ne : N₀ ≠ ⊤ := t.subgroupOf_inf_N_ne_top
  have h60Ky : 60 ≤ Nat.card ↥t.Ky := t.card_Ky_ge_sixty
  letI : Fintype F := Fintype.ofFinite F
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    set q := Nat.card F
    have hq : 2 ≤ q := Finite.one_lt_card
    have hprod : (q ^ 2 - 1) * (q ^ 2 - q) = (q - 1) * (q * (q ^ 2 - 1)) := by
      have e1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      have e2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
      zify [e1, e2, (by omega : 1 ≤ q)]
      ring
    rw [hprod, Nat.mul_div_cancel_left _ (by omega)]
  have h60SL : 60 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← Nat.card_congr e.toEquiv]
    exact h60Ky
  have h4 : 4 ≤ Nat.card F := by
    rw [hcardSL] at h60SL
    by_contra h
    have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
    have hq3 : Nat.card F ≤ 3 := by omega
    have hq : Nat.card F = 2 ∨ Nat.card F = 3 := by omega
    rcases hq with hq | hq <;> rw [hq] at h60SL <;> norm_num at h60SL
  rcases CFSG.ClassicalInvolution.normal_cases_of_equiv_sl2 h4 e N₀ hN₀normal with
    hbot | hcenter | htop
  · have hN₁bot : t.Ky ⊓ t.d.N = ⊥ := t.inf_N_eq_bot_of_subgroupOf_eq_bot hbot
    exact t.commutator_Ky_inf_N_Z_ne_bot
      (by rw [hN₁bot, Subgroup.commutator_bot_left])
  · exact t.commutator_Ky_inf_N_Z_ne_bot
      (t.commutator_eq_bot_of_le_center (le_of_eq hcenter))
  · exact hN₀ne htop

theorem not_lieModel_PSL2 :
    ¬ ∃ n : ℕ, CFSG.Blueprint.LieModel ↥t.Ky .PSL 2 2 n := by
  rintro ⟨n, hn⟩
  haveI hsimple : IsSimpleGroup ↥t.Ky := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hn
  let N₀ : Subgroup ↥t.Ky := (t.Ky ⊓ t.d.N).subgroupOf t.Ky
  haveI hN₀normal : N₀.Normal := t.normal_inf_N
  have hN₀ne : N₀ ≠ ⊤ := t.subgroupOf_inf_N_ne_top
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₀ with hbot | htop
  · have hN₁bot : t.Ky ⊓ t.d.N = ⊥ := t.inf_N_eq_bot_of_subgroupOf_eq_bot hbot
    exact t.commutator_Ky_inf_N_Z_ne_bot
      (by rw [hN₁bot, Subgroup.commutator_bot_left])
  · exact hN₀ne htop

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
