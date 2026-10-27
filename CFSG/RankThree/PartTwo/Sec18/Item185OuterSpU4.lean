module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterLin
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSU4Two
import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27 AutNoE27)

private theorem spU4_swap_mul_swap_mem_alt {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  decide

private theorem spU4_exists_alt_fix_zero_moves (y : Fin 6) (hy : y ≠ 0) :
    ∃ h ∈ alternatingGroup (Fin 6), h 0 = 0 ∧ h y ≠ y := by
  fin_cases y
  · exact absurd rfl hy
  · exact ⟨Equiv.swap 1 2 * Equiv.swap 1 3, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide, by decide⟩
  · exact ⟨Equiv.swap 2 1 * Equiv.swap 2 3, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide, by decide⟩
  · exact ⟨Equiv.swap 3 1 * Equiv.swap 3 2, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide, by decide⟩
  · exact ⟨Equiv.swap 4 1 * Equiv.swap 4 2, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide, by decide⟩
  · exact ⟨Equiv.swap 5 1 * Equiv.swap 5 2, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide, by decide⟩

private theorem spU4_exists_alt_map_zero (x : Fin 6) :
    ∃ a ∈ alternatingGroup (Fin 6), a 0 = x := by
  fin_cases x
  · exact ⟨1, one_mem _, rfl⟩
  · exact ⟨Equiv.swap 0 2 * Equiv.swap 0 1, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 2, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 3, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 4, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide⟩
  · exact ⟨Equiv.swap 0 1 * Equiv.swap 0 5, spU4_swap_mul_swap_mem_alt (by decide) (by decide),
      by decide⟩

private theorem spU4_eq_one_of_comm_alt_six (g : Equiv.Perm (Fin 6))
    (hg : ∀ a ∈ alternatingGroup (Fin 6), a * g = g * a) : g = 1 := by
  have h0 : g 0 = 0 := by
    by_contra hne
    obtain ⟨h, hh, h0h, hyh⟩ := spU4_exists_alt_fix_zero_moves (g 0) hne
    have key := congrArg (fun p : Equiv.Perm (Fin 6) => p 0) (hg h hh)
    simp only [Equiv.Perm.mul_apply, h0h] at key
    exact hyh key
  refine Equiv.ext fun x => ?_
  obtain ⟨a, ha, ha0⟩ := spU4_exists_alt_map_zero x
  have key := congrArg (fun p : Equiv.Perm (Fin 6) => p 0) (hg a ha)
  simp only [Equiv.Perm.mul_apply, h0, ha0] at key
  simpa using key.symm

private theorem spU4_center_eq_bot_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_center_iff] at hx
  have hmem : e x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [h, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hmem, map_one])

private theorem spU4_mem_fixedSubgroup {X : Type} [Group X] (σ : MulAut X) (x : X) :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

private theorem spU4_fixedFacts_of_simple {S : Type} [Group S] (σ : MulAut S)
    (hs : IsSimpleGroup (fixedSubgroup σ)) (hz : Subgroup.center (fixedSubgroup σ) = ⊥) :
    FixedFactsAt σ := by
  haveI := hs
  left
  refine ⟨⊤, inferInstance, Subgroup.topEquiv.isSimpleGroup, ?_, ?_⟩
  · intro hc
    obtain ⟨x, hx⟩ := exists_ne (1 : fixedSubgroup σ)
    have hxc : x ∈ Subgroup.center (fixedSubgroup σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact congrArg Subtype.val (hc ⟨y, Subgroup.mem_top y⟩ ⟨x, Subgroup.mem_top x⟩)
    rw [hz, Subgroup.mem_bot] at hxc
    exact hx hxc
  · rw [Subgroup.coe_top, Subgroup.centralizer_univ, hz]

private theorem spU4_fixedFacts_of_perm_six {S : Type} [Group S] (σ : MulAut S)
    (e : fixedSubgroup σ ≃* Equiv.Perm (Fin 6)) : FixedFactsAt σ := by
  have hA : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  left
  refine ⟨(alternatingGroup (Fin 6)).comap e.toMonoidHom, inferInstance, ?_, ?_, ?_⟩
  · exact (MulEquiv.ofBijective
      (MonoidHom.subgroupComap e.toMonoidHom (alternatingGroup (Fin 6)))
      ⟨MonoidHom.subgroupComap_injective _ _ e.injective,
        MonoidHom.subgroupComap_surjective _ _ e.surjective⟩).isSimpleGroup
  · intro hc
    have hx0 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 6) :=
      spU4_swap_mul_swap_mem_alt (by decide) (by decide)
    have hy0 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 3 ∈ alternatingGroup (Fin 6) :=
      spU4_swap_mul_swap_mem_alt (by decide) (by decide)
    have hcomm := hc
      ⟨e.symm (Equiv.swap 0 1 * Equiv.swap 0 2), by simpa using hx0⟩
      ⟨e.symm (Equiv.swap 0 1 * Equiv.swap 0 3), by simpa using hy0⟩
    have key := congrArg (fun p : (alternatingGroup (Fin 6)).comap e.toMonoidHom =>
      e (p : fixedSubgroup σ)) hcomm
    simp only [Subgroup.coe_mul, map_mul, MulEquiv.apply_symm_apply] at key
    have key' := congrArg (fun p : Equiv.Perm (Fin 6) => p 0) key
    revert key'
    decide
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    rw [Subgroup.mem_bot]
    have hperm : e g = 1 := by
      apply spU4_eq_one_of_comm_alt_six
      intro a ha
      have hn : e.symm a ∈ (alternatingGroup (Fin 6)).comap e.toMonoidHom := by
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        exact ha
      have hc := congrArg e (hg (e.symm a) hn)
      simpa only [map_mul, MulEquiv.apply_symm_apply] using hc
    exact e.injective (by rw [hperm, map_one])

section SpHelpers

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.IVK (fixedField fixedField_card_pow)

private theorem spU4_nonempty_fixedSubgroup {F : Type} [Field F] [CharP F 2] (σ₀ : F ≃+* F)
    (H : gsp 2 F) :
    Nonempty (StatedSp 2 (fixedField σ₀) ≃*
      fixedSubgroup (conjAut 2 F H * fieldAut 2 F σ₀ * (conjAut 2 F H)⁻¹)) := by
  set c := conjAut 2 F H with hc
  set Φ : StatedSp 2 (fixedField σ₀) →* StatedProj (StatedSp 2 F) :=
    (proj 2 F).comp (KFacts.spIncl σ₀) with hΦ
  have hΨ : Function.Injective (c.toMonoidHom.comp Φ) :=
    c.injective.comp (KFacts.proj_spIncl_injective σ₀)
  have hrange : (c.toMonoidHom.comp Φ).range = fixedSubgroup (c * fieldAut 2 F σ₀ * c⁻¹) := by
    ext x
    rw [MonoidHom.mem_range, spU4_mem_fixedSubgroup]
    constructor
    · rintro ⟨y, rfl⟩
      have hy : fieldAut 2 F σ₀ (Φ y) = Φ y :=
        (KFacts.mem_range_proj_spIncl_iff σ₀ (Φ y)).mp (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
      show (c * fieldAut 2 F σ₀ * c⁻¹) (c (Φ y)) = c (Φ y)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy]
    · intro hx
      rw [MulAut.mul_apply, MulAut.mul_apply] at hx
      have hz : fieldAut 2 F σ₀ (c⁻¹ x) = c⁻¹ x := by
        apply c.injective
        rw [hx, MulAut.apply_inv_self]
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp
        ((KFacts.mem_range_proj_spIncl_iff σ₀ (c⁻¹ x)).mpr hz)
      exact ⟨y, by show c (Φ y) = x; rw [hy, MulAut.apply_inv_self]⟩
  exact ⟨(MonoidHom.ofInjective hΨ).trans (MulEquiv.subgroupCongr hrange)⟩

private theorem spU4_fixedFacts_statedProj {F : Type} [Field F] [Finite F] [CharP F 2]
    (σ : MulAut (StatedProj (StatedSp 2 F))) (hσ : σ ∉ innerAut (StatedProj (StatedSp 2 F)))
    (hσ3 : σ ^ 3 = 1) : FixedFactsAt σ := by
  have hnot : σ ∉ (conjAut 2 F).range := by
    rintro ⟨A, rfl⟩
    exact hσ (KFacts.conjAut_mem_inner_of_charTwo A)
  obtain ⟨σ₀, hσ₀, H, rfl⟩ := KFacts.sp4_even_order_three_field_descent σ hσ3 hnot
  obtain ⟨k, hk1, hk⟩ : ∃ k : ℕ, 1 ≤ k ∧ Nat.card (fixedField σ₀) = 2 ^ k := by
    haveI : Fintype (fixedField σ₀) := Fintype.ofFinite _
    obtain ⟨m, -, hm⟩ := FiniteField.card (fixedField σ₀) 2
    exact ⟨m, m.pos, by rw [Nat.card_eq_fintype_card, hm]⟩
  obtain ⟨ψ⟩ := spU4_nonempty_fixedSubgroup σ₀ H
  rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
  · haveI : Fintype (fixedField σ₀) := Fintype.ofFinite _
    have hfc : Fintype.card (fixedField σ₀) = 2 := by
      rw [← Nat.card_eq_fintype_card, hk]
      norm_num
    obtain ⟨e₁⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm hfc
    exact spU4_fixedFacts_of_perm_six _ (ψ.symm.trans e₁)
  · have h4 : 4 ≤ Nat.card (fixedField σ₀) := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    haveI hS : IsSimpleGroup (StatedProj (StatedSp 2 (fixedField σ₀))) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (fixedField σ₀) 2
        (by norm_num) (Or.inl (Or.inr h4))
    have hZ : Subgroup.center (StatedProj (StatedSp 2 (fixedField σ₀))) = ⊥ :=
      CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.SpFour.center_statedProj_eq_bot
    let eC := ψ.symm.trans (CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.SpFour.projEquiv
      (F := fixedField σ₀))
    exact spU4_fixedFacts_of_simple _ eC.isSimpleGroup (spU4_center_eq_bot_of_equiv eC hZ)

private theorem spU4_noOmega_statedProj (F : Type) [Field F] [Finite F] [CharP F 2] :
    NoOmega (StatedProj (StatedSp 2 F)) :=
  noOmega_of_fixed_facts fun σ hσ hσ3 => spU4_fixedFacts_statedProj σ hσ hσ3

end SpHelpers

section SpU4


theorem not_isSimpleGroup_projSp_two_two_one :
    ¬ IsSimpleGroup (projSp 2 (GaloisField 2 1)) := by
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨e₁⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm hcard
  let e : projSp 2 (GaloisField 2 1) ≃* Equiv.Perm (Fin 6) :=
    (KFacts.statedSpEquivProjSpOfCharTwo (GaloisField 2 1)).symm.trans e₁
  intro hS
  haveI := hS
  have hperm : IsSimpleGroup (Equiv.Perm (Fin 6)) := e.symm.isSimpleGroup
  rcases hperm.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 6)) with h | h
  · have hmem : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 6) :=
      spU4_swap_mul_swap_mem_alt (by decide) (by decide)
    rw [h, Subgroup.mem_bot] at hmem
    have := congrArg (fun p : Equiv.Perm (Fin 6) => p 2) hmem
    revert this
    decide
  · have hs : Equiv.swap (0 : Fin 6) 1 ∈ alternatingGroup (Fin 6) := by
      rw [h]
      exact Subgroup.mem_top _
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hs
    revert hs
    decide

theorem noOmega_projSp_two_two {n : ℕ} (hn : 2 ≤ n) :
    NoOmega (projSp 2 (GaloisField 2 n)) := by
  open CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports in
  have e : projSp 2 (GaloisField 2 n) ≃* StatedProj (StatedSp 2 (GaloisField 2 n)) :=
    (statedProjEquivMapMk (StatedSp 2 (GaloisField 2 n))).symm
  exact NoOmega.of_mulEquiv e (spU4_noOmega_statedProj (GaloisField 2 n))

theorem not_three_dvd_outer_projSU_four_two_one :
    ¬ 3 ∣ Nat.card (Outer (projSU 4 2 1)) :=
  CFSG.RankThree.PartTwo.Sec4.RonanK432.not_three_dvd_card_outer_projSU_four_two le_rfl
    (by norm_num)

@[expose] def GapU48 : Prop :=
  ∀ σ : MulAut (projSU 4 2 3), σ ∉ innerAut (projSU 4 2 3) → σ ^ 3 = 1 → FixedFactsAt σ

theorem noOmega_projSU_four_two_three (hK1 : GapU48) : NoOmega (projSU 4 2 3) :=
  noOmega_of_fixed_facts hK1

end SpU4

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
