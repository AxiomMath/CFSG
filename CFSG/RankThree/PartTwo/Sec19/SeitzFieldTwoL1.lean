module

public import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
public import CFSG.LieType.SeitzGeneration.RegimesOuterNarrow
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SeitzGeneration

theorem not_le_linearAutGroup_of_not_narrow {F : Type} [Field F] [Finite F] (h3 : (3 : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL 3 F))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hN : ¬ NarrowScope 3 E) : ¬ E ≤ linearAutGroup 3 F := by
  intro hL
  apply hN
  unfold NarrowScope
  refine ⟨?_, Or.inr ?_⟩
  ·
    unfold RankLE2
    intro F' hF'
    have hrange : (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ≤
        linearAutGroup 3 F :=
      KFacts.innAut_le_linearAutGroup 3 F
    have hEA := CFSG.Open.IsElemAbelian.map hF'
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))
    have hle : F'.map (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) ≤
        linearAutGroup 3 F := by
      rintro _ ⟨x, -, rfl⟩
      exact hrange ⟨x, rfl⟩
    have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F)
      (le_refl 3)
    have h9 := Sec4.card_inf_linearAutGroup_three_le h3 hEA
    rw [inf_eq_left.mpr hle, Subgroup.card_map_of_injective hinj] at h9
    exact h9.trans (by norm_num)
  ·
    unfold PlaneRank2 RankLE2
    intro F' hF'
    have hS : (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ⊔ E ≤
        linearAutGroup 3 F :=
      sup_le (KFacts.innAut_le_linearAutGroup 3 F) hL
    have hB := CFSG.Open.IsElemAbelian.map hF'
      ((MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ⊔ E).subtype
    have hBL : F'.map
        ((MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ⊔ E).subtype ≤
          linearAutGroup 3 F := by
      rintro _ ⟨x, -, rfl⟩
      exact hS x.2
    have h9 := Sec4.card_inf_linearAutGroup_three_le h3 hB
    rw [inf_eq_left.mpr hBL, Subgroup.card_map_of_injective
      ((MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ⊔ E).subtype_injective]
      at h9
    exact h9.trans (by norm_num)

theorem exists_ne_one_inf_linearAutGroup {F : Type} [Field F] [Finite F] (h3 : (3 : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL 3 F))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hc : Nat.card E = 9) (hn : ¬ E ≤ linearAutGroup 3 F) :
    ∃ y ∈ E, y ∈ linearAutGroup 3 F ∧ y ≠ 1 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' F
  have hcycK := (card_ringAut_and_isCyclic hp F (by rw [Nat.card_eq_fintype_card, hK])).2
  have hcyc : IsCyclic (fieldAut 3 F).range :=
    isCyclic_of_surjective (fieldAut 3 F).rangeRestrict (fieldAut 3 F).rangeRestrict_surjective
  have hCN : (fieldAut 3 F).range ≤
      Subgroup.normalizer
        ((linearAutGroup 3 F : Subgroup _) : Set (MulAut (projectiveSL 3 F))) := by
    have key : ∀ σ : F ≃+* F, ∀ x ∈ linearAutGroup 3 F,
        fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹ ∈ linearAutGroup 3 F := by
      intro σ x hx
      rw [Sec4.linearAutGroup_three_eq_range] at hx ⊢
      obtain ⟨A, rfl⟩ := hx
      refine ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) A, ?_⟩
      rw [fieldAut_mul_conjAut, mul_inv_cancel_right]
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key σ x, fun hx => ?_⟩
    have h := key σ⁻¹ (fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹) hx
    rw [map_inv] at h
    have e : (fieldAut 3 F σ)⁻¹ * (fieldAut 3 F σ * x * (fieldAut 3 F σ)⁻¹) *
        ((fieldAut 3 F σ)⁻¹)⁻¹ = x := by group
    rw [e] at h
    exact h
  have hBNC : ∀ b ∈ E, ∃ n ∈ linearAutGroup 3 F, ∃ c ∈ (fieldAut 3 F).range, b = n * c := by
    intro b hb
    by_cases hbN : b ∈ linearAutGroup 3 F
    · exact ⟨b, hbN, 1, one_mem _, (mul_one b).symm⟩
    · obtain ⟨σ, -, H, hH⟩ :=
        KFacts.linear_order_three_field_descent (by norm_num) b (hE.2 b hb) hbN
      refine ⟨conjAut 3 F H * conjAut 3 F (Matrix.GeneralLinearGroup.map (σ : F →+* F) H⁻¹),
        ?_, fieldAut 3 F σ, ⟨σ, rfl⟩, ?_⟩
      · rw [Sec4.linearAutGroup_three_eq_range]
        exact ⟨_, map_mul _ _ _⟩
      · rw [hH, ← map_inv, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc]
  have h1 := Sec4.card_le_three_mul_card_inf hE hcyc hCN hBNC
  by_contra hcon
  have hbot : E ⊓ linearAutGroup 3 F = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    by_contra hy1
    exact hcon ⟨y, (Subgroup.mem_inf.mp hy).1, (Subgroup.mem_inf.mp hy).2, hy1⟩
  rw [hbot, Subgroup.card_bot, hc] at h1
  omega

end CFSG.RankThree.PartTwo.Sec19

end
