module

public import CFSG.Milestones.ASVolI.F437.Kinds
public import CFSG.Milestones.ASVolI.F431.Final
public import CFSG.Milestones.ASVolI.F431.ATopSp

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

@[expose] def burnsideF437_F437KindDeg (κ : GLKind) (degree : ℕ) : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E)
    (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y) (M : Type) [Group M]
    (ε : Y →* M) (z : M) (hyp : HypF_4_31 κ degree Gp M₁ M₂ β ε z),
    let chart := hyp.amalgam.toHypF_4_4g.chart
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
    ∀ fb : ↥(M₁ ⊓ M₂), (fb : E) ∈ Tb →
      (fb : E) ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (fb : E) * (fb : E) = 1 → ¬ chart.IsTypeIIIInv (fb : E) →
      ChF.IsSylowOf 2
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(fb : E)} : Set E))
        (cenIn Gp (fb : E)) →
      (chart.IsFieldInv (fb : E) ∨ chart.IsGraphInv (fb : E)) ∧
      ((∃ subdegree, 0 < subdegree ∧ degree = 2 * subdegree ∧
          chart.IsFieldInv (fb : E) ∧
          IsGenLie (f437Dbar Gp (fb : E)) κ 2 subdegree ∧
          F437QuotientAssembly Gp M₁ M₂ (fb : E) κ subdegree) ∨
        (chart.IsGraphInv (fb : E) ∧ (κ = .U4 ∨ κ = .U5) ∧
          IsGenLie (f437Dbar Gp (fb : E)) .Sp4 2 degree ∧
          chart.GraphFixedMarkingGoal (fb : E) ∧
          F437QuotientAssembly Gp M₁ M₂ (fb : E) .Sp4 degree)) ∧
      F437RestrictionAssembly Gp M₁ M₂ β (fb : E) ∧
      (((f437DbarOne Gp M₁ (fb : E)).subgroupOf M₁).map (f1 (c := β)) ⊓
          ((f437DbarTwo Gp M₂ (fb : E)).subgroupOf M₂).map (f2 (c := β)) =
        ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) (fb : E)).subgroupOf (M₁ ⊓ M₂)).map (bmap β)) ∧
      ((∀ e ∈ f437Ebar (fb : E), ∀ d ∈ f437Dbar Gp (fb : E),
          e * d * e⁻¹ ∈ f437Dbar Gp (fb : E)) ∧
        Subgroup.centralizer ((f437Dbar Gp (fb : E) : Subgroup E) : Set E) ⊓
          f437Ebar (fb : E) = Subgroup.zpowers (fb : E) ∧
        (∀ e ∈ f437Ebar (fb : E), ∃ d ∈ f437Dbar Gp (fb : E),
          ∃ h ∈ f437Ebar (fb : E) ⊓ (M₁ ⊓ M₂), e = d * h) ∧
        (∀ e ∈ f437Ebar (fb : E),
          e ∈ Subgroup.normalizer ((cenIn (Gp ⊓ (M₁ ⊓ M₂)) (fb : E) : Subgroup E) : Set E) →
          e ∈ Subgroup.normalizer ((f437DbarOne Gp M₁ (fb : E) : Subgroup E) : Set E))) ∧
      (ChF.IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
          (Subgroup.centralizer ({bM β ε fb} : Set M)) ∨
        (κ = .U4 ∧ degree = 1 ∧ Nonempty (E ≃* MulAut Gp) ∧
          Nonempty (E ≃* β.G0) ∧ IsL43 M))

theorem burnsideF437_F437Kind_iff_deg (κ : GLKind) :
    burnsideF437_F437Kind κ ↔ ∀ degree, burnsideF437_F437KindDeg κ degree := Iff.rfl

theorem burnsideF437_F437KindDeg_of_odd {κ : GLKind} {degree : ℕ}
    (hodd : ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
      (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
      HypF_4_31 κ degree Gp M₁ M₂ β ε z → Odd Gp.index) :
    burnsideF437_F437KindDeg κ degree := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z hyp chart Tb hTb fb hfbT hfbS hsq hiii hsyl
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  have hfG : (fb : E) ∉ Gp := burnsideF437_not_mem_Gp hsyl (fun h => hfbS h.1) hsq
  exact absurd (burnsideF4d_two_elt_mem (hodd E Gp M₁ M₂ Y β M ε z hyp) (k := 1)
    (by rw [pow_one, sq]; exact hsq)) hfG

section Odd

set_option linter.unusedSectionVars false


theorem burnsideF437_F437Kind_L3 : burnsideF437_F437Kind .L3 := by
  rw [burnsideF437_F437Kind_iff_deg]
  intro degree
  refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
  exact burnsideF4d_L3_odd (burnsideF4d_L3_two_le_f hyp) hyp

theorem burnsideF437_F437Kind_F4tw_odd : burnsideF437_F437Kind .F4tw := by
  rw [burnsideF437_F437Kind_iff_deg]
  intro degree
  refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
  obtain ⟨-, hfo, -⟩ := hyp.amalgam.model
  by_cases hf3 : 3 ≤ degree
  · exact burnsideF4j_odd_index_F4tw hyp.amalgam hf3
  · have h1 : degree = 1 := by obtain ⟨k, hk⟩ := hfo; omega
    subst h1
    rw [burnsideF4m_top_F4two hyp.amalgam, Subgroup.index_top]
    exact odd_one

theorem burnsideF437_F437KindDeg_odd_degree {κ : GLKind} {degree : ℕ}
    (hκ : κ = .Sp4 ∨ κ = .G2 ∨ κ = .D4tw) (hdeg : Odd degree) :
    burnsideF437_F437KindDeg κ degree := by
  refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
  rcases hκ with rfl | rfl | rfl
  · by_cases hf3 : 3 ≤ degree
    · exact burnsideF4j_odd_index_Sp4 hyp.amalgam hf3 hdeg
    · have h1 : degree = 1 := by obtain ⟨k, hk⟩ := hdeg; omega
      subst h1
      rw [burnsideF4m_top_Sp4two hyp.amalgam, Subgroup.index_top]
      exact odd_one
  · by_cases hf2 : 2 ≤ degree
    · exact burnsideF4jb_odd_index_G2 hyp.amalgam hdeg hf2
    · have h1 : degree = 1 := by obtain ⟨k, hk⟩ := hdeg; omega
      subst h1
      rw [burnsideF4m_top_G2two hyp.amalgam, Subgroup.index_top]
      exact odd_one
  · exact burnsideF4jb_odd_index_D4tw hyp.amalgam hdeg

theorem burnsideF437_F437KindDeg_of_lie (hlie : burnsideF4m_LieCoreInput) {κ : GLKind}
    {degree : ℕ} (hκ : κ = .Sp4 ∨ κ = .G2 ∨ κ = .D4tw ∨ κ = .U4 ∨ κ = .U5) (hdeg : 2 ≤ degree) :
    burnsideF437_F437KindDeg κ degree := by
  refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
  rcases hκ with rfl | rfl | rfl | rfl | rfl
  · exact burnsideF4m_odd_index_Sp4_lie hlie hyp hdeg
  · exact burnsideF4m_odd_index_G2_lie hlie hyp hdeg
  · exact burnsideF4m_odd_index_D4tw_lie hlie hyp hdeg
  · exact burnsideF4m_odd_index_U4_lie hlie hyp hdeg
  · exact burnsideF4m_odd_index_U5_lie' hlie hyp hdeg

theorem burnsideF437_F_4_37_of_lie (hlie : burnsideF4m_LieCoreInput)
    (hU4 : burnsideF437_F437KindDeg .U4 1) (hU5 : burnsideF437_F437KindDeg .U5 1) : F_4_37 := by
  rw [burnsideF437_F_4_37_iff_kinds]
  intro κ
  rw [burnsideF437_F437Kind_iff_deg]
  intro degree
  cases κ with
  | L3 => exact (burnsideF437_F437Kind_iff_deg _).mp burnsideF437_F437Kind_L3 degree
  | F4tw => exact (burnsideF437_F437Kind_iff_deg _).mp burnsideF437_F437Kind_F4tw_odd degree
  | G2d => exact (burnsideF437_F437Kind_iff_deg _).mp burnsideF437_F437Kind_G2d degree
  | Tits => exact (burnsideF437_F437Kind_iff_deg _).mp burnsideF437_F437Kind_Tits degree
  | Sp4 =>
    rcases Nat.even_or_odd degree with he | ho
    · by_cases h0 : degree = 0
      · subst h0
        refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
        exact absurd hyp.amalgam.model.2.1 (by decide)
      · exact burnsideF437_F437KindDeg_of_lie hlie (Or.inl rfl) (by obtain ⟨k, hk⟩ := he; omega)
    · exact burnsideF437_F437KindDeg_odd_degree (Or.inl rfl) ho
  | G2 =>
    rcases Nat.even_or_odd degree with he | ho
    · by_cases h0 : degree = 0
      · subst h0
        refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
        exact absurd hyp.amalgam.model.2.1 (by decide)
      · exact burnsideF437_F437KindDeg_of_lie hlie (Or.inr (Or.inl rfl))
          (by obtain ⟨k, hk⟩ := he; omega)
    · exact burnsideF437_F437KindDeg_odd_degree (Or.inr (Or.inl rfl)) ho
  | D4tw =>
    rcases Nat.even_or_odd degree with he | ho
    · by_cases h0 : degree = 0
      · subst h0
        refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
        exact absurd hyp.amalgam.model.2.1 (by decide)
      · exact burnsideF437_F437KindDeg_of_lie hlie (Or.inr (Or.inr (Or.inl rfl)))
          (by obtain ⟨k, hk⟩ := he; omega)
    · exact burnsideF437_F437KindDeg_odd_degree (Or.inr (Or.inr rfl)) ho
  | U4 =>
    by_cases h1 : degree = 1
    · subst h1; exact hU4
    · by_cases h0 : degree = 0
      · subst h0
        refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
        exact absurd hyp.amalgam.model.2.1 (by decide)
      · exact burnsideF437_F437KindDeg_of_lie hlie (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          (by omega)
  | U5 =>
    by_cases h1 : degree = 1
    · subst h1; exact hU5
    · by_cases h0 : degree = 0
      · subst h0
        refine burnsideF437_F437KindDeg_of_odd fun E _ Gp M₁ M₂ Y _ β M _ ε z hyp => ?_
        exact absurd hyp.amalgam.model.2.1 (by decide)
      · exact burnsideF437_F437KindDeg_of_lie hlie (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          (by omega)

end Odd

end CFSG.ASVolI
