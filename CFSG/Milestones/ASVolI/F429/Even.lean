module

public import CFSG.Milestones.ASVolI.F429.Final
public import CFSG.Milestones.ASVolI.F429.OddExt
public import CFSG.Milestones.ASVolI.F429.C2ab
public import CFSG.Milestones.ASVolI.F429.C2Sp4
public import CFSG.Milestones.ASVolI.F429.aC5L3
public import CFSG.Milestones.ASVolI.F429.aC5Sp4
public import CFSG.Milestones.ASVolI.F429.aC5corrU4
public import CFSG.Milestones.ASVolI.F429.C6U4
public import CFSG.Milestones.ASVolI.F429.aC2U5
public import CFSG.Milestones.ASVolI.F429.bC6U5

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

@[expose] def burnsideF429_EvenU2 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    ∀ hyp : HypF_4_4 κ 2 f Gp M₁ M₂, (κ = .U4 ∨ κ = .U5) → ¬ Odd Gp.index →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C2 κ f Gp M₁ M₂ hyp T

@[expose] def burnsideF429_EvenD6 : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 .D4tw 2 f Gp M₁ M₂ → 2 ≤ f → ¬ Odd Gp.index →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C6 .D4tw f Gp M₁ M₂ T

@[expose] def burnsideF429_EvenU6 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → (κ = .U4 ∨ κ = .U5) → 2 ≤ f → ¬ Odd Gp.index →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C6 κ f Gp M₁ M₂ T

@[expose] def burnsideF429_C2c (κ : GLKind) (f : ℕ) {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E)
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (T : Subgroup E) : Prop :=
  let chart := hyp.toHypF_4_4g.chart
  ∀ t ∈ T, t ∉ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) → t * t = 1 →
    chart.IsFieldInv t ∨
      (chart.IsGraphInv t ∧ IsGenLie ↥(cenIn Gp t) GLKind.Sp4 2 f ∧
        chart.GraphFixedMarkingGoal t) ∨
      (chart.IsTypeIIIInv t ∧ ∃ s z : E,
        t = s * z ∧ chart.IsGraphInv s ∧
          chart.coordinatePayload.RankInvolution 1 z ∧ s * z = z * s ∧
          IsGenLie ↥(cenIn Gp s) .Sp4 2 f ∧ chart.GraphFixedMarkingGoal s ∧
          Subgroup.centralizer ({t} : Set E) =
            Subgroup.centralizer ({s} : Set E) ⊓ Subgroup.centralizer ({z} : Set E))

@[expose] def burnsideF429_EvenU2c : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    ∀ hyp : HypF_4_4 κ 2 f Gp M₁ M₂, (κ = .U4 ∨ κ = .U5) → ¬ Odd Gp.index →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C2c κ f Gp M₁ M₂ hyp T

@[expose] def burnsideF429_EvenU5c6 : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 .U5 2 f Gp M₁ M₂ → 2 ≤ f → ¬ Odd Gp.index →
    ∀ T : Subgroup E, ChF.IsSylowOf 2 T (M₁ ⊓ M₂) → burnsideF429_C6 .U5 f Gp M₁ M₂ T

section Even

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_c2_L3 {f : ℕ} (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C2 .L3 f Gp M₁ M₂ hyp T :=
  ⟨(burnsideF429_c2ab_L3 hyp hf hT).1, (burnsideF429_c2ab_L3 hyp hf hT).2,
    fun _ ht hts htt => Or.inl (burnsideF429_c2c_L3 hyp hT ht hts htt)⟩

theorem burnsideF429_c2_Sp4 {f : ℕ} (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C2 .Sp4 f Gp M₁ M₂ hyp T :=
  ⟨(burnsideF429_c2ab_Sp4 hyp hf hT).1, (burnsideF429_c2ab_Sp4 hyp hf hT).2,
    fun _ ht hts htt => Or.inl (burnsideF429_c2c_Sp4 hyp hT ht hts htt)⟩

theorem burnsideF429_even_cases {κ : GLKind} {f : ℕ} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂)
    (hκ : κ.IsLie) (hodd : ¬ Odd Gp.index) :
    ((κ = .L3 ∨ κ = .Sp4 ∨ κ = .G2 ∨ κ = .D4tw) ∧ 2 ≤ f) ∨ κ = .U4 ∨ κ = .U5 := by
  have hf1 : 1 ≤ f := burnsideF429_one_le_f hyp hκ
  have hnc : ¬ burnsideF429_OddCase' κ f := fun hc =>
    hodd (burnsideF429_odd_index_of_case' hyp hκ hc)
  have hf2 : (κ = .L3 ∨ κ = .Sp4 ∨ κ = .G2 ∨ κ = .D4tw) → 2 ≤ f := by
    intro hk
    by_contra h
    have hf : f = 1 := by omega
    subst hf
    apply hnc
    left
    right
    right
    refine ⟨rfl, ?_, ?_⟩ <;> rcases hk with rfl | rfl | rfl | rfl <;> decide
  cases κ with
  | L3 => exact Or.inl ⟨Or.inl rfl, hf2 (Or.inl rfl)⟩
  | Sp4 => exact Or.inl ⟨Or.inr (Or.inl rfl), hf2 (Or.inr (Or.inl rfl))⟩
  | G2 => exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), hf2 (Or.inr (Or.inr (Or.inl rfl)))⟩
  | D4tw => exact Or.inl ⟨Or.inr (Or.inr (Or.inr rfl)), hf2 (Or.inr (Or.inr (Or.inr rfl)))⟩
  | F4tw => exact absurd (Or.inl (Or.inl rfl)) hnc
  | U4 => exact Or.inr (Or.inl rfl)
  | U5 => exact Or.inr (Or.inr rfl)
  | G2d => exact absurd rfl hκ.1
  | Tits => exact absurd rfl hκ.2

theorem burnsideF429_Even2_of (hU2 : burnsideF429_EvenU2) : burnsideF429_Even2 := by
  intro κ f E _ Gp M₁ M₂ hyp hκ hodd T hT
  rcases burnsideF429_even_cases hyp hκ hodd with ⟨hk, hf⟩ | hU
  · rcases hk with rfl | rfl | rfl | rfl
    · exact burnsideF429_c2_L3 hyp hf hT
    · exact burnsideF429_c2_Sp4 hyp hf hT
    · exact burnsideF429b_c2_G2 hyp hf hT
    · exact burnsideF429b_c2_D4tw hyp hT
  · exact hU2 κ f E Gp M₁ M₂ hyp hU hodd T hT

theorem burnsideF429_Even5_proof : burnsideF429_Even5 := by
  intro κ f E _ Gp M₁ M₂ hyp hκ hodd T hT
  have hC5 : ∀ {κ : GLKind} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂), κ ≠ .U4 →
      burnsideF429_C5 κ Gp M₁ M₂ hyp T → burnsideF429_C5corr κ Gp M₁ M₂ hyp T := by
    intro κ hyp hκ h
    rcases h with h | h
    · exact burnsideF429_C5corr_of_i hyp h
    · exact absurd h.1 hκ
  rcases burnsideF429_even_cases hyp hκ hodd with ⟨hk, hf⟩ | hU
  · rcases hk with rfl | rfl | rfl | rfl
    · exact hC5 hyp (by decide) (burnsideF429a_c5_L3 hyp hf hT)
    · exact hC5 hyp (by decide) (burnsideF429a_c5_Sp4 hyp hf hT)
    · exact hC5 hyp (by decide) (burnsideF429b_c5_G2 hyp hf hT)
    · exact hC5 hyp (by decide) (burnsideF429b_c5_D4tw hyp hT)
  · rcases hU with rfl | rfl
    · exact burnsideF429a_c5corr_U4 hyp hodd hT
    · exact hC5 hyp (by decide) (burnsideF429a_c5_U5 hyp hT)

theorem burnsideF429_Even6_of (hD6 : burnsideF429_EvenD6) (hU6 : burnsideF429_EvenU6) :
    burnsideF429_Even6 := by
  intro κ f E _ Gp M₁ M₂ hyp hκ hodd T hT
  have hf1 : 1 ≤ f := burnsideF429_one_le_f hyp hκ
  rcases burnsideF429_even_cases hyp hκ hodd with ⟨hk, hf⟩ | hU
  · rcases hk with rfl | rfl | rfl | rfl
    · exact burnsideF429_c6_L3 hyp hf hT
    · exact burnsideF429_c6_Sp4 hyp hf hT
    · exact burnsideF429b_c6_G2 hyp hf hT
    · exact hD6 f E Gp M₁ M₂ hyp hf hodd T hT
  · by_cases hf : f = 1
    · exact Or.inr ⟨hf, hU⟩
    · exact hU6 κ f E Gp M₁ M₂ hyp hU (by omega) hodd T hT

theorem burnsideF429_EvenD6_proof : burnsideF429_EvenD6 :=
  fun _ _ _ _ _ _ hyp hf _ _ hT => burnsideF429b_c6_D4tw hyp hf hT

theorem burnsideF429_EvenU2_of (hU2c : burnsideF429_EvenU2c) : burnsideF429_EvenU2 := by
  intro κ f E _ Gp M₁ M₂ hyp hU hodd T hT
  have hc := hU2c κ f E Gp M₁ M₂ hyp hU hodd T hT
  rcases hU with rfl | rfl
  · exact ⟨(burnsideF429a_c2ab_U4 hyp hT).1, (burnsideF429a_c2ab_U4 hyp hT).2, hc⟩
  · exact ⟨(burnsideF429a_c2ab_U5 hyp hT).1, (burnsideF429a_c2ab_U5 hyp hT).2, hc⟩

theorem burnsideF429_EvenU6_of (hU5 : burnsideF429_EvenU5c6) : burnsideF429_EvenU6 := by
  intro κ f E _ Gp M₁ M₂ hyp hU hf hodd T hT
  rcases hU with rfl | rfl
  · exact burnsideF429_c6_U4 hyp hf hT
  · exact hU5 f E Gp M₁ M₂ hyp hf hodd T hT

theorem burnsideF429_EvenU5c6_proof : burnsideF429_EvenU5c6 :=
  fun _ _ _ _ _ _ hyp hf hodd _ hT => burnsideF429b_c6_U5 hyp hf hodd hT

theorem burnsideF429_corr_of_U2c (hU2c : burnsideF429_EvenU2c) : burnsideF429_F_4_29_corr :=
  burnsideF429_corr_of (burnsideF429_Even2_of (burnsideF429_EvenU2_of hU2c))
    burnsideF429_Even5_proof
    (burnsideF429_Even6_of burnsideF429_EvenD6_proof
      (burnsideF429_EvenU6_of burnsideF429_EvenU5c6_proof))

end Even

end CFSG.ASVolI
