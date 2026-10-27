module

public import CFSG.Milestones.ASVolI.F431.A35Engine
public import CFSG.Milestones.ASVolI.F431.AU5Final

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open scoped commutatorElement

@[expose] def burnsideF4m_A35Rest'' : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .F4tw ∧ f < 3) ∨ κ = .Tits ∨ (κ = .U4 ∧ f < 2) ∨
      (κ = .U5 ∧ f < 2)) →
    ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j))

section D4

set_option linter.unusedSectionVars false


open CFSG.Quasithin.H13.F431.D4q.Struct in
theorem burnsideF4m_core1_D4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) : burnsideF4m_Core1 Gp M₁ := by
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, σ, hσ3, hf1, hK, hσq, Ψ, h1, -⟩ :=
    burnsideF4m_D4_chart hyp.toHypF_4_4g
  have hc : ∀ a b : E, ⁅a, b⁆ ∈ Gp := burnsideF4m_commutator_mem_of_out hyp.centralizer_trivial
    (burnsideF4m_out_transport Ψ (burnsideF4m_D4_out_comm σ hf1 hK hσq))
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  exact burnsideF4m_core1_of_model hc _ hφ (burnsideF4m_inf_eq_map Ψ h1)
    (burnsideF4m_D4_P0_center_le σ hσ3 hf1 hK hσq)

theorem burnsideF4m_A35_D4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .D4tw f Gp M₁ M₂ β ε z) (hodd : Odd Gp.index) :
    ∃ (K' : Type) (_ : Group K') (_ : Finite K') (θ : E ≃* K') (N1 N2 : Subgroup K')
      (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁) (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂)
      (T : Subgroup K') (I : Finset K') (z₀' : K'), F431LieK T N1 N2 I z₀' ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) i)
          (amalgamMap ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
            ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) j) := by
  haveI := hyp.amalgam.finite
  obtain ⟨chart, hm⟩ := hyp.amalgam.lie_amalgam
  obtain ⟨K, _, _, _, σ, hσ3, hf1, hK, hσq, φ, hP1, hP2, -⟩ := burnsideF4m_A42_chart_D4 chart hm
  have S1 := CFSG.Quasithin.H13.F431.D4q.Loc.stdTwo_d4 σ hσ3 hf1 hK hσq
  have S3 := CFSG.Quasithin.H13.F431.D4q.Loc.stdOrient_d4 σ hσ3 hf1 hK hσq
  have YS := CFSG.Quasithin.H13.F431.D4q.Hex.d4_yamStd σ hf1 hK hσq
  have hBT : CFSG.LieType.BorelTits.Holds ↥Gp 2 :=
    CFSG.LieType.BorelTits.holds_of_lieModel (burnsideF4g_lieModel_D4tw hyp.amalgam.model)
      (by decide)
  exact burnsideF4m_A35_engine hyp (by decide) hodd (burnsideF4m_core1_D4 hyp.amalgam) S1 S3
    YS.isYAmalgamPair YS.above φ hP1 hP2 hBT

theorem burnsideF4m_F_4_35_D4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}
    (hyp : HypF_4_31 .D4tw f Gp M₁ M₂ β ε z) (i j : ↥(M₁ ⊓ M₂))
    (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hi1 : i ≠ 1) (hj1 : j ≠ 1) (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  have hU : ¬ ((GLKind.D4tw = .U4 ∨ GLKind.D4tw = .U5) ∧ f = 1) := by
    rintro ⟨h | h, -⟩ <;> exact absurd h (by decide)
  obtain ⟨K', _, _, θ, N1, N2, h1, h2, T, I, z₀', L, hnf⟩ :=
    burnsideF4m_A35_D4 hyp (burnsideF4m_odd_index_nonU2 hyp hU)
  exact burnsideF4m_F_4_35_of_lieK hyp (by decide) (by decide) θ h1 h2 L hnf i j hi hj hi1 hi2
    hj1 hj2

theorem burnsideF4m_A35Rest'_of'' (hrest : burnsideF4m_A35Rest'') : burnsideF4m_A35Rest' := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hk i j hi hj hi1 hj1 hi2 hj2
  rcases hk with hk | ⟨rfl, -⟩ | hk | hk | hk | hk
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inl hk) i j hi hj hi1 hj1 hi2 hj2
  · exact burnsideF4m_F_4_35_D4 hyp i j hi hj hi1 hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inl hk)) i j hi hj hi1 hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inl hk))) i j hi hj hi1 hj1 hi2
      hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inr (Or.inl hk)))) i j hi hj hi1
      hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr (Or.inr (Or.inr hk)))) i j hi hj hi1
      hj1 hi2 hj2

end D4

end CFSG.ASVolI
