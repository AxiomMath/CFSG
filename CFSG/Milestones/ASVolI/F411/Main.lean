module

public import CFSG.Milestones.ASVolI.F411.Inputs
public import CFSG.Milestones.ASVolI.F411.BT
public import CFSG.Milestones.ASVolI.F4Lie
public import CFSG.Milestones.ASVolI.F411.Core

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

theorem burnsideF411_exists_sylow_inf {E : Type} [Group E] [Finite E] {p : ℕ} [Fact p.Prime]
    {Gp M₁ M₂ : Subgroup E} (hN : Gp.Normal)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    ∃ T : Subgroup E, IsPGroup p T ∧ ¬ p ∣ T.index ∧ T ≤ M₁ ⊓ M₂ := by
  classical
  obtain ⟨⟨S₀, hS₀, hB⟩, -⟩ := hP
  have hS₀B : S₀ ≤ Gp ⊓ (M₁ ⊓ M₂) := hB ▸ le_inf hS₀.1 Subgroup.le_normalizer
  have hBi : ¬ p ∣ (Gp ⊓ (M₁ ⊓ M₂)).relIndex Gp := by
    intro h
    apply hS₀.2.2
    rw [← Subgroup.relIndex_mul_relIndex S₀ (Gp ⊓ (M₁ ⊓ M₂)) Gp hS₀B inf_le_left]
    exact Dvd.dvd.mul_left h _
  have hGH : Gp ⊔ (M₁ ⊓ M₂) = ⊤ := burnsideF411_sup_eq_top le_rfl hsplit
  have hidx : (M₁ ⊓ M₂).index = (Gp ⊓ (M₁ ⊓ M₂)).relIndex Gp := by
    have h1 := Subgroup.relIndex_mul_card Gp (M₁ ⊓ M₂)
    have hrel : Gp.relIndex (M₁ ⊓ M₂) = Gp.index := by
      rw [← Subgroup.relIndex_sup_left, hGH, Subgroup.relIndex_top_right]
    have h2 := Subgroup.card_mul_index (M₁ ⊓ M₂)
    have h3 := Subgroup.card_mul_index Gp
    have h4 := Subgroup.relIndex_mul_card (Gp ⊓ (M₁ ⊓ M₂)) Gp
    rw [inf_of_le_left (inf_le_left : Gp ⊓ (M₁ ⊓ M₂) ≤ Gp)] at h4
    rw [hrel] at h1
    have hpos : 0 < Gp.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hcpos : 0 < Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) := Nat.card_pos
    have e1 : Gp.index * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) * (M₁ ⊓ M₂).index =
        Gp.index * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) *
          (Gp ⊓ (M₁ ⊓ M₂)).relIndex Gp := by
      calc Gp.index * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) * (M₁ ⊓ M₂).index
          = Nat.card (M₁ ⊓ M₂ : Subgroup E) * (M₁ ⊓ M₂).index := by rw [h1]
        _ = Nat.card E := h2
        _ = Nat.card Gp * Gp.index := h3.symm
        _ = (Gp ⊓ (M₁ ⊓ M₂)).relIndex Gp * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) * Gp.index := by
          rw [h4]
        _ = Gp.index * Nat.card (Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) *
            (Gp ⊓ (M₁ ⊓ M₂)).relIndex Gp := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos hcpos) e1
  let T₀ : Sylow p ↥(M₁ ⊓ M₂) := default
  refine ⟨(T₀ : Subgroup ↥(M₁ ⊓ M₂)).map (M₁ ⊓ M₂).subtype, T₀.isPGroup'.map _, ?_,
    Subgroup.map_subtype_le _⟩
  rw [Subgroup.index_map_subtype, hidx]
  intro h
  rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
  · exact T₀.not_dvd_index h
  · exact hBi h

@[expose] def burnsideF411_LieInputs : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp ≠ ⊤ →
      burnsideF411_CentSylow p Gp ∧ burnsideF411_Swap M₁ M₂

theorem burnsideF411_rigidExt_of_inputs
    (h : burnsideF411_LieInputs) : burnsideF4n_F411RigidExt := by
  refine burnsideF411_rigidExt_of_local fun κ p f E _ Gp M₁ M₂ hyp hGp => ?_
  haveI : Finite E := hyp.finite
  haveI : Fact p.Prime := ⟨burnsideF4a_prime_of_isGenLie hyp.model⟩
  obtain ⟨hFC, hSw⟩ := h κ p f E Gp M₁ M₂ hyp hGp
  have hκ : κ.IsLie := not_or.mp fun h' => hGp (hyp.canonical h')
  have hBT := burnsideF411_borelTitsIn hyp hκ
  have hP := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  have hRK := burnsideF411_rankOne_of_F45 as_F_4_5 ChF.nativeChartCompatibility hyp
  have hQ := burnsideF411_pCoreOf_ne_bot as_F_4_5 as_F_4_6 ChF.nativeChartCompatibility hyp hκ
  exact ⟨burnsideF411_exists_sylow_inf hyp.normal hyp.split hP,
    burnsideF411_ident_of hyp.normal hyp.split hP hBT hFC hRK.1 hRK.2 hQ.1 hQ.2, hSw⟩

end CFSG.ASVolI
