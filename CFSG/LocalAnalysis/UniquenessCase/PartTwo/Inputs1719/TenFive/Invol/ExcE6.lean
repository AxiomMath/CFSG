module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcHeads
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcReeG2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcInnerDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcE6GraphCoset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem exists_inv_good_E6_graph_field {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = (p ^ e) ^ 2) (δ : K →+* K)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) (hδ1 : ∃ c, δ c ≠ c) (g : adjointGroup TwistTag.E6.tag K)
    (a : Fin TwistTag.E6.tag.rank → Kˣ) (β : MulAut (adjointGroup TwistTag.E6.tag K))
    (hβg : ∀ u : adjointGroup TwistTag.E6.tag K, (β u : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ *
          (rootDiagUnit TwistTag.E6.tag a)⁻¹ * (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hβ : β ^ 2 = 1) :
    ∃ x : adjointGroup TwistTag.E6.tag K, orderOf x = p ∧ β x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, _, -, hall⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hK δ hδ
  obtain ⟨-, hconj⟩ := hall g a
  obtain ⟨ψ, hψ, -⟩ := hconj β hβg (by rw [← sq]; exact hβ)
  have hK' : Nat.card K = p ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK'
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h3 : 3 < p ^ (2 * e) :=
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (2 * e) := Nat.pow_le_pow_right hp.pos (by omega)
  have hδ2 : ∀ c, δ (δ c) = c := fun c => by
    rw [hδ, hδ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  obtain ⟨x, hx, hinv, hgood⟩ :=
    exists_diagramMap_entrywise_inv_good_E6 hp hp2 hK' h3 δ hδ2 hδ1
  have hσ₀ : (ψ * β * ψ⁻¹) x = x⁻¹ := Subtype.ext ((hψ x).trans hinv)
  have hβeq : β = ψ⁻¹ * (ψ * β * ψ⁻¹) * ψ⁻¹⁻¹ := by group
  exact exists_inv_good_of_conj hβeq hx hσ₀ (Or.inl hgood)

theorem involInvertsGood_E6 {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) :
    InvolInvertsGood p (adjointGroup .E6 K) := by
  classical
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hK
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  have hβ1 : β ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hβ
    omega
  obtain ⟨-, -, hexist⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hexpr⟩ := hexist β
  obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hσ2 : σ ^ 2 = 1 := hsq β g a σ ε hexpr hβ2
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h := ε.2
    change (ε : ℕ) < 2 at h
    omega
  have hQ : exactQ Tag.E6 K ε = (diagramMap TwistTag.E6 K : ModGL Tag.E6 K) ^ (ε : ℕ) := rfl
  have hQ0 : (ε : ℕ) = 0 → exactQ Tag.E6 K ε = 1 := fun h0 => by
    rw [hQ, h0, pow_zero]
    rfl
  have hQ1 : (ε : ℕ) = 1 → exactQ Tag.E6 K ε = (diagramMap TwistTag.E6 K : ModGL Tag.E6 K) :=
    fun h0 => by rw [hQ, h0, pow_one]
  by_cases hσ : σ = 1
  · subst hσ
    have h1 : ∀ h : adjointGroup Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
        (h : ModGL Tag.E6 K) = h := fun h => Units.ext (entrywise_id _)
    rcases hε with h0 | h0
    · obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_good_inner_diagonal
        (Or.inr (Or.inr (Or.inl rfl))) hp hp2 hK h3 β hβ2 hβ1 g a fun h => by
          rw [hexpr h, hQ0 h0, h1 h, inv_one, mul_one, mul_one]
      exact ⟨x, hx, hinv, Or.inl hgood⟩
    · obtain ⟨x, hx, hinv, hgood⟩ := exists_inv_good_E6_graph hp hp2 hK h3 g a β (fun h => by
        have h2 := hexpr h
        rw [hQ1 h0, h1 h] at h2
        exact h2) hβ2
      exact ⟨x, hx, hinv, Or.inl hgood⟩
  · obtain ⟨hfe, hσc, -⟩ := hfacts p e hp he hK σ hσ2 hσ
    rcases hε with h0 | h0
    · exact exists_inv_good_of_field_coset (Or.inr (Or.inr (Or.inl rfl))) hp hp2 he hK hfe h3 σ
        hσc hσ g a β (fun u => by rw [hexpr u, hQ0 h0, inv_one, mul_one, mul_one]) hβ2
    · obtain ⟨e₀, rfl⟩ : ∃ e₀, e = 2 * e₀ := ⟨e / 2, (Nat.two_mul_div_two_of_even hfe).symm⟩
      have he₀ : 1 ≤ e₀ := by omega
      have hK' : Nat.card K = (p ^ e₀) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
      have hσe : ∀ c, σ c = c ^ (p ^ e₀) := fun c => by
        rw [hσc, Nat.mul_div_cancel_left e₀ two_pos]
      obtain ⟨c₀, hc₀⟩ : ∃ c, σ c ≠ c := by
        by_contra! h
        exact hσ (RingEquiv.ext h)
      exact exists_inv_good_E6_graph_field hp hp2 he₀ hK' σ.toRingHom hσe ⟨c₀, hc₀⟩ g a β
        (fun u => by
          have h2 := hexpr u
          rw [hQ1 h0] at h2
          exact h2) hβ2

theorem involQAt_E6 : InvolQAt .E6 := by
  intro S _ _ n p e hp2 h3 _ hS
  obtain ⟨⟨hp, he, -⟩, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  exact InvolInvertsGood.of_mulEquiv φ.symm (involInvertsGood_E6 hp hp2 he hK h3)

theorem w4Lem10_5InvolQ_of_E7_twisted (hE7 : InvolQAt .E7) (h2E6 : InvolQAt .twistedE6)
    (h3D4 : InvolQAt .trialityD4) : W4Lem10_5InvolQ :=
  w4Lem10_5InvolQ_of_remaining exists_ree_inv_good involQAt_E6 hE7 h2E6 h3D4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
