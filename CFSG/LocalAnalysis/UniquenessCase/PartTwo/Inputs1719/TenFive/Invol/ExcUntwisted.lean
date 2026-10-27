module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcField
public import CFSG.LieType.Chevalley.CLSOddG2F4E8AllInvolutionFourGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LieType.Ree (ReeTag)


private lemma conj_invol_inverts_good {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {K : Type} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e)
    (g : adjointGroup τ K) (hσ : orderOf (MulAut.conj g) = 2) :
    ∃ x : adjointGroup τ K, orderOf x = p ∧ MulAut.conj g x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  have hsq : MulAut.conj (g * g) = 1 := by
    rw [map_mul, ← pow_two, ← hσ]
    exact pow_orderOf_eq_one _
  have hg2 : g * g = 1 :=
    mulAut_conj_injective_of_center_eq_bot (center_adjointGroup_eq_bot (τ := τ) (K := K))
      (hsq.trans (map_one (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))).symm)
  have hg1 : g ≠ 1 := by
    intro hg
    rw [hg, map_one, orderOf_one] at hσ
    omega
  obtain ⟨x, hx, hinv, hgood⟩ :=
    exists_inv_good_of_involution hτ hp hp2 hK h3 g hg2 hg1
  exact ⟨x, hx, by simpa [MulAut.conj_apply] using hinv, Or.inl hgood⟩

theorem involInvertsGood_F4_G2 {τ : Tag} {K : Type} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e)
    (hτ : τ = .F4 ∨ (τ = .G2 ∧ p ≠ 3)) : InvolInvertsGood p (adjointGroup τ K) := by
  classical
  have hτlist : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := by
    rcases hτ with rfl | ⟨rfl, -⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have hτlist5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with rfl | ⟨rfl, -⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hK
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  by_cases hin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup τ K)
  · obtain ⟨g, rfl⟩ := hin
    exact conj_invol_inverts_good hτlist hp hp2 hK h3 g hβ
  · obtain ⟨hnf, Θ, hΘ, -, hker, hinv⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 he K hK τ hτ
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf β
    have hΘβ := hΘ β g σ hgσ
    rcases hinv β hβ2 with h1 | ⟨hfe, hσc, -⟩
    · have h2 : β ∈ Θ.ker := MonoidHom.mem_ker.2 h1
      rw [hker] at h2
      exact absurd h2 hin
    · rw [hΘβ] at hσc
      have hσ1 : σ ≠ 1 := by
        intro h1
        apply hin
        have h2 : β ∈ Θ.ker := MonoidHom.mem_ker.2 (hΘβ.trans h1)
        rwa [hker] at h2
      refine exists_inv_good_of_field_coset hτlist5 hp hp2 he hK hfe h3 σ hσc hσ1 g 1 β ?_ hβ2
      intro u
      rw [hgσ u, rootDiagUnit_one, inv_one, mul_one, mul_one]

theorem involInvertsGood_E8 {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) :
    InvolInvertsGood p (adjointGroup .E8 K) := by
  classical
  have hτlist : (Tag.E8 : Tag) = .G2 ∨ Tag.E8 = .F4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hK
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  by_cases hin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup .E8 K)
  · obtain ⟨g, rfl⟩ := hin
    exact conj_invol_inverts_good hτlist hp hp2 hK h3 g hβ
  · obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form .E8 (Or.inr (Or.inr rfl)) K
    obtain ⟨g, a, σ, ε, hgaσ⟩ := hnf β
    obtain ⟨-, -, -, -, hsq, hquad⟩ :=
      ordinary_E_field_graph_quotient_and_involutions .E8 (Or.inr (Or.inr rfl)) K
    have hQ : exactQ Tag.E8 K ε = 1 := rfl
    have hβ' : ∀ u, (β u : ModGL Tag.E8 K) = (g : ModGL Tag.E8 K) * rootDiagUnit Tag.E8 a *
        Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.E8 K) * (rootDiagUnit Tag.E8 a)⁻¹ *
          (g : ModGL Tag.E8 K)⁻¹ := fun u => by
      rw [hgaσ u, hQ, inv_one, mul_one, mul_one]
    by_cases hσ1 : σ = 1
    · subst hσ1
      obtain ⟨c, hc⟩ :=
        CFSG.LieType.Chevalley.OddG2F4E8AllInvolution.rootDiagAut_mem_inner_of_det_eq_one
          det_cartan_E8 a (K := K)
      have h1 : ∀ u : adjointGroup Tag.E8 K,
          Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (u : ModGL Tag.E8 K) = u := fun u =>
        Units.ext (entrywise_id (R := K) _)
      have hβeq : β = MulAut.conj g * rootDiagAut Tag.E8 K a := MulEquiv.ext fun u =>
        Subtype.ext (by
          rw [hβ' u, h1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
            Subgroup.coe_inv, coe_rootDiagAut]
          group)
      exact (hin ⟨g * c, by rw [map_mul, hc, hβeq]⟩).elim
    · obtain ⟨hfe, hσc, -⟩ := hquad p e hp he hK σ (hsq β g a σ ε hgaσ hβ2) hσ1
      exact exists_inv_good_of_field_coset (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hp hp2 he hK
        hfe h3 σ hσc hσ1 g a β hβ' hβ2

private lemma involInvertsGood_G2_three_ree
    (hR : ∀ (a : ℕ) (L : Type) [Field L] [Finite L] [CharP L ReeTag.G2.prime], 1 ≤ a →
      Nat.card L = 3 ^ (2 * a + 1) → ∃ x : adjointGroup ReeTag.G2.tag L, orderOf x = 3 ∧
        ReeTag.G2.finiteReeAut L a x = x⁻¹ ∧ IsSpecialGood 3 x)
    {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 3 ^ e)
    (h3 : 3 < 3 ^ e) : InvolInvertsGood 3 (adjointGroup ReeTag.G2.tag K) := by
  classical
  have : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three he hK
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  by_cases hin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup ReeTag.G2.tag K)
  · obtain ⟨g, rfl⟩ := hin
    exact conj_invol_inverts_good (τ := ReeTag.G2.tag) (Or.inl rfl) Nat.prime_three (by norm_num)
      hK h3 g hβ
  · obtain ⟨-, hnf, -, hk, -, hEven, hOdd⟩ :=
      G2_three_exact_automorphism_normal_form he K hK
    obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf β
    rcases hk β g k k.2 hgk hβ2 with hk0 | hkf
    · refine absurd ⟨g, ?_⟩ hin
      rw [hgk, hk0, pow_zero, mul_one]
    · rw [hkf] at hgk
      rcases Nat.even_or_odd e with hfe | hfo
      · obtain ⟨-, σ, hσ1, -, hσc, -, hφσ⟩ := hEven hfe
        refine exists_inv_good_of_field_coset (τ := ReeTag.G2.tag) (Or.inl rfl) Nat.prime_three
          (by norm_num) he hK hfe h3 σ hσc hσ1 g 1 β ?_ hβ2
        intro u
        rw [rootDiagUnit_one, inv_one, mul_one, mul_one, hgk, MulAut.mul_apply, MulAut.conj_apply,
          Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hφσ]
      · obtain ⟨b, hb⟩ := hfo
        obtain ⟨-, hFb, -⟩ := hOdd b hb
        rw [hFb] at hgk
        have hb1 : 1 ≤ b := by
          rcases Nat.eq_zero_or_pos b with hb0 | hbpos
          · exfalso
            rw [hb0] at hb
            norm_num at hb
            rw [hb] at h3
            norm_num at h3
          · exact hbpos
        have hK' : Nat.card K = 3 ^ (2 * b + 1) := by rw [hK, hb]
        obtain ⟨ψ, hψ⟩ :=
          CFSG.LieType.Ree.G2_exceptional_coset_involution_conj b K hK' g
            (by rw [← hgk]; exact hβ2)
        have hconj : β = ψ⁻¹ * ReeTag.G2.finiteReeAut K b * ψ⁻¹⁻¹ := by
          rw [hgk]
          have h1 := congrArg (fun φ => ψ⁻¹ * φ * ψ) hψ
          rw [show ψ⁻¹ * (ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K b) * ψ⁻¹) * ψ
              = MulAut.conj g * ReeTag.G2.finiteReeAut K b from by group] at h1
          rw [inv_inv]
          exact h1
        obtain ⟨x, hx, hFinv, hxgood⟩ := hR b K hb1 hK'
        exact exists_inv_good_of_conj hconj hx hFinv (Or.inl hxgood)

theorem involInvertsGood_G2_three
    (hR : ∀ (a : ℕ) (L : Type) [Field L] [Finite L] [CharP L ReeTag.G2.prime], 1 ≤ a →
      Nat.card L = 3 ^ (2 * a + 1) → ∃ x : adjointGroup ReeTag.G2.tag L, orderOf x = 3 ∧
        ReeTag.G2.finiteReeAut L a x = x⁻¹ ∧ IsSpecialGood 3 x)
    {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = 3 ^ e)
    (h3 : 3 < 3 ^ e) : InvolInvertsGood 3 (adjointGroup .G2 K) :=
  involInvertsGood_G2_three_ree hR he hK h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
