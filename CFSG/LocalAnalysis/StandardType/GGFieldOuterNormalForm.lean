module

public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem ggFieldOuterNormalForm_E78
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8) (α : MulAut (adjointGroup τ K)) (h2 : α * α = 1)
    (hout : ∀ c : adjointGroup τ K, α ≠ MulAut.conj c) :
    ∃ (e : ℕ) (σ : K ≃+* K) (g : adjointGroup τ K), f = 2 * e ∧ (∀ c, σ c = c ^ 2 ^ e) ∧
      α = MulAut.conj g * entrywiseAdjointAut τ σ := by
  obtain ⟨hex, Θ, hΘ, -, -, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hex α
  have hΘα : Θ α = σ := hΘ α g σ hgσ
  have hα2 : α ^ 2 = 1 := by simpa only [pow_two] using h2
  have hαeq : α = MulAut.conj g * entrywiseAdjointAut τ σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    simpa only [MulAut.mul_apply, MulAut.conj_apply, coe_entrywiseAdjointAut,
      Subgroup.coe_mul, Subgroup.coe_inv] using hgσ h
  rcases hinv α hα2 with h1 | ⟨heven, hpow⟩
  · have hσ1 : σ = 1 := by rw [← hΘα]; exact h1
    have hid : entrywiseAdjointAut τ (1 : K ≃+* K) = 1 := by
      have h1id : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
      refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
      rw [coe_entrywiseAdjointAut, MulAut.one_apply, Units.coe_map, h1id]
      exact entrywise_id (R := K) _
    exact absurd (by rw [hαeq, hσ1, hid, mul_one]) (hout g)
  · refine ⟨f / 2, σ, g, (Nat.two_mul_div_two_of_even heven).symm, fun c => ?_, hαeq⟩
    rw [← hΘα]
    exact hpow c

theorem ggFieldOuterNormalForm_F4
    {f : ℕ} (hf : 1 ≤ f) (hfe : Even f) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f)
    (α : MulAut (adjointGroup ReeTag.F4.tag K)) (h2 : α * α = 1)
    (hout : ∀ c : adjointGroup ReeTag.F4.tag K, α ≠ MulAut.conj c) :
    ∃ (e : ℕ) (g : adjointGroup ReeTag.F4.tag K), f = 2 * e ∧
      α = MulAut.conj g * ReeTag.F4.finiteFrobeniusAut K ^ e := by
  obtain ⟨-, hex, ⟨-, -, -, -⟩, hinv, -, hFr, -⟩ :=
    even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hex α
  have hα2 : α ^ 2 = 1 := by simpa only [pow_two] using h2
  rcases hinv α g (k : ℕ) k.isLt hgk hα2 with hk0 | hkf
  · exact absurd (by rw [hgk, hk0, pow_zero, mul_one]) (hout g)
  · obtain ⟨e, he⟩ := hfe
    refine ⟨e, g, by omega, ?_⟩
    rw [hgk, hkf, hFr e (by omega)]

end CFSG.StandardType
