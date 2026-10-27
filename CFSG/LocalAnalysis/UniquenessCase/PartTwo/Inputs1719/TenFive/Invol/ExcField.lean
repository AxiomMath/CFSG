module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRootE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRootG2
public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.StandardType.AutSt (entrywiseAdjointAut_xPar)


theorem exists_entrywise_inv_good {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    ∃ x : adjointGroup τ K, orderOf x = p ∧ entrywiseAdjointAut τ σ x = x⁻¹ ∧
      IsSpecialGood p x := by
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have h := congrArg (fun φ : K ≃+* K => φ c) hσ2
    simpa only [pow_two, RingAut.mul_apply, RingAut.one_apply] using h
  obtain ⟨c₀, hc₀⟩ : ∃ c, σ c ≠ c := by
    by_contra! h
    exact hσ1 (RingEquiv.ext h)
  have hc₀' : c₀ ≠ σ c₀ := fun h => hc₀ h.symm
  let θ : K := c₀ - σ c₀
  have hθ : θ ≠ 0 := sub_ne_zero.mpr hc₀'
  have hσθ : σ θ = -θ := by
    change σ (c₀ - σ c₀) = -(c₀ - σ c₀)
    rw [map_sub, hσσ]
    ring
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  ·
    let i : Fin Tag.G2.rank := ⟨0, by decide⟩
    have hsingle : (![1, 0] : Fin Tag.G2.rank → ℤ) = Pi.single i 1 := by
      ext j
      fin_cases j <;> rfl
    have hx : xPar (rootOperatorFamily Tag.G2) (Pi.single i 1) θ =
        xPar (rootOperatorFamily Tag.G2) ![1, 0] θ :=
      congrArg (fun γ : Fin Tag.G2.rank → ℤ =>
        xPar (rootOperatorFamily Tag.G2) γ θ) hsingle.symm
    refine ⟨xPar (rootOperatorFamily Tag.G2) (Pi.single i 1) θ, ?_, ?_, ?_⟩
    · exact orderOf_xPar (F := rootOperatorFamily Tag.G2) hp (isRoot_single Tag.G2 i) hθ
    · rw [entrywiseAdjointAut_xPar, hσθ, ← xPar_neg]
    · rw [hx]
      exact (isSpecialGood_xPar_G2 hp hp2 hK h3 θ).1
  ·
    let i : Fin Tag.F4.rank := ⟨0, by decide⟩
    refine ⟨xPar (rootOperatorFamily Tag.F4) (Pi.single i 1) θ, ?_, ?_, ?_⟩
    · exact orderOf_xPar (F := rootOperatorFamily Tag.F4) hp (isRoot_single Tag.F4 i) hθ
    · rw [entrywiseAdjointAut_xPar, hσθ, ← xPar_neg]
    · exact isSpecialGood_xPar_single (Or.inl rfl) hp hp2 hK h3 i θ
  ·
    let i : Fin Tag.E6.rank := ⟨0, by decide⟩
    refine ⟨xPar (rootOperatorFamily Tag.E6) (Pi.single i 1) θ, ?_, ?_, ?_⟩
    · exact orderOf_xPar (F := rootOperatorFamily Tag.E6) hp (isRoot_single Tag.E6 i) hθ
    · rw [entrywiseAdjointAut_xPar, hσθ, ← xPar_neg]
    · exact isSpecialGood_xPar_single (Or.inr (Or.inl rfl)) hp hp2 hK h3 i θ
  ·
    let i : Fin Tag.E7.rank := ⟨0, by decide⟩
    refine ⟨xPar (rootOperatorFamily Tag.E7) (Pi.single i 1) θ, ?_, ?_, ?_⟩
    · exact orderOf_xPar (F := rootOperatorFamily Tag.E7) hp (isRoot_single Tag.E7 i) hθ
    · rw [entrywiseAdjointAut_xPar, hσθ, ← xPar_neg]
    · exact isSpecialGood_xPar_single (Or.inr (Or.inr (Or.inl rfl))) hp hp2 hK h3 i θ
  ·
    let i : Fin Tag.E8.rank := ⟨0, by decide⟩
    refine ⟨xPar (rootOperatorFamily Tag.E8) (Pi.single i 1) θ, ?_, ?_, ?_⟩
    · exact orderOf_xPar (F := rootOperatorFamily Tag.E8) hp (isRoot_single Tag.E8 i) hθ
    · rw [entrywiseAdjointAut_xPar, hσθ, ← xPar_neg]
    · exact isSpecialGood_xPar_single (Or.inr (Or.inr (Or.inr rfl))) hp hp2 hK h3 i θ

theorem exists_inv_good_of_field_coset {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (hfe : Even e) (h3 : 3 < p ^ e) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ (e / 2)))
    (hσ1 : σ ≠ 1) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (β : MulAut (adjointGroup τ K))
    (hβ : ∀ u, (β u : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hβ2 : β ^ 2 = 1) :
    ∃ x : adjointGroup τ K, orderOf x = p ∧ β x = x⁻¹ ∧
      (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  obtain ⟨r, hr⟩ := hfe
  have : Fintype K := Fintype.ofFinite K
  have he' : 1 ≤ e / 2 := by omega
  have hK' : Nat.card K = (p ^ (e / 2)) ^ 2 := by
    rw [hK, ← pow_mul]
    congr 1
    omega
  obtain ⟨hQ1, -⟩ :=
    exceptional_Lang_quadratic_field_coset_conjugacy hp he' K hK' σ.toRingHom hσ
  obtain ⟨_, _, hall⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hall g a
  obtain ⟨ψ, hψ, -⟩ := hconj β hβ (by rw [← sq]; exact hβ2)
  have hψeq : ψ * β * ψ⁻¹ = entrywiseAdjointAut τ σ := by
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    exact (hψ u).trans (coe_entrywiseAdjointAut τ σ u).symm
  have hβeq : β = ψ⁻¹ * entrywiseAdjointAut τ σ * ψ⁻¹⁻¹ := by
    rw [← hψeq]
    group
  have hσ2 : σ ^ 2 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← sq, ← hK', Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hK
  obtain ⟨x, hxo, hxi, hxg⟩ :=
    exists_entrywise_inv_good hτ hp hp2 hK h3 σ hσ2 hσ1
  exact exists_inv_good_of_conj (σ₀ := entrywiseAdjointAut τ σ) (γ := ψ⁻¹) hβeq hxo hxi
    (Or.inl hxg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
