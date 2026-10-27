module

public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.RankThree.E6.LargePrimeStabilizers

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ringHom_apply_eq_of_mul_self {K : Type*} [Field K] (σ : K →+* K) {ε : K}
    (h : ε * ε = 1) : σ ε = ε := by
  have h2 : (ε - 1) * (ε + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h1 | h1
  · rw [sub_eq_zero.1 h1, map_one]
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_one]

theorem exists_twistHom_pinnedX (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K,
      twistHom t K σ (pinnedX t.tag K α c) = pinnedX t.tag K (permLattice t.perm α) (ε * σ c) := by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := K) t hα
  refine ⟨ε, hε, fun c => ?_⟩
  have hσ : Units.map (entrywiseHom σ) (pinnedX t.tag K α c) = pinnedX t.tag K α (σ c) :=
    Units.ext (entrywise_pinnedX σ α c)
  rw [twistHom_apply, hσ, h]

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem exists_phi3Theta_pinnedX {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ ε : Ω, ε * ε = 1 ∧ ∀ c : Ω, phi3Theta Ω Fr (pinnedX Tag.E6 Ω α c) =
      pinnedX Tag.E6 Ω (-(e6CoxeterSq • α)) (ε * Fr c) := by
  obtain ⟨ε₁, h₁, hF⟩ := exists_twistHom_pinnedX TwistTag.E6 Fr (α := α) hα
  have hF' : ∀ c : Ω, twistE6 Ω Fr (pinnedX Tag.E6 Ω α c) =
      pinnedX Tag.E6 Ω (permLattice e6Rho α) (ε₁ * Fr c) := hF
  have hρα : IsRoot Tag.E6 (permLattice e6Rho α) := hα.permLattice TwistTag.E6.cartan_perm
  obtain ⟨ε₂, h₂, hN⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω phi3V hρα
  refine ⟨ε₂ * ε₁, by linear_combination (ε₂ * ε₂) * h₁ + h₂, fun c => ?_⟩
  rw [phi3Theta_apply, hF', hN, phi3V_smul, permLattice_e6Rho_e6Rho, mul_assoc]

theorem exists_conj_phi3Theta_pinnedX (w : WeylGroup Tag.E6) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) :
    ∃ ε : Ω, ε * ε = 1 ∧ ∀ c : Ω,
      canonicalRep (coxeterSystem Tag.E6) Ω w * phi3Theta Ω Fr
          ((canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ * pinnedX Tag.E6 Ω β c *
            canonicalRep (coxeterSystem Tag.E6) Ω w) *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ =
        pinnedX Tag.E6 Ω (-((w * e6CoxeterSq * w⁻¹) • β)) (ε * Fr c) := by
  have hβ' : IsRoot Tag.E6 (w⁻¹ • β) := CFSG.LieType.Chevalley.IsRoot.smul hβ w⁻¹
  obtain ⟨ε₁, h₁, hX₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω w hβ'
  rw [smul_inv_smul] at hX₁
  have hinv : ∀ c : Ω, (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ * pinnedX Tag.E6 Ω β c *
      canonicalRep (coxeterSystem Tag.E6) Ω w = pinnedX Tag.E6 Ω (w⁻¹ • β) (ε₁ * c) :=
    fun c => by
      have h := hX₁ (ε₁ * c)
      rw [← mul_assoc, h₁, one_mul] at h
      rw [← h]
      group
  obtain ⟨ε₂, h₂, hθ⟩ := exists_phi3Theta_pinnedX (Fr := Fr) hβ'
  have hγ : IsRoot Tag.E6 (-(e6CoxeterSq • w⁻¹ • β)) :=
    CFSG.LieType.Chevalley.IsRoot.neg (CFSG.LieType.Chevalley.IsRoot.smul hβ' e6CoxeterSq)
  obtain ⟨ε₃, h₃, hX₃⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω w hγ
  have hσ₁ : Fr ε₁ = ε₁ := ringHom_apply_eq_of_mul_self Fr h₁
  refine ⟨ε₃ * ε₂ * ε₁, by linear_combination (ε₃ * ε₃) * (ε₂ * ε₂) * h₁ +
    (ε₃ * ε₃) * h₂ + h₃, fun c => ?_⟩
  rw [hinv, hθ, map_mul, hσ₁, hX₃, smul_neg, ← mul_smul, ← mul_smul]
  congr 1
  ring

variable (Ω Fr) in
@[expose] def phi3ThetaConj (w : WeylGroup Tag.E6) : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom.comp
    ((phi3Theta Ω Fr).comp (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹).toMonoidHom)

theorem phi3ThetaConj_apply (w : WeylGroup Tag.E6) (g : ModGL Tag.E6 Ω) :
    phi3ThetaConj Ω Fr w g = canonicalRep (coxeterSystem Tag.E6) Ω w *
      phi3Theta Ω Fr ((canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ * g *
        canonicalRep (coxeterSystem Tag.E6) Ω w) * (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ := by
  simp only [phi3ThetaConj, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, inv_inv]

theorem phi3ThetaConj_conj (w : WeylGroup Tag.E6) (g : ModGL Tag.E6 Ω) :
    phi3ThetaConj Ω Fr w (canonicalRep (coxeterSystem Tag.E6) Ω w * g *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) =
      canonicalRep (coxeterSystem Tag.E6) Ω w * phi3Theta Ω Fr g *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ := by
  rw [phi3ThetaConj_apply]
  congr 3
  group

theorem phi3Theta_injective : Function.Injective (phi3Theta Ω Fr) := by
  intro a b h
  rw [phi3Theta_apply, phi3Theta_apply] at h
  have h2 : twistE6 Ω Fr a = twistE6 Ω Fr b := mul_left_cancel (mul_right_cancel h)
  exact twistHom_injective TwistTag.E6 Ω Fr h2

theorem phi3ThetaConj_injective (w : WeylGroup Tag.E6) :
    Function.Injective (phi3ThetaConj Ω Fr w) := by
  intro a b h
  rw [phi3ThetaConj_apply, phi3ThetaConj_apply] at h
  have h' := phi3Theta_injective (mul_left_cancel (mul_right_cancel h))
  exact mul_left_cancel (mul_right_cancel h')

end CFSG.RankThree.Classical2
