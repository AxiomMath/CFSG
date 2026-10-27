module

public import CFSG.RankThree.PartOne.KE6.Tw6Weyl
public import CFSG.RankThree.Classical2.TwistedE6Phi3Transport
public import CFSG.RankThree.PartOne.KE.A1Main

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.Lattice (e6T3W)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

abbrev tw6N (Ω : Type) [Field Ω] :
    ModGL Tag.E6 Ω :=
  canonicalRep (coxeterSystem Tag.E6) Ω tw6W

variable (Ω Fr) in
@[expose] def tw6Theta :
    ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj (tw6N Ω)).toMonoidHom.comp (twistE6 Ω Fr)

theorem tw6Theta_apply
    (g : ModGL Tag.E6 Ω) :
    tw6Theta Ω Fr g = tw6N Ω * twistE6 Ω Fr g * (tw6N Ω)⁻¹ :=
  rfl

theorem twistedFixedPoints_tw6N :
    twistedFixedPoints (tw6N Ω) (twistE6 Ω Fr) = (tw6Theta Ω Fr).eqLocus (MonoidHom.id _) :=
  rfl

theorem tw6Theta_injective : Function.Injective (tw6Theta Ω Fr) := by
  intro a b h
  rw [tw6Theta_apply, tw6Theta_apply] at h
  have h2 : twistE6 Ω Fr a = twistE6 Ω Fr b := mul_left_cancel (mul_right_cancel h)
  exact twistHom_injective TwistTag.E6 Ω Fr h2

theorem exists_tw6Theta_pinnedX {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ ε : Ω, ε * ε = 1 ∧ ∀ c : Ω, tw6Theta Ω Fr (pinnedX Tag.E6 Ω α c) =
      pinnedX Tag.E6 Ω (-(e6T3W • α)) (ε * Fr c) := by
  obtain ⟨ε₁, h₁, hF⟩ := exists_twistHom_pinnedX TwistTag.E6 Fr (α := α) hα
  have hF' : ∀ c : Ω, twistE6 Ω Fr (pinnedX Tag.E6 Ω α c) =
      pinnedX Tag.E6 Ω (permLattice e6Rho α) (ε₁ * Fr c) := hF
  have hρα : IsRoot Tag.E6 (permLattice e6Rho α) := hα.permLattice TwistTag.E6.cartan_perm
  obtain ⟨ε₂, h₂, hN⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω tw6W hρα
  refine ⟨ε₂ * ε₁, by linear_combination (ε₂ * ε₂) * h₁ + h₂, fun c => ?_⟩
  rw [tw6Theta_apply, hF', hN, tw6W_smul, permLattice_e6Rho_e6Rho, mul_assoc]

variable (Ω Fr) in
@[expose] def tw6ThetaConj
    (x : WeylGroup Tag.E6) : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω x)).toMonoidHom.comp
    ((tw6Theta Ω Fr).comp (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹).toMonoidHom)

theorem tw6ThetaConj_apply
    (x : WeylGroup Tag.E6) (g : ModGL Tag.E6 Ω) :
    tw6ThetaConj Ω Fr x g = canonicalRep (coxeterSystem Tag.E6) Ω x *
      tw6Theta Ω Fr ((canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ * g *
        canonicalRep (coxeterSystem Tag.E6) Ω x) * (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ := by
  simp only [tw6ThetaConj, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, inv_inv]

theorem tw6ThetaConj_conj
    (x : WeylGroup Tag.E6) (g : ModGL Tag.E6 Ω) :
    tw6ThetaConj Ω Fr x (canonicalRep (coxeterSystem Tag.E6) Ω x * g *
        (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹) =
      canonicalRep (coxeterSystem Tag.E6) Ω x * tw6Theta Ω Fr g *
        (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ := by
  rw [tw6ThetaConj_apply]
  congr 3
  group

theorem tw6ThetaConj_injective (x : WeylGroup Tag.E6) :
    Function.Injective (tw6ThetaConj Ω Fr x) := by
  intro a b h
  rw [tw6ThetaConj_apply, tw6ThetaConj_apply] at h
  have h' := tw6Theta_injective (mul_left_cancel (mul_right_cancel h))
  exact mul_left_cancel (mul_right_cancel h')

theorem exists_conj_tw6Theta_pinnedX (x : WeylGroup Tag.E6)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    ∃ ε : Ω, ε * ε = 1 ∧ ∀ c : Ω,
      tw6ThetaConj Ω Fr x (pinnedX Tag.E6 Ω β c) =
        pinnedX Tag.E6 Ω (-((x * e6T3W * x⁻¹) • β)) (ε * Fr c) := by
  have hβ' : IsRoot Tag.E6 (x⁻¹ • β) := CFSG.LieType.Chevalley.IsRoot.smul hβ x⁻¹
  obtain ⟨ε₁, h₁, hX₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω x hβ'
  rw [smul_inv_smul] at hX₁
  have hinv : ∀ c : Ω, (canonicalRep (coxeterSystem Tag.E6) Ω x)⁻¹ * pinnedX Tag.E6 Ω β c *
      canonicalRep (coxeterSystem Tag.E6) Ω x = pinnedX Tag.E6 Ω (x⁻¹ • β) (ε₁ * c) :=
    fun c => by
      have h := hX₁ (ε₁ * c)
      rw [← mul_assoc, h₁, one_mul] at h
      rw [← h]
      group
  obtain ⟨ε₂, h₂, hθ⟩ := exists_tw6Theta_pinnedX (Fr := Fr) hβ'
  have hγ : IsRoot Tag.E6 (-(e6T3W • x⁻¹ • β)) :=
    CFSG.LieType.Chevalley.IsRoot.neg (CFSG.LieType.Chevalley.IsRoot.smul hβ' e6T3W)
  obtain ⟨ε₃, h₃, hX₃⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω x hγ
  have hσ₁ : Fr ε₁ = ε₁ := ringHom_apply_eq_of_mul_self Fr h₁
  refine ⟨ε₃ * ε₂ * ε₁, by linear_combination (ε₃ * ε₃) * (ε₂ * ε₂) * h₁ +
    (ε₃ * ε₃) * h₂ + h₃, fun c => ?_⟩
  rw [tw6ThetaConj_apply, hinv, hθ, map_mul, hσ₁, hX₃, smul_neg, ← mul_smul, ← mul_smul]
  congr 1
  ring

end CFSG.RankThree.PartOne.KE6
