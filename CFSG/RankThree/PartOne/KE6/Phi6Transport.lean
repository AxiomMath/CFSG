module

public import CFSG.RankThree.Classical2.TwistedE6Phi3Transport
public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.RankThree.PartOne.KE6.Phi6Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)

variable {L : Type} [Field L] {Fr : L →+* L}

variable (L Fr) in
@[expose] def phi6Theta :
    ModGL Tag.E6 L →* ModGL Tag.E6 L :=
  (MulAut.conj (phi6N L)).toMonoidHom.comp (Units.map (entrywiseHom Fr))

theorem phi6Theta_apply
    (g : ModGL Tag.E6 L) :
    phi6Theta L Fr g = phi6N L * Units.map (entrywiseHom Fr) g * (phi6N L)⁻¹ :=
  rfl

theorem twistedFixedPoints_phi6N :
    twistedFixedPoints (phi6N L) (Units.map (entrywiseHom Fr)) =
      (phi6Theta L Fr).eqLocus (MonoidHom.id _) :=
  rfl

theorem phi6Theta_injective :
    Function.Injective (phi6Theta L Fr) := by
  intro a b h
  rw [phi6Theta_apply, phi6Theta_apply] at h
  have h2 : Units.map (entrywiseHom Fr) a = Units.map (entrywiseHom Fr) b :=
    mul_left_cancel (mul_right_cancel h)
  have hinj : Function.Injective (Units.map (entrywiseHom Fr) : ModGL Tag.E6 L →* ModGL Tag.E6 L) :=
    Units.map_injective (f := entrywiseHom Fr) (entrywise_injective (σ := Fr))
  exact hinj h2

theorem exists_phi6Theta_pinnedX {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ ε : L, ε * ε = 1 ∧ ∀ c : L, phi6Theta L Fr (pinnedX Tag.E6 L α c) =
      pinnedX Tag.E6 L (e6CoxeterSq • α) (ε * Fr c) := by
  obtain ⟨ε, hε, hN⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L e6CoxeterSq hα
  refine ⟨ε, hε, fun c => ?_⟩
  have hσ : Units.map (entrywiseHom Fr) (pinnedX Tag.E6 L α c) = pinnedX Tag.E6 L α (Fr c) :=
    Units.ext (entrywise_pinnedX Fr α c)
  rw [phi6Theta_apply, hσ, hN]

variable (L Fr) in
@[expose] def phi6ThetaConj
    (w : WeylGroup Tag.E6) : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L w)).toMonoidHom.comp
    ((phi6Theta L Fr).comp (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹).toMonoidHom)

theorem phi6ThetaConj_apply
    (w : WeylGroup Tag.E6) (g : ModGL Tag.E6 L) :
    phi6ThetaConj L Fr w g = canonicalRep (coxeterSystem Tag.E6) L w *
      phi6Theta L Fr ((canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * g *
        canonicalRep (coxeterSystem Tag.E6) L w) * (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ := by
  simp only [phi6ThetaConj, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, inv_inv]

theorem phi6ThetaConj_conj
    (w : WeylGroup Tag.E6) (g : ModGL Tag.E6 L) :
    phi6ThetaConj L Fr w (canonicalRep (coxeterSystem Tag.E6) L w * g *
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) =
      canonicalRep (coxeterSystem Tag.E6) L w * phi6Theta L Fr g *
        (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ := by
  rw [phi6ThetaConj_apply]
  congr 3
  group

theorem phi6ThetaConj_injective
    (w : WeylGroup Tag.E6) : Function.Injective (phi6ThetaConj L Fr w) := by
  intro a b h
  rw [phi6ThetaConj_apply, phi6ThetaConj_apply] at h
  have h' := phi6Theta_injective (mul_left_cancel (mul_right_cancel h))
  exact mul_left_cancel (mul_right_cancel h')

theorem exists_conj_phi6Theta_pinnedX (w : WeylGroup Tag.E6)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    ∃ ε : L, ε * ε = 1 ∧ ∀ c : L,
      phi6ThetaConj L Fr w (pinnedX Tag.E6 L β c) =
        pinnedX Tag.E6 L ((w * e6CoxeterSq * w⁻¹) • β) (ε * Fr c) := by
  have hβ' : IsRoot Tag.E6 (w⁻¹ • β) := CFSG.LieType.Chevalley.IsRoot.smul hβ w⁻¹
  obtain ⟨ε₁, h₁, hX₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hβ'
  rw [smul_inv_smul] at hX₁
  have hinv : ∀ c : L, (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ * pinnedX Tag.E6 L β c *
      canonicalRep (coxeterSystem Tag.E6) L w = pinnedX Tag.E6 L (w⁻¹ • β) (ε₁ * c) :=
    fun c => by
      have h := hX₁ (ε₁ * c)
      rw [← mul_assoc, h₁, one_mul] at h
      rw [← h]
      group
  obtain ⟨ε₂, h₂, hθ⟩ := exists_phi6Theta_pinnedX (Fr := Fr) hβ'
  have hγ : IsRoot Tag.E6 (e6CoxeterSq • w⁻¹ • β) :=
    CFSG.LieType.Chevalley.IsRoot.smul hβ' e6CoxeterSq
  obtain ⟨ε₃, h₃, hX₃⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hγ
  have hσ₁ : Fr ε₁ = ε₁ := ringHom_apply_eq_of_mul_self Fr h₁
  refine ⟨ε₃ * ε₂ * ε₁, by linear_combination (ε₃ * ε₃) * (ε₂ * ε₂) * h₁ +
    (ε₃ * ε₃) * h₂ + h₃, fun c => ?_⟩
  rw [phi6ThetaConj_apply, hinv, hθ, map_mul, hσ₁, hX₃, ← mul_smul, ← mul_smul]
  congr 1
  ring

end CFSG.RankThree.PartOne.KE6
