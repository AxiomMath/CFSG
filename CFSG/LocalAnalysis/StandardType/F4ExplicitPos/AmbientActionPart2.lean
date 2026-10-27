module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart13
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientActionPart1

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.StandardType.F4ExplicitPos.AmbientAction
variable {U X : Type*} [Group U] [Group X]

section F4Equations
open CFSG.StandardType.F4ExplicitPos.BaseChange
variable {K L : Type} {X : Type*} [Field K] [Field L] [Algebra K L] [Finite K] [Group X] [Finite X]

theorem psi_betaF4_action (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (b : B1) (u : adjointGroup .F4 K) :
    ψ (betaF4 ψ G0 B1 hG0 hker hcenter hBN hinner b * u *
        (betaF4 ψ G0 B1 hG0 hker hcenter hBN hinner b)⁻¹) =
      (b : X) * ψ u * (b : X)⁻¹ :=
  psi_beta_action ψ G0 B1 hG0 hker hcenter hBN hinner b u

theorem betaF4_ker (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X)) :
    (betaF4 ψ G0 B1 hG0 hker hcenter hBN hinner).ker =
      (Subgroup.centralizer (G0 : Set X)).subgroupOf B1 :=
  beta_ker ψ G0 B1 hG0 hker hcenter hBN hinner

theorem thetaF4_ker
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X)) :
    ((thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L)).ker =
      (betaF4 ψ G0 B1 hG0 hker hcenter hBN hinner).ker := by
  ext b
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, thetaF4, MonoidHom.comp_apply,
    show (1 : adjointGroup .F4 L) = jF4 (1 : adjointGroup .F4 K) from
      (map_one (jF4 : adjointGroup .F4 K →* adjointGroup .F4 L)).symm]
  exact (jF4_injective).eq_iff

theorem iotaF4_normalizer
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (b : B1) (x : G0) :
    (iotaF4 ψ G0 hG0 hker hcenter
        ((G0.normalizerMonoidHom ⟨b, hBN b.property⟩) x) : adjointGroup .F4 L) =
      thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner b *
        iotaF4 ψ G0 hG0 hker hcenter x *
        (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner b)⁻¹ := by
  have hx : (G0.normalizerMonoidHom ⟨b, hBN b.property⟩) x =
      eF4 ψ G0 hG0 hker hcenter
        (alpha ψ G0 B1 hG0 hker hcenter hBN b
          ((eF4 ψ G0 hG0 hker hcenter).symm x)) := by
    rw [eF4, psiEquiv_alpha_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [hx, iotaF4, thetaF4, betaF4, MonoidHom.comp_apply, MonoidHom.comp_apply]
  change jF4 ((eF4 ψ G0 hG0 hker hcenter).symm
      ((eF4 ψ G0 hG0 hker hcenter)
        (alpha ψ G0 B1 hG0 hker hcenter hBN b
          ((eF4 ψ G0 hG0 hker hcenter).symm x)))) =
    jF4 (betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b) *
      jF4 ((eF4 ψ G0 hG0 hker hcenter).symm x) *
      (jF4 (betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b))⁻¹
  rw [MulEquiv.symm_apply_apply]
  rw [show alpha ψ G0 B1 hG0 hker hcenter hBN b
        ((eF4 ψ G0 hG0 hker hcenter).symm x) =
      betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b *
        (eF4 ψ G0 hG0 hker hcenter).symm x *
        (betaOf ψ G0 B1 hG0 hker hcenter hBN hinner b)⁻¹ from by
      rw [← MulAut.conj_apply, beta_conj]]
  rw [map_mul, map_mul, map_inv]

theorem frobF4_iotaF4
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (ψ : adjointGroup .F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥) (x : G0) :
    frobF4 Fr hFr
        (iotaF4 ψ G0 hG0 hker hcenter x) =
      iotaF4 ψ G0 hG0 hker hcenter x := by
  rw [iotaF4, MonoidHom.comp_apply]
  exact frobF4_jF4 Fr hFr _

theorem frobF4_thetaF4
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (b : B1) :
    frobF4 Fr hFr
        (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner b) =
      thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner b := by
  rw [thetaF4, MonoidHom.comp_apply]
  exact frobF4_jF4 Fr hFr _

theorem thetaD_ker_eq
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (D : Subgroup X) (hDB : D ≤ B1) :
    (((thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L)).comp
        (Subgroup.inclusion hDB)).ker =
      (Subgroup.centralizer (G0 : Set X)).subgroupOf D := by
  ext d
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
    thetaF4, betaF4, MonoidHom.comp_apply]
  rw [show (1 : adjointGroup .F4 L) = jF4 (1 : adjointGroup .F4 K) from
      (map_one (jF4 : adjointGroup .F4 K →* adjointGroup .F4 L)).symm,
    (jF4_injective).eq_iff]
  rw [beta_eq_one_iff]
  rfl

theorem theta_image_card
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (D : Subgroup X) (hDB : D ≤ B1) :
    Nat.card ((D.subgroupOf B1).map
        (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L)) *
      Nat.card ((Subgroup.centralizer (G0 : Set X)).subgroupOf D) = Nat.card D := by
  have hcard := Subgroup.card_ker_mul_card_range
    ((thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L).comp
      (Subgroup.inclusion hDB))
  rw [thetaD_ker_eq ψ G0 B1 hG0 hker hcenter hBN hinner D hDB,
    MonoidHom.range_comp, Subgroup.inclusion_range, Nat.mul_comm] at hcard
  exact hcard

theorem thetaD_image_card_le
    (ψ : adjointGroup .F4 K →* X) (G0 B1 : Subgroup X)
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hcenter : Subgroup.center (adjointGroup .F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (D : Subgroup X) (hDB : D ≤ B1) {p : ℕ} (hDcard : Nat.card D = p ^ 2) :
    Nat.card ((D.subgroupOf B1).map
        (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L)) ≤ p ^ 2 := by
  have hcard : Nat.card ((D.subgroupOf B1).map
        (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L)) *
      Nat.card ((Subgroup.centralizer (G0 : Set X)).subgroupOf D) = Nat.card D :=
    theta_image_card ψ G0 B1 hG0 hker hcenter hBN hinner D hDB
  rw [hDcard] at hcard
  rw [Nat.mul_comm (Nat.card ((D.subgroupOf B1).map
        (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L)))
      (Nat.card ((Subgroup.centralizer (G0 : Set X)).subgroupOf D))] at hcard
  have hk : 1 ≤ Nat.card ((Subgroup.centralizer (G0 : Set X)).subgroupOf D) :=
    Nat.succ_le_of_lt Nat.card_pos
  calc Nat.card ((D.subgroupOf B1).map
          (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L))
      = 1 * Nat.card ((D.subgroupOf B1).map
          (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L)) :=
        (one_mul _).symm
    _ ≤ Nat.card ((Subgroup.centralizer (G0 : Set X)).subgroupOf D) *
          Nat.card ((D.subgroupOf B1).map
            (thetaF4 ψ G0 B1 hG0 hker hcenter hBN hinner : B1 →* adjointGroup .F4 L)) :=
        Nat.mul_le_mul_right _ hk
    _ = p ^ 2 := hcard

end F4Equations

section ActualRealization

open BaseChange CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Steinberg.Adjoint

variable {K Lf X : Type} [Field K] [Finite K] [CharP K 2] [Field Lf] [Algebra K Lf] [Group X]
    [Finite X]

theorem f4_hinner
    {ψ : adjointGroup .F4 K →* X} {G0 B1 : Subgroup X}
    (hG0 : ψ.range = G0) (hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 K))
    (hdiag : ∀ b ∈ B1, GGPsiInnerDiag (f4Datum K) ψ b) :
    ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X) := by
  intro b hb
  obtain ⟨g, hg, hc⟩ :=
    CFSG.StandardType.F4ExplicitPos.InnerDirect.f4_exists_inner_correction (K := K) (G := X)
      ψ hker (hdiag b hb)
  refine ⟨g, ?_, ?_⟩
  · rwa [hG0] at hg
  · rwa [hG0] at hc

end ActualRealization
end CFSG.StandardType.F4ExplicitPos.AmbientAction
end

end
