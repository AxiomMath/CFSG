module

public import CFSG.RankThree.PartOne.KE.FourA1Group
public import CFSG.RankThree.PartOne.KGD.ThreeA1Twisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL conjSL_one diagUnitOne)
open CFSG.RankThree.PartOne.KGD (threeA1Tw_conjSL_fixes threeA1Tw_torus_mul_rootSL2)
open scoped Pointwise MatrixGroups commutatorElement

section Generic

variable {τ : Tag} {L : Type} [Field L] {r₁ r₂ r₃ r₄ : Fin τ.rank → ℤ}

theorem fourA1Tw_mem_center_of_mul_eq_one
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D))
    {A B C D : SL2 L} (h : fourProd τ L r₁ r₂ r₃ r₄ A B C D = 1) :
    A ∈ Subgroup.center (SL2 L) ∧ B ∈ Subgroup.center (SL2 L) ∧
      C ∈ Subgroup.center (SL2 L) ∧ D ∈ Subgroup.center (SL2 L) := by
  unfold fourProd at h
  have hD : rootSL2 τ L r₄ D = (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  have hABC : rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C =
      (rootSL2 τ L r₄ D)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hC : rootSL2 τ L r₃ C = (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B)⁻¹ * (rootSL2 τ L r₄ D)⁻¹ :=
    eq_inv_mul_of_mul_eq hABC
  have hAB : rootSL2 τ L r₁ A * rootSL2 τ L r₂ B =
      (rootSL2 τ L r₄ D)⁻¹ * (rootSL2 τ L r₃ C)⁻¹ := eq_mul_inv_of_mul_eq hABC
  have hB : rootSL2 τ L r₂ B = (rootSL2 τ L r₁ A)⁻¹ *
      ((rootSL2 τ L r₄ D)⁻¹ * (rootSL2 τ L r₃ C)⁻¹) := eq_inv_mul_of_mul_eq hAB
  have hA : rootSL2 τ L r₁ A = (rootSL2 τ L r₂ B * rootSL2 τ L r₃ C * rootSL2 τ L r₄ D)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc rootSL2 τ L r₁ A * (rootSL2 τ L r₂ B * rootSL2 τ L r₃ C * rootSL2 τ L r₄ D)
        = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C * rootSL2 τ L r₄ D := by group
      _ = 1 := h
  have key : ∀ (r : Fin τ.rank → ℤ) (M : SL2 L),
      (∀ D : SL2 L, Commute (rootSL2 τ L r D) (rootSL2 τ L r M)) →
        M ∈ Subgroup.center (SL2 L) := by
    intro r M hM
    rw [Subgroup.mem_center_iff]
    intro D
    apply rootSL2_injective_of_field r
    rw [map_mul, map_mul]
    exact hM D
  refine ⟨key r₁ A fun U => ?_, key r₂ B fun U => ?_, key r₃ C fun U => ?_,
    key r₄ D fun U => ?_⟩
  · rw [hA]
    exact (((hc12 U B).mul_right (hc13 U C)).mul_right (hc14 U D)).inv_right
  · rw [hB]
    exact (hc12 A U).symm.inv_right.mul_right
      ((hc24 U D).inv_right.mul_right (hc23 U C).inv_right)
  · rw [hC]
    exact (((hc13 A U).symm.mul_right (hc23 B U).symm).inv_right).mul_right
      (hc34 U D).inv_right
  · rw [hD]
    exact ((((hc14 A U).symm.mul_right (hc24 B U).symm).mul_right (hc34 C U).symm)).inv_right

theorem fourA1Tw_exists_central_of_mu_eq {M : Type*} [Group M]
    (μ : SL2 L × SL2 L × SL2 L × SL2 L →* M)
    (hker : ∀ A B C D : SL2 L, μ (A, B, C, D) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) ∧ D ∈ Subgroup.center (SL2 L))
    {P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ : SL2 L}
    (h : μ (P₁, P₂, P₃, P₄) = μ (Q₁, Q₂, Q₃, Q₄)) :
    ∃ z₁ ∈ Subgroup.center (SL2 L), ∃ z₂ ∈ Subgroup.center (SL2 L),
      ∃ z₃ ∈ Subgroup.center (SL2 L), ∃ z₄ ∈ Subgroup.center (SL2 L),
        P₁ = z₁ * Q₁ ∧ P₂ = z₂ * Q₂ ∧ P₃ = z₃ * Q₃ ∧ P₄ = z₄ * Q₄ := by
  have h1 : μ (P₁ * Q₁⁻¹, P₂ * Q₂⁻¹, P₃ * Q₃⁻¹, P₄ * Q₄⁻¹) = 1 := by
    have e : (P₁ * Q₁⁻¹, P₂ * Q₂⁻¹, P₃ * Q₃⁻¹, P₄ * Q₄⁻¹) =
        (P₁, P₂, P₃, P₄) * (Q₁, Q₂, Q₃, Q₄)⁻¹ := rfl
    rw [e, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hker _ _ _ _ h1
  exact ⟨_, h₁, _, h₂, _, h₃, _, h₄, by group, by group, by group, by group⟩

theorem fourA1Tw_commutator_step {M : Type*} [Group M]
    (μ : SL2 L × SL2 L × SL2 L × SL2 L →* M)
    (hker : ∀ A B C D : SL2 L, μ (A, B, C, D) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) ∧ D ∈ Subgroup.center (SL2 L))
    (G₁ G₂ G₃ G₄ : SL2 L →* SL2 L) (S₄ : Subgroup (SL2 L))
    (hS₄ : ∀ B : SL2 L, B ∈ S₄ ↔ G₄ (G₃ (G₂ (G₁ B))) = B)
    {A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : SL2 L}
    (e₁ : μ (G₄ D₁, G₁ A₁, G₂ B₁, G₃ C₁) = μ (A₁, B₁, C₁, D₁))
    (e₂ : μ (G₄ D₂, G₁ A₂, G₂ B₂, G₃ C₂) = μ (A₂, B₂, C₂, D₂)) :
    ⁅A₁, A₂⁆ ∈ S₄ ∧ ⁅μ (A₁, B₁, C₁, D₁), μ (A₂, B₂, C₂, D₂)⁆ =
      μ (⁅A₁, A₂⁆, G₁ ⁅A₁, A₂⁆, G₂ (G₁ ⁅A₁, A₂⁆), G₃ (G₂ (G₁ ⁅A₁, A₂⁆))) := by
  obtain ⟨z₁, hz₁, z₂, hz₂, z₃, hz₃, z₄, hz₄, h1a, h1b, h1c, h1d⟩ :=
    fourA1Tw_exists_central_of_mu_eq μ hker e₁
  obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, w₄, hw₄, h2a, h2b, h2c, h2d⟩ :=
    fourA1Tw_exists_central_of_mu_eq μ hker e₂
  have hA₁ : A₁ = z₁⁻¹ * G₄ D₁ := eq_inv_mul_of_mul_eq h1a.symm
  have hA₂ : A₂ = w₁⁻¹ * G₄ D₂ := eq_inv_mul_of_mul_eq h2a.symm
  have hB₁ : B₁ = z₂⁻¹ * G₁ A₁ := eq_inv_mul_of_mul_eq h1b.symm
  have hB₂ : B₂ = w₂⁻¹ * G₁ A₂ := eq_inv_mul_of_mul_eq h2b.symm
  have hC₁ : C₁ = z₃⁻¹ * G₂ B₁ := eq_inv_mul_of_mul_eq h1c.symm
  have hC₂ : C₂ = w₃⁻¹ * G₂ B₂ := eq_inv_mul_of_mul_eq h2c.symm
  have hD₁ : D₁ = z₄⁻¹ * G₃ C₁ := eq_inv_mul_of_mul_eq h1d.symm
  have hD₂ : D₂ = w₄⁻¹ * G₃ C₂ := eq_inv_mul_of_mul_eq h2d.symm
  have hB : ⁅B₁, B₂⁆ = G₁ ⁅A₁, A₂⁆ := by
    rw [hB₁, hB₂, commutator_mul_central (inv_mem hz₂) (inv_mem hw₂), map_commutatorElement]
  have hC : ⁅C₁, C₂⁆ = G₂ ⁅B₁, B₂⁆ := by
    rw [hC₁, hC₂, commutator_mul_central (inv_mem hz₃) (inv_mem hw₃), map_commutatorElement]
  have hD : ⁅D₁, D₂⁆ = G₃ ⁅C₁, C₂⁆ := by
    rw [hD₁, hD₂, commutator_mul_central (inv_mem hz₄) (inv_mem hw₄), map_commutatorElement]
  have hA : ⁅A₁, A₂⁆ = G₄ ⁅D₁, D₂⁆ := by
    rw [hA₁, hA₂, commutator_mul_central (inv_mem hz₁) (inv_mem hw₁), map_commutatorElement]
  have hmem : ⁅A₁, A₂⁆ ∈ S₄ := by
    refine (hS₄ _).2 ?_
    rw [← hB, ← hC, ← hD, ← hA]
  refine ⟨hmem, ?_⟩
  have hc : ⁅μ (A₁, B₁, C₁, D₁), μ (A₂, B₂, C₂, D₂)⁆ =
      μ (⁅A₁, A₂⁆, ⁅B₁, B₂⁆, ⁅C₁, C₂⁆, ⁅D₁, D₂⁆) := by
    rw [← map_commutatorElement]
    rfl
  rw [hc, hD, hC, hB]

theorem fourA1Tw_diag_mem_rootSpan
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (h₄ : IsRoot τ r₄)
    (μ : SL2 L × SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C D, μ (A, B, C, D) = fourProd τ L r₁ r₂ r₃ r₄ A B C D)
    (G₁ G₂ G₃ : SL2 L →* SL2 L) (X : SL2 L) :
    μ (X, G₁ X, G₂ (G₁ X), G₃ (G₂ (G₁ X))) ∈ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) := by
  rw [hμ, rootSpan_fourRootSet h₁ h₂ h₃ h₄]
  exact mul_mem (mul_mem (mul_mem
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨X, rfl⟩)))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨G₁ X, rfl⟩))))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨G₂ (G₁ X), rfl⟩)))
    (Subgroup.mem_sup_right ⟨G₃ (G₂ (G₁ X)), rfl⟩)

theorem fourA1Tw_diag_mem_fixed (μ : SL2 L × SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (Φ : ModGL τ L →* ModGL τ L) (n : ModGL τ L) (G₁ G₂ G₃ G₄ : SL2 L →* SL2 L)
    (hΘ : ∀ A B C D : SL2 L, n * Φ (μ (A, B, C, D)) * n⁻¹ = μ (G₄ D, G₁ A, G₂ B, G₃ C))
    {X : SL2 L} (hX : G₄ (G₃ (G₂ (G₁ X))) = X) :
    μ (X, G₁ X, G₂ (G₁ X), G₃ (G₂ (G₁ X))) ∈ twistedFixedPoints n Φ := by
  rw [mem_twistedFixedPoints, hΘ, hX]

theorem fourA1Tw_commutator_eq_map
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (h₄ : IsRoot τ r₄)
    (μ : SL2 L × SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C D, μ (A, B, C, D) = fourProd τ L r₁ r₂ r₃ r₄ A B C D)
    (hker : ∀ A B C D : SL2 L, μ (A, B, C, D) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) ∧ D ∈ Subgroup.center (SL2 L))
    (Φ : ModGL τ L →* ModGL τ L) (n : ModGL τ L) (G₁ G₂ G₃ G₄ : SL2 L →* SL2 L)
    (hΘ : ∀ A B C D : SL2 L, n * Φ (μ (A, B, C, D)) * n⁻¹ = μ (G₄ D, G₁ A, G₂ B, G₃ C))
    (S₄ : Subgroup (SL2 L)) (hS₄ : ∀ B : SL2 L, B ∈ S₄ ↔ G₄ (G₃ (G₂ (G₁ B))) = B)
    (hp₄ : Group.IsPerfect S₄) (ν : SL2 L →* ModGL τ L)
    (hν : ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X), G₃ (G₂ (G₁ X)))) :
    ⁅rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ,
      rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ⁆ = S₄.map ν := by
  classical
  have hQS : rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) =
      rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ ⊔
        rootRankOneGroup τ L r₄ :=
    rootSpan_fourRootSet h₁ h₂ h₃ h₄
  have hνΓ : ∀ X ∈ S₄, ν X ∈ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ :=
    fun X hX => by
      rw [hν]
      exact Subgroup.mem_inf.2 ⟨fourA1Tw_diag_mem_rootSpan h₁ h₂ h₃ h₄ μ hμ G₁ G₂ G₃ X,
        fourA1Tw_diag_mem_fixed μ Φ n G₁ G₂ G₃ G₄ hΘ ((hS₄ X).1 hX)⟩
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨A₁, B₁, C₁, D₁, rfl⟩ := mem_sup_four hc12 hc13 hc14 hc23 hc24 hc34
      (by rw [← hQS]; exact (Subgroup.mem_inf.1 hg₁).1)
    obtain ⟨A₂, B₂, C₂, D₂, rfl⟩ := mem_sup_four hc12 hc13 hc14 hc23 hc24 hc34
      (by rw [← hQS]; exact (Subgroup.mem_inf.1 hg₂).1)
    rw [← hμ A₁ B₁ C₁ D₁] at hg₁ ⊢
    rw [← hμ A₂ B₂ C₂ D₂] at hg₂ ⊢
    have e₁ : μ (G₄ D₁, G₁ A₁, G₂ B₁, G₃ C₁) = μ (A₁, B₁, C₁, D₁) := by
      have h := (mem_twistedFixedPoints.1 (Subgroup.mem_inf.1 hg₁).2 :
        n * Φ (μ (A₁, B₁, C₁, D₁)) * n⁻¹ = _)
      rwa [hΘ] at h
    have e₂ : μ (G₄ D₂, G₁ A₂, G₂ B₂, G₃ C₂) = μ (A₂, B₂, C₂, D₂) := by
      have h := (mem_twistedFixedPoints.1 (Subgroup.mem_inf.1 hg₂).2 :
        n * Φ (μ (A₂, B₂, C₂, D₂)) * n⁻¹ = _)
      rwa [hΘ] at h
    obtain ⟨hmem, hcomm⟩ := fourA1Tw_commutator_step μ hker G₁ G₂ G₃ G₄ S₄ hS₄ e₁ e₂
    exact ⟨⁅A₁, A₂⁆, hmem, by rw [hν]; exact hcomm.symm⟩
  · rintro _ ⟨X, hX, rfl⟩
    refine perfect_le_of_commutator_mem hp₄
      (K := (⁅rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ,
        rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ⁆).comap ν)
      (fun a ha b hb => ?_) hX
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hνΓ a ha) (hνΓ b hb)

theorem fourA1Tw_map_isQuasisimple {M : Type*} [Group M]
    (μ : SL2 L × SL2 L × SL2 L × SL2 L →* M)
    (hker : ∀ A B C D : SL2 L, μ (A, B, C, D) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) ∧ D ∈ Subgroup.center (SL2 L))
    (G₁ G₂ G₃ : SL2 L →* SL2 L) (S₄ : Subgroup (SL2 L)) [Finite S₄]
    (hq₄ : CFSG.IsQuasisimple S₄) (ν : SL2 L →* M)
    (hν : ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X), G₃ (G₂ (G₁ X)))) :
    Finite (S₄.map ν) ∧ CFSG.IsQuasisimple (S₄.map ν) := by
  let φ : S₄ →* S₄.map ν :=
    (ν.comp S₄.subtype).codRestrict (S₄.map ν) (fun x => ⟨x, x.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨_, X, hX, rfl⟩
    exact ⟨⟨X, hX⟩, Subtype.ext rfl⟩
  have hφ1 : ∃ k, φ k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, a, b, hab⟩ := hq₄
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hsc : ∀ k : S₄, (k : SL2 L) ∈ Subgroup.center (SL2 L) := fun k => by
      have h1 : ν k = 1 := congrArg Subtype.val (hcon k)
      rw [hν] at h1
      exact (hker _ _ _ _ h1).1
    have hab' : a' * b' = b' * a' :=
      Subtype.ext (Subgroup.mem_center_iff.1 (hsc b') a')
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']
  exact ⟨Finite.of_surjective φ hφs,
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq₄ hφs hφ1⟩

theorem fourA1Tw_normalized
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (h₄ : IsRoot τ r₄)
    (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄))
    (hyR : y ∈ twistedFixedPoints n Φ) {u : ModGL τ L}
    (hu : u ∈ ⁅rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ,
      rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ⁆) :
    y * u * y⁻¹ ∈ ⁅rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ,
      rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ⁆ := by
  have hN : y ∈ Subgroup.normalizer
      (rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) : Set (ModGL τ L)) :=
    (sup_le (torusGroup_le_normalizer_rootSpan (fourRootSet_isRoot h₁ h₂ h₃ h₄))
      Subgroup.le_normalizer) hy
  have hΓn : ∀ g ∈ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ,
      y * g * y⁻¹ ∈ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ :=
    fun g hg => Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hN g).1
      (Subgroup.mem_inf.1 hg).1, mul_mem (mul_mem hyR (Subgroup.mem_inf.1 hg).2) (inv_mem hyR)⟩
  have h1 : ⁅rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ,
      rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ⁆ ≤
      (⁅rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ,
        rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ⊓ twistedFixedPoints n Φ⁆).comap
        (MulAut.conj y).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hΓn g₁ hg₁) (hΓn g₂ hg₂)
  have h2 := h1 hu
  simpa [MulAut.conj_apply] using h2

theorem fourA1Tw_centralizer [IsAlgClosed L]
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (h₄ : IsRoot τ r₄)
    (μ : SL2 L × SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C D, μ (A, B, C, D) = fourProd τ L r₁ r₂ r₃ r₄ A B C D)
    (hker : ∀ A B C D : SL2 L, μ (A, B, C, D) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) ∧ D ∈ Subgroup.center (SL2 L))
    (G₁ G₂ G₃ : SL2 L →* SL2 L) (S₁ S₂ S₃ S₄ : Subgroup (SL2 L))
    (hS₃ : S₃ = S₄.map G₁) (hS₂ : S₂ = S₃.map G₂) (hS₁ : S₁ = S₂.map G₃)
    (hp₁ : Group.IsPerfect S₁) (hp₂ : Group.IsPerfect S₂) (hp₃ : Group.IsPerfect S₃)
    (hp₄ : Group.IsPerfect S₄)
    (hz₁ : Subgroup.centralizer ((S₁.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₂ : Subgroup.centralizer ((S₂.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₃ : Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₄ : Subgroup.centralizer ((S₄.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄))
    (hcomm : ∀ U ∈ S₄, y * μ (U, G₁ U, G₂ (G₁ U), G₃ (G₂ (G₁ U))) =
      μ (U, G₁ U, G₂ (G₁ U), G₃ (G₂ (G₁ U))) * y) :
    y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer
      ((rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  classical
  have hQS : rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) =
      rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ ⊔
        rootRankOneGroup τ L r₄ :=
    rootSpan_fourRootSet h₁ h₂ h₃ h₄
  obtain ⟨b, A, B, C, D, rfl⟩ := exists_decomp_four hc12 hc13 hc14 hc23 hc24 hc34 h₁ h₂ h₃ h₄ hy
  obtain ⟨hc1', hc2', hc3', hc4'⟩ := conj_four_rootSL2 hc12 hc13 hc14 hc23 hc24 hc34
    h₁ h₂ h₃ h₄ b A B C D
  have htH : rootDiagUnit τ b ∈ torusGroup τ L := rootDiagUnit_mem_torusGroup b
  set y := rootDiagUnit τ b * fourProd τ L r₁ r₂ r₃ r₄ A B C D with hydef
  set X₁ : GL (Fin 2) L := diagUnitOne (rootChar b r₁) * Matrix.SpecialLinearGroup.toGL A
    with hX₁
  set X₂ : GL (Fin 2) L := diagUnitOne (rootChar b r₂) * Matrix.SpecialLinearGroup.toGL B
    with hX₂
  set X₃ : GL (Fin 2) L := diagUnitOne (rootChar b r₃) * Matrix.SpecialLinearGroup.toGL C
    with hX₃
  set X₄ : GL (Fin 2) L := diagUnitOne (rootChar b r₄) * Matrix.SpecialLinearGroup.toGL D
    with hX₄
  have hcen : ∀ U ∈ S₄, ∃ z₁ ∈ Subgroup.center (SL2 L), ∃ z₂ ∈ Subgroup.center (SL2 L),
      ∃ z₃ ∈ Subgroup.center (SL2 L), ∃ z₄ ∈ Subgroup.center (SL2 L),
        conjSL X₁ U = z₁ * U ∧ conjSL X₂ (G₁ U) = z₂ * G₁ U ∧
          conjSL X₃ (G₂ (G₁ U)) = z₃ * G₂ (G₁ U) ∧
            conjSL X₄ (G₃ (G₂ (G₁ U))) = z₄ * G₃ (G₂ (G₁ U)) := by
    intro U hU
    have h2 : y * μ (U, G₁ U, G₂ (G₁ U), G₃ (G₂ (G₁ U))) * y⁻¹ =
        μ (U, G₁ U, G₂ (G₁ U), G₃ (G₂ (G₁ U))) := by
      rw [hcomm U hU, mul_inv_cancel_right]
    have h3 : y * μ (U, G₁ U, G₂ (G₁ U), G₃ (G₂ (G₁ U))) * y⁻¹ =
        μ (conjSL X₁ U, conjSL X₂ (G₁ U), conjSL X₃ (G₂ (G₁ U)),
          conjSL X₄ (G₃ (G₂ (G₁ U)))) := by
      rw [hμ, hμ]
      unfold fourProd
      calc y * (rootSL2 τ L r₁ U * rootSL2 τ L r₂ (G₁ U) * rootSL2 τ L r₃ (G₂ (G₁ U)) *
            rootSL2 τ L r₄ (G₃ (G₂ (G₁ U)))) * y⁻¹
          = (y * rootSL2 τ L r₁ U * y⁻¹) * (y * rootSL2 τ L r₂ (G₁ U) * y⁻¹) *
              (y * rootSL2 τ L r₃ (G₂ (G₁ U)) * y⁻¹) *
                (y * rootSL2 τ L r₄ (G₃ (G₂ (G₁ U))) * y⁻¹) := by group
        _ = _ := by rw [hc1' U, hc2' (G₁ U), hc3' (G₂ (G₁ U)), hc4' (G₃ (G₂ (G₁ U)))]
    rw [h3] at h2
    exact fourA1Tw_exists_central_of_mu_eq μ hker h2
  have hcen1 : ∀ V ∈ S₄, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₁ V = z * V := fun V hV => by
    obtain ⟨z, hz, -, -, -, -, -, -, e1, -, -, -⟩ := hcen V hV
    exact ⟨z, hz, e1⟩
  have hcen2 : ∀ V ∈ S₃, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₂ V = z * V := fun V hV => by
    rw [hS₃] at hV
    obtain ⟨U, hU, rfl⟩ := hV
    obtain ⟨-, -, z, hz, -, -, -, -, -, e2, -, -⟩ := hcen U hU
    exact ⟨z, hz, e2⟩
  have hcen3 : ∀ V ∈ S₂, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₃ V = z * V := fun V hV => by
    rw [hS₂, hS₃] at hV
    obtain ⟨W, hW, rfl⟩ := hV
    obtain ⟨U, hU, rfl⟩ := hW
    obtain ⟨-, -, -, -, z, hz, -, -, -, -, e3, -⟩ := hcen U hU
    exact ⟨z, hz, e3⟩
  have hcen4 : ∀ V ∈ S₁, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₄ V = z * V := fun V hV => by
    rw [hS₁, hS₂, hS₃] at hV
    obtain ⟨W, hW, rfl⟩ := hV
    obtain ⟨W', hW', rfl⟩ := hW
    obtain ⟨U, hU, rfl⟩ := hW'
    obtain ⟨-, -, -, -, -, -, z, hz, -, -, -, e4⟩ := hcen U hU
    exact ⟨z, hz, e4⟩
  have hU₁ := threeA1Tw_conjSL_fixes hp₄ X₁ hcen1
  have hU₂ := threeA1Tw_conjSL_fixes hp₃ X₂ hcen2
  have hU₃ := threeA1Tw_conjSL_fixes hp₂ X₃ hcen3
  have hU₄ := threeA1Tw_conjSL_fixes hp₁ X₄ hcen4
  obtain ⟨hT₁, hF₁⟩ := threeA1Tw_torus_mul_rootSL2 h₁ hz₄ b A X₁ hX₁ hU₁
  obtain ⟨hT₂, hF₂⟩ := threeA1Tw_torus_mul_rootSL2 h₂ hz₃ b B X₂ hX₂ hU₂
  obtain ⟨hT₃, hF₃⟩ := threeA1Tw_torus_mul_rootSL2 h₃ hz₂ b C X₃ hX₃ hU₃
  obtain ⟨hT₄, hF₄⟩ := threeA1Tw_torus_mul_rootSL2 h₄ hz₁ b D X₄ hX₄ hU₄
  have hA : rootSL2 τ L r₁ A ∈ torusGroup τ L := by
    have := mul_mem (inv_mem htH) hT₁
    rwa [inv_mul_cancel_left] at this
  have hB : rootSL2 τ L r₂ B ∈ torusGroup τ L := by
    have := mul_mem (inv_mem htH) hT₂
    rwa [inv_mul_cancel_left] at this
  have hC : rootSL2 τ L r₃ C ∈ torusGroup τ L := by
    have := mul_mem (inv_mem htH) hT₃
    rwa [inv_mul_cancel_left] at this
  have hD : rootSL2 τ L r₄ D ∈ torusGroup τ L := by
    have := mul_mem (inv_mem htH) hT₄
    rwa [inv_mul_cancel_left] at this
  have hyH : y ∈ torusGroup τ L :=
    mul_mem htH (mul_mem (mul_mem (mul_mem hA hB) hC) hD)
  refine ⟨hyH, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe, hQS] at hg
  obtain ⟨A', B', C', D', rfl⟩ := mem_sup_four hc12 hc13 hc14 hc23 hc24 hc34 hg
  have f₁ : Commute y (rootSL2 τ L r₁ A') := by
    have h := hc1' A'
    rw [hF₁ A'] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have f₂ : Commute y (rootSL2 τ L r₂ B') := by
    have h := hc2' B'
    rw [hF₂ B'] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have f₃ : Commute y (rootSL2 τ L r₃ C') := by
    have h := hc3' C'
    rw [hF₃ C'] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have f₄ : Commute y (rootSL2 τ L r₄ D') := by
    have h := hc4' D'
    rw [hF₄ D'] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  exact (((f₁.mul_right f₂).mul_right f₃).mul_right f₄).eq.symm

end Generic

theorem four_A1_twisted_cyclic_family
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {r₁ r₂ r₃ r₄ : Fin τ.rank → ℤ}
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc14 : ∀ A D : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₄ D))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (hc24 : ∀ B D : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₄ D))
    (hc34 : ∀ C D : SL2 L, Commute (rootSL2 τ L r₃ C) (rootSL2 τ L r₄ D))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (h₄ : IsRoot τ r₄)
    (μ : SL2 L × SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C D, μ (A, B, C, D) = fourProd τ L r₁ r₂ r₃ r₄ A B C D)
    (Fr : L →+* L) (n : ModGL τ L) (G₁ G₂ G₃ G₄ : SL2 L →* SL2 L)
    (hΘ : ∀ A B C D : SL2 L, n * Units.map (entrywiseHom Fr) (μ (A, B, C, D)) * n⁻¹ =
      μ (G₄ D, G₁ A, G₂ B, G₃ C))
    (S₁ S₂ S₃ S₄ : Subgroup (SL2 L)) [Finite S₄]
    (hS₃ : S₃ = S₄.map G₁) (hS₂ : S₂ = S₃.map G₂) (hS₁ : S₁ = S₂.map G₃)
    (hS₄ : ∀ B : SL2 L, B ∈ S₄ ↔ G₄ (G₃ (G₂ (G₁ B))) = B)
    (hq₁ : CFSG.IsQuasisimple S₁) (hq₂ : CFSG.IsQuasisimple S₂) (hq₃ : CFSG.IsQuasisimple S₃)
    (hq₄ : CFSG.IsQuasisimple S₄)
    (hz₁ : Subgroup.centralizer ((S₁.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₂ : Subgroup.centralizer ((S₂.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₃ : Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₄ : Subgroup.centralizer ((S₄.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    ∃ P : Subgroup (ModGL τ L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄) ∧
      P ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧ P ≤ adjointGroup τ L ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (fourRootSet r₁ r₂ r₃ r₄),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
        (∀ u ∈ P, y * u = u * y) →
        y ∈ subtorusSigma n (Units.map (entrywiseHom Fr)) (fourRootSet r₁ r₂ r₃ r₄)) := by
  classical
  have hker : ∀ A B C D : SL2 L, μ (A, B, C, D) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) ∧
        D ∈ Subgroup.center (SL2 L) := fun A B C D h =>
    fourA1Tw_mem_center_of_mul_eq_one hc12 hc13 hc14 hc23 hc24 hc34 (by rw [← hμ]; exact h)
  obtain ⟨ν, hν⟩ : ∃ ν : SL2 L →* ModGL τ L,
      ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X), G₃ (G₂ (G₁ X))) :=
    ⟨μ.comp ((MonoidHom.id (SL2 L)).prod (G₁.prod ((G₂.comp G₁).prod (G₃.comp (G₂.comp G₁))))),
      fun X => rfl⟩
  have hPeq := fourA1Tw_commutator_eq_map hc12 hc13 hc14 hc23 hc24 hc34 h₁ h₂ h₃ h₄ μ hμ hker
    (Units.map (entrywiseHom Fr)) n G₁ G₂ G₃ G₄ hΘ S₄ hS₄ hq₄.1 ν hν
  obtain ⟨hPfin, hPq⟩ := fourA1Tw_map_isQuasisimple μ hker G₁ G₂ G₃ S₄ hq₄ ν hν
  have hρadj : ∀ r (A : SL2 L), rootSL2 τ L r A ∈ adjointGroup τ L := fun r A =>
    (exceptional_Lang_root_rank_one_data τ L r).2.2.2.2.1 A
  refine ⟨S₄.map ν, hPfin, hPq, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, -, rfl⟩
    rw [hν]
    exact fourA1Tw_diag_mem_rootSpan h₁ h₂ h₃ h₄ μ hμ G₁ G₂ G₃ X
  · rintro _ ⟨X, hX, rfl⟩
    rw [hν]
    exact fourA1Tw_diag_mem_fixed μ (Units.map (entrywiseHom Fr)) n G₁ G₂ G₃ G₄ hΘ
      ((hS₄ X).1 hX)
  · rintro _ ⟨X, -, rfl⟩
    rw [hν, hμ]
    unfold fourProd
    exact mul_mem (mul_mem (mul_mem (hρadj _ _) (hρadj _ _)) (hρadj _ _)) (hρadj _ _)
  · intro y hy hyR u hu
    rw [← hPeq] at hu ⊢
    exact fourA1Tw_normalized h₁ h₂ h₃ h₄ n (Units.map (entrywiseHom Fr)) hy hyR hu
  · intro y hy hyR hcomm
    obtain ⟨hyH, hcZ⟩ := fourA1Tw_centralizer hc12 hc13 hc14 hc23 hc24 hc34 h₁ h₂ h₃ h₄ μ hμ
      hker G₁ G₂ G₃ S₁ S₂ S₃ S₄ hS₃ hS₂ hS₁ hq₁.1 hq₂.1 hq₃.1 hq₄.1 hz₁ hz₂ hz₃ hz₄ hy
      (fun U hU => by rw [← hν]; exact hcomm _ ⟨U, hU, rfl⟩)
    exact ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hcZ⟩

end CFSG.RankThree.PartOne.KE
