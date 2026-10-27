module

public import CFSG.RankThree.PartOne.KE.E7TwelveFamily

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL conjSL_one diagUnitOne)
open CFSG.RankThree.PartOne.KE
open scoped Pointwise MatrixGroups commutatorElement

section Generic

variable {τ : Tag} {L : Type} [Field L] {r₁ r₂ r₃ : Fin τ.rank → ℤ}

theorem threeA1Tw_mem_center_of_mul_eq_one
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    {A B C : SL2 L}
    (h : rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C = 1) :
    A ∈ Subgroup.center (SL2 L) ∧ B ∈ Subgroup.center (SL2 L) ∧
      C ∈ Subgroup.center (SL2 L) := by
  have hA : rootSL2 τ L r₁ A = (rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h)
  have hAB : rootSL2 τ L r₁ A * rootSL2 τ L r₂ B = (rootSL2 τ L r₃ C)⁻¹ :=
    eq_inv_of_mul_eq_one_left h
  have hB : rootSL2 τ L r₂ B = (rootSL2 τ L r₁ A)⁻¹ * (rootSL2 τ L r₃ C)⁻¹ :=
    eq_inv_mul_of_mul_eq hAB
  have hC : rootSL2 τ L r₃ C = (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B)⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  have key : ∀ (r : Fin τ.rank → ℤ) (M : SL2 L),
      (∀ D : SL2 L, Commute (rootSL2 τ L r D) (rootSL2 τ L r M)) →
        M ∈ Subgroup.center (SL2 L) := by
    intro r M hM
    rw [Subgroup.mem_center_iff]
    intro D
    apply rootSL2_injective_of_field r
    rw [map_mul, map_mul]
    exact hM D
  refine ⟨key r₁ A fun D => ?_, key r₂ B fun D => ?_, key r₃ C fun D => ?_⟩
  · rw [hA]
    exact ((hc12 D B).mul_right (hc13 D C)).inv_right
  · rw [hB]
    exact (hc12 A D).symm.inv_right.mul_right (hc23 D C).inv_right
  · rw [hC]
    exact ((hc13 A D).symm.mul_right (hc23 B D).symm).inv_right

theorem threeA1Tw_exists_central_of_mu_eq {M : Type*} [Group M]
    (μ : SL2 L × SL2 L × SL2 L →* M)
    (hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L))
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : SL2 L} (h : μ (P₁, P₂, P₃) = μ (Q₁, Q₂, Q₃)) :
    ∃ z₁ ∈ Subgroup.center (SL2 L), ∃ z₂ ∈ Subgroup.center (SL2 L),
      ∃ z₃ ∈ Subgroup.center (SL2 L), P₁ = z₁ * Q₁ ∧ P₂ = z₂ * Q₂ ∧ P₃ = z₃ * Q₃ := by
  have h1 : μ (P₁ * Q₁⁻¹, P₂ * Q₂⁻¹, P₃ * Q₃⁻¹) = 1 := by
    have e : (P₁ * Q₁⁻¹, P₂ * Q₂⁻¹, P₃ * Q₃⁻¹) = (P₁, P₂, P₃) * (Q₁, Q₂, Q₃)⁻¹ := rfl
    rw [e, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨h₁, h₂, h₃⟩ := hker _ _ _ h1
  exact ⟨_, h₁, _, h₂, _, h₃, by group, by group, by group⟩

theorem threeA1Tw_commutator_step {M : Type*} [Group M] (μ : SL2 L × SL2 L × SL2 L →* M)
    (hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L))
    (G₁ G₂ G₃ : SL2 L →* SL2 L) (S₃ : Subgroup (SL2 L))
    (hS₃ : ∀ B : SL2 L, B ∈ S₃ ↔ G₃ (G₂ (G₁ B)) = B)
    {A₁ B₁ C₁ A₂ B₂ C₂ : SL2 L}
    (e₁ : μ (G₃ C₁, G₁ A₁, G₂ B₁) = μ (A₁, B₁, C₁))
    (e₂ : μ (G₃ C₂, G₁ A₂, G₂ B₂) = μ (A₂, B₂, C₂)) :
    ⁅A₁, A₂⁆ ∈ S₃ ∧ ⁅μ (A₁, B₁, C₁), μ (A₂, B₂, C₂)⁆ =
      μ (⁅A₁, A₂⁆, G₁ ⁅A₁, A₂⁆, G₂ (G₁ ⁅A₁, A₂⁆)) := by
  obtain ⟨z₁, hz₁, z₂, hz₂, z₃, hz₃, h1a, h1b, h1c⟩ :=
    threeA1Tw_exists_central_of_mu_eq μ hker e₁
  obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, h2a, h2b, h2c⟩ :=
    threeA1Tw_exists_central_of_mu_eq μ hker e₂
  have hA₁ : A₁ = z₁⁻¹ * G₃ C₁ := eq_inv_mul_of_mul_eq h1a.symm
  have hA₂ : A₂ = w₁⁻¹ * G₃ C₂ := eq_inv_mul_of_mul_eq h2a.symm
  have hB₁ : B₁ = z₂⁻¹ * G₁ A₁ := eq_inv_mul_of_mul_eq h1b.symm
  have hB₂ : B₂ = w₂⁻¹ * G₁ A₂ := eq_inv_mul_of_mul_eq h2b.symm
  have hC₁ : C₁ = z₃⁻¹ * G₂ B₁ := eq_inv_mul_of_mul_eq h1c.symm
  have hC₂ : C₂ = w₃⁻¹ * G₂ B₂ := eq_inv_mul_of_mul_eq h2c.symm
  have hB : ⁅B₁, B₂⁆ = G₁ ⁅A₁, A₂⁆ := by
    rw [hB₁, hB₂, commutator_mul_central (inv_mem hz₂) (inv_mem hw₂), map_commutatorElement]
  have hC : ⁅C₁, C₂⁆ = G₂ ⁅B₁, B₂⁆ := by
    rw [hC₁, hC₂, commutator_mul_central (inv_mem hz₃) (inv_mem hw₃), map_commutatorElement]
  have hA : ⁅A₁, A₂⁆ = G₃ ⁅C₁, C₂⁆ := by
    rw [hA₁, hA₂, commutator_mul_central (inv_mem hz₁) (inv_mem hw₁), map_commutatorElement]
  have hmem : ⁅A₁, A₂⁆ ∈ S₃ := by
    refine (hS₃ _).2 ?_
    rw [← hB, ← hC, ← hA]
  refine ⟨hmem, ?_⟩
  have hc : ⁅μ (A₁, B₁, C₁), μ (A₂, B₂, C₂)⁆ = μ (⁅A₁, A₂⁆, ⁅B₁, B₂⁆, ⁅C₁, C₂⁆) := by
    rw [← map_commutatorElement]
    rfl
  rw [hc, hC, hB]

theorem threeA1Tw_diag_mem_rootSpan
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) =
      rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (G₁ G₂ : SL2 L →* SL2 L) (X : SL2 L) :
    μ (X, G₁ X, G₂ (G₁ X)) ∈ rootSpan τ L (threeRootSet r₁ r₂ r₃) := by
  rw [hμ, rootSpan_threeRootSet h₁ h₂ h₃]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨X, rfl⟩))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨G₁ X, rfl⟩)))
    (Subgroup.mem_sup_right ⟨G₂ (G₁ X), rfl⟩)

theorem threeA1Tw_diag_mem_fixed (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (Φ : ModGL τ L →* ModGL τ L) (n : ModGL τ L) (G₁ G₂ G₃ : SL2 L →* SL2 L)
    (hΘ : ∀ A B C : SL2 L, n * Φ (μ (A, B, C)) * n⁻¹ = μ (G₃ C, G₁ A, G₂ B))
    {X : SL2 L} (hX : G₃ (G₂ (G₁ X)) = X) :
    μ (X, G₁ X, G₂ (G₁ X)) ∈ twistedFixedPoints n Φ := by
  rw [mem_twistedFixedPoints, hΘ, hX]

theorem threeA1Tw_commutator_eq_map
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) =
      rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L))
    (Φ : ModGL τ L →* ModGL τ L) (n : ModGL τ L) (G₁ G₂ G₃ : SL2 L →* SL2 L)
    (hΘ : ∀ A B C : SL2 L, n * Φ (μ (A, B, C)) * n⁻¹ = μ (G₃ C, G₁ A, G₂ B))
    (S₃ : Subgroup (SL2 L)) (hS₃ : ∀ B : SL2 L, B ∈ S₃ ↔ G₃ (G₂ (G₁ B)) = B)
    (hp₃ : Group.IsPerfect S₃) (ν : SL2 L →* ModGL τ L)
    (hν : ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X))) :
    ⁅rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ,
      rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ⁆ = S₃.map ν := by
  classical
  have hQS : rootSpan τ L (threeRootSet r₁ r₂ r₃) =
      rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ :=
    rootSpan_threeRootSet h₁ h₂ h₃
  have hνΓ : ∀ X ∈ S₃, ν X ∈ rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ :=
    fun X hX => by
      rw [hν]
      exact Subgroup.mem_inf.2 ⟨threeA1Tw_diag_mem_rootSpan h₁ h₂ h₃ μ hμ G₁ G₂ X,
        threeA1Tw_diag_mem_fixed μ Φ n G₁ G₂ G₃ hΘ ((hS₃ X).1 hX)⟩
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨A₁, B₁, C₁, rfl⟩ := mem_sup_three hc12 hc13 hc23
      (by rw [← hQS]; exact (Subgroup.mem_inf.1 hg₁).1)
    obtain ⟨A₂, B₂, C₂, rfl⟩ := mem_sup_three hc12 hc13 hc23
      (by rw [← hQS]; exact (Subgroup.mem_inf.1 hg₂).1)
    rw [← hμ A₁ B₁ C₁] at hg₁ ⊢
    rw [← hμ A₂ B₂ C₂] at hg₂ ⊢
    have e₁ : μ (G₃ C₁, G₁ A₁, G₂ B₁) = μ (A₁, B₁, C₁) := by
      have h := (mem_twistedFixedPoints.1 (Subgroup.mem_inf.1 hg₁).2 :
        n * Φ (μ (A₁, B₁, C₁)) * n⁻¹ = _)
      rwa [hΘ] at h
    have e₂ : μ (G₃ C₂, G₁ A₂, G₂ B₂) = μ (A₂, B₂, C₂) := by
      have h := (mem_twistedFixedPoints.1 (Subgroup.mem_inf.1 hg₂).2 :
        n * Φ (μ (A₂, B₂, C₂)) * n⁻¹ = _)
      rwa [hΘ] at h
    obtain ⟨hmem, hcomm⟩ := threeA1Tw_commutator_step μ hker G₁ G₂ G₃ S₃ hS₃ e₁ e₂
    exact ⟨⁅A₁, A₂⁆, hmem, by rw [hν]; exact hcomm.symm⟩
  · rintro _ ⟨X, hX, rfl⟩
    refine perfect_le_of_commutator_mem hp₃
      (K := (⁅rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ,
        rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ⁆).comap ν)
      (fun a ha b hb => ?_) hX
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hνΓ a ha) (hνΓ b hb)

theorem threeA1Tw_map_isQuasisimple {M : Type*} [Group M] (μ : SL2 L × SL2 L × SL2 L →* M)
    (hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L))
    (G₁ G₂ : SL2 L →* SL2 L) (S₃ : Subgroup (SL2 L)) [Finite S₃]
    (hq₃ : CFSG.IsQuasisimple S₃) (ν : SL2 L →* M)
    (hν : ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X))) :
    Finite (S₃.map ν) ∧ CFSG.IsQuasisimple (S₃.map ν) := by
  let φ : S₃ →* S₃.map ν :=
    (ν.comp S₃.subtype).codRestrict (S₃.map ν) (fun x => ⟨x, x.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨_, X, hX, rfl⟩
    exact ⟨⟨X, hX⟩, Subtype.ext rfl⟩
  have hφ1 : ∃ k, φ k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, a, b, hab⟩ := hq₃
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hsc : ∀ k : S₃, (k : SL2 L) ∈ Subgroup.center (SL2 L) := fun k => by
      have h1 : ν k = 1 := congrArg Subtype.val (hcon k)
      rw [hν] at h1
      exact (hker _ _ _ h1).1
    have hab' : a' * b' = b' * a' :=
      Subtype.ext (Subgroup.mem_center_iff.1 (hsc b') a')
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']
  exact ⟨Finite.of_surjective φ hφs,
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq₃ hφs hφ1⟩

theorem threeA1Tw_normalized
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃))
    (hyR : y ∈ twistedFixedPoints n Φ) {u : ModGL τ L}
    (hu : u ∈ ⁅rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ,
      rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ⁆) :
    y * u * y⁻¹ ∈ ⁅rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ,
      rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ⁆ := by
  have hS3 : ∀ α ∈ threeRootSet r₁ r₂ r₃, IsRoot τ α := by
    intro α hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h₁, IsRoot.neg h₁, h₂, IsRoot.neg h₂, h₃, IsRoot.neg h₃]
  have hN : y ∈ Subgroup.normalizer
      (rootSpan τ L (threeRootSet r₁ r₂ r₃) : Set (ModGL τ L)) :=
    (sup_le (KE.torusGroup_le_normalizer_rootSpan hS3) Subgroup.le_normalizer) hy
  have hΓn : ∀ g ∈ rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ,
      y * g * y⁻¹ ∈ rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ :=
    fun g hg => Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hN g).1
      (Subgroup.mem_inf.1 hg).1, mul_mem (mul_mem hyR (Subgroup.mem_inf.1 hg).2) (inv_mem hyR)⟩
  have h1 : ⁅rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ,
      rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ⁆ ≤
      (⁅rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ,
        rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ⁆).comap
        (MulAut.conj y).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hΓn g₁ hg₁) (hΓn g₂ hg₂)
  have h2 := h1 hu
  simpa [MulAut.conj_apply] using h2

theorem threeA1Tw_conjSL_fixes {S : Subgroup (SL2 L)} (hS : Group.IsPerfect S)
    (X : GL (Fin 2) L)
    (hX : ∀ V ∈ S, ∃ z ∈ Subgroup.center (SL2 L), conjSL X V = z * V) :
    ∀ U ∈ S, conjSL X U = U := by
  intro U hU
  have hle : S ≤ (conjSL X).eqLocus (MonoidHom.id (SL2 L)) := by
    refine perfect_le_of_commutator_mem hS fun a ha b hb => ?_
    obtain ⟨za, hza, ea⟩ := hX a ha
    obtain ⟨zb, hzb, eb⟩ := hX b hb
    show conjSL X ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, ea, eb, commutator_mul_central hza hzb]
  exact hle hU

theorem threeA1Tw_torus_mul_rootSL2 [IsAlgClosed L]
    {r : Fin τ.rank → ℤ} (hr : IsRoot τ r) {S : Subgroup (SL2 L)}
    (hz : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (b : Fin τ.rank → Lˣ) (M : SL2 L) (X : GL (Fin 2) L)
    (hX : X = diagUnitOne (rootChar b r) * Matrix.SpecialLinearGroup.toGL M)
    (hSX : ∀ U ∈ S, conjSL X U = U) :
    rootDiagUnit τ b * rootSL2 τ L r M ∈ torusGroup τ L ∧
      ∀ A' : SL2 L, rootSL2 τ L r (conjSL X A') = rootSL2 τ L r A' := by
  have htH : rootDiagUnit τ b ∈ torusGroup τ L := rootDiagUnit_mem_torusGroup b
  have hconj := conj_rootSL2_torus_mul hr b M
  rw [← hX] at hconj
  have hc : ∀ U ∈ S, (rootDiagUnit τ b * rootSL2 τ L r M) * rootSL2 τ L r U =
      rootSL2 τ L r U * (rootDiagUnit τ b * rootSL2 τ L r M) := fun U hU => by
    have h := hconj U
    rw [hSX U hU] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hyH : rootDiagUnit τ b * rootSL2 τ L r M ∈
      (torusGroup τ L : Set (ModGL τ L)) * (rootRankOneGroup τ L r : Set (ModGL τ L)) :=
    ⟨rootDiagUnit τ b, htH, rootSL2 τ L r M, ⟨M, rfl⟩, rfl⟩
  have hall := commute_rootSL2_of_commute_fixed hr hz hyH hc
  refine ⟨mem_torusGroup_of_centralizes_rootSL2 hr hyH hall, fun A' => ?_⟩
  have h := hconj A'
  rw [hall A', mul_inv_cancel_right] at h
  exact h.symm

theorem threeA1Tw_centralizer [IsAlgClosed L]
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃) (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) =
      rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L))
    (G₁ G₂ : SL2 L →* SL2 L) (S₁ S₂ S₃ : Subgroup (SL2 L))
    (hS₂ : S₂ = S₃.map G₁) (hS₁ : S₁ = S₂.map G₂)
    (hp₁ : Group.IsPerfect S₁) (hp₂ : Group.IsPerfect S₂) (hp₃ : Group.IsPerfect S₃)
    (hz₁ : Subgroup.centralizer ((S₁.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₂ : Subgroup.centralizer ((S₂.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₃ : Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    {y : ModGL τ L} (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃))
    (hcomm : ∀ U ∈ S₃, y * μ (U, G₁ U, G₂ (G₁ U)) = μ (U, G₁ U, G₂ (G₁ U)) * y) :
    y ∈ torusGroup τ L ∧ y ∈ Subgroup.centralizer
      ((rootSpan τ L (threeRootSet r₁ r₂ r₃) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  classical
  have hQS : rootSpan τ L (threeRootSet r₁ r₂ r₃) =
      rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ :=
    rootSpan_threeRootSet h₁ h₂ h₃
  obtain ⟨b, A, B, C, rfl⟩ := exists_decomp hc12 hc13 hc23 h₁ h₂ h₃ hy
  obtain ⟨hc1', hc2', hc3'⟩ := conj_three_rootSL2 hc12 hc13 hc23 h₁ h₂ h₃ b A B C
  have htH : rootDiagUnit τ b ∈ torusGroup τ L := rootDiagUnit_mem_torusGroup b
  set y := rootDiagUnit τ b * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    with hydef
  set X₁ : GL (Fin 2) L := diagUnitOne (rootChar b r₁) * Matrix.SpecialLinearGroup.toGL A
    with hX₁
  set X₂ : GL (Fin 2) L := diagUnitOne (rootChar b r₂) * Matrix.SpecialLinearGroup.toGL B
    with hX₂
  set X₃ : GL (Fin 2) L := diagUnitOne (rootChar b r₃) * Matrix.SpecialLinearGroup.toGL C
    with hX₃
  have hcen : ∀ U ∈ S₃, ∃ z₁ ∈ Subgroup.center (SL2 L), ∃ z₂ ∈ Subgroup.center (SL2 L),
      ∃ z₃ ∈ Subgroup.center (SL2 L), conjSL X₁ U = z₁ * U ∧ conjSL X₂ (G₁ U) = z₂ * G₁ U ∧
        conjSL X₃ (G₂ (G₁ U)) = z₃ * G₂ (G₁ U) := by
    intro U hU
    have h2 : y * μ (U, G₁ U, G₂ (G₁ U)) * y⁻¹ = μ (U, G₁ U, G₂ (G₁ U)) := by
      rw [hcomm U hU, mul_inv_cancel_right]
    have h3 : y * μ (U, G₁ U, G₂ (G₁ U)) * y⁻¹ =
        μ (conjSL X₁ U, conjSL X₂ (G₁ U), conjSL X₃ (G₂ (G₁ U))) := by
      rw [hμ, hμ]
      calc y * (rootSL2 τ L r₁ U * rootSL2 τ L r₂ (G₁ U) * rootSL2 τ L r₃ (G₂ (G₁ U))) * y⁻¹
          = (y * rootSL2 τ L r₁ U * y⁻¹) * (y * rootSL2 τ L r₂ (G₁ U) * y⁻¹) *
              (y * rootSL2 τ L r₃ (G₂ (G₁ U)) * y⁻¹) := by group
        _ = _ := by rw [hc1' U, hc2' (G₁ U), hc3' (G₂ (G₁ U))]
    rw [h3] at h2
    exact threeA1Tw_exists_central_of_mu_eq μ hker h2
  have hcen1 : ∀ V ∈ S₃, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₁ V = z * V := fun V hV => by
    obtain ⟨z, hz, _, _, _, _, e1, _, _⟩ := hcen V hV
    exact ⟨z, hz, e1⟩
  have hcen2 : ∀ V ∈ S₂, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₂ V = z * V := fun V hV => by
    rw [hS₂] at hV
    obtain ⟨U, hU, rfl⟩ := hV
    obtain ⟨_, _, z, hz, _, _, _, e2, _⟩ := hcen U hU
    exact ⟨z, hz, e2⟩
  have hcen3 : ∀ V ∈ S₁, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₃ V = z * V := fun V hV => by
    rw [hS₁] at hV
    obtain ⟨W, hW, rfl⟩ := hV
    rw [hS₂] at hW
    obtain ⟨U, hU, rfl⟩ := hW
    obtain ⟨_, _, _, _, z, hz, _, _, e3⟩ := hcen U hU
    exact ⟨z, hz, e3⟩
  have hU₁ := threeA1Tw_conjSL_fixes hp₃ X₁ hcen1
  have hU₂ := threeA1Tw_conjSL_fixes hp₂ X₂ hcen2
  have hU₃ := threeA1Tw_conjSL_fixes hp₁ X₃ hcen3
  obtain ⟨hT₁, hF₁⟩ := threeA1Tw_torus_mul_rootSL2 h₁ hz₃ b A X₁ hX₁ hU₁
  obtain ⟨hT₂, hF₂⟩ := threeA1Tw_torus_mul_rootSL2 h₂ hz₂ b B X₂ hX₂ hU₂
  obtain ⟨hT₃, hF₃⟩ := threeA1Tw_torus_mul_rootSL2 h₃ hz₁ b C X₃ hX₃ hU₃
  have hA : rootSL2 τ L r₁ A ∈ torusGroup τ L := by
    have := mul_mem (inv_mem htH) hT₁
    rwa [inv_mul_cancel_left] at this
  have hB : rootSL2 τ L r₂ B ∈ torusGroup τ L := by
    have := mul_mem (inv_mem htH) hT₂
    rwa [inv_mul_cancel_left] at this
  have hC : rootSL2 τ L r₃ C ∈ torusGroup τ L := by
    have := mul_mem (inv_mem htH) hT₃
    rwa [inv_mul_cancel_left] at this
  have hyH : y ∈ torusGroup τ L := mul_mem htH (mul_mem (mul_mem hA hB) hC)
  refine ⟨hyH, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [SetLike.mem_coe, hQS] at hg
  obtain ⟨A', B', C', rfl⟩ := mem_sup_three hc12 hc13 hc23 hg
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
  exact ((f₁.mul_right f₂).mul_right f₃).eq.symm

end Generic

theorem three_A1_twisted_cyclic_family
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {r₁ r₂ r₃ : Fin τ.rank → ℤ}
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (Fr : L →+* L) (n : ModGL τ L) (G₁ G₂ G₃ : SL2 L →* SL2 L)
    (hΘ : ∀ A B C : SL2 L, n * Units.map (entrywiseHom Fr) (μ (A, B, C)) * n⁻¹ =
      μ (G₃ C, G₁ A, G₂ B))
    (S₁ S₂ S₃ : Subgroup (SL2 L)) [Finite S₃]
    (hS₂ : S₂ = S₃.map G₁) (hS₁ : S₁ = S₂.map G₂)
    (hS₃ : ∀ B : SL2 L, B ∈ S₃ ↔ G₃ (G₂ (G₁ B)) = B)
    (hq₁ : CFSG.IsQuasisimple S₁) (hq₂ : CFSG.IsQuasisimple S₂) (hq₃ : CFSG.IsQuasisimple S₃)
    (hz₁ : Subgroup.centralizer ((S₁.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₂ : Subgroup.centralizer ((S₂.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₃ : Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    ∃ P : Subgroup (ModGL τ L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan τ L (threeRootSet r₁ r₂ r₃) ∧
      P ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧ P ≤ adjointGroup τ L ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
        (∀ u ∈ P, y * u = u * y) →
        y ∈ subtorusSigma n (Units.map (entrywiseHom Fr)) (threeRootSet r₁ r₂ r₃)) := by
  classical
  have hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) := fun A B C h =>
    threeA1Tw_mem_center_of_mul_eq_one hc12 hc13 hc23 (by rw [← hμ]; exact h)
  obtain ⟨ν, hν⟩ : ∃ ν : SL2 L →* ModGL τ L, ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X)) :=
    ⟨μ.comp ((MonoidHom.id (SL2 L)).prod (G₁.prod (G₂.comp G₁))), fun X => rfl⟩
  have hPeq := threeA1Tw_commutator_eq_map hc12 hc13 hc23 h₁ h₂ h₃ μ hμ hker
    (Units.map (entrywiseHom Fr)) n G₁ G₂ G₃ hΘ S₃ hS₃ hq₃.1 ν hν
  obtain ⟨hPfin, hPq⟩ := threeA1Tw_map_isQuasisimple μ hker G₁ G₂ S₃ hq₃ ν hν
  have hρadj : ∀ r (A : SL2 L), rootSL2 τ L r A ∈ adjointGroup τ L := fun r A =>
    (exceptional_Lang_root_rank_one_data τ L r).2.2.2.2.1 A
  refine ⟨S₃.map ν, hPfin, hPq, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, -, rfl⟩
    rw [hν]
    exact threeA1Tw_diag_mem_rootSpan h₁ h₂ h₃ μ hμ G₁ G₂ X
  · rintro _ ⟨X, hX, rfl⟩
    rw [hν]
    exact threeA1Tw_diag_mem_fixed μ (Units.map (entrywiseHom Fr)) n G₁ G₂ G₃ hΘ
      ((hS₃ X).1 hX)
  · rintro _ ⟨X, -, rfl⟩
    rw [hν, hμ]
    exact mul_mem (mul_mem (hρadj _ _) (hρadj _ _)) (hρadj _ _)
  · intro y hy hyR u hu
    rw [← hPeq] at hu ⊢
    exact threeA1Tw_normalized h₁ h₂ h₃ n (Units.map (entrywiseHom Fr)) hy hyR hu
  · intro y hy hyR hcomm
    obtain ⟨hyH, hcZ⟩ := threeA1Tw_centralizer hc12 hc13 hc23 h₁ h₂ h₃ μ hμ hker G₁ G₂
      S₁ S₂ S₃ hS₂ hS₁ hq₁.1 hq₂.1 hq₃.1 hz₁ hz₂ hz₃ hy
      (fun U hU => by rw [← hν]; exact hcomm _ ⟨U, hU, rfl⟩)
    exact ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hcZ⟩

end CFSG.RankThree.PartOne.KGD
