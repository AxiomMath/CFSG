module

public import CFSG.RankThree.PartOne.KGD.ThreeA1Twisted
public import CFSG.RankThree.PartOne.TCX.A1Layer

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.RankThree.Classical (conjSL)

open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.TCX
open scoped Pointwise MatrixGroups commutatorElement

section Center

theorem center_sl2_eq_one {K : Type} [Field K] [CharP K 2] {Z : SL(2, K)}
    (hZ : Z ∈ Subgroup.center SL(2, K)) : Z = 1 :=
  eq_one_of_commute_transvections Z (Subgroup.mem_center_iff.1 hZ (uSL 1)).symm
    (Subgroup.mem_center_iff.1 hZ (vSL 1)).symm

end Center

section Family

variable {τ : Tag} {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
  {r₁ r₂ r₃ : Fin τ.rank → ℤ}

omit [IsAlgClosed L] in
theorem a3_join
    (hc12 : ∀ A B : SL(2, L), Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL(2, L), Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL(2, L), Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (μ : SL(2, L) × SL(2, L) × SL(2, L) →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (Φ : ModGL τ L →* ModGL τ L) (n : ModGL τ L) (G₁ G₂ G₃ : SL(2, L) →* SL(2, L))
    (hΘ : ∀ A B C : SL(2, L), n * Φ (μ (A, B, C)) * n⁻¹ = μ (G₃ C, G₁ A, G₂ B))
    (S₃ : Subgroup SL(2, L)) (hS₃ : ∀ B : SL(2, L), B ∈ S₃ ↔ G₃ (G₂ (G₁ B)) = B)
    (ν : SL(2, L) →* ModGL τ L) (hν : ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X))) :
    rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ twistedFixedPoints n Φ ≤ S₃.map ν := by
  have hker : ∀ A B C : SL(2, L), μ (A, B, C) = 1 → A ∈ Subgroup.center SL(2, L) ∧
      B ∈ Subgroup.center SL(2, L) ∧ C ∈ Subgroup.center SL(2, L) := fun A B C h =>
    threeA1Tw_mem_center_of_mul_eq_one hc12 hc13 hc23 (by rw [← hμ]; exact h)
  intro y hy
  obtain ⟨hyQ, hyR⟩ := Subgroup.mem_inf.1 hy
  rw [rootSpan_threeRootSet h₁ h₂ h₃] at hyQ
  obtain ⟨A, B, C, rfl⟩ := mem_sup_three hc12 hc13 hc23 hyQ
  rw [← hμ A B C] at hyR ⊢
  have e : μ (G₃ C, G₁ A, G₂ B) = μ (A, B, C) := by
    have h := (mem_twistedFixedPoints.1 hyR : n * Φ (μ (A, B, C)) * n⁻¹ = _)
    rwa [hΘ] at h
  obtain ⟨z₁, hz₁, z₂, hz₂, z₃, hz₃, e1, e2, e3⟩ :=
    threeA1Tw_exists_central_of_mu_eq μ hker e
  rw [center_sl2_eq_one hz₁, one_mul] at e1
  rw [center_sl2_eq_one hz₂, one_mul] at e2
  rw [center_sl2_eq_one hz₃, one_mul] at e3
  have hA : A ∈ S₃ := by
    refine (hS₃ A).2 ?_
    rw [e2, e3, e1]
  refine ⟨A, hA, ?_⟩
  rw [hν, e2, ← e3]

theorem a3_family
    (hc12 : ∀ A B : SL(2, L), Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL(2, L), Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL(2, L), Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (μ : SL(2, L) × SL(2, L) × SL(2, L) →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (Fr : L →+* L) (n : ModGL τ L) (G₁ G₂ G₃ : SL(2, L) →* SL(2, L))
    (hΘ : ∀ A B C : SL(2, L), n * Units.map (entrywiseHom Fr) (μ (A, B, C)) * n⁻¹ =
      μ (G₃ C, G₁ A, G₂ B))
    (S₁ S₂ S₃ : Subgroup SL(2, L)) [Finite S₃]
    (hS₂ : S₂ = S₃.map G₁) (hS₁ : S₁ = S₂.map G₂)
    (hS₃ : ∀ B : SL(2, L), B ∈ S₃ ↔ G₃ (G₂ (G₁ B)) = B)
    (hq₁ : CFSG.IsQuasisimple S₁) (hq₂ : CFSG.IsQuasisimple S₂) (hq₃ : CFSG.IsQuasisimple S₃)
    (hz₁ : Subgroup.centralizer ((S₁.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₂ : Subgroup.centralizer ((S₂.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₃ : Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (ν : SL(2, L) →* ModGL τ L) (hν : ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X))) :
    IsSigmaFamily n Fr (threeRootSet r₁ r₂ r₃) (fun _ : Unit => S₃.map ν) ∧
      rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ≤ S₃.map ν := by
  classical
  have hker : ∀ A B C : SL(2, L), μ (A, B, C) = 1 → A ∈ Subgroup.center SL(2, L) ∧
      B ∈ Subgroup.center SL(2, L) ∧ C ∈ Subgroup.center SL(2, L) := fun A B C h =>
    threeA1Tw_mem_center_of_mul_eq_one hc12 hc13 hc23 (by rw [← hμ]; exact h)
  have hPeq := threeA1Tw_commutator_eq_map hc12 hc13 hc23 h₁ h₂ h₃ μ hμ hker
    (Units.map (entrywiseHom Fr)) n G₁ G₂ G₃ hΘ S₃ hS₃ hq₃.1 ν hν
  obtain ⟨hPfin, hPq⟩ := threeA1Tw_map_isQuasisimple μ hker G₁ G₂ S₃ hq₃ ν hν
  have hρadj : ∀ r (A : SL(2, L)), rootSL2 τ L r A ∈ adjointGroup τ L := fun r A =>
    (exceptional_Lang_root_rank_one_data τ L r).2.2.2.2.1 A
  refine ⟨⟨fun _ => hPfin, fun _ => hPq, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ y hy hyR u hu => ?_, fun y hy hyR hcomm => ?_⟩,
    a3_join hc12 hc13 hc23 h₁ h₂ h₃ μ hμ _ n G₁ G₂ G₃ hΘ S₃ hS₃ ν hν⟩
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
  · rw [← hPeq] at hu ⊢
    exact threeA1Tw_normalized h₁ h₂ h₃ n (Units.map (entrywiseHom Fr)) hy hyR hu
  · obtain ⟨hyH, hcZ⟩ := threeA1Tw_centralizer hc12 hc13 hc23 h₁ h₂ h₃ μ hμ hker G₁ G₂
      S₁ S₂ S₃ hS₂ hS₁ hq₁.1 hq₂.1 hq₃.1 hz₁ hz₂ hz₃ hy
      (fun U hU => by rw [← hν]; exact hcomm () _ ⟨U, hU, rfl⟩)
    exact ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hcZ⟩

end Family

end CFSG.RankThree.PartOne.TCX.Tri
