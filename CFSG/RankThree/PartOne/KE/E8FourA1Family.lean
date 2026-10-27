module

public import CFSG.RankThree.PartOne.KE.FourA1Twisted
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.RankThree.PartOne.KGD.D4QA3

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.QuadraticSL2 (map_conjSL)
open CFSG.RankThree.PartOne.KGD (twHom twHom_apply isQuasisimple_map_twHom centralizer_map_twHom
  iterateFrobenius_bijective map_map_sl2 glMap_diagUnitOne exists_twist_antidiag
  exists_rootSL2_neg_eq)
open scoped MatrixGroups Matrix

section Generic

variable {L : Type} [Field L]

theorem e8_rootSL2_commute_of_orth {r r' : Fin Tag.E8.rank → ℤ}
    (hr : IsRoot .E8 r) (hr' : IsRoot .E8 r')
    (h : r ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r') = 0) (A B : SL2 L) :
    Commute (rootSL2 .E8 L r A) (rootSL2 .E8 L r' B) := by
  have hA : rootSL2 .E8 L r A ∈ rootSpan .E8 L ({r, -r} : Set (Fin Tag.E8.rank → ℤ)) :=
    rootRankOneGroup_le_rootSpan hr (by simp) (by simp) ⟨A, rfl⟩
  have hB : rootSL2 .E8 L r' B ∈ rootSpan .E8 L ({r', -r'} : Set (Fin Tag.E8.rank → ℤ)) :=
    rootRankOneGroup_le_rootSpan hr' (by simp) (by simp) ⟨B, rfl⟩
  refine rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl)))
    (S₁ := {r, -r}) (S₂ := {r', -r'}) ?_ ?_ ?_ _ hA _ hB
  · intro α hα
    rcases hα with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  · intro α hα
    rcases hα with rfl | rfl
    exacts [hr', IsRoot.neg hr']
  · intro α hα β hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
      simp [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, h]

theorem twHom_comp_four (Fr : L →+* L) (M₁ M₂ M₃ M₄ : GL (Fin 2) L) (B : SL2 L) :
    twHom Fr M₄ (twHom Fr M₃ (twHom Fr M₂ (twHom Fr M₁ B))) =
      conjSL (M₄ * Matrix.GeneralLinearGroup.map Fr
        (M₃ * Matrix.GeneralLinearGroup.map Fr
          (M₂ * Matrix.GeneralLinearGroup.map Fr M₁)))
        (Matrix.SpecialLinearGroup.map (Fr.comp (Fr.comp (Fr.comp Fr))) B) := by
  simp only [twHom_apply, map_conjSL, ← conjSL_mul, map_mul, map_map_sl2]

end Generic

section E8

variable {L : Type} [Field L]

theorem e8_four_A1_family [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {n : ModGL .E8 L} (hn : n ∈ monomialSubgroup .E8 L)
    {r₁ r₂ r₃ r₄ : Fin Tag.E8.rank → ℤ}
    (h₁ : IsRoot .E8 r₁) (h₂ : IsRoot .E8 r₂) (h₃ : IsRoot .E8 r₃) (h₄ : IsRoot .E8 r₄)
    (hw₁ : weylQuotientHom .E8 L ⟨n, hn⟩ • r₁ = r₂) (hw₂ : weylQuotientHom .E8 L ⟨n, hn⟩ • r₂ = r₃)
    (hw₃ : weylQuotientHom .E8 L ⟨n, hn⟩ • r₃ = r₄)
    (hw₄ : weylQuotientHom .E8 L ⟨n, hn⟩ • r₄ = -r₁)
    (o12 : r₁ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₂) = 0)
    (o13 : r₁ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₃) = 0)
    (o14 : r₁ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₄) = 0)
    (o23 : r₂ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₃) = 0)
    (o24 : r₂ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₄) = 0)
    (o34 : r₃ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₄) = 0) :
    ∃ P : Unit → Subgroup (ModGL .E8 L),
      IsSigmaFamily n (iterateFrobenius L ℓ f) (fourRootSet r₁ r₂ r₃ r₄) P := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrbij : Function.Bijective Fr := iterateFrobenius_bijective
  have hc12 : ∀ A B : SL2 L, Commute (rootSL2 .E8 L r₁ A) (rootSL2 .E8 L r₂ B) :=
    e8_rootSL2_commute_of_orth h₁ h₂ o12
  have hc13 : ∀ A C : SL2 L, Commute (rootSL2 .E8 L r₁ A) (rootSL2 .E8 L r₃ C) :=
    e8_rootSL2_commute_of_orth h₁ h₃ o13
  have hc14 : ∀ A D : SL2 L, Commute (rootSL2 .E8 L r₁ A) (rootSL2 .E8 L r₄ D) :=
    e8_rootSL2_commute_of_orth h₁ h₄ o14
  have hc23 : ∀ B C : SL2 L, Commute (rootSL2 .E8 L r₂ B) (rootSL2 .E8 L r₃ C) :=
    e8_rootSL2_commute_of_orth h₂ h₃ o23
  have hc24 : ∀ B D : SL2 L, Commute (rootSL2 .E8 L r₂ B) (rootSL2 .E8 L r₄ D) :=
    e8_rootSL2_commute_of_orth h₂ h₄ o24
  have hc34 : ∀ C D : SL2 L, Commute (rootSL2 .E8 L r₃ C) (rootSL2 .E8 L r₄ D) :=
    e8_rootSL2_commute_of_orth h₃ h₄ o34
  have hmw := mapsRootLines_weylQuotientHom (τ := .E8) (R := L) ⟨n, hn⟩
  obtain ⟨s₁, hs₁⟩ := exists_conj_rootSL2_eq hn hmw h₁ hw₁
  obtain ⟨s₂, hs₂⟩ := exists_conj_rootSL2_eq hn hmw h₂ hw₂
  obtain ⟨s₃, hs₃⟩ := exists_conj_rootSL2_eq hn hmw h₃ hw₃
  obtain ⟨s₄, hs₄⟩ := exists_conj_rootSL2_eq hn hmw h₄ hw₄
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) h₁
  set M₁ : GL (Fin 2) L := diagUnitOne s₁ with hM₁
  set M₂ : GL (Fin 2) L := diagUnitOne s₂ with hM₂
  set M₃ : GL (Fin 2) L := diagUnitOne s₃ with hM₃
  set M₄ : GL (Fin 2) L := CFSG.RankThree.Classical.swapGL * diagUnitOne a * diagUnitOne s₄
    with hM₄
  set μ : SL2 L × SL2 L × SL2 L × SL2 L →* ModGL .E8 L :=
    fourMul .E8 L r₁ r₂ r₃ r₄ hc12 hc13 hc14 hc23 hc24 hc34 with hμdef
  have hμ : ∀ A B C D, μ (A, B, C, D) = fourProd .E8 L r₁ r₂ r₃ r₄ A B C D :=
    fourMul_apply hc12 hc13 hc14 hc23 hc24 hc34
  have e1 : ∀ A : SL2 L, n * rootSL2 .E8 L r₁ (Matrix.SpecialLinearGroup.map Fr A) * n⁻¹ =
      rootSL2 .E8 L r₂ (twHom Fr M₁ A) := fun A => by
    rw [hs₁, twHom_apply]
  have e2 : ∀ B : SL2 L, n * rootSL2 .E8 L r₂ (Matrix.SpecialLinearGroup.map Fr B) * n⁻¹ =
      rootSL2 .E8 L r₃ (twHom Fr M₂ B) := fun B => by
    rw [hs₂, twHom_apply]
  have e3 : ∀ C : SL2 L, n * rootSL2 .E8 L r₃ (Matrix.SpecialLinearGroup.map Fr C) * n⁻¹ =
      rootSL2 .E8 L r₄ (twHom Fr M₃ C) := fun C => by
    rw [hs₃, twHom_apply]
  have e4 : ∀ D : SL2 L, n * rootSL2 .E8 L r₄ (Matrix.SpecialLinearGroup.map Fr D) * n⁻¹ =
      rootSL2 .E8 L r₁ (twHom Fr M₄ D) := fun D => by
    rw [hs₄, ha, twHom_apply, hM₄,
      conjSL_mul (CFSG.RankThree.Classical.swapGL * diagUnitOne a) (diagUnitOne s₄)]
  have hΘ : ∀ A B C D : SL2 L,
      n * Units.map (entrywiseHom Fr) (μ (A, B, C, D)) * n⁻¹ =
        μ (twHom Fr M₄ D, twHom Fr M₁ A, twHom Fr M₂ B, twHom Fr M₃ C) := by
    intro A B C D
    rw [hμ, hμ]
    unfold fourProd
    rw [map_mul, map_mul, map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field,
      entrywise_rootSL2_of_field, entrywise_rootSL2_of_field]
    calc n * (rootSL2 .E8 L r₁ (Matrix.SpecialLinearGroup.map Fr A) *
          rootSL2 .E8 L r₂ (Matrix.SpecialLinearGroup.map Fr B) *
          rootSL2 .E8 L r₃ (Matrix.SpecialLinearGroup.map Fr C) *
          rootSL2 .E8 L r₄ (Matrix.SpecialLinearGroup.map Fr D)) * n⁻¹
        = (n * rootSL2 .E8 L r₁ (Matrix.SpecialLinearGroup.map Fr A) * n⁻¹) *
          (n * rootSL2 .E8 L r₂ (Matrix.SpecialLinearGroup.map Fr B) * n⁻¹) *
          (n * rootSL2 .E8 L r₃ (Matrix.SpecialLinearGroup.map Fr C) * n⁻¹) *
          (n * rootSL2 .E8 L r₄ (Matrix.SpecialLinearGroup.map Fr D) * n⁻¹) := by group
      _ = rootSL2 .E8 L r₂ (twHom Fr M₁ A) * rootSL2 .E8 L r₃ (twHom Fr M₂ B) *
          rootSL2 .E8 L r₄ (twHom Fr M₃ C) * rootSL2 .E8 L r₁ (twHom Fr M₄ D) := by
        rw [e1, e2, e3, e4]
      _ = rootSL2 .E8 L r₁ (twHom Fr M₄ D) * rootSL2 .E8 L r₂ (twHom Fr M₁ A) *
          rootSL2 .E8 L r₃ (twHom Fr M₂ B) * rootSL2 .E8 L r₄ (twHom Fr M₃ C) := by
        rw [(((hc12 (twHom Fr M₄ D) (twHom Fr M₁ A)).symm.mul_left
          (hc13 (twHom Fr M₄ D) (twHom Fr M₂ B)).symm).mul_left
          (hc14 (twHom Fr M₄ D) (twHom Fr M₃ C)).symm).eq]
        group
  obtain ⟨k₄, _, _, _, hk₄⟩ := exists_finite_field_into ℓ (4 * f) (by omega) L
  set Fr₄ : L →+* L := iterateFrobenius L ℓ (4 * f) with hFr₄def
  have hFr₄ : ∀ c, Fr₄ c = c ^ Nat.card k₄ := fun c => by
    rw [hk₄]
    exact iterateFrobenius_def ℓ (4 * f) c
  have hFr4eq : Fr.comp (Fr.comp (Fr.comp Fr)) = Fr₄ := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, hFrdef, hFr₄def, iterateFrobenius_def]
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hk4 : 4 ≤ Nat.card k₄ := by
    rw [hk₄]
    calc 4 ≤ 2 ^ 4 := by norm_num
      _ ≤ ℓ ^ 4 := Nat.pow_le_pow_left hℓ.two_le 4
      _ ≤ ℓ ^ (4 * f) := Nat.pow_le_pow_right hℓ.pos (by omega)
  set g : GL (Fin 2) L := M₄ * Matrix.GeneralLinearGroup.map Fr
    (M₃ * Matrix.GeneralLinearGroup.map Fr (M₂ * Matrix.GeneralLinearGroup.map Fr M₁))
    with hgdef
  set y : Lˣ := a * (s₄ * Units.map Fr.toMonoidHom (s₃ * Units.map Fr.toMonoidHom
    (s₂ * Units.map Fr.toMonoidHom s₁))) with hydef
  have hg : g = CFSG.RankThree.Classical.swapGL * diagUnitOne y := by
    rw [hgdef, hM₄, hM₃, hM₂, hM₁, glMap_diagUnitOne, diagUnitOne_mul, glMap_diagUnitOne,
      diagUnitOne_mul, glMap_diagUnitOne, mul_assoc, mul_assoc, diagUnitOne_mul,
      diagUnitOne_mul]
  obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k₄) Fr₄ hFr₄ 1 y g (by
    rw [hg, coe_swapGL_mul_diagUnitOne]
    simp)
  set S₄ : Subgroup (SL2 L) := (Matrix.SpecialLinearGroup.map (algebraMap k₄ L)).range.map
    (conjSL Pm) with hS₄def
  have hS₄ : ∀ B : SL2 L, B ∈ S₄ ↔
      twHom Fr M₄ (twHom Fr M₃ (twHom Fr M₂ (twHom Fr M₁ B))) = B := by
    intro B
    rw [twHom_comp_four, hFr4eq, ← hgdef, ← hPm]
    exact (sl2_twistedFixed_iff Fr₄ (frobenius_fixed_iff Fr₄ hFr₄) Pm B).symm
  obtain ⟨hfin₄, hq₄⟩ := sl2_conj_range_quasisimple (K := k₄) (L := L) hk4 Pm
  have hz₄ := sl2_conj_range_centralizer (K := k₄) (L := L) Pm
  have hq₃ := isQuasisimple_map_twHom (Fr := Fr) M₁ hq₄
  have hq₂ := isQuasisimple_map_twHom (Fr := Fr) M₂ hq₃
  have hq₁ := isQuasisimple_map_twHom (Fr := Fr) M₃ hq₂
  have hz₃ := centralizer_map_twHom hFrbij M₁ hz₄
  have hz₂ := centralizer_map_twHom hFrbij M₂ hz₃
  have hz₁ := centralizer_map_twHom hFrbij M₃ hz₂
  have : Finite S₄ := hfin₄
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ :=
    four_A1_twisted_cyclic_family hc12 hc13 hc14 hc23 hc24 hc34 h₁ h₂ h₃ h₄ μ hμ Fr n
      (twHom Fr M₁) (twHom Fr M₂) (twHom Fr M₃) (twHom Fr M₄) hΘ _ _ _ S₄ rfl rfl rfl hS₄
      hq₁ hq₂ hq₃ hq₄ hz₁ hz₂ hz₃ hz₄
  exact ⟨fun _ => P, fun _ => hPfin, fun _ => hPq, fun _ => hPQ, fun _ => hPR, fun _ => hPadj,
    fun _ y' hy hyR u hu => hPnorm y' hy hyR u hu,
    fun y' hy hyR hcomm => hPcent y' hy hyR fun u hu => hcomm () u hu⟩

end E8

end CFSG.RankThree.PartOne.KE
