module

public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.RankThree.PartOne.KGD.D4QA3

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.QuadraticSL2 (map_conjSL)
open CFSG.RankThree.PartOne.KGD (twHom twHom_apply isQuasisimple_map_twHom centralizer_map_twHom
  iterateFrobenius_bijective map_map_sl2 glMap_diagUnitOne glMap_swapGL exists_twist_antidiag
  exists_rootSL2_neg_eq)
open CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Matrix Pointwise

set_option linter.unusedSectionVars false


section Block

variable {τ : Tag} {L : Type} [Field L]

theorem a1_block_of_fixed {r : Fin τ.rank → ℤ} (hr : IsRoot τ r) (n : ModGL τ L)
    (Φ : ModGL τ L →* ModGL τ L) {S : Subgroup (SL2 L)} (hfin : Finite S)
    (hq : CFSG.IsQuasisimple S)
    (hz : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hSfix : ∀ B : SL2 L, n * Φ (rootSL2 τ L r B) * n⁻¹ = rootSL2 τ L r B ↔ B ∈ S) :
    Finite ↥(rootSpan τ L {r, -r} ⊓ twistedFixedPoints n Φ) ∧
      CFSG.IsQuasisimple ↥(rootSpan τ L {r, -r} ⊓ twistedFixedPoints n Φ) ∧
      ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L {r, -r},
        (∀ u ∈ rootSpan τ L {r, -r} ⊓ twistedFixedPoints n Φ, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (rootSpan τ L {r, -r} : Set (ModGL τ L)) := by
  classical
  have hinj : Function.Injective (rootSL2 τ L r) := rootSL2_injective_of_field r
  have hrange : rootSpan τ L {r, -r} = (rootSL2 τ L r).range := by
    rw [rootSpan, iSup_insert, iSup_singleton, ← range_rootSL2_of_isRoot hr]
  have hroots : ∀ α ∈ ({r, -r} : Set (Fin τ.rank → ℤ)), IsRoot τ α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  have hPeq : rootSpan τ L {r, -r} ⊓ twistedFixedPoints n Φ = S.map (rootSL2 τ L r) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgQ, hgR⟩ := Subgroup.mem_inf.1 hg
      rw [hrange] at hgQ
      obtain ⟨A, rfl⟩ := hgQ
      exact ⟨A, (hSfix A).1 hgR, rfl⟩
    · rintro _ ⟨A, hA, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, (hSfix A).2 hA⟩
      rw [hrange]
      exact ⟨A, rfl⟩
  have hfinP : Finite (S.map (rootSL2 τ L r)) := by
    have : Finite S := hfin
    exact Finite.of_equiv S (Subgroup.equivMapOfInjective S (rootSL2 τ L r) hinj)
  have hqP : CFSG.IsQuasisimple (S.map (rootSL2 τ L r)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective S (rootSL2 τ L r) hinj)
      hq
  refine ⟨?_, ?_, fun y hy hc => ?_⟩
  · rw [hPeq]
    exact hfinP
  · rw [hPeq]
    exact hqP
  · have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
      (rootSpan τ L {r, -r}) (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hroots)
    have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L {r, -r} : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := hy
    rw [e] at hy'
    have hy2 : y ∈ (torusGroup τ L : Set (ModGL τ L)) *
        (rootRankOneGroup τ L r : Set (ModGL τ L)) := by
      obtain ⟨t, ht, q, hq', rfl⟩ := hy'
      rw [SetLike.mem_coe, hrange] at hq'
      exact ⟨t, ht, q, hq', rfl⟩
    have hcS : ∀ A ∈ S, y * rootSL2 τ L r A = rootSL2 τ L r A * y := fun A hA =>
      hc (rootSL2 τ L r A) (by rw [hPeq]; exact ⟨A, hA, rfl⟩)
    have hall := commute_rootSL2_of_commute_fixed hr hz hy2 hcS
    refine ⟨mem_torusGroup_of_centralizes_rootSL2 hr hy2 hall, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [SetLike.mem_coe, hrange] at hg
    obtain ⟨A, rfl⟩ := hg
    exact (hall A).symm

end Block

section Twist

variable {L : Type} [Field L]

theorem twHom_comp_two (Fr : L →+* L) (M₁ M₂ : GL (Fin 2) L) (B : SL2 L) :
    twHom Fr M₂ (twHom Fr M₁ B) =
      conjSL (M₂ * Matrix.GeneralLinearGroup.map Fr M₁)
        (Matrix.SpecialLinearGroup.map (Fr.comp Fr) B) := by
  simp only [twHom_apply, map_conjSL, ← conjSL_mul, map_map_sl2]

end Twist

section Family

variable {L : Type} [Field L]

theorem pair_A1_family {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] [IsAlgClosed L] (hf : 1 ≤ f)
    {n : ModGL .E8 L} (hn : n ∈ monomialSubgroup .E8 L) {r₁ r₂ : Fin Tag.E8.rank → ℤ}
    (h₁ : IsRoot .E8 r₁) (h₂ : IsRoot .E8 r₂)
    (hw₁ : weylQuotientHom .E8 L ⟨n, hn⟩ • r₁ = r₂)
    (hw₂ : weylQuotientHom .E8 L ⟨n, hn⟩ • r₂ = -r₁)
    (o12 : r₁ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₂) = 0) :
    ∃ P : Unit → Subgroup (ModGL .E8 L),
      IsSigmaFamily n (iterateFrobenius L ℓ f) ({r₁, -r₁} ∪ {r₂, -r₂}) P := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  set Fr₂ : L →+* L := Fr.comp Fr with hFr₂def
  have hFr₂ : ∀ c, Fr₂ c = c ^ (ℓ ^ (2 * f)) := fun c => by
    rw [hFr₂def, RingHom.comp_apply, hFr, hFr, ← pow_mul, ← pow_add, two_mul]
  set n₂ : ModGL .E8 L := n * Units.map (entrywiseHom Fr) n with hn₂
  have hFeFe : ∀ x : ModGL .E8 L, Units.map (entrywiseHom Fr) (Units.map (entrywiseHom Fr) x) =
      Units.map (entrywiseHom Fr₂) x := fun x => by
    refine Units.ext ?_
    simp only [Units.coe_map]
    exact entrywise_entrywise Fr Fr _
  have hT2 : ∀ x : ModGL .E8 L, n₂ * Units.map (entrywiseHom Fr₂) x * n₂⁻¹ =
      n * Units.map (entrywiseHom Fr) (n * Units.map (entrywiseHom Fr) x * n⁻¹) * n⁻¹ :=
    fun x => by
    rw [← hFeFe, hn₂, map_mul, map_mul, map_inv]
    group
  have hS : ∀ r, IsRoot .E8 r → ∀ x ∈ ({r, -r} : Set (Fin Tag.E8.rank → ℤ)), IsRoot .E8 x :=
    fun r hr x hx => by
    rcases hx with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  obtain ⟨k₂, _, _, _, hk₂⟩ := exists_finite_field_into ℓ (2 * f) (by omega) L
  have hFr₂k : ∀ c, Fr₂ c = c ^ Nat.card k₂ := fun c => by
    rw [hk₂]
    exact hFr₂ c
  have hk4 : 4 ≤ Nat.card k₂ := by
    rw [hk₂]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ.two_le 2
      _ ≤ ℓ ^ (2 * f) := Nat.pow_le_pow_right hℓ.pos (by omega)
  have hmw := mapsRootLines_weylQuotientHom (τ := .E8) (R := L) ⟨n, hn⟩
  have hblock : ∀ r r' : Fin Tag.E8.rank → ℤ, IsRoot .E8 r → IsRoot .E8 r' →
      weylQuotientHom .E8 L ⟨n, hn⟩ • r = r' → weylQuotientHom .E8 L ⟨n, hn⟩ • r' = -r →
      Finite ↥(rootSpan .E8 L {r, -r} ⊓
        twistedFixedPoints n₂ (Units.map (entrywiseHom Fr₂))) ∧
      CFSG.IsQuasisimple ↥(rootSpan .E8 L {r, -r} ⊓
        twistedFixedPoints n₂ (Units.map (entrywiseHom Fr₂))) ∧
      ∀ y ∈ torusGroup .E8 L ⊔ rootSpan .E8 L {r, -r},
        (∀ u ∈ rootSpan .E8 L {r, -r} ⊓ twistedFixedPoints n₂ (Units.map (entrywiseHom Fr₂)),
          y * u = u * y) →
        y ∈ torusGroup .E8 L ∧ y ∈ Subgroup.centralizer
          (rootSpan .E8 L {r, -r} : Set (ModGL .E8 L)) := by
    intro r r' hr hr' hw hw'
    obtain ⟨s₁, hs₁⟩ := exists_conj_rootSL2_eq hn hmw hr hw
    obtain ⟨s₂, hs₂⟩ := exists_conj_rootSL2_eq hn hmw hr' hw'
    obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) hr
    set M₁ : GL (Fin 2) L := diagUnitOne s₁ with hM₁
    set M₂ : GL (Fin 2) L := swapGL * diagUnitOne a * diagUnitOne s₂ with hM₂
    have e1 : ∀ A : SL2 L, n * rootSL2 .E8 L r (Matrix.SpecialLinearGroup.map Fr A) * n⁻¹ =
        rootSL2 .E8 L r' (twHom Fr M₁ A) := fun A => by
      rw [hs₁, twHom_apply]
    have e2 : ∀ B : SL2 L, n * rootSL2 .E8 L r' (Matrix.SpecialLinearGroup.map Fr B) * n⁻¹ =
        rootSL2 .E8 L r (twHom Fr M₂ B) := fun B => by
      rw [hs₂, ha, twHom_apply, hM₂, conjSL_mul (swapGL * diagUnitOne a) (diagUnitOne s₂)]
    have hsq : ∀ A : SL2 L, n₂ * Units.map (entrywiseHom Fr₂) (rootSL2 .E8 L r A) * n₂⁻¹ =
        rootSL2 .E8 L r (twHom Fr M₂ (twHom Fr M₁ A)) := fun A => by
      rw [hT2, entrywise_rootSL2_of_field, e1, entrywise_rootSL2_of_field, e2]
    set g : GL (Fin 2) L := M₂ * Matrix.GeneralLinearGroup.map Fr M₁ with hgdef
    set y : Lˣ := a * (s₂ * Units.map Fr.toMonoidHom s₁) with hydef
    have hg : g = swapGL * diagUnitOne y := by
      rw [hgdef, hM₂, hM₁, glMap_diagUnitOne, mul_assoc, mul_assoc, diagUnitOne_mul,
        diagUnitOne_mul]
    obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k₂) Fr₂ hFr₂k 1 y g (by
      rw [hg, coe_swapGL_mul_diagUnitOne]
      simp)
    set S : Subgroup (SL2 L) := (Matrix.SpecialLinearGroup.map (algebraMap k₂ L)).range.map
      (conjSL Pm) with hSdef
    have hinj : Function.Injective (rootSL2 .E8 L r) := rootSL2_injective_of_field r
    have hSfix : ∀ B : SL2 L, n₂ * Units.map (entrywiseHom Fr₂) (rootSL2 .E8 L r B) * n₂⁻¹ =
        rootSL2 .E8 L r B ↔ B ∈ S := by
      intro B
      rw [hsq, hinj.eq_iff, twHom_comp_two, ← hgdef, ← hPm]
      exact sl2_twistedFixed_iff Fr₂ (frobenius_fixed_iff Fr₂ hFr₂k) Pm B
    obtain ⟨hfin, hq⟩ := sl2_conj_range_quasisimple (K := k₂) (L := L) hk4 Pm
    have hz := sl2_conj_range_centralizer (K := k₂) (L := L) Pm
    exact a1_block_of_fixed hr n₂ (Units.map (entrywiseHom Fr₂)) hfin hq hz hSfix
  obtain ⟨hfin₁, hq₁, hc₁⟩ := hblock r₁ r₂ h₁ h₂ hw₁ hw₂
  obtain ⟨-, -, hc₂⟩ := hblock r₂ (-r₁) h₂ (IsRoot.neg h₁) hw₂ (by rw [smul_neg, hw₁])
  have hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hn⟩ • u =
      CFSG.RankThree.E6.weylMatrix (weylQuotientHom .E8 L ⟨n, hn⟩) *ᵥ u := fun u =>
    (CFSG.RankThree.E6.weylMatrix_mulVec _ u).symm
  have hmap12 : ∀ α ∈ ({r₁, -r₁} : Set (Fin Tag.E8.rank → ℤ)),
      CFSG.RankThree.E6.weylMatrix (weylQuotientHom .E8 L ⟨n, hn⟩) *ᵥ α ∈
        ({r₂, -r₂} : Set (Fin Tag.E8.rank → ℤ)) := by
    intro α hα
    rw [CFSG.RankThree.E6.weylMatrix_mulVec]
    rcases hα with rfl | rfl
    · rw [hw₁]; exact Or.inl rfl
    · rw [smul_neg, hw₁]; exact Or.inr rfl
  have hmap21 : ∀ α ∈ ({r₂, -r₂} : Set (Fin Tag.E8.rank → ℤ)),
      CFSG.RankThree.E6.weylMatrix (weylQuotientHom .E8 L ⟨n, hn⟩) *ᵥ α ∈
        ({r₁, -r₁} : Set (Fin Tag.E8.rank → ℤ)) := by
    intro α hα
    rw [CFSG.RankThree.E6.weylMatrix_mulVec]
    rcases hα with rfl | rfl
    · rw [hw₂]; exact Or.inr rfl
    · rw [smul_neg, hw₂, neg_neg]; exact Or.inl rfl
  have hT₁₂ := twist_rootSpan_le (L := L) Fr _ n hn hnW (hS r₁ h₁) hmap12
  have hT₂₁ := twist_rootSpan_le (L := L) Fr _ n hn hnW (hS r₂ h₂) hmap21
  have hcomm := rootSpan_commute_of_orth (L := L) (τ := Tag.E8) (Or.inr (Or.inr (Or.inr rfl)))
    (hS r₁ h₁) (hS r₂ h₂) (by
      intro α hα β hβ
      rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
        simp [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, o12])
  exact two_family_exchange Fr n (hS r₁ h₁) (hS r₂ h₂) hT₁₂ hT₂₁ hcomm n₂
    (Units.map (entrywiseHom Fr₂)) hT2 hfin₁ hq₁ hc₁ hc₂

end Family

end CFSG.RankThree.PartOne.KE8F
