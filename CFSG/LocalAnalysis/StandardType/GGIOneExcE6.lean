module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcLift
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDE6Field
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

@[expose] def GGE6ThreeRankSixTwoLocal : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    ∀ E : Subgroup (MulAut (TableBExc.RecipeGroup .E6 K)),
      (E : Set (MulAut (TableBExc.RecipeGroup .E6 K))) ⊆ TableBExc.RecipeID .E6 K →
      IsElemAbelian 3 E → 3 ^ 6 ≤ Nat.card E →
      ∃ U : Subgroup (TableBExc.RecipeGroup .E6 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U

@[expose] def GGE6OuterThreeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    ∀ φ : MulAut (TableBExc.RecipeGroup .E6 K), φ ^ 3 = 1 →
      φ ∉ TableBExc.RecipeID .E6 K → 3 ∣ n

theorem ggIE_finite_mulAut {R : Type} [Group R] [Finite R] : Finite (MulAut R) :=
  Finite.of_injective (fun φ : MulAut R => (φ : R → R)) DFunLike.coe_injective

section Certs


theorem ggIE_pow_three_mem_inn_closure_E6 {K : Type} [Field K] [Finite K]
    {φ : MulAut (TableBExc.RecipeGroup .E6 K)}
    (hφ : φ ∈ Subgroup.closure
      (LargeEvenInnSet (TableBExc.RecipeGroup .E6 K) ∪
        LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false))) :
    φ ^ 3 ∈ (MulAut.conj : TableBExc.RecipeGroup .E6 K →* _).range := by
  set N := (MulAut.conj : TableBExc.RecipeGroup .E6 K →*
    MulAut (TableBExc.RecipeGroup .E6 K)).range with hN
  set π := QuotientGroup.mk' N with hπ
  set S : Set (MulAut (TableBExc.RecipeGroup .E6 K) ⧸ N) :=
    π '' LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false) with hS
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨φ₁, h₁, rfl⟩ _ ⟨φ₂, h₂, rfl⟩
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf h₁
    obtain ⟨b, hb⟩ := TableB.exists_isDiagOf h₂
    change π φ₁ * π φ₂ = π φ₂ * π φ₁
    rw [← map_mul, ← map_mul, TableBExc.isDiagOf_comm ha hb]
  have hcube : ∀ x ∈ S, x ^ 3 = 1 := by
    rintro _ ⟨φ₁, h₁, rfl⟩
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf h₁
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact TableBExc.diag_pow_three_mem_inn ha
  have hcS : ∀ x ∈ Subgroup.closure S, ∀ s ∈ S, Commute x s := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact fun s hs => hcomm y hy s hs
    | one => exact fun s _ => Commute.one_left s
    | mul y z _ _ hy hz => exact fun s hs => (hy s hs).mul_left (hz s hs)
    | inv y _ hy => exact fun s hs => (hy s hs).inv_left
  have hcC : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz => exact hcS x hx z hz
    | one => exact Commute.one_right x
    | mul z w _ _ hz hw => exact hz.mul_right hw
    | inv z _ hz => exact hz.inv_right
  have hC : ∀ x ∈ Subgroup.closure S, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hcube y hy
    | one => exact one_pow 3
    | mul y z hy' hz' hy hz => rw [(hcC y hy' z hz').mul_pow, hy, hz, one_mul]
    | inv y _ hy => rw [inv_pow, hy, inv_one]
  have hle : Subgroup.closure (LargeEvenInnSet (TableBExc.RecipeGroup .E6 K) ∪
      LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) ≤
      (Subgroup.closure S).comap π := by
    rw [Subgroup.closure_le]
    rintro ψ (⟨x, rfl⟩ | hψ)
    · show π (MulAut.conj x) ∈ Subgroup.closure S
      have hx : MulAut.conj x ∈ N := ⟨x, rfl⟩
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hx]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨ψ, hψ, rfl⟩
  have h1 := hC _ (hle hφ)
  rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem ggIE_outdiagOdd_E6_three {K : Type} [Field K] [Finite K] :
    GGOutdiagOdd 3 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  have : Finite (TableBExc.RecipeGroup .E6 K) := TableBExc.finite_recipeGroup .E6 K
  have hN := InndiagE6.ggInndiagNormal_E6 (K := K)
  have hle : ggInndiag (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) ≤
      Subgroup.closure (LargeEvenInnSet (TableBExc.RecipeGroup .E6 K) ∪
        LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
    · rw [Subgroup.closure_le]
      exact fun ψ hψ => hψ
  have : Finite (MulAut (TableBExc.RecipeGroup .E6 K)) := ggIE_finite_mulAut
  exact ⟨ggInndiag _ _, ⟨fun φ hφ α => hN.conj_mem α hφ⟩, fun φ hφ _ => subset_ggInndiag hφ,
    TwE6Delta.odd_relIndex_of_pow_three_mem fun φ hφ => ggIE_pow_three_mem_inn_closure_E6 (hle hφ)⟩

theorem ggIE_endNodeIOne_E6_three (hT : GGE6ThreeRankSixTwoLocal)
    (hX : GGE6InnerDiagBoundThreeInput) (hO : GGE6OuterThreeInput) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) :
    GGEndNodeIOne 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  ggIE_endNodeIOne_of_bounds Nat.prime_three (TableBExc.center_recipeGroup_eq_bot .E6 K)
    (fun ⟨φ, hφ3, hφI⟩ => hX K n hn hK h3 (hO K n hn hK h3 φ hφ3 hφI))
    (fun E hEI hE hcard => hT K n hn hK h3 E hEI hE hcard)

theorem ggIE_labelAll_E6_three (hT : GGE6ThreeRankSixTwoLocal)
    (hX : GGE6InnerDiagBoundThreeInput) (hO : GGE6OuterThreeInput) {lab : LargeEvenLabel}
    (htag : lab.tag = .E6) (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd 3 R I ∧
      ∃ r, GGTorusLift 3 r R ∧ GGEndNodeIOne 3 r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h3 hlab
  subst htag
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  have h1 := TableBExc.recipeChevalleyE6_torusLift_three h3 hQ
  obtain ⟨K, _, _, hK, hQK, hl⟩ := h1
  exact ⟨K, inferInstance, inferInstance, hK, hQK, ggIE_outdiagOdd_E6_three, 5, hl,
    ggIE_endNodeIOne_E6_three hT hX hO hn hK h3⟩

end Certs

end CFSG.StandardType
