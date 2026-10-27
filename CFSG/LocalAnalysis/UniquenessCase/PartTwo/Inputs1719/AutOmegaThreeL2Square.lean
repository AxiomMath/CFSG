module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.GroupTheory.ConjActionModPCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFourFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def K_19_13_autOmega : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), Even n → 2 < n →
    (IsL2Square X n ∨ (S17.IsL2U3Product X n ∧ IsPowTwo n)) →
    ∀ Q : Subgroup (MulAut X), IsPGroup 3 Q →
      ∀ α ∈ Q, ∀ β ∈ Q, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α

theorem center_eq_bot_of_isL2Square_or_isL2U3Product {X : Type} [Group X] {n : ℕ}
    (h : IsL2Square X n ∨ S17.IsL2U3Product X n) : Subgroup.center X = ⊥ := by
  rcases h with ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ | ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩
  · have : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
    have : Finite B := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB)
    refine CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e ?_
    rw [Subgroup.center_prod, S17.center_eq_bot_of_lieModel_psl2 hA,
      S17.center_eq_bot_of_lieModel_psl2 hB, Subgroup.bot_prod_bot]
  · have : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
    refine CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e ?_
    rw [Subgroup.center_prod, S17.center_eq_bot_of_lieModel_psl2 hA, S17.center_eq_bot_of_isU3 hB,
      Subgroup.bot_prod_bot]

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_ker_conjModPCore_of_autOmega {I P : Subgroup G}
    (hPN : P ≤ normalizer (I : Set G)) (hP : IsPGroup 3 P)
    (hK : ∀ Q : Subgroup (MulAut (Bar2 I)), IsPGroup 3 Q →
      ∀ α ∈ Q, ∀ β ∈ Q, α ^ 3 = 1 → β ^ 3 = 1 → α * β = β * α)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) :
    x * y * x⁻¹ * y⁻¹ ∈ (CFSG.GroupTheory.conjModPCore 2 I P hPN).ker.map P.subtype := by
  set φ := CFSG.GroupTheory.conjModPCore 2 I P hPN
  have hQ : IsPGroup 3 φ.range := hP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hpow : ∀ (z : ↥P), (z : G) ^ 3 = 1 → φ z ^ 3 = 1 := fun z hz => by
    rw [← map_pow, show z ^ 3 = 1 from Subtype.ext (by simpa using hz), map_one]
  have hc := hK φ.range hQ _ ⟨⟨x, hx⟩, rfl⟩ _ ⟨⟨y, hy⟩, rfl⟩ (hpow ⟨x, hx⟩ hx3) (hpow ⟨y, hy⟩ hy3)
  refine ⟨⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
  group

theorem inf_inf_map_ker_conjModPCore_eq_bot {I P : Subgroup G}
    (hPN : P ≤ normalizer (I : Set G)) (hP : IsPGroup 3 P)
    (hZ : Subgroup.center (Bar2 I) = ⊥) :
    P ⊓ I ⊓ (CFSG.GroupTheory.conjModPCore 2 I P hPN).ker.map P.subtype = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨-, hgI⟩, a, ha, rfl⟩
  rw [Subgroup.mem_bot]
  have h1 := CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 I P hPN a.2 hgI
  have h2 : MulAut.conj (QuotientGroup.mk (⟨(a : G), hgI⟩ : ↥I) : Bar2 I) = 1 := by
    rw [← h1]
    exact ha
  have h3 : (QuotientGroup.mk (⟨(a : G), hgI⟩ : ↥I) : Bar2 I) ∈ Subgroup.center (Bar2 I) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun f : MulAut (Bar2 I) => f z) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    calc z * _ = _ * z * _⁻¹ * _ := by rw [hz]
      _ = _ := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h3
  have h2g : IsPGroup 2 (CFSG.pCore 2 ↥I) := CFSG.pCore_isPGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdis := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P ((CFSG.pCore 2 ↥I).map I.subtype)
    hP (h2g.map I.subtype)
  exact Subgroup.disjoint_def.mp hdis a.2 ⟨⟨(a : G), hgI⟩, h3, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
