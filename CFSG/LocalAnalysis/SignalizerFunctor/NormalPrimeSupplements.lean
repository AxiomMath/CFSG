module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem hom_card_kernel_mul_card_of_surjective
    {ImageType : Type imageUniverse} [Group ImageType]
    (homomorphism : GroupType →* ImageType) (surjective : Function.Surjective homomorphism) :
    Nat.card homomorphism.ker * Nat.card ImageType = Nat.card GroupType := by
  have card_formula := homomorphism.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr surjective, Subgroup.card_top] at card_formula
  exact card_formula

theorem supplement_index_dvd_normal_card (normal supplement : Subgroup GroupType)
    [normal.Normal] (whole : normal ⊔ supplement = ⊤) : supplement.index ∣ Nat.card normal := by
  let projection := QuotientGroup.mk' normal
  let restricted := projection.domRestrict supplement
  have surjective : Function.Surjective restricted := by
    intro imageElement
    obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective normal imageElement
    have member : element ∈ normal ⊔ supplement := by rw [whole]; trivial
    obtain ⟨normalElement, normal_member, supplementElement, supplement_member, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.mp member
    refine ⟨⟨supplementElement, supplement_member⟩, ?_⟩
    change projection supplementElement = projection (normalElement * supplementElement)
    have trivial : projection normalElement = 1 := (QuotientGroup.eq_one_iff _).mpr normal_member
    rw [map_mul, trivial, one_mul]
  have restricted_card := hom_card_kernel_mul_card_of_surjective restricted surjective
  have normal_card := normal.card_mul_index
  rw [Subgroup.index_eq_card] at normal_card
  have supplement_card := supplement.card_mul_index
  have equal_product : Nat.card restricted.ker * supplement.index * Nat.card (GroupType ⧸ normal) =
      Nat.card normal * Nat.card (GroupType ⧸ normal) := by
    calc
      Nat.card restricted.ker * supplement.index * Nat.card (GroupType ⧸ normal) =
          (Nat.card restricted.ker * Nat.card (GroupType ⧸ normal)) * supplement.index := by ring
      _ = Nat.card supplement * supplement.index := by rw [restricted_card]
      _ = Nat.card GroupType := supplement_card
      _ = Nat.card normal * Nat.card (GroupType ⧸ normal) := normal_card.symm
  have equal := Nat.mul_right_cancel (Nat.card_pos (α := GroupType ⧸ normal)) equal_product
  exact ⟨Nat.card restricted.ker, by rw [mul_comm]; exact equal.symm⟩

theorem normal_pgroup_le_of_coprime_index (prime : ℕ) (prime_prime : prime.Prime)
    (normal subgroup : Subgroup GroupType) [normal.Normal]
    (pgroup : IsPGroup prime normal) (coprime : Nat.Coprime prime subgroup.index) : normal ≤ subgroup := by
  classical
  let : Fact prime.Prime := ⟨prime_prime⟩
  let internalSylow : Sylow prime subgroup := Classical.choice inferInstance
  obtain ⟨ambientSylow, restricted_equal⟩ := internalSylow.exists_comap_subtype_eq
  let embedded := (internalSylow : Subgroup subgroup).map subgroup.subtype
  have embedded_le : embedded ≤ (ambientSylow : Subgroup GroupType) := by
    change (internalSylow : Subgroup subgroup).map subgroup.subtype ≤ _
    rw [← restricted_equal, Subgroup.map_comap_eq]
    exact inf_le_right
  have factorization_equal : (Nat.card subgroup).factorization prime =
      (Nat.card GroupType).factorization prime := by
    have card_formula := subgroup.card_mul_index
    conv_rhs => rw [← card_formula]
    rw [Nat.factorization_mul Nat.card_pos.ne' (by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne')]
    simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
      (prime_prime.coprime_iff_not_dvd.mp coprime), add_zero]
  have embedded_card : Nat.card embedded = Nat.card (ambientSylow : Subgroup GroupType) := by
    rw [Subgroup.card_map_of_injective subgroup.subtype_injective, internalSylow.card_eq_multiplicity,
      ambientSylow.card_eq_multiplicity, factorization_equal]
  have embedded_equal := Subgroup.eq_of_le_of_card_ge embedded_le embedded_card.ge
  exact (pgroup.le_sylow_of_normal ambientSylow).trans
    (by rw [← embedded_equal]; exact Subgroup.map_subtype_le _)

theorem normal_prime_subgroup_le_supplement (prime : ℕ) (prime_prime : prime.Prime)
    (complement supplement normal : Subgroup GroupType) [complement.Normal] [normal.Normal]
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (whole : complement ⊔ supplement = ⊤) (normal_pgroup : IsPGroup prime normal) :
    normal ≤ supplement :=
  normal_pgroup_le_of_coprime_index prime prime_prime normal supplement normal_pgroup
    (complement_coprime.of_dvd_right (supplement_index_dvd_normal_card complement supplement whole))

end CFSG.SignalizerFunctor.Helpers
