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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.Monster.B.Generic

open Subgroup
open scoped commutatorElement

theorem center_eq_bot_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G) : center G = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right fun h =>
    hnonab (center_eq_top_iff.mp h)

theorem commutator_eq_top_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G) : commutator G = ⊤ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left fun h =>
    hnonab ((commutator_eq_bot_iff G).mp h)

theorem commutatorElement_mul_center {G : Type*} [Group G] {z₁ z₂ : G} (h₁ : z₁ ∈ center G)
    (h₂ : z₂ ∈ center G) (a b : G) : ⁅z₁ * a, z₂ * b⁆ = ⁅a, b⁆ := by
  have c₁ : ∀ g : G, ⁅z₁, g⁆ = 1 := fun g =>
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp h₁ g).symm
  have c₂ : ∀ g : G, ⁅g, z₂⁆ = 1 := fun g =>
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp h₂ g)
  have d₁ : ∀ g : G, z₁ * g * z₁⁻¹ = g := fun g => by
    rw [← mem_center_iff.mp h₁ g, mul_inv_cancel_right]
  have d₂ : ∀ g : G, z₂ * g * z₂⁻¹ = g := fun g => by
    rw [← mem_center_iff.mp h₂ g, mul_inv_cancel_right]
  rw [commutatorElement_mul_left_eq_conj_mul, c₁, mul_one, d₁,
    commutatorElement_mul_right_eq_mul_conj, c₂, one_mul, d₂]

theorem central_double_extension_derived_perfect {E : Type*} [Group E] (Z : Subgroup E)
    [Z.Normal] (hZc : Z ≤ center E) (hZ2 : Nat.card Z = 2) (hZd : Z ≤ commutator E)
    (hsimple : IsSimpleGroup (commutator (E ⧸ Z)))
    (hnonab : ¬ IsMulCommutative (commutator (E ⧸ Z)))
    (hindex : (commutator (E ⧸ Z)).index = 2) (hcenter : center (E ⧸ Z) = ⊥) :
    Group.IsPerfect (commutator E) ∧ (commutator E).index = 2 ∧ center E = Z ∧
      (center (commutator E)).map (commutator E).subtype = Z ∧
      (∃ e : commutator E ⧸ Z.subgroupOf (commutator E) ≃* commutator (E ⧸ Z),
        ∀ g : commutator E, (e g : E ⧸ Z) = ((g : E) : E ⧸ Z)) ∧
      ¬ ∃ L : Subgroup E, L ≤ commutator E ∧ Z ⊓ L = ⊥ ∧ Z ⊔ L = commutator E := by
  set π := QuotientGroup.mk' Z
  set D := commutator E with hD_def
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hmapD : D.map π = commutator (E ⧸ Z) := by
    rw [hD_def, _root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ hπs]
  have hcomapQ : (commutator (E ⧸ Z)).comap π = D := by
    rw [← hmapD, comap_map_eq, hker, sup_eq_left.mpr hZd]
  have hindexD : D.index = 2 := by
    rw [← hcomapQ, index_comap_of_surjective _ hπs, hindex]
  have hQperf : ⁅commutator (E ⧸ Z), commutator (E ⧸ Z)⁆ = commutator (E ⧸ Z) :=
    Subgroup.isPerfect_iff.mp ⟨commutator_eq_top_of_isSimpleGroup hnonab⟩
  have hDD : ⁅D, D⁆.map π = commutator (E ⧸ Z) := by rw [map_commutator, hmapD, hQperf]
  have hD_eq : D = ⁅D, D⁆ ⊔ Z := by
    rw [← hker, ← comap_map_eq, hDD, hcomapQ]
  have hperf : ⁅D, D⁆ = D := by
    refine le_antisymm (commutator_le_left D D) ?_
    let f : E ⧸ ⁅D, D⁆ →* E ⧸ D :=
      QuotientGroup.map _ _ (MonoidHom.id E) (by simpa using commutator_le_left D D)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (E ⧸ D) := isCyclic_of_prime_card (p := 2) (by rw [← index_eq_card, hindexD])
    have hcomm : IsMulCommutative (E ⧸ ⁅D, D⁆) := by
      refine f.isMulCommutative_of_isCyclic_of_ker_le_center ?_
      rw [QuotientGroup.ker_map]
      rintro _ ⟨d, hd, rfl⟩
      simp only [SetLike.mem_coe, mem_comap, MonoidHom.id_apply] at hd
      rw [hD_eq] at hd
      obtain ⟨e, he, z, hz, rfl⟩ := mem_sup_of_normal_right.mp hd
      rw [mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        have hz' := mem_center_iff.mp (hZc hz) g
        have he' : ((e : E) : E ⧸ ⁅D, D⁆) = 1 := (QuotientGroup.eq_one_iff e).mpr he
        simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, he', one_mul]
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hz']
    exact (Normal.quotient_commutative_iff_commutator_le.mp hcomm)
  have hcenterE : center E = Z := by
    refine le_antisymm (fun g hg => ?_) hZc
    have h := map_center_le_center hπs (mem_map_of_mem π hg)
    rw [hcenter, mem_bot] at h
    rw [← hker]
    exact h
  have hmemQ : ∀ g : D, π g ∈ commutator (E ⧸ Z) := fun g => hmapD ▸ mem_map_of_mem π g.2
  have hcenterD : (center D).map D.subtype = Z := by
    refine le_antisymm ?_ fun z hz => ⟨⟨z, hZd hz⟩, mem_center_iff.mpr fun g =>
      Subtype.ext (mem_center_iff.mp (hZc hz) g), rfl⟩
    rintro _ ⟨g, hg, rfl⟩
    have hcent : (⟨π g, hmemQ g⟩ : commutator (E ⧸ Z)) ∈ center (commutator (E ⧸ Z)) := by
      rw [mem_center_iff]
      rintro ⟨y, hy⟩
      rw [← hmapD] at hy
      obtain ⟨d, hd, rfl⟩ := hy
      have := congrArg (fun x : D => π x) (mem_center_iff.mp hg ⟨d, hd⟩)
      exact Subtype.ext (by simpa using this)
    rw [center_eq_bot_of_isSimpleGroup hnonab, mem_bot] at hcent
    rw [← hker]
    exact congrArg Subtype.val hcent
  let φ : D →* commutator (E ⧸ Z) := (π.comp D.subtype).codRestrict _ hmemQ
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hmapD] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨⟨d, hd⟩, rfl⟩
  have hφker : φ.ker = Z.subgroupOf D := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    exact Subtype.ext_iff
  refine ⟨Subgroup.isPerfect_iff.mpr hperf, hindexD, hcenterE, hcenterD,
    ⟨(QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs), fun g => rfl⟩, ?_⟩
  rintro ⟨L, -, hZL, hZLD⟩
  have hDL : ⁅D, D⁆ ≤ L := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [← hZLD] at hg₁ hg₂
    obtain ⟨z₁, hz₁, l₁, hl₁, rfl⟩ := mem_sup_of_normal_left.mp hg₁
    obtain ⟨z₂, hz₂, l₂, hl₂, rfl⟩ := mem_sup_of_normal_left.mp hg₂
    rw [commutatorElement_mul_center (hZc hz₁) (hZc hz₂), commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂)
  have hZL' : Z ≤ L := hZd.trans (hperf ▸ hDL)
  rw [inf_eq_left.mpr hZL'] at hZL
  rw [hZL] at hZ2
  simp at hZ2

end CFSG.Monster.B.Generic
