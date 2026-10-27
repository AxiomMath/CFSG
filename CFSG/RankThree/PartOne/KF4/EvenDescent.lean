module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.RankThree.PartOne.KE.A1SL2

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open scoped commutatorElement

theorem layer_eq_top_of_isQuasisimple {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    CFSG.layer G = ⊤ :=
  CFSG.WholeGroup.layer_eq_top_of_isQuasisimple h

theorem isSolvable_centralizer_commutator (D : Type*) [Group D] :
    Group.IsSolvable (Subgroup.centralizer
      ((⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ : Subgroup D) : Set D)) := by
  set R : Subgroup D := ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ with hR
  set V : Subgroup D := Subgroup.centralizer (R : Set D) with hV
  refine ⟨2, ?_⟩
  rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_zero]
  set T1 : Subgroup V := ⁅(⊤ : Subgroup V), (⊤ : Subgroup V)⁆ with hT1
  have hT1R : ∀ a ∈ T1, (a : D) ∈ R := by
    intro a ha
    have h1 : T1.map V.subtype = ⁅(⊤ : Subgroup V).map V.subtype, (⊤ : Subgroup V).map V.subtype⁆ :=
      Subgroup.map_commutator _ _ _
    have h2 : (⊤ : Subgroup V).map V.subtype = V := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h3 : T1.map V.subtype ≤ R := by
      rw [h1, h2, hR]
      exact Subgroup.commutator_mono le_top le_top
    exact h3 (Subgroup.mem_map_of_mem V.subtype ha)
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot]
  have hbV : (b : D) ∈ Subgroup.centralizer (R : Set D) := b.2
  have hcomm := Subgroup.mem_centralizer_iff.1 hbV (a : D) (hT1R a ha)
  apply Subtype.ext
  change (a : D) * (b : D) * (a : D)⁻¹ * (b : D)⁻¹ = 1
  rw [hcomm]
  group

theorem odd_card_inf_centralizer_derived {C : Type*} [Group C] {D : Subgroup C}
    (hsolv : ∀ V : Subgroup D, V.Normal → Group.IsSolvable V → Odd (Nat.card V)) :
    Odd (Nat.card ↥(D ⊓ Subgroup.centralizer ((⁅D, D⁆ : Subgroup C) : Set C))) := by
  set R0 : Subgroup D := ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ with hR0
  have hmap : R0.map D.subtype = ⁅D, D⁆ := by
    rw [hR0, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set V : Subgroup D := Subgroup.centralizer (R0 : Set D) with hV
  have hVe : V = (D ⊓ Subgroup.centralizer ((⁅D, D⁆ : Subgroup C) : Set C)).subgroupOf D := by
    ext v
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨v.2, fun r hr => ?_⟩
      rw [← hmap] at hr
      obtain ⟨ρ, hρ, rfl⟩ := hr
      exact congrArg Subtype.val (h ρ hρ)
    · rintro ⟨-, h⟩ ρ hρ
      exact Subtype.ext (h (ρ : C) (by rw [← hmap]; exact Subgroup.mem_map_of_mem _ hρ))
  have hVn : V.Normal := inferInstance
  have hodd := hsolv V hVn (isSolvable_centralizer_commutator D)
  rw [hVe] at hodd
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
    D ⊓ Subgroup.centralizer ((⁅D, D⁆ : Subgroup C) : Set C) ≤ D)).toEquiv] at hodd

section Descent


theorem exists_finite_subfield_descent {τ : Tag} (K : Type) [Field K] [Finite K] (L : Type)
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] {h : ModGL τ L}
    (hh : h ∈ adjointGroup τ L) :
    ∃ (M : Subfield L) (_ : Finite M) (ι : K →+* M), M.subtype.comp ι = algebraMap K L ∧
      ∃ g ∈ adjointGroup τ M, baseChangeGL M.subtype g = h := by
  obtain ⟨S, hS⟩ := exists_finset_descent hh
  obtain ⟨E, hEfin, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) S
  obtain ⟨y, hy, hyh⟩ := hS E hSE
  refine ⟨E, hEfin, (algebraMap K L).codRestrict E (fun a => hKE ⟨a, rfl⟩), ?_, y, hy, hyh⟩
  ext a
  rfl

end Descent

end CFSG.RankThree.PartOne.KF4
