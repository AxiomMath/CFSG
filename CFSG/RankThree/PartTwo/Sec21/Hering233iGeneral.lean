module

import CFSG.RankThree.PartTwo.Sec21.Item229Pre
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem inf_eq_bot_of_simple {G : Type*} [Group G] {K N : Subgroup G} [IsSimpleGroup K]
    (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) (hKN : K ≤ Subgroup.normalizer (N : Set G))
    (hN : Group.IsSolvable N) : K ⊓ N = ⊥ := by
  have hn : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf K) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx.2
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hKN' : K ≤ N := fun x hx => by
      have : (⟨x, hx⟩ : K) ∈ N.subgroupOf K := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have hsol : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKN')
        (Subgroup.inclusion_injective hKN')
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have hperf : Group.IsPerfect K :=
      isPerfect_of_isSimpleGroup ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
    have : Nontrivial K := IsSimpleGroup.toNontrivial
    exact Group.IsPerfect.not_isSolvable K hsol

theorem le_center_of_central_ext {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp : CFSG.pCore p X ≤ Subgroup.center X) {M : Subgroup X} [hM : M.Normal] {Q : Type*}
    [Group Q] (f : M →* Q) (hQ : IsPGroup p f.range)
    (hker : f.ker.map M.subtype ≤ Subgroup.center X) : M ≤ Subgroup.center X := by
  obtain ⟨P⟩ : Nonempty (Sylow p M) := inferInstance
  have hfs : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hPtop : ((P.mapSurjective hfs : Sylow p f.range) : Subgroup f.range) = ⊤ :=
    ((P.mapSurjective hfs).is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at hPtop
  have hfac : ∀ m : M, ∃ x ∈ (P : Subgroup M), ∃ k : M, k ∈ f.ker ∧ m = x * k := by
    intro m
    have hm : f.rangeRestrict m ∈ (P : Subgroup M).map f.rangeRestrict := by
      rw [hPtop]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxm⟩ := hm
    refine ⟨x, hx, x⁻¹ * m, ?_, by simp⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : f x = f m := congrArg Subtype.val hxm
    rw [this, inv_mul_cancel]
  have hkc : ∀ k : M, k ∈ f.ker → ∀ n : M, k * n = n * k := by
    intro k hk n
    have hk' : (k : X) ∈ Subgroup.center X := hker ⟨k, hk, rfl⟩
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hk' (n : X)).symm)
  have hPn : (P : Subgroup M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨x, hx, k, hk, rfl⟩ := hfac g
    have h1 : x * k * n * (x * k)⁻¹ = x * n * x⁻¹ := by
      have : k * n * k⁻¹ = n := by rw [hkc k hk n, mul_inv_cancel_right]
      calc x * k * n * (x * k)⁻¹ = x * (k * n * k⁻¹) * x⁻¹ := by simp [mul_assoc]
        _ = x * n * x⁻¹ := by rw [this]
    rw [h1]
    exact (P : Subgroup M).mul_mem ((P : Subgroup M).mul_mem hx hn) ((P : Subgroup M).inv_mem hx)
  have hPc : (P : Subgroup M).Characteristic := Sylow.characteristic_of_normal P hPn
  have hPX : ((P : Subgroup M).map M.subtype).Normal := inferInstance
  have hPXp : IsPGroup p ((P : Subgroup M).map M.subtype) := P.isPGroup'.map M.subtype
  have hPXle : (P : Subgroup M).map M.subtype ≤ CFSG.pCore p X := le_sSup ⟨hPX, hPXp⟩
  intro m hm
  obtain ⟨x, hx, k, hk, hmk⟩ := hfac ⟨m, hm⟩
  have hm' : m = (x : X) * (k : X) := congrArg Subtype.val hmk
  have hx' : (x : X) ∈ Subgroup.center X := hp (hPXle ⟨x, hx, rfl⟩)
  have hk' : (k : X) ∈ Subgroup.center X := hker ⟨k, hk, rfl⟩
  rw [hm']
  exact Subgroup.mul_mem _ hx' hk'

theorem oTwoP_le_center {X : Type*} [Group X] [Finite X]
    (hO2 : CFSG.pCore 2 X ≤ Subgroup.center X) (hO3 : CFSG.pCore 3 X ≤ Subgroup.center X) :
    Sec4.oTwoP 3 X ≤ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Sec4.oTwoP 3 X →* X ⧸ CFSG.pCore 2 X :=
    (QuotientGroup.mk' (CFSG.pCore 2 X)).comp (Sec4.oTwoP 3 X).subtype
  have hrange : f.range ≤ CFSG.pCore 3 (X ⧸ CFSG.pCore 2 X) := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  refine le_center_of_central_ext (p := 3) hO3 f (CFSG.pCore_isPGroup.to_le hrange) ?_
  rintro _ ⟨x, hx, rfl⟩
  apply hO2
  exact (QuotientGroup.eq_one_iff _).mp hx

end CFSG.RankThree.PartTwo.Sec21.Hering233i
