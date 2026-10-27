module

public import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Tim78P210Basic

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

@[expose] def omegaTwoSub (B : Subgroup G) : Subgroup G :=
  (CFSG.omega ↥B (p := 2) 2).map B.subtype

theorem mem_omegaTwoSub_iff {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {x : G} :
    x ∈ omegaTwoSub B ↔ x ∈ B ∧ x ^ 4 = 1 := by
  let I : Subgroup ↥B :=
    { carrier := {y | y ^ 4 = 1}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have hab : a * b = b * a := Subtype.ext (hB a a.2 b b.2)
        show (a * b) ^ 4 = 1
        rw [(Commute.mul_pow hab 4), ha, hb, one_mul]
      inv_mem' := fun {a} ha => by
        show a⁻¹ ^ 4 = 1
        rw [inv_pow, ha, inv_one] }
  have hω : CFSG.omega ↥B (p := 2) 2 = I := by
    have h : CFSG.omega ↥B (p := 2) 2 = Subgroup.closure {y : ↥B | y ^ 4 = 1} := by
      simp only [CFSG.omega]
      norm_num
    rw [h]
    exact le_antisymm ((Subgroup.closure_le _).mpr fun y hy => hy)
      fun y hy => Subgroup.subset_closure hy
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hω] at hy
    refine ⟨y.2, ?_⟩
    have : (y ^ 4 : ↥B) = 1 := hy
    have h2 := congrArg Subtype.val this
    rw [Subgroup.coe_pow] at h2
    exact h2
  · rintro ⟨hxB, hx⟩
    refine ⟨⟨x, hxB⟩, ?_, rfl⟩
    rw [hω]
    show (⟨x, hxB⟩ : ↥B) ^ 4 = 1
    exact Subtype.ext (by rw [Subgroup.coe_pow]; exact hx)

structure HypH (M B : Subgroup G) : Prop where
  o2 : pCore 2 G = ⊥
  max : IsMaximalTwoLocal M
  fstar : generalizedFitting M = pCore 2 M
  le : B ≤ M
  normal : M ≤ Subgroup.normalizer (B : Set G)
  comm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  ti : IsTI B

namespace HypH

variable [Finite G] {M B : Subgroup G} (H : HypH M B)
include H

theorem le_Q : B ≤ inSubgroup (pCore 2) M :=
  le_of_isMulCommutative_normal H.fstar H.le H.normal
    ⟨⟨fun a b => Subtype.ext (H.comm _ a.2 _ b.2)⟩⟩

theorem two : IsPGroup 2 B :=
  (inSubgroup_pCore_two M).1.to_le H.le_Q

theorem normalizer_eq {D : Subgroup G} (hDB : D ≤ B) (hD1 : D ≠ ⊥)
    (hMD : M ≤ Subgroup.normalizer (D : Set G)) : Subgroup.normalizer (D : Set G) = M := by
  by_contra hne
  exact H.max.2 _ (lt_of_le_of_ne hMD (Ne.symm hne)) ⟨D, hD1, H.two.to_le hDB, rfl⟩

omit [Finite G] in
theorem le_normalizer_omegaOne : M ≤ Subgroup.normalizer (PartTwo.omegaOneSub B : Set G) := by
  intro m hm
  rw [← conjSubgroup_eq_self_iff, ← omegaOneSub_conj H.comm m,
    conjSubgroup_eq_self_iff.mpr (H.normal hm)]

omit [Finite G] in
theorem le_normalizer_omegaTwo : M ≤ Subgroup.normalizer (omegaTwoSub B : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_omegaTwoSub_iff H.comm, mem_omegaTwoSub_iff H.comm]
  have hmB := Subgroup.mem_normalizer_iff.mp (H.normal hm)
  constructor
  · rintro ⟨hx, hx4⟩
    refine ⟨(hmB x).mp hx, ?_⟩
    rw [conj_pow, hx4]
    group
  · rintro ⟨hx, hx4⟩
    refine ⟨(hmB x).mpr hx, ?_⟩
    rw [conj_pow] at hx4
    calc x ^ 4 = m⁻¹ * (m * x ^ 4 * m⁻¹) * m := by group
      _ = 1 := by rw [hx4]; group

end HypH

theorem omegaTwoSub_le (B : Subgroup G) : omegaTwoSub B ≤ B := Subgroup.map_subtype_le _

theorem comm_omegaTwoSub {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ omegaTwoSub B, ∀ y ∈ omegaTwoSub B, x * y = y * x := fun x hx y hy =>
  hB x (omegaTwoSub_le B hx) y (omegaTwoSub_le B hy)

theorem pow_four_of_mem_omegaTwoSub {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {x : G} (hx : x ∈ omegaTwoSub B) : x ^ 4 = 1 :=
  ((mem_omegaTwoSub_iff hB).mp hx).2

theorem omegaOneSub_omegaTwoSub {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    PartTwo.omegaOneSub (omegaTwoSub B) = PartTwo.omegaOneSub B := by
  ext x
  rw [mem_omegaOneSub_iff (comm_omegaTwoSub hB), mem_omegaOneSub_iff hB,
    mem_omegaTwoSub_iff hB]
  constructor
  · rintro ⟨⟨hx, -⟩, hxx⟩
    exact ⟨hx, hxx⟩
  · rintro ⟨hx, hxx⟩
    refine ⟨⟨hx, ?_⟩, hxx⟩
    calc x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hxx, one_mul]

variable [Finite G] in
theorem isTI_omegaTwoSub {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hTI : IsTI B) : IsTI (omegaTwoSub B) := by
  intro g
  by_cases h : omegaTwoSub B ⊓ conjSubgroup g (omegaTwoSub B) = ⊥
  · exact Or.inl h
  · right
    have hBg : conjSubgroup g B = B := by
      refine conjSubgroup_eq_of_isTI hTI fun hbot => h ?_
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
      have : z ∈ B ⊓ conjSubgroup g B := Subgroup.mem_inf.mpr ⟨omegaTwoSub_le B hz1,
        mem_conjSubgroup.mpr (omegaTwoSub_le B (mem_conjSubgroup.mp hz2))⟩
      rwa [hbot] at this
    have hg := conjSubgroup_eq_self_iff.mp hBg
    have hc : ∀ y : G, (g⁻¹ * y * g) ^ 4 = g⁻¹ * y ^ 4 * g := fun y => by
      simpa using conj_pow (a := g⁻¹) (b := y) (i := 4)
    have hg2 : conjSubgroup g (omegaTwoSub B) = omegaTwoSub B := by
      ext x
      rw [mem_conjSubgroup, mem_omegaTwoSub_iff hB, mem_omegaTwoSub_iff hB]
      constructor
      · rintro ⟨hx, hx4⟩
        refine ⟨?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp hg _).mp hx
          rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
        · rw [hc] at hx4
          calc x ^ 4 = g * (g⁻¹ * x ^ 4 * g) * g⁻¹ := by group
            _ = 1 := by rw [hx4]; group
      · rintro ⟨hx, hx4⟩
        refine ⟨?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
          rwa [inv_inv] at this
        · rw [hc, hx4]
          group
    rw [hg2, inf_idem]

end CFSG.RankThree.GF2n.Tim78
