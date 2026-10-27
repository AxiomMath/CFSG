module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCenterOfOddQuotientKernel
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Lifting a quotient centralizer across an odd center

If an involution normalizes a finite group `E` and a coset modulo `Z(E)` is
fixed, coprime one-cohomology supplies a representative of that coset fixed
by the involution.  This public extraction is the reusable centralizer
surjectivity input for the Section-4 PSL₂ transport.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped IsMulCommutative

universe u

public lemma zpow_eq_one_or_self_of_sq_eq_one_local
    {G : Type u} [Group G] {t : G}
    (ht : t * t = 1) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  by_cases ht1 : t = 1
  · left
    simp [ht1]
  · have hord : orderOf t = 2 :=
      (orderOf_eq_prime_iff (x := t)).2 ⟨by simpa [pow_two] using ht, ht1⟩
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      change k % (2 : ℤ) = 0 at hk
      simp [hk]
    · right
      change k % (2 : ℤ) = 1 at hk
      simp [hk]

/-- Lift a centralizer element from `E/Z(E)` to an element of `E` fixed by
the normalizing involution `s`: if `[s,x] ∈ Z(E)`, then `s` fixes some
`z*x` with `z ∈ Z(E)`. -/
public theorem centralizer_lift_of_odd_center
    {G : Type u} [Group G] [Finite G]
    (E : Subgroup G) (s : G)
    (hsE : Subgroup.zpowers s ≤ Subgroup.normalizer (E : Set G))
    (hs2 : s * s = 1)
    (hZodd : Odd (Nat.card ((Subgroup.center E).map E.subtype)))
    {x : E}
    (hxfix : s * (x : G) * s⁻¹ * (x : G)⁻¹ ∈
      (Subgroup.center E).map E.subtype) :
    ∃ z : (Subgroup.center E).map E.subtype,
      s * ((z : G) * (x : G)) * s⁻¹ = (z : G) * (x : G) := by
  classical
  by_cases hs1 : s = 1
  · refine ⟨1, ?_⟩
    simp [hs1]
  let A : Subgroup G := Subgroup.zpowers s
  let Z : Subgroup G := (Subgroup.center E).map E.subtype
  have hmap (a : G) (ha : a ∈ A) : ∀ y : G, y ∈ Z → a * y * a⁻¹ ∈ Z := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨c, hc, rfl⟩
    have haE : a ∈ Subgroup.normalizer (E : Set G) := hsE ha
    have hconj_mem : a * (c : G) * a⁻¹ ∈ E :=
      ((Subgroup.mem_normalizer_iff.mp haE) (c : G)).mp (c : E).2
    have hconj_center : (⟨a * (c : G) * a⁻¹, hconj_mem⟩ : E) ∈
        Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro e
      have hainv : a⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
        (Subgroup.normalizer (E : Set G)).inv_mem haE
      have hback : a⁻¹ * (e : G) * a ∈ E := by
        have h := ((Subgroup.mem_normalizer_iff.mp hainv) (e : G)).mp e.property
        simpa using h
      have hc_comm : (c : G) * (a⁻¹ * (e : G) * a) =
          (a⁻¹ * (e : G) * a) * (c : G) := by
        have h := Subgroup.mem_center_iff.mp hc
          (⟨a⁻¹ * (e : G) * a, hback⟩ : E)
        exact (congrArg Subtype.val h).symm
      apply Subtype.ext
      change (e : G) * (a * (c : G) * a⁻¹) =
        (a * (c : G) * a⁻¹) * (e : G)
      calc
        (e : G) * (a * (c : G) * a⁻¹) =
            a * ((a⁻¹ * (e : G) * a) * (c : G)) * a⁻¹ := by group
        _ = a * ((c : G) * (a⁻¹ * (e : G) * a)) * a⁻¹ := by
          rw [← hc_comm]
        _ = (a * (c : G) * a⁻¹) * (e : G) := by group
    exact Subgroup.mem_map.mpr
      ⟨⟨a * (c : G) * a⁻¹, hconj_mem⟩, hconj_center, rfl⟩
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hmap a ha y hy
    · intro hy
      have hainvA : a⁻¹ ∈ A := A.inv_mem ha
      have hback := hmap a⁻¹ hainvA (a * y * a⁻¹) hy
      change a⁻¹ * (a * y * a⁻¹) * (a⁻¹)⁻¹ ∈ Z at hback
      simpa [mul_assoc] using hback
  let : MulDistribMulAction A Z :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
  let : MulDistribMulAction (↑A) (↑Z) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
  let : CommGroup Z := by
    dsimp [Z]
    infer_instance
  have hAcard : Nat.card A = 2 := by
    dsimp [A]
    have hord : orderOf s = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using hs2) hs1
    rw [Nat.card_zpowers, hord]
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Z) := by
    rw [hAcard]
    exact hZodd.coprime_two_right.symm
  have hdefect (a : A) : (x : G)⁻¹ * (a : G) * (x : G) * (a : G)⁻¹ ∈ Z := by
    rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨k, hk⟩
    rcases zpow_eq_one_or_self_of_sq_eq_one_local hs2 k with h1 | hs
    · have ha : (a : G) = 1 := by
        simpa [hk] using h1
      rw [ha]
      simp
    · have ha : (a : G) = s := by
        simpa [hk] using hs
      rw [ha]
      have hrewrite : (x : G)⁻¹ * s * (x : G) * s⁻¹ =
          (x : G)⁻¹ * (s * (x : G) * s⁻¹ * (x : G)⁻¹) * (x : G) := by group
      rw [hrewrite]
      obtain ⟨d0, hd0, hd0val⟩ := hxfix
      have hd0center : (d0 : E) ∈ Subgroup.center E := hd0
      have hfix : (x : G)⁻¹ * (d0 : G) * x = (d0 : G) := by
        have h := Subgroup.mem_center_iff.mp hd0center x
        have hd : (d0 : G) * (x : G) = (x : G) * (d0 : G) :=
          by simpa using (congrArg Subtype.val h).symm
        calc
          (x : G)⁻¹ * (d0 : G) * x = (x : G)⁻¹ * ((d0 : G) * (x : G)) := by group
          _ = (x : G)⁻¹ * ((x : G) * (d0 : G)) := by rw [hd]
          _ = d0 := by group
      rw [← hd0val]
      rw [Subgroup.mem_map]
      refine ⟨d0, hd0, ?_⟩
      simp [hfix]
  let cocycle : A → Z := fun a =>
    ⟨(x : G)⁻¹ * (a : G) * (x : G) * (a : G)⁻¹, hdefect a⟩
  have hcocycle : @IsCocycle₁ (↑A) (↑Z) _ _
      (Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ) cocycle := by
    intro a b
    apply Subtype.ext
    let : MulDistribMulAction (↑A) (↑Z) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
    change (x : G)⁻¹ * (a * b : G) * (x : G) * (a * b : G)⁻¹ =
      ((x : G)⁻¹ * (a : G) * (x : G) * (a : G)⁻¹) *
        (a * ((x : G)⁻¹ * (b : G) * (x : G) * (b : G)⁻¹) * a⁻¹)
    simp only [Subgroup.coe_inv]
    group
  obtain ⟨z, hz⟩ :=
    @exists_coboundary_of_cocycle_of_coprime_card (↑A) (↑Z) _ _ _ _
      (Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ)
      cocycle hcocycle hcop
  let sA : A := ⟨s, Subgroup.mem_zpowers s⟩
  let defect : G := (x : G)⁻¹ * s * (x : G) * s⁻¹
  have hcs : defect = ((sA • z : Z) : G)⁻¹ * (z : G) := by
    let : MulDistribMulAction (↑A) (↑Z) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
    have h := congrArg Subtype.val (hz sA)
    change (x : G)⁻¹ * s * (x : G) * s⁻¹ =
      ((sA • z : Z) : G)⁻¹ * (z : G) at h
    simpa [defect, cocycle, sA] using h
  have hzsmul : ((sA • z : Z) : G) = s * (z : G) * s⁻¹ := by
    let : MulDistribMulAction (↑A) (↑Z) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer A Z hAZ
    change s * (z : G) * s⁻¹ = s * (z : G) * s⁻¹
    rfl
  obtain ⟨d0, hd0, hd0val⟩ := hxfix
  have hd0center : (d0 : E) ∈ Subgroup.center E := hd0
  have hfix : (x : G)⁻¹ * (d0 : G) * x = (d0 : G) := by
    have h := Subgroup.mem_center_iff.mp hd0center x
    have hd : (d0 : G) * (x : G) = (x : G) * (d0 : G) :=
      by simpa using (congrArg Subtype.val h).symm
    calc
      (x : G)⁻¹ * (d0 : G) * x = (x : G)⁻¹ * ((d0 : G) * (x : G)) := by group
      _ = (x : G)⁻¹ * ((x : G) * (d0 : G)) := by rw [hd]
      _ = d0 := by group
  have ha_eq : defect = (d0 : G) := by
    dsimp [defect]
    calc
      (x : G)⁻¹ * s * (x : G) * s⁻¹ =
          (x : G)⁻¹ * (s * (x : G) * s⁻¹) := by group
      _ = (x : G)⁻¹ * ((d0 : G) * (x : G)) := by
        congr 1
        calc
          s * (x : G) * s⁻¹ =
              s * (x : G) * s⁻¹ * (x : G)⁻¹ * (x : G) := by group
          _ = (d0 : G) * (x : G) := by
            exact congrArg (fun y : G => y * (x : G)) hd0val.symm
      _ = (d0 : G) := by
        calc
          (x : G)⁻¹ * ((d0 : G) * (x : G)) =
              (x : G)⁻¹ * (d0 : G) * (x : G) := by group
          _ = (d0 : G) := hfix
  have hzs : s * (z : G) * s⁻¹ = (z : G) * defect⁻¹ := by
    have h1 : (s * (z : G) * s⁻¹) * defect = (z : G) := by
      rw [hcs, hzsmul]
      group
    calc
      s * (z : G) * s⁻¹ = (s * (z : G) * s⁻¹) * 1 := by simp
      _ = (s * (z : G) * s⁻¹) * (defect * defect⁻¹) := by group
      _ = ((s * (z : G) * s⁻¹) * defect) * defect⁻¹ := by group
      _ = (z : G) * defect⁻¹ := by rw [h1]
  have hxs : s * (x : G) * s⁻¹ = defect * (x : G) := by
    calc
      s * (x : G) * s⁻¹ =
          s * (x : G) * s⁻¹ * (x : G)⁻¹ * (x : G) := by group
      _ = (d0 : G) * (x : G) := by
        exact congrArg (fun y : G => y * (x : G)) hd0val.symm
      _ = defect * (x : G) := by
        exact congrArg (fun y : G => y * (x : G)) ha_eq.symm
  refine ⟨z, ?_⟩
  calc
    s * ((z : G) * (x : G)) * s⁻¹ =
        (s * (z : G) * s⁻¹) * (s * (x : G) * s⁻¹) := by group
    _ = ((z : G) * defect⁻¹) * (defect * (x : G)) := by rw [hzs, hxs]
    _ = (z : G) * (x : G) := by group

end CFSG.GorensteinWalter
