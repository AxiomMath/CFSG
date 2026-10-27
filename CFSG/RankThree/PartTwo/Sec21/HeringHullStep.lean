module

public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringHull

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem trivial_mod_theta_of_llRel {Z K : Subgroup G} {x : G} (hZK : llRel Z K)
    (hK : K ≤ Subgroup.centralizer ({x} : Set G)) (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) :
    ∀ z ∈ Z, z⁻¹ * (x * z * x⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) Z := by
  intro z hz
  have hZK' : Z = inSubgroup perfectResidual (Z ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore 3) Z :=
    hZK
  have hJZ : inSubgroup perfectResidual (Z ⊓ K) ≤ Z ⊓ K := Subgroup.map_subtype_le _
  have hJθ : inSubgroup perfectResidual (Z ⊓ K) ≤
      Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) Z : Set G) :=
    (hJZ.trans inf_le_left).trans (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta Z)
  have hz2 : z ∈ (inSubgroup perfectResidual (Z ⊓ K) : Set G) *
      (inSubgroup (aschbacherSolvableCore 3) Z : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hJθ, ← hZK']
    exact hz
  obtain ⟨j, hj, t, ht, hjt⟩ := Set.mem_mul.mp hz2
  subst hjt
  have ht' : t ∈ inSubgroup (aschbacherSolvableCore 3) Z := ht
  have hjc : j * x = x * j := Subgroup.mem_centralizer_singleton_iff.mp (hK (hJZ hj).2)
  have hjx : x * j * x⁻¹ = j := by
    rw [← hjc, mul_inv_cancel_right]
  have hxθ : x ∈ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) Z : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.normalizer_le_normalizer_theta Z hxZ
  have hxt : x * t * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Z :=
    (Subgroup.mem_normalizer_iff.mp hxθ t).mp ht
  have hconj : (j * t)⁻¹ * (x * (j * t) * x⁻¹) = t⁻¹ * (x * t * x⁻¹) := by
    calc (j * t)⁻¹ * (x * (j * t) * x⁻¹)
        = t⁻¹ * (j⁻¹ * (x * j * x⁻¹)) * (x * t * x⁻¹) := by group
      _ = t⁻¹ * (x * t * x⁻¹) := by rw [hjx]; group
  rw [hconj]
  exact (inSubgroup (aschbacherSolvableCore 3) Z).mul_mem
    ((inSubgroup (aschbacherSolvableCore 3) Z).inv_mem ht') hxt

theorem le_centralizer_of_isQuasisimple {P Z : Subgroup G} {x : G} (hP : IsQuasisimple P)
    (hPZ : P ≤ Z) (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (htriv : ∀ z ∈ Z, z⁻¹ * (x * z * x⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) Z) :
    P ≤ Subgroup.centralizer ({x} : Set G) := by
  set θZ := inSubgroup (aschbacherSolvableCore 3) Z
  have hPN : P ≤ Subgroup.normalizer (θZ : Set G) :=
    hPZ.trans (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta Z)
  haveI : (θZ.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have hwP : ∀ p : P, (p : G)⁻¹ * (x * p * x⁻¹) ∈ P := fun p =>
    P.mul_mem (P.inv_mem p.2) ((Subgroup.mem_normalizer_iff.mp hxP (p : G)).mp p.2)
  have hcases := CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hP
    (θZ.subgroupOf P)
  rcases hcases with hc | htop
  ·
    haveI : Group.IsPerfect P := hP.1
    have hcenG : ∀ a b : P, Commute ((a : G)⁻¹ * (x * a * x⁻¹)) (b : G) := by
      intro a b
      have hmem : (⟨(a : G)⁻¹ * (x * a * x⁻¹), hwP a⟩ : P) ∈ θZ.subgroupOf P :=
        Subgroup.mem_subgroupOf.mpr (htriv a (hPZ a.2))
      have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp (hc hmem) b)
      exact h.symm
    have key : ∀ a b : G, Commute (a⁻¹ * (x * a * x⁻¹)) b →
        (a * b)⁻¹ * (x * (a * b) * x⁻¹) = a⁻¹ * (x * a * x⁻¹) * (b⁻¹ * (x * b * x⁻¹)) := by
      intro a b hcb
      calc (a * b)⁻¹ * (x * (a * b) * x⁻¹)
          = b⁻¹ * (a⁻¹ * (x * a * x⁻¹)) * (x * b * x⁻¹) := by group
        _ = a⁻¹ * (x * a * x⁻¹) * b⁻¹ * (x * b * x⁻¹) := by rw [hcb.inv_right.eq]
        _ = a⁻¹ * (x * a * x⁻¹) * (b⁻¹ * (x * b * x⁻¹)) := mul_assoc _ _ _
    obtain ⟨Fp, hFp⟩ : ∃ f : P →* P, ∀ a : P, (f a : G) = (a : G)⁻¹ * (x * a * x⁻¹) :=
      ⟨{ toFun := fun a => ⟨(a : G)⁻¹ * (x * a * x⁻¹), hwP a⟩
         map_one' := Subtype.ext (by simp)
         map_mul' := fun a b => Subtype.ext (key a b (hcenG a b)) }, fun _ => rfl⟩
    have hcomm_img : ∀ a b : P, Commute (Fp a) (Fp b) := by
      intro a b
      have h := hcenG a (Fp b)
      rw [hFp b] at h
      show Fp a * Fp b = Fp b * Fp a
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hFp]
      exact h
    have hFcomm : ∀ a b : P, Fp ⁅a, b⁆ = 1 := by
      intro a b
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hcomm_img a b
    have hfix : ∀ g : P, Fp g = 1 → x * (g : G) = (g : G) * x := by
      intro g hg
      have h1 : (g : G)⁻¹ * (x * g * x⁻¹) = 1 := by
        have h := congrArg Subtype.val hg
        rwa [hFp, Subgroup.coe_one] at h
      exact mul_inv_eq_iff_eq_mul.mp (inv_mul_eq_one.mp h1).symm
    intro p hp
    have hcl : commutator P ≤ (Subgroup.centralizer ({x} : Set G)).subgroupOf P := by
      refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      exact (hfix _ (hFcomm g₁ g₂)).symm
    have hpP : (⟨p, hp⟩ : P) ∈ commutator P := Group.IsPerfect.mem_commutator
    exact Subgroup.mem_subgroupOf.mp (hcl hpP)
  ·
    exfalso
    obtain ⟨-, hsimp, a₀, b₀, hab⟩ := hP
    have hθsolv : Group.IsSolvable θZ :=
      (CFSG.RankThree.PartTwo.Sec6.theta_solvable_and_not_dvd Z).1
    have hPθ : P ≤ θZ := by
      intro p hp
      have hmem : (⟨p, hp⟩ : P) ∈ θZ.subgroupOf P := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    haveI : Group.IsSolvable θZ := hθsolv
    haveI : Group.IsSolvable P :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPθ)
        (Subgroup.inclusion_injective hPθ)
    haveI := hsimp
    have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr
      (inferInstance : Group.IsSolvable (↥P ⧸ Subgroup.center ↥P))
    exact hab (hcomm a₀ b₀)

end CFSG.RankThree.PartTwo.Sec21.HeringHull
