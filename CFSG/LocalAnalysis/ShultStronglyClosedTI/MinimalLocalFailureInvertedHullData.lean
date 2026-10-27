module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSimple

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def minimalLocalFailureInvertedSet (P : Subgroup G) (z : G) : Set G :=
  {x | x ∈ P ∧ rightConjugateElem x z = x⁻¹}

@[expose] def minimalLocalFailureInvertedOvergroup (P : Subgroup G) (z : G) : Subgroup G :=
  Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ⊔ Subgroup.zpowers z

@[expose] def minimalLocalFailureInvertedHull (P : Subgroup G) (z : G) : Subgroup G :=
  let A := minimalLocalFailureInvertedOvergroup P z
  let zA : A := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  (involutionPointHull zA).map A.subtype

theorem invertedHull_inv_mem_set (P : Subgroup G) (z : G) {x : G}
    (hx : x ∈ minimalLocalFailureInvertedSet P z) :
    x⁻¹ ∈ minimalLocalFailureInvertedSet P z := by
  refine ⟨P.inv_mem hx.1, ?_⟩
  simpa only [rightConjugateElem, mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hx.2

theorem invertedHull_involution_normalizes_set (P : Subgroup G) (z : G)
    (hz : orderOf z = 2) :
    z ∈ Subgroup.normalizer (minimalLocalFailureInvertedSet P z) := by
  apply Subgroup.mem_set_normalizer_iff''.mpr
  intro x
  have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
  have hzsq : z * z = 1 := by simpa only [pow_two] using
    (orderOf_eq_prime_iff.mp hz).1
  constructor
  · intro hx
    change rightConjugateElem x z ∈ minimalLocalFailureInvertedSet P z
    rw [hx.2]
    exact invertedHull_inv_mem_set P z hx
  · intro hx
    have hh := invertedHull_inv_mem_set P z hx
    have hinv : (z⁻¹ * x * z)⁻¹ = x := by
      have hfixed := hx.2
      change z⁻¹ * (z⁻¹ * x * z) * z = (z⁻¹ * x * z)⁻¹ at hfixed
      have htwice : z⁻¹ * (z⁻¹ * x * z) * z = x := by
        rw [hzinv]
        calc
          z * (z * x * z) * z = (z * z) * x * (z * z) := by group
          _ = x := by rw [hzsq, one_mul, mul_one]
      exact hfixed.symm.trans htwice
    exact hinv ▸ hh

theorem invertedHull_overgroup_normalizes_set (P : Subgroup G) (z : G)
    (hz : orderOf z = 2) :
    minimalLocalFailureInvertedOvergroup P z ≤
      Subgroup.normalizer (minimalLocalFailureInvertedSet P z) := by
  exact sup_le (Subgroup.centralizer_le_normalizer _)
    (Subgroup.zpowers_le.mpr (invertedHull_involution_normalizes_set P z hz))

theorem invertedHull_centralizer_normal (P : Subgroup G) (z : G)
    (hz : orderOf z = 2) :
    ((Subgroup.centralizer (minimalLocalFailureInvertedSet P z)).subgroupOf
      (minimalLocalFailureInvertedOvergroup P z)).Normal := by
  let I := minimalLocalFailureInvertedSet P z
  have hnorm : Subgroup.normalizer I ≤
      Subgroup.normalizer (Subgroup.centralizer I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer I)).mp inferInstance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (le_sup_left : Subgroup.centralizer I ≤ minimalLocalFailureInvertedOvergroup P z)).mpr
      ((invertedHull_overgroup_normalizes_set P z hz).trans hnorm)

theorem invertedHull_involution_not_mem_centralizer [Finite G]
    (P : Subgroup G) (hPodd : Odd (Nat.card P)) (z : G)
    (hI : ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1) :
    z ∉ Subgroup.centralizer (minimalLocalFailureInvertedSet P z) := by
  intro hzM
  obtain ⟨x, hx, hxne⟩ := hI
  have hcomm := Subgroup.mem_centralizer_iff.mp hzM x hx
  have hfix : rightConjugateElem x z = x := by
    dsimp [rightConjugateElem]
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  have hself : x = x⁻¹ := hfix.symm.trans hx.2
  have hsq : x ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hself
  have horder : orderOf x = 2 := orderOf_eq_prime hsq hxne
  exact hPodd.ne_two_of_dvd_nat (P.orderOf_dvd_natCard hx.1) horder

theorem invertedHull_centralizer_index_two [Finite G]
    (P : Subgroup G) (hPodd : Odd (Nat.card P)) (z : G) (hz : orderOf z = 2)
    (hI : ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1) :
    ((Subgroup.centralizer (minimalLocalFailureInvertedSet P z)).subgroupOf
      (minimalLocalFailureInvertedOvergroup P z)).index = 2 := by
  let M := Subgroup.centralizer (minimalLocalFailureInvertedSet P z)
  let A := minimalLocalFailureInvertedOvergroup P z
  let MA := M.subgroupOf A
  let : MA.Normal := invertedHull_centralizer_normal P z hz
  let zA : A := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  have hgen : MA ⊔ Subgroup.zpowers zA = ⊤ := by
    apply Subgroup.map_injective (f := A.subtype) Subtype.val_injective
    change (M.subgroupOf A ⊔ Subgroup.zpowers zA).map A.subtype =
      (⊤ : Subgroup A).map A.subtype
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le
        (show M ≤ A from le_sup_left),
      MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.subtype_range]
    rfl
  have hzM := invertedHull_involution_not_mem_centralizer P hPodd z hI
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨zA, hzM, ?_⟩
  intro a
  have ha : a ∈ MA ⊔ Subgroup.zpowers zA := hgen ▸ Subgroup.mem_top a
  obtain ⟨m, hm, t, ht, hmt⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  have hzA : orderOf zA = 2 := (Subgroup.orderOf_coe zA).symm.trans hz
  rcases involution_zpowers_elements hzA ht with htone | htz
  · right
    rw [← hmt, htone, mul_one]
    exact hm
  · left
    rw [← hmt, htz, mul_assoc]
    have hzz : zA * zA = 1 := by simpa only [pow_two] using
      (orderOf_eq_prime_iff.mp hzA).1
    rw [hzz, mul_one]
    exact hm

theorem invertedHull_conjugates_invert_set (P : Subgroup G) (z : G)
    (hz : orderOf z = 2) (a : G) (ha : a ∈ minimalLocalFailureInvertedOvergroup P z)
    (x : G) (hx : x ∈ minimalLocalFailureInvertedSet P z) :
    rightConjugateElem x (rightConjugateElem z a) = x⁻¹ := by
  let y := rightConjugateElem x a⁻¹
  have hay : a⁻¹ ∈ Subgroup.normalizer (minimalLocalFailureInvertedSet P z) :=
    (invertedHull_overgroup_normalizes_set P z hz)
      ((minimalLocalFailureInvertedOvergroup P z).inv_mem ha)
  have hy : y ∈ minimalLocalFailureInvertedSet P z :=
    (Subgroup.mem_set_normalizer_iff''.mp hay x).mp hx
  calc
    rightConjugateElem x (rightConjugateElem z a) =
        a⁻¹ * rightConjugateElem y z * a := by dsimp [y, rightConjugateElem]; group
    _ = a⁻¹ * y⁻¹ * a := by rw [hy.2]
    _ = x⁻¹ := by dsimp [y, rightConjugateElem]; group

theorem invertedHull_overgroup_proper [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G) (hPodd : Odd (Nat.card P))
    (hI : ∃ x ∈ minimalLocalFailureInvertedSet P z, x ≠ 1) :
    minimalLocalFailureInvertedOvergroup P z ≠ ⊤ := by
  let M := Subgroup.centralizer (minimalLocalFailureInvertedSet P z)
  let A := minimalLocalFailureInvertedOvergroup P z
  have hzM : z ∉ M := invertedHull_involution_not_mem_centralizer P hPodd z hI
  have hnormal := invertedHull_centralizer_normal P z h.local_datum.distinguished_order
  have hindex := invertedHull_centralizer_index_two P hPodd z
    h.local_datum.distinguished_order hI
  intro htop
  change A = ⊤ at htop
  have hMnormal : M.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : M ≤ A)).mp
      hnormal |> fun hn => (Subgroup.normalizer_eq_top_iff.mp
        (top_le_iff.mp (htop ▸ hn)))
  let : M.Normal := hMnormal
  rcases minimalLocalFailure_normal_eq_bot_or_top h M with hbot | hMtop
  · have hrel : M.relIndex A = 2 := hindex
    rw [htop, Subgroup.relIndex_top_right, hbot, Subgroup.index_bot] at hrel
    exact local_point_ambient_card_ne_two h.local_datum hrel
  · exact hzM (hMtop ▸ Subgroup.mem_top z)

end CFSG.ShultStronglyClosedTI
