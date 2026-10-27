module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Lemma (a)
-/

public theorem sq_surjective_of_odd_card
    {X : Type*} [Group X] [Finite X] (hXodd : Odd (Nat.card X)) :
    Function.Surjective (fun x : X => x ^ 2) := by
  intro x
  have hxord_dvd : orderOf x ∣ Nat.card X := orderOf_dvd_natCard x
  have hxord_odd : Odd (orderOf x) := hXodd.of_dvd_nat hxord_dvd
  have hxord_coprime : Nat.Coprime 2 (orderOf x) := by
    simpa using hxord_odd.coprime_two_left
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := x) (n := 2) hxord_coprime
  refine ⟨x ^ m, ?_⟩
  calc
    (x ^ m) ^ 2 = x ^ (m * 2) := by rw [pow_mul]
    _ = x ^ (2 * m) := by rw [Nat.mul_comm]
    _ = (x ^ 2) ^ m := by rw [pow_mul]
    _ = x := hm

private theorem sq_injective_of_odd_card
    {X : Type*} [Group X] [Finite X] (hXodd : Odd (Nat.card X)) :
    Function.Injective (fun x : X => x ^ 2) := by
  classical
  exact Finite.injective_iff_surjective.2 (sq_surjective_of_odd_card hXodd)

private theorem rightConjugateElem_mul {M : Type*} [Group M] (x y t : M) :
    rightConjugateElem (x * y) t =
      rightConjugateElem x t * rightConjugateElem y t := by
  simp [rightConjugateElem, mul_assoc]

private theorem rightConjugateElem_inv {M : Type*} [Group M] (x t : M) :
    rightConjugateElem x⁻¹ t = (rightConjugateElem x t)⁻¹ := by
  simp [rightConjugateElem, mul_assoc]

private theorem rightConjugateElem_mem_of_mem_normalizer
    {M : Type*} [Group M] {t x : M} {X : Subgroup M}
    (hXnorm : t ∈ Subgroup.normalizer (X : Set M)) (hx : x ∈ X) :
    rightConjugateElem x t ∈ X := by
  have htinv_norm : t⁻¹ ∈ Subgroup.normalizer (X : Set M) :=
    (Subgroup.normalizer (X : Set M)).inv_mem hXnorm
  simpa [rightConjugateElem] using
    (Subgroup.mem_normalizer_iff.mp htinv_norm x).1 hx

private theorem rightConjugateElem_eq_self_of_mem_centralizer
    {M : Type*} [Group M] {t x : M} (ht : IsInvolution t)
    (hx : x ∈ Subgroup.centralizer ({t} : Set M)) :
    rightConjugateElem x t = x := by
  change ∀ y ∈ ({t} : Set M), y * x = x * y at hx
  have hcomm : t * x = x * t := hx t (by simp)
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  calc
    rightConjugateElem x t = t * x * t := by
      rw [rightConjugateElem, ht.inv_eq_self]
    _ = x * (t * t) := by rw [hcomm, mul_assoc]
    _ = x := by simp [htt]

private theorem mem_centralizer_of_rightConjugateElem_eq_self
    {M : Type*} [Group M] {t x : M} (ht : IsInvolution t)
    (hx : rightConjugateElem x t = x) :
    x ∈ Subgroup.centralizer ({t} : Set M) := by
  change ∀ y ∈ ({t} : Set M), y * x = x * y
  intro y hy
  rw [Set.mem_singleton_iff.mp hy]
  have htinv : t⁻¹ = t := ht.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have htx : t * x * t = x := by
    simpa [rightConjugateElem, htinv] using hx
  calc
    t * x = t * x * 1 := by simp
    _ = t * x * (t * t) := by rw [htt]
    _ = (t * x * t) * t := by simp [mul_assoc]
    _ = x * t := by rw [htx]

private theorem rightConjugateElem_inv_mul_self_eq_sq_of_left_decomp
    {M : Type*} [Group M] {t y z : M} (ht : IsInvolution t)
    (hy : y ∈ Subgroup.centralizer ({t} : Set M))
    (hz : rightConjugateElem z t = z⁻¹) :
    (rightConjugateElem (y * z) t)⁻¹ * (y * z) = z ^ 2 := by
  have hyfix : rightConjugateElem y t = y :=
    rightConjugateElem_eq_self_of_mem_centralizer ht hy
  calc
    (rightConjugateElem (y * z) t)⁻¹ * (y * z) =
        (rightConjugateElem y t * rightConjugateElem z t)⁻¹ * (y * z) := by
      rw [rightConjugateElem_mul]
    _ = (y * z⁻¹)⁻¹ * (y * z) := by rw [hyfix, hz]
    _ = z ^ 2 := by simp [pow_two, mul_assoc]

private theorem mul_inv_rightConjugateElem_eq_sq_of_right_decomp
    {M : Type*} [Group M] {t y z : M} (ht : IsInvolution t)
    (hy : y ∈ Subgroup.centralizer ({t} : Set M))
    (hz : rightConjugateElem z t = z⁻¹) :
    (z * y) * (rightConjugateElem (z * y) t)⁻¹ = z ^ 2 := by
  have hyfix : rightConjugateElem y t = y :=
    rightConjugateElem_eq_self_of_mem_centralizer ht hy
  calc
    (z * y) * (rightConjugateElem (z * y) t)⁻¹ =
        (z * y) * (rightConjugateElem z t * rightConjugateElem y t)⁻¹ := by
      rw [rightConjugateElem_mul]
    _ = (z * y) * (z⁻¹ * y)⁻¹ := by rw [hyfix, hz]
    _ = z ^ 2 := by simp [pow_two, mul_assoc]

private theorem rightConjugateElem_anti_fixed_of_sq_eq_inv_mul_self
    {M : Type*} [Group M] [Finite M] {t x z : M} {X : Subgroup M}
    (ht : IsInvolution t) (hXodd : Odd (Nat.card X))
    (hXnorm : t ∈ Subgroup.normalizer (X : Set M))
    (hz : z ∈ X)
    (hzsq : z ^ 2 = (rightConjugateElem x t)⁻¹ * x) :
    rightConjugateElem z t = z⁻¹ := by
  have hφzX : rightConjugateElem z t ∈ X :=
    rightConjugateElem_mem_of_mem_normalizer hXnorm hz
  have hsq :
      (⟨rightConjugateElem z t, hφzX⟩ : X) ^ 2 =
        (⟨z⁻¹, X.inv_mem hz⟩ : X) ^ 2 := by
    apply Subtype.ext
    change (rightConjugateElem z t) ^ 2 = (z⁻¹) ^ 2
    calc
      (rightConjugateElem z t) ^ 2 = rightConjugateElem (z ^ 2) t := by
        rw [pow_two, pow_two, rightConjugateElem_mul]
      _ = rightConjugateElem ((rightConjugateElem x t)⁻¹ * x) t := by
        rw [hzsq]
      _ = x⁻¹ * rightConjugateElem x t := by
        rw [rightConjugateElem_mul, rightConjugateElem_inv]
        simp [rightConjugateElem_involutive_of_isInvolution ht x]
      _ = ((rightConjugateElem x t)⁻¹ * x)⁻¹ := by simp
      _ = (z ^ 2)⁻¹ := by rw [hzsq]
      _ = (z⁻¹) ^ 2 := by simp [pow_two]
  exact congrArg Subtype.val ((sq_injective_of_odd_card hXodd) hsq)

private theorem rightConjugateElem_anti_fixed_of_sq_eq_mul_inv
    {M : Type*} [Group M] [Finite M] {t x z : M} {X : Subgroup M}
    (ht : IsInvolution t) (hXodd : Odd (Nat.card X))
    (hXnorm : t ∈ Subgroup.normalizer (X : Set M))
    (hz : z ∈ X)
    (hzsq : z ^ 2 = x * (rightConjugateElem x t)⁻¹) :
    rightConjugateElem z t = z⁻¹ := by
  have hφzX : rightConjugateElem z t ∈ X :=
    rightConjugateElem_mem_of_mem_normalizer hXnorm hz
  have hsq :
      (⟨rightConjugateElem z t, hφzX⟩ : X) ^ 2 =
        (⟨z⁻¹, X.inv_mem hz⟩ : X) ^ 2 := by
    apply Subtype.ext
    change (rightConjugateElem z t) ^ 2 = (z⁻¹) ^ 2
    calc
      (rightConjugateElem z t) ^ 2 = rightConjugateElem (z ^ 2) t := by
        rw [pow_two, pow_two, rightConjugateElem_mul]
      _ = rightConjugateElem (x * (rightConjugateElem x t)⁻¹) t := by
        rw [hzsq]
      _ = rightConjugateElem x t * x⁻¹ := by
        rw [rightConjugateElem_mul, rightConjugateElem_inv]
        simp [rightConjugateElem_involutive_of_isInvolution ht x]
      _ = (x * (rightConjugateElem x t)⁻¹)⁻¹ := by simp
      _ = (z ^ 2)⁻¹ := by rw [hzsq]
      _ = (z⁻¹) ^ 2 := by simp [pow_two]
  exact congrArg Subtype.val ((sq_injective_of_odd_card hXodd) hsq)

private theorem left_fixed_factor_mem_centralizer
    {M : Type*} [Group M] {t x z : M}
    (ht : IsInvolution t)
    (hzanti : rightConjugateElem z t = z⁻¹)
    (hzsq : z ^ 2 = (rightConjugateElem x t)⁻¹ * x) :
    x * z⁻¹ ∈ Subgroup.centralizer ({t} : Set M) := by
  have hx_eq : x = rightConjugateElem x t * z ^ 2 := by
    calc
      x = rightConjugateElem x t * ((rightConjugateElem x t)⁻¹ * x) := by
        simp
      _ = rightConjugateElem x t * z ^ 2 := by rw [← hzsq]
  apply mem_centralizer_of_rightConjugateElem_eq_self ht
  calc
    rightConjugateElem (x * z⁻¹) t =
        rightConjugateElem x t * (rightConjugateElem z t)⁻¹ := by
      rw [rightConjugateElem_mul, rightConjugateElem_inv]
    _ = rightConjugateElem x t * z := by rw [hzanti]; simp
    _ = rightConjugateElem x t * (z ^ 2 * z⁻¹) := by simp [pow_two, mul_assoc]
    _ = (rightConjugateElem x t * z ^ 2) * z⁻¹ := by simp [mul_assoc]
    _ = x * z⁻¹ := by rw [← hx_eq]

private theorem right_fixed_factor_mem_centralizer
    {M : Type*} [Group M] {t x z : M}
    (ht : IsInvolution t)
    (hzanti : rightConjugateElem z t = z⁻¹)
    (hzsq : z ^ 2 = x * (rightConjugateElem x t)⁻¹) :
    z⁻¹ * x ∈ Subgroup.centralizer ({t} : Set M) := by
  have hx_eq : x = z ^ 2 * rightConjugateElem x t := by
    calc
      x = (x * (rightConjugateElem x t)⁻¹) * rightConjugateElem x t := by
        simp [mul_assoc]
      _ = z ^ 2 * rightConjugateElem x t := by rw [← hzsq]
  apply mem_centralizer_of_rightConjugateElem_eq_self ht
  calc
    rightConjugateElem (z⁻¹ * x) t =
        (rightConjugateElem z t)⁻¹ * rightConjugateElem x t := by
      rw [rightConjugateElem_mul, rightConjugateElem_inv]
    _ = z * rightConjugateElem x t := by rw [hzanti]; simp
    _ = (z⁻¹ * z ^ 2) * rightConjugateElem x t := by simp [pow_two]
    _ = z⁻¹ * (z ^ 2 * rightConjugateElem x t) := by simp [mul_assoc]
    _ = z⁻¹ * x := by rw [← hx_eq]

public theorem lemma_a
    {M : Type*} [Group M] [Finite M]
    (t : M) (X : Subgroup M)
    (ht : IsInvolution t)
    (hXodd : Odd (Nat.card X))
    (hXnorm : t ∈ Subgroup.normalizer (X : Set M)) :
    let Y : Subgroup M := X ⊓ Subgroup.centralizer ({t} : Set M)
    let Z : Set M := {x : M | x ∈ X ∧ rightConjugateElem x t = x⁻¹}
    (Set.BijOn (fun p : Y × Z => (p.1 : M) * (p.2 : M)) Set.univ (X : Set M)) ∧
      Set.BijOn (fun p : Y × Z => (p.2 : M) * (p.1 : M)) Set.univ (X : Set M) ∧
        Nat.card X = Nat.card Y * Nat.card Z := by
  classical
  let Y : Subgroup M := X ⊓ Subgroup.centralizer ({t} : Set M)
  let Z : Set M := {x : M | x ∈ X ∧ rightConjugateElem x t = x⁻¹}
  have hleft :
      Set.BijOn (fun p : Y × Z => (p.1 : M) * (p.2 : M)) Set.univ (X : Set M) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p _hp
      exact X.mul_mem p.1.property.1 p.2.property.1
    · intro p _hp q _hq hpq
      rcases p with ⟨py, pz⟩
      rcases q with ⟨qy, qz⟩
      change (py : M) * (pz : M) = (qy : M) * (qz : M) at hpq
      have hzsq :
          (pz : M) ^ 2 = (qz : M) ^ 2 := by
        have hp_formula :
            (rightConjugateElem ((py : M) * (pz : M)) t)⁻¹ *
                ((py : M) * (pz : M)) = (pz : M) ^ 2 :=
          rightConjugateElem_inv_mul_self_eq_sq_of_left_decomp ht
            py.property.2 pz.property.2
        have hq_formula :
            (rightConjugateElem ((qy : M) * (qz : M)) t)⁻¹ *
                ((qy : M) * (qz : M)) = (qz : M) ^ 2 :=
          rightConjugateElem_inv_mul_self_eq_sq_of_left_decomp ht
            qy.property.2 qz.property.2
        calc
          (pz : M) ^ 2 =
              (rightConjugateElem ((py : M) * (pz : M)) t)⁻¹ *
                ((py : M) * (pz : M)) := hp_formula.symm
          _ = (rightConjugateElem ((qy : M) * (qz : M)) t)⁻¹ *
                ((qy : M) * (qz : M)) := by rw [hpq]
          _ = (qz : M) ^ 2 := hq_formula
      have hz_eq : pz = qz := by
        have hsq_sub :
            (⟨(pz : M), pz.property.1⟩ : X) ^ 2 =
              (⟨(qz : M), qz.property.1⟩ : X) ^ 2 := by
          apply Subtype.ext
          exact hzsq
        have hXeq :
            (⟨(pz : M), pz.property.1⟩ : X) =
              (⟨(qz : M), qz.property.1⟩ : X) :=
          (sq_injective_of_odd_card hXodd) hsq_sub
        have hM : (pz : M) = (qz : M) :=
          congrArg (fun x : X => (x : M)) hXeq
        exact Subtype.ext hM
      have hzM : (pz : M) = (qz : M) := congrArg Subtype.val hz_eq
      have hprod : (py : M) * (pz : M) = (qy : M) * (pz : M) := by
        simpa [hzM.symm] using hpq
      have hyM : (py : M) = (qy : M) := by
        calc
          (py : M) = (py : M) * (pz : M) * (pz : M)⁻¹ := by simp [mul_assoc]
          _ = (qy : M) * (pz : M) * (pz : M)⁻¹ := by rw [hprod]
          _ = (qy : M) := by simp [mul_assoc]
      exact Prod.ext (Subtype.ext hyM) hz_eq
    · intro x hxX
      let a : M := (rightConjugateElem x t)⁻¹ * x
      have hφxX : rightConjugateElem x t ∈ X :=
        rightConjugateElem_mem_of_mem_normalizer hXnorm hxX
      have haX : a ∈ X := X.mul_mem (X.inv_mem hφxX) hxX
      obtain ⟨zX, hzXsq⟩ :=
        sq_surjective_of_odd_card (X := X) hXodd ⟨a, haX⟩
      let z : M := zX
      have hzX : z ∈ X := zX.property
      have hzsq : z ^ 2 = a := by
        exact congrArg Subtype.val hzXsq
      have hzanti : rightConjugateElem z t = z⁻¹ :=
        rightConjugateElem_anti_fixed_of_sq_eq_inv_mul_self ht hXodd hXnorm hzX hzsq
      let y : M := x * z⁻¹
      have hyX : y ∈ X := X.mul_mem hxX (X.inv_mem hzX)
      have hyC : y ∈ Subgroup.centralizer ({t} : Set M) :=
        left_fixed_factor_mem_centralizer ht hzanti hzsq
      refine ⟨(⟨⟨y, ⟨hyX, hyC⟩⟩, ⟨z, ⟨hzX, hzanti⟩⟩⟩ : Y × Z), by simp, ?_⟩
      dsimp [y, z]
      simp [mul_assoc]
  have hright :
      Set.BijOn (fun p : Y × Z => (p.2 : M) * (p.1 : M)) Set.univ (X : Set M) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p _hp
      exact X.mul_mem p.2.property.1 p.1.property.1
    · intro p _hp q _hq hpq
      rcases p with ⟨py, pz⟩
      rcases q with ⟨qy, qz⟩
      change (pz : M) * (py : M) = (qz : M) * (qy : M) at hpq
      have hzsq :
          (pz : M) ^ 2 = (qz : M) ^ 2 := by
        have hp_formula :
            ((pz : M) * (py : M)) *
                (rightConjugateElem ((pz : M) * (py : M)) t)⁻¹ = (pz : M) ^ 2 :=
          mul_inv_rightConjugateElem_eq_sq_of_right_decomp ht
            py.property.2 pz.property.2
        have hq_formula :
            ((qz : M) * (qy : M)) *
                (rightConjugateElem ((qz : M) * (qy : M)) t)⁻¹ = (qz : M) ^ 2 :=
          mul_inv_rightConjugateElem_eq_sq_of_right_decomp ht
            qy.property.2 qz.property.2
        calc
          (pz : M) ^ 2 =
              ((pz : M) * (py : M)) *
                (rightConjugateElem ((pz : M) * (py : M)) t)⁻¹ := hp_formula.symm
          _ = ((qz : M) * (qy : M)) *
                (rightConjugateElem ((qz : M) * (qy : M)) t)⁻¹ := by rw [hpq]
          _ = (qz : M) ^ 2 := hq_formula
      have hz_eq : pz = qz := by
        have hsq_sub :
            (⟨(pz : M), pz.property.1⟩ : X) ^ 2 =
              (⟨(qz : M), qz.property.1⟩ : X) ^ 2 := by
          apply Subtype.ext
          exact hzsq
        have hXeq :
            (⟨(pz : M), pz.property.1⟩ : X) =
              (⟨(qz : M), qz.property.1⟩ : X) :=
          (sq_injective_of_odd_card hXodd) hsq_sub
        have hM : (pz : M) = (qz : M) :=
          congrArg (fun x : X => (x : M)) hXeq
        exact Subtype.ext hM
      have hzM : (pz : M) = (qz : M) := congrArg Subtype.val hz_eq
      have hprod : (pz : M) * (py : M) = (pz : M) * (qy : M) := by
        simpa [hzM.symm] using hpq
      have hyM : (py : M) = (qy : M) := by
        calc
          (py : M) = (pz : M)⁻¹ * ((pz : M) * (py : M)) := by simp
          _ = (pz : M)⁻¹ * ((pz : M) * (qy : M)) := by rw [hprod]
          _ = (qy : M) := by simp
      exact Prod.ext (Subtype.ext hyM) hz_eq
    · intro x hxX
      let a : M := x * (rightConjugateElem x t)⁻¹
      have hφxX : rightConjugateElem x t ∈ X :=
        rightConjugateElem_mem_of_mem_normalizer hXnorm hxX
      have haX : a ∈ X := X.mul_mem hxX (X.inv_mem hφxX)
      obtain ⟨zX, hzXsq⟩ :=
        sq_surjective_of_odd_card (X := X) hXodd ⟨a, haX⟩
      let z : M := zX
      have hzX : z ∈ X := zX.property
      have hzsq : z ^ 2 = a := by
        exact congrArg Subtype.val hzXsq
      have hzanti : rightConjugateElem z t = z⁻¹ :=
        rightConjugateElem_anti_fixed_of_sq_eq_mul_inv ht hXodd hXnorm hzX hzsq
      let y : M := z⁻¹ * x
      have hyX : y ∈ X := X.mul_mem (X.inv_mem hzX) hxX
      have hyC : y ∈ Subgroup.centralizer ({t} : Set M) :=
        right_fixed_factor_mem_centralizer ht hzanti hzsq
      refine ⟨(⟨⟨y, ⟨hyX, hyC⟩⟩, ⟨z, ⟨hzX, hzanti⟩⟩⟩ : Y × Z), by simp, ?_⟩
      dsimp [y, z]
      simp
  have hcard : Nat.card X = Nat.card Y * Nat.card Z := by
    calc
      Nat.card X = (X : Set M).ncard := Nat.card_coe_set_eq _
      _ = Nat.card Y * Nat.card Z := by
        simpa [Nat.card_prod] using hleft.ncard_eq.symm
  exact ⟨hleft, hright, hcard⟩

end PFchapter1section1
end CFSG.BenderSuzuki
