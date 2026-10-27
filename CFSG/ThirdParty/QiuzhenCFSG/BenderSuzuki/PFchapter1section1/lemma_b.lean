module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Lemma (b)
-/

private theorem lemmaB_rightConjugateElem_mul
    {M : Type*} [Group M] (x y t : M) :
    rightConjugateElem (x * y) t =
      rightConjugateElem x t * rightConjugateElem y t := by
  simp [rightConjugateElem, mul_assoc]

private theorem lemmaB_rightConjugateElem_inv
    {M : Type*} [Group M] (x t : M) :
    rightConjugateElem x⁻¹ t = (rightConjugateElem x t)⁻¹ := by
  simp [rightConjugateElem, mul_assoc]

private theorem lemmaB_rightConjugateElem_eq_self_of_mem_centralizer
    {M : Type*} [Group M] {t y : M} (ht : IsInvolution t)
    (hy : y ∈ Subgroup.centralizer ({t} : Set M)) :
    rightConjugateElem y t = y := by
  change ∀ x ∈ ({t} : Set M), x * y = y * x at hy
  have hcomm : t * y = y * t := hy t (by simp)
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  calc
    rightConjugateElem y t = t * y * t := by
      rw [rightConjugateElem, ht.inv_eq_self]
    _ = y * (t * t) := by rw [hcomm, mul_assoc]
    _ = y := by simp [htt]

private theorem lemmaB_rightConjugateElem_conj_anti_fixed
    {M : Type*} [Group M] {t y z : M}
    (ht : IsInvolution t)
    (hy : y ∈ Subgroup.centralizer ({t} : Set M))
    (hz : rightConjugateElem z t = z⁻¹) :
    rightConjugateElem (y * z * y⁻¹) t = (y * z * y⁻¹)⁻¹ := by
  have hyfix : rightConjugateElem y t = y :=
    lemmaB_rightConjugateElem_eq_self_of_mem_centralizer ht hy
  calc
    rightConjugateElem (y * z * y⁻¹) t =
        rightConjugateElem (y * z) t * rightConjugateElem y⁻¹ t := by
      rw [lemmaB_rightConjugateElem_mul]
    _ = (rightConjugateElem y t * rightConjugateElem z t) *
        (rightConjugateElem y t)⁻¹ := by
      rw [lemmaB_rightConjugateElem_mul, lemmaB_rightConjugateElem_inv]
    _ = (y * z * y⁻¹)⁻¹ := by
      rw [hyfix, hz]
      group

public theorem lemma_b
    {M : Type*} [Group M] [Finite M]
    (t : M) (X : Subgroup M)
    (ht : IsInvolution t)
    (hXodd : Odd (Nat.card X))
    (hXnorm : t ∈ Subgroup.normalizer (X : Set M)) :
    let Zsub : Subgroup X :=
      Subgroup.closure {x : X | rightConjugateElem (x : M) t = (x : M)⁻¹}
    Zsub.Normal := by
  classical
  let Y : Subgroup M := X ⊓ Subgroup.centralizer ({t} : Set M)
  let Z : Set M := {x : M | x ∈ X ∧ rightConjugateElem x t = x⁻¹}
  let Zset : Set X := {x : X | rightConjugateElem (x : M) t = (x : M)⁻¹}
  let Zsub : Subgroup X := Subgroup.closure Zset
  change Zsub.Normal
  obtain ⟨hleft, _hright, _hcard⟩ := lemma_a t X ht hXodd hXnorm
  have hY_conj :
      ∀ y : X, (y : M) ∈ Subgroup.centralizer ({t} : Set M) →
        ∀ n : X, n ∈ Zsub → y * n * y⁻¹ ∈ Zsub := by
    intro y hy n hn
    induction hn using Subgroup.closure_induction with
    | mem z hz =>
        apply Subgroup.subset_closure
        change rightConjugateElem ((y * z * y⁻¹ : X) : M) t =
          ((y * z * y⁻¹ : X) : M)⁻¹
        exact lemmaB_rightConjugateElem_conj_anti_fixed ht hy hz
    | one =>
        simp
    | mul a b _ha _hb ha_conj hb_conj =>
        have hmul : (y * a * y⁻¹) * (y * b * y⁻¹) ∈ Zsub :=
          Zsub.mul_mem ha_conj hb_conj
        simpa [mul_assoc] using hmul
    | inv a _ha ha_conj =>
        have hinv : (y * a * y⁻¹)⁻¹ ∈ Zsub := Zsub.inv_mem ha_conj
        simpa [mul_assoc] using hinv
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨p, _hp, hp⟩ := hleft.surjOn (show (g : M) ∈ (X : Set M) from g.property)
  let y : X := ⟨(p.1 : M), p.1.property.1⟩
  let z : X := ⟨(p.2 : M), p.2.property.1⟩
  have hyC : (y : M) ∈ Subgroup.centralizer ({t} : Set M) := p.1.property.2
  have hzZ : z ∈ Zset := by
    change rightConjugateElem (z : M) t = (z : M)⁻¹
    exact p.2.property.2
  have hzSub : z ∈ Zsub := Subgroup.subset_closure hzZ
  have hg_eq : g = y * z := by
    apply Subtype.ext
    exact hp.symm
  have hinner : z * n * z⁻¹ ∈ Zsub :=
    Zsub.mul_mem (Zsub.mul_mem hzSub hn) (Zsub.inv_mem hzSub)
  have hconj : y * (z * n * z⁻¹) * y⁻¹ ∈ Zsub :=
    hY_conj y hyC (z * n * z⁻¹) hinner
  simpa [hg_eq, mul_assoc] using hconj

end PFchapter1section1
end CFSG.BenderSuzuki
