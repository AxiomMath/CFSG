module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Fixed

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.5: the odd centralizer decomposition

This file packages the source passage from the empty fixed-point set of `tu`
to the Peterfalvi decomposition of `C_X(tu)`.  It stops before the prime-
support argument proving that the generated anti-fixed subgroup is disjoint
from the fixed subgroup.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- An involution which inverts `a` normalizes the centralizer of `a`. -/
public theorem lemma115_inverter_mem_normalizer_centralizer_singleton
    {X : Type u} [Group X] {a t : X}
    (ht : IsInvolution t)
    (ha : rightConjugateElem a t = a⁻¹) :
    t ∈ Subgroup.normalizer
      (Subgroup.centralizer ({a} : Set X) : Set X) := by
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have hata : t * a * t = a⁻¹ := by
    simpa [rightConjugateElem, ht.inv_eq_self] using ha
  have hforward : ∀ {x : X}, x * a = a * x →
      (t * x * t⁻¹) * a = a * (t * x * t⁻¹) := by
    intro x hxa
    have hxainv : x * a⁻¹ = a⁻¹ * x :=
      (show Commute x a from hxa).inv_right.eq
    have hatainv : t * a⁻¹ * t = a := by
      have hinv := congrArg Inv.inv hata
      simpa [ht.inv_eq_self, mul_inv_rev, mul_assoc] using hinv
    calc
      (t * x * t⁻¹) * a = t * x * t * a := by rw [ht.inv_eq_self]
      _ = (t * x * t * a) * (t * t) := by rw [htt, mul_one]
      _ = t * x * (t * a * t) * t := by group
      _ = t * x * a⁻¹ * t := by rw [hata]
      _ = t * (x * a⁻¹) * t := by group
      _ = t * (a⁻¹ * x) * t := by rw [hxainv]
      _ = (t * a⁻¹ * t) * (t * x * t) := by
        calc
          t * (a⁻¹ * x) * t = t * a⁻¹ * x * t := by group
          _ = t * a⁻¹ * (t * t) * x * t := by rw [htt, mul_one]
          _ = (t * a⁻¹ * t) * (t * x * t) := by group
      _ = a * (t * x * t⁻¹) := by rw [hatainv, ht.inv_eq_self]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · exact hforward
  · intro hxa
    have hback := hforward hxa
    have hconjEq : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [ht.inv_eq_self]
      calc
        t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [htt]; simp
    simpa [hconjEq] using hback

/-- Peterfalvi `lemma_a`, rewritten as the two source-facing set
factorizations `D = I_D(t) C_D(t) = C_D(t) I_D(t)`. -/
public theorem lemma115_peterfalvi_factorization
    {X : Type u} [Group X] [Finite X]
    {D : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X)) :
    (D : Set X) = peterfalviKSet D t *
        (peterfalviV D t : Set X) ∧
      (D : Set X) = (peterfalviV D t : Set X) *
        peterfalviKSet D t := by
  obtain ⟨hleft, hright, _hcard⟩ :=
    PFchapter1section1.lemma_a t D ht hDodd hDnorm
  constructor
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨p, _hp, hp⟩ := hright.surjOn hx
      exact Set.mem_mul.mpr
        ⟨p.2, p.2.property, p.1, p.1.property, hp⟩
    · intro x hx
      rcases Set.mem_mul.mp hx with ⟨k, hk, v, hv, hkv⟩
      rw [← hkv]
      exact D.mul_mem hk.1 hv.1
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨p, _hp, hp⟩ := hleft.surjOn hx
      exact Set.mem_mul.mpr
        ⟨p.1, p.1.property, p.2, p.2.property, hp⟩
    · intro x hx
      rcases Set.mem_mul.mp hx with ⟨v, hv, k, hk, hkv⟩
      rw [← hkv]
      exact D.mul_mem hv.1 hk.1

/-- The source centralizer `C_X(tu)` is odd and therefore has the full
Peterfalvi decomposition.  The closure of its anti-fixed set is normal and,
together with its `t`-fixed subgroup, generates the centralizer. -/
public theorem lemma115_centralizer_tu_decomposition
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (h114 : Lemma114Conclusion d83 d) :
    let C := Subgroup.centralizer ({t * d83.u} : Set X)
    let B := peterfalviKSet C t
    let V := peterfalviV C t
    (C : Set X) = B * (V : Set X) ∧
      (C : Set X) = (V : Set X) * B ∧
      ((Subgroup.closure B).subgroupOf C).Normal ∧
      Subgroup.closure B ⊔ V = C := by
  let C : Subgroup X := Subgroup.centralizer ({t * d83.u} : Set X)
  let B : Set X := peterfalviKSet C t
  let V : Subgroup X := peterfalviV C t
  have hCodd : Odd (Nat.card C) := by
    simpa [C] using lemma115_centralizer_tu_odd
      hM ht htM d83 htwo h42 d h102 h114
  have htuinv : rightConjugateElem (t * d83.u) t =
      (t * d83.u)⁻¹ := by
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    simp [rightConjugateElem, ht.inv_eq_self,
      d83.u_involution.inv_eq_self, ← mul_assoc, htt]
  have htNormC : t ∈ Subgroup.normalizer (C : Set X) := by
    simpa [C] using
      lemma115_inverter_mem_normalizer_centralizer_singleton ht htuinv
  have hfactor :
      (C : Set X) = B * (V : Set X) ∧
        (C : Set X) = (V : Set X) * B := by
    simpa [B, V] using
      lemma115_peterfalvi_factorization ht hCodd htNormC
  refine ⟨hfactor.1, hfactor.2, ?_, ?_⟩
  · simpa [B] using lemma101_peterfalviKernel_normal ht hCodd htNormC
  · simpa [B, V] using
      lemma101_peterfalviKernel_sup_fixed_eq ht hCodd htNormC

end CFSG.BenderSuzuki
