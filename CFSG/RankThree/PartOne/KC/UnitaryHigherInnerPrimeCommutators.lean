module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOdd

public section

namespace CFSG.RankThree.PartOne

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

@[expose] def idQodd {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (t : MulAut (primeFormP h (idGram K n))) : Set (MulAut (primeFormP h (idGram K n))) :=
  {z | z ∈ idCenterN h t ⊓ (B ⊓ Subgroup.centralizer
    ({t} : Set (MulAut (primeFormP h (idGram K n))))) ∧ Odd (orderOf z)}

theorem higher_unitary_inner_prime_local_core_commutators_odd {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hq : 3 < ℓ ^ f) (hn3 : 3 ≤ n) (hnp : n < p) (hp : p.Prime)
    (hpℓ : p ≠ ℓ) (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B)
    (t : MulAut (primeFormP h (idGram K n)))
    (ht : t ∈ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range) (htp : orderOf t = p)
    (A : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hAB : A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n)))))
    (hA : IsPGroup p ↥A) :
    Odd (Nat.card ↥⁅CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n))))), A⁆) ∧
    (∀ z ∈ ⁅CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n))))), A⁆,
      z ∈ idQodd h B t) ∧
    (∀ a ∈ idCenterN h t ⊓ (B ⊓ Subgroup.centralizer ({t} :
          Set (MulAut (primeFormP h (idGram K n))))),
        ∀ b ∈ idCenterN h t ⊓ (B ⊓ Subgroup.centralizer ({t} :
          Set (MulAut (primeFormP h (idGram K n))))), a * b = b * a) ∧
    ((idCenterN h t ⊓ (B ⊓ Subgroup.centralizer ({t} :
        Set (MulAut (primeFormP h (idGram K n)))))).subgroupOf
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n)))))).Normal := by
  classical
  have hfin : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c _ hcn hcp
    have hcop : Nat.Coprime n p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hnp)).symm
    have : c ^ Nat.gcd n p = 1 := pow_gcd_eq_one.mpr ⟨hcn, hcp⟩
    rwa [hcop, pow_one] at this
  obtain ⟨x, hxp, hxo, hxt⟩ := exists_lift_of_orderOf (h := h) hn3 hq hp hZp ht htp
  have L : LiftData h n p x := ⟨hn3, hq, hp, hpℓ, hZp, hxp⟩
  have ht' : t = primeFormConjHom h (idGram K n) (liftUnitary x) := by
    rw [primeFormConjHom_liftUnitary, hxt]
  subst ht'
  have hp2 : p ≠ 2 := by omega
  have hAstab : A ≤ idStab x := hAB.trans inf_le_right
  have hr : Nat.card (primaryFactors (idEnd x)) < p := by
    have h1 := card_primaryFactors_le L.squarefree_idEnd
    rw [show Module.finrank K (Fin n → K) = n from Module.finrank_fin_fun K] at h1
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    omega
  have hfix : ∀ a : ↥A, L.FixesIdempotents hAstab a := fun a =>
    L.fixesIdempotents_of_card_lt hA hAstab hr a
  have hmain := fun {s a : MulAut (primeFormP h (idGram K n))}
      (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
        (B ⊓ idStab x)) (ha : a ∈ A) =>
    L.commutator_mem_odd hp2 B hB hAB hA hfix hs ha
  have hcomm : ∀ z₁ ∈ idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) ⊓
      (B ⊓ idStab x), ∀ z₂ ∈ idCenterN h (primeFormConjHom h (idGram K n) (liftUnitary x)) ⊓
        (B ⊓ idStab x), Commute z₁ z₂ := fun z₁ h₁ z₂ h₂ =>
    L.Q0_comm (Subgroup.mem_inf.mp h₁).1 (Subgroup.mem_inf.mp h₂).1
  have hle : ⁅CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
      (B ⊓ idStab x), A⁆ ≤ oddOrderSubgroup _ hcomm :=
    Subgroup.commutator_le.mpr fun s hs a ha => hmain hs ha
  refine ⟨odd_card_of_forall_odd_orderOf _ (fun z hz => (hle hz).2), fun z hz => hle hz,
    fun a ha b hb => L.Q0_comm (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp hb).1,
    L.Q0_normal B hB⟩

end CFSG.RankThree.PartOne
