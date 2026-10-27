module

public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPrimeCommutators
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitFixed

public section

namespace CFSG.RankThree.PartOne

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

theorem nonsplit_unitary_inner_actor_local_core_commutators_odd {ℓ f n p : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) (hq : 3 < ℓ ^ f) (hn3 : 3 ≤ n) (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpq : ¬p ∣ ℓ ^ f + 1)
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
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
      (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n)))))).Normal ∧
    (∃! x : gramSU h (idGram K n),
      orderOf x = p ∧ MulAut.conj (x : primeFormP h (idGram K n)) = t) ∧
    ∀ x : gramSU h (idGram K n), orderOf x = p →
      MulAut.conj (x : primeFormP h (idGram K n)) = t →
        Nat.card ↥(idAdjointOrbits x) ≤ 1 + (p - 1) / orderOf (-((ℓ : ZMod p) ^ f)) ∧
        1 + (p - 1) / orderOf (-((ℓ : ZMod p) ^ f)) < p := by
  classical
  have hfin : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hp2 : p ≠ 2 := by omega
  have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
    intro c hc _ hcp
    have hc' : c ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h c).mpr hc
    have hcop : Nat.Coprime (ℓ ^ f + 1) p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).symm
    have : c ^ Nat.gcd (ℓ ^ f + 1) p = 1 := pow_gcd_eq_one.mpr ⟨hc', hcp⟩
    rwa [hcop, pow_one] at this
  obtain ⟨x, hxp, hxo, hxt⟩ := exists_lift_of_orderOf (h := h) hn3 hq hp hZp ht htp
  have huniq : ∃! y : gramSU h (idGram K n),
      orderOf y = p ∧ MulAut.conj (y : primeFormP h (idGram K n)) = t := by
    refine ⟨x, ⟨hxo, hxt⟩, ?_⟩
    rintro y ⟨hyo, hyt⟩
    have hyp : y ^ p = 1 := by
      rw [← hyo]
      exact pow_orderOf_eq_one y
    have hπ : (y : primeFormP h (idGram K n)) = (x : primeFormP h (idGram K n)) :=
      conj_injective hn3 hq (hyt.trans hxt.symm)
    exact eq_of_mk_eq_of_pow_eq_one_of_noTorsion hZp (by omega) hyp hxp hπ
  have hlt : 1 + (p - 1) / orderOf (-((ℓ : ZMod p) ^ f)) < p := by
    have hne : orderOf (-((ℓ : ZMod p) ^ f)) ≠ 1 := by
      intro h1
      have h2 : -((ℓ : ZMod p) ^ f) = 1 := orderOf_eq_one_iff.mp h1
      have h3 : ((ℓ ^ f + 1 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination -h2
      exact hpq ((ZMod.natCast_eq_zero_iff _ _).mp h3)
    rcases Nat.lt_or_ge (orderOf (-((ℓ : ZMod p) ^ f))) 2 with hd | hd
    · have : orderOf (-((ℓ : ZMod p) ^ f)) = 0 := by omega
      rw [this, Nat.div_zero]
      omega
    · have := Nat.div_le_div_left hd (by norm_num : 0 < 2) (a := p - 1)
      omega
  have hkappa : ∀ y : gramSU h (idGram K n), orderOf y = p →
      MulAut.conj (y : primeFormP h (idGram K n)) = t →
        Nat.card ↥(idAdjointOrbits y) ≤ 1 + (p - 1) / orderOf (-((ℓ : ZMod p) ^ f)) ∧
        1 + (p - 1) / orderOf (-((ℓ : ZMod p) ^ f)) < p := by
    intro y hyo _
    have hyp : y ^ p = 1 := by
      rw [← hyo]
      exact pow_orderOf_eq_one y
    have Ly : LiftData h n p y := ⟨hn3, hq, hp, hpℓ, hZp, hyp⟩
    refine ⟨?_, hlt⟩
    rw [Ly.card_idAdjointOrbits]
    exact card_adjointOrbits_le Ly.primaryData hp hpℓ Ly.pow_toLinU
  have L : LiftData h n p x := ⟨hn3, hq, hp, hpℓ, hZp, hxp⟩
  have hκ : Nat.card (adjointOrbits h (toLinU h n (liftUnitary x))) < p :=
    lt_of_le_of_lt (card_adjointOrbits_le L.primaryData hp hpℓ L.pow_toLinU) hlt
  have ht' : t = primeFormConjHom h (idGram K n) (liftUnitary x) := by
    rw [primeFormConjHom_liftUnitary, hxt]
  subst ht'
  have hAstab : A ≤ idStab x := hAB.trans inf_le_right
  have hfix : ∀ a : ↥A, L.FixesIdempotents hAstab a := fun a =>
    L.fixesIdempotents_of_card_orbits_lt hp2 hA hAstab hκ a
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
    L.Q0_normal B hB, huniq, hkappa⟩

end CFSG.RankThree.PartOne
