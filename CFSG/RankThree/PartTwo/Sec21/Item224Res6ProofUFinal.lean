module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUMain

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

namespace Item224Res6Proof

theorem le_inner_of_coprime_card_outer {X : Type*} [Group X] [Finite (MulAut X)]
    (hout : Nat.Coprime (Nat.card (Outer X)) 3) {E : Subgroup (MulAut X)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : E ≤ (MulAut.conj : X →* MulAut X).range := by
  intro e he
  set z : Outer X := (e : Outer X) with hz
  have h1 : orderOf z ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hz, ← QuotientGroup.mk_pow, hE.2 e he, QuotientGroup.mk_one]
  have h2 : orderOf z ∣ Nat.card (Outer X) := orderOf_dvd_natCard z
  have h3 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hout.symm h1 h2
  rw [orderOf_eq_one_iff, hz, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem nonempty_projSU_mulEquiv_uP {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m) :
    Nonempty (projSU n 2 m ≃* uP (Sec4.unitaryFieldData_galoisField 2 m hm) n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := Sec4.unitaryFieldData_galoisField 2 m hm
  have hq : ¬(n = 3 ∧ 2 ^ m = 2) := fun h3 => by omega
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    Sec4.isPrimeFormGram_one_GL (by omega) hq
  exact ⟨(Sec4.projSUEquivStatedProj n 2 m).trans
    ((unitaryPSUEquiv hU (by omega)).symm.trans e₃.symm)⟩

theorem autTorusBorelTits_uP_of_coprime {n m : ℕ} (hn : n = 4 ∨ n = 5) (hm : 1 ≤ m)
    (hme : Even m) (hout : Nat.Coprime (2 * m * (2 ^ m + 1)) 3) :
    AutTorusBorelTits (uP (Sec4.unitaryFieldData_galoisField 2 m hm) n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := Sec4.unitaryFieldData_galoisField 2 m hm
  have : CharP (GaloisField 2 (2 * m)) 2 := hU.charP
  have hq : ¬(n = 3 ∧ 2 ^ m = 2) := fun h3 => by omega
  have hdvd := Sec4.card_outer_primeFormP_dvd hU (n := n) (by omega) hq
  have hcop : Nat.Coprime (Nat.card (Outer (uP hU n))) 3 :=
    Nat.Coprime.coprime_dvd_left hdvd hout
  have : Finite (MulAut (uP hU n)) := by
    have : Finite (uP hU n) := inferInstance
    exact Finite.of_injective (fun σ : MulAut (uP hU n) => (σ : uP hU n → uP hU n))
      fun a b hab => MulEquiv.ext (congrFun hab)
  intro E hE hE9 _ _ T hT hT1 hTE
  exact oddFixedBorelTits_uP hU hme hn hE hE9 (le_inner_of_coprime_card_outer hcop hE) hT hT1 hTE

end Item224Res6Proof

open Item224Res6Proof

theorem ks224U5BorelTits : KS224U5BorelTits := by
  intro X _ _ hX
  obtain ⟨e⟩ := hX
  obtain ⟨e'⟩ := nonempty_projSU_mulEquiv_uP (n := 5) (m := 2) (by norm_num) (by norm_num)
  exact autTorusBorelTits_of_mulEquiv (e.trans e')
    (autTorusBorelTits_uP_of_coprime (Or.inr rfl) (by norm_num) even_two (by norm_num))

end CFSG.RankThree.PartTwo.Sec21
