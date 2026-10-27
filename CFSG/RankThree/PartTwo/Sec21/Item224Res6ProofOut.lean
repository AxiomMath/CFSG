module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofLie
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

namespace Item224Res6Proof

theorem outTwoCyclic_primeFormP {m n : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 m K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ m = 2)) :
    OutTwoCyclic (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := Sec4.isPrimeFormGram_one_GL
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, hdvd⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  set P := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hP
  set ψ := primeFormFieldFactor h hC hn hq with hψ
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  have hcyc : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic h.prime K h.card).2
  intro Q hQ hQI
  refine isCyclic_of_injective (ψ.comp Q.subtype) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨x, hxQ⟩ hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at hx
  have hxD : x ∈ D := by
    rw [← hker]
    exact hx
  set z : D ⧸ (inner P).subgroupOf D := ((⟨x, hxD⟩ : D) : D ⧸ (inner P).subgroupOf D) with hz
  obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
  have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hz2 : orderOf z ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hz, ← QuotientGroup.mk_pow]
    have : (⟨x, hxD⟩ : D) ^ 2 ^ k = 1 := Subtype.ext hxk
    rw [this, QuotientGroup.mk_one]
  have hzodd : orderOf z ∣ 2 ^ m + 1 := (orderOf_dvd_natCard z).trans hdvd
  have hcop : Nat.Coprime (2 ^ k) (2 ^ m + 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr
      (Even.add_one (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩)))
  have hz1 : z = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop hz2 hzodd
  have hxI : x ∈ inner P :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨x, hxD⟩ : D)).mp hz1)
  have hxbot : x ∈ Q ⊓ (MulAut.conj : P →* MulAut P).range := ⟨hxQ, hxI⟩
  rw [hQI, Subgroup.mem_bot] at hxbot
  exact Subgroup.mem_bot.mpr (Subtype.ext hxbot)

theorem outTwoCyclic_projSU_two {n m : ℕ} (hn : 4 ≤ n) (hm : 1 ≤ m) :
    OutTwoCyclic (projSU n 2 m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := Sec4.unitaryFieldData_galoisField 2 m hm
  have hC : IsPrimeFormGram (1 : GL (Fin n) (GaloisField 2 (2 * m))) := Sec4.isPrimeFormGram_one_GL
  have hq : ¬(n = 3 ∧ 2 ^ m = 2) := fun h3 => by omega
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC (by omega) hq
  have e : projSU n 2 m ≃* primeFormP hU
      ((1 : GL (Fin n) (GaloisField 2 (2 * m))) : Matrix (Fin n) (Fin n) _) :=
    (Sec4.projSUEquivStatedProj n 2 m).trans ((unitaryPSUEquiv hU (by omega)).symm.trans e₃.symm)
  exact outTwoCyclic_of_mulEquiv e (outTwoCyclic_primeFormP hU (by omega) hq)

end Item224Res6Proof

open Item224Res6Proof

theorem ks224U4OutTwoCyclic : KS224U4OutTwoCyclic := by
  intro X _ _ n hn _ hX
  obtain ⟨e⟩ := hX
  exact outTwoCyclic_of_mulEquiv e (outTwoCyclic_projSU_two le_rfl hn)

theorem ks224U5OutTwoCyclic : KS224U5OutTwoCyclic := by
  intro X _ _ hX
  obtain ⟨e⟩ := hX
  exact outTwoCyclic_of_mulEquiv e (outTwoCyclic_projSU_two (by norm_num) (by norm_num))

end CFSG.RankThree.PartTwo.Sec21
