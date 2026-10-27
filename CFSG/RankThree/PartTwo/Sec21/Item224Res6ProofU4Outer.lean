module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofU4Three
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUFinal
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofNine
import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

namespace Item224Res6Proof

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K)

omit [Finite K] [CharP K 2] in
theorem le_inner_of_innerThreeFixed_uP4 (hf : Even f) {E : Subgroup (MulAut (uP h 4))}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hI : InnerThreeFixed (uP h 4) E)
    (hx : ∃ x : uP h 4, orderOf x = 3 ∧ x ∉ Subgroup.center (uP h 4) ∧ ∀ e ∈ E, e x = x) :
    E ≤ (MulAut.conj : uP h 4 →* MulAut (uP h 4)).range := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have hnq : ¬(4 = 3 ∧ 2 ^ f = 2) := fun h3 => absurd h3.1 (by norm_num)
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hcinj := conj_injective_uP h hn3 hnq
  have hcop3 : Nat.Coprime (2 ^ f + 1) 3 := (coprime_two_pow_add_one hf h.one_le).2
  have hgcd : Nat.gcd 4 (2 ^ f + 1) = 1 := by
    have h1 := Nat.Coprime.pow_right 2 (coprime_two_pow_add_one hf h.one_le).1
    rw [Nat.coprime_comm] at h1
    exact h1
  obtain ⟨x₀, hx₀3, -, hx₀E⟩ := hx
  have hcx₀E : MulAut.conj x₀ ∈ E := hI x₀ hx₀3 hx₀E
  have hcx₀ord : orderOf (MulAut.conj x₀) = 3 := by rw [orderOf_injective _ hcinj, hx₀3]
  intro e he
  by_contra hein
  have he3 : e ^ 3 = 1 := hE.2 e he
  have he1 : e ≠ 1 := fun h1 => hein (h1 ▸ one_mem _)
  have heord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hσ1 : primeFormFieldFactor h isPrimeFormGram_one hn3 hnq e ≠ 1 := by
    intro h1
    have heD : e ∈ primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3 hnq]
      exact h1
    apply hein
    have hdvd := card_primeFormD_quotient_dvd h (1 : GL (Fin 4) K)
    obtain ⟨y, hy⟩ : ∃ y : primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ⧸
        (inner (uP h 4)).subgroupOf (primeFormD h ((1 : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)),
        y = ((⟨e, heD⟩ : primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :
          _) := ⟨_, rfl⟩
    have hy3 : y ^ 3 = 1 := by
      rw [hy, ← QuotientGroup.mk_pow]
      have : (⟨e, heD⟩ : primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow]; exact he3)
      rw [this, QuotientGroup.mk_one]
    have h1' : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have h2' : orderOf y ∣ 2 ^ f + 1 := (orderOf_dvd_natCard y).trans hdvd
    have h3' : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop3.symm h1' h2'
    rw [orderOf_eq_one_iff, hy, QuotientGroup.eq_one_iff] at h3'
    exact Subgroup.mem_subgroupOf.mp h3'
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn3 hnq e with hσdef
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, he3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨hpf, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hnq Nat.prime_three
      hp2 (by norm_num) e heord σ rfl hσord
  set cM := primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) M with hcM
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := 4) (K := K)) σ with hfσ
  have he' : e = cM * fσ * cM⁻¹ := by rw [← hM]; group
  have hZ3 : ¬ 3 ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4) := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h (by norm_num), hgcd]
    norm_num
  obtain ⟨-, -, -, -, -, hjinj, hrange, -⟩ :=
    CFSG.RankThree.Classical.prime_subfield_fixed_group_package h Nat.prime_three hp2 hσord 4 hn3
      hnq hZ3
  set j := CFSG.RankThree.Classical.primeSubfieldPSU h Nat.prime_three hp2 hσord 4 with hj
  have h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three hp2 hσord
  have := h₀.finite
  have := h₀.charP
  have hjfix : ∀ w, fσ (j w) = j w := by
    intro w
    have hw : j w ∈ CFSG.RankThree.Classical.fieldFixedPSU h 4 σ := by
      rw [← hrange]
      exact ⟨w, rfl⟩
    exact hw
  have hx'fix : fσ (cM⁻¹ x₀) = cM⁻¹ x₀ := by
    have h1 : fσ = cM⁻¹ * e * cM := hM.symm
    rw [h1]
    change cM⁻¹ (e (cM (cM⁻¹ x₀))) = cM⁻¹ x₀
    rw [MulAut.apply_inv_self, hx₀E e he]
  have hx'mem : cM⁻¹ x₀ ∈ j.range := by
    rw [hrange]
    exact hx'fix
  obtain ⟨y, hy⟩ := hx'mem
  have hy3 : orderOf y = 3 := by
    rw [← orderOf_injective j hjinj y, hy, MulEquiv.orderOf_eq, hx₀3]
  have hf₀ : Even (f / 3) := by
    obtain ⟨k, hk⟩ := hpf
    rw [hk, Nat.mul_div_cancel_left k (by norm_num)]
    rw [hk] at hf
    rcases Nat.even_mul.mp hf with h3 | hk'
    · exact absurd h3 (by decide)
    · exact hk'
  obtain ⟨z₀, hz₀3, hz₀c, hz₀n⟩ := exists_commuting_three_uP4 h₀ hf₀ y hy3
  obtain ⟨z, hz⟩ : ∃ z : uP h 4, z = cM (j z₀) := ⟨_, rfl⟩
  have hez : e z = z := by
    rw [he', hz]
    change cM (fσ (cM⁻¹ (cM (j z₀)))) = cM (j z₀)
    rw [MulAut.inv_apply_self, hjfix]
  have hx₀' : x₀ = cM (j y) := by rw [hy, MulAut.apply_inv_self]
  have hyz : y * z₀ * y⁻¹ = z₀ := by rw [← hz₀c, mul_inv_cancel_right]
  have hcz : MulAut.conj x₀ z = z := by
    rw [MulAut.conj_apply, hx₀', hz]
    calc cM (j y) * cM (j z₀) * (cM (j y))⁻¹ = cM (j (y * z₀ * y⁻¹)) := by
          simp only [map_mul, map_inv]
      _ = cM (j z₀) := by rw [hyz]
  have hS : E ⊓ MulAction.stabilizer (MulAut (uP h 4)) z = E := by
    refine eq_of_card_nine hE9 inf_le_left (a := MulAut.conj x₀) (b := e)
      (Subgroup.mem_inf.mpr ⟨hcx₀E, ?_⟩) hcx₀ord (Subgroup.mem_inf.mpr ⟨he, ?_⟩) ?_
    · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hcz
    · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hez
    · intro hmem
      have hle : Subgroup.zpowers (MulAut.conj x₀) ≤
          (MulAut.conj : uP h 4 →* MulAut (uP h 4)).range := Subgroup.zpowers_le.mpr ⟨x₀, rfl⟩
      exact hein (hle hmem)
  have hfixE : ∀ g ∈ E, g z = z := by
    intro g hg
    have h1 : g ∈ E ⊓ MulAction.stabilizer (MulAut (uP h 4)) z := by
      rw [hS]
      exact hg
    have h2 := (Subgroup.mem_inf.mp h1).2
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2
  have hz3 : orderOf z = 3 := by
    rw [hz, MulEquiv.orderOf_eq, orderOf_injective j hjinj, hz₀3]
  have hczE : MulAut.conj z ∈ E := hI z hz3 hfixE
  have hczmem : MulAut.conj z ∈ Subgroup.zpowers (MulAut.conj x₀) := by
    by_contra hnot
    have hEI : E ⊓ (MulAut.conj : uP h 4 →* MulAut (uP h 4)).range = E :=
      eq_of_card_nine hE9 inf_le_left (Subgroup.mem_inf.mpr ⟨hcx₀E, ⟨x₀, rfl⟩⟩) hcx₀ord
        (Subgroup.mem_inf.mpr ⟨hczE, ⟨z, rfl⟩⟩) hnot
    apply hein
    have h1 : e ∈ E ⊓ (MulAut.conj : uP h 4 →* MulAut (uP h 4)).range := by
      rw [hEI]
      exact he
    exact (Subgroup.mem_inf.mp h1).2
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hczmem
  rw [← map_zpow] at hi
  have hzx : x₀ ^ i = z := hcinj hi
  apply hz₀n
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  apply hjinj
  apply cM.injective
  rw [map_zpow, map_zpow, ← hx₀', hzx, hz]

theorem autTorusBorelTits_uP4 {m : ℕ} (hm : 1 ≤ m) (hme : Even m) :
    AutTorusBorelTits (uP (Sec4.unitaryFieldData_galoisField 2 m hm) 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := Sec4.unitaryFieldData_galoisField 2 m hm
  have : CharP (GaloisField 2 (2 * m)) 2 := hU.charP
  intro E hE hE9 hI hx T hT hT1 hTE
  exact oddFixedBorelTits_uP hU hme (Or.inl rfl) hE hE9
    (le_inner_of_innerThreeFixed_uP4 hU hme hE hE9 hI hx) hT hT1 hTE

end Item224Res6Proof

open Item224Res6Proof

theorem ks224U4BorelTits : KS224U4BorelTits := by
  intro X _ _ n hn he hX
  obtain ⟨e⟩ := hX
  obtain ⟨e'⟩ := nonempty_projSU_mulEquiv_uP (n := 4) (m := n) le_rfl hn
  exact autTorusBorelTits_of_mulEquiv (e.trans e') (autTorusBorelTits_uP4 hn he)

end CFSG.RankThree.PartTwo.Sec21
