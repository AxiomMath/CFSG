module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUAux
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K) {n : ℕ}

abbrev uP (h : UnitaryFieldData 2 f K) (n : ℕ) : Type :=
  primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem eq_of_mk_eq_of_pow_three [Finite (uS h n)] (hZ3 : Nat.Coprime (Nat.card (uZ h n)) 3)
    {x y : uS h n} (hxy : QuotientGroup.mk' (uZ h n) x = QuotientGroup.mk' (uZ h n) y)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) : x = y := by
  have hz : x * y⁻¹ ∈ uZ h n := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change QuotientGroup.mk' (uZ h n) x * (QuotientGroup.mk' (uZ h n) y)⁻¹ = 1
    rw [hxy, mul_inv_cancel]
  have hcomm : Commute (x * y⁻¹) y :=
    Subgroup.mem_center_iff.mp (uZ_le_center h hz) y |>.symm
  have hz3 : (x * y⁻¹) ^ 3 = 1 := by
    have h1 := hcomm.mul_pow 3
    rw [inv_mul_cancel_right, hx, hy, mul_one] at h1
    exact h1.symm
  have h1 : orderOf (x * y⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have h2 : orderOf (x * y⁻¹) ∣ Nat.card (uZ h n) := by
    rw [← Subgroup.orderOf_mk (x * y⁻¹) hz]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (x * y⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hZ3.symm h1 h2
  rw [orderOf_eq_one_iff, mul_inv_eq_one] at h3
  exact h3

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem conj_injective_uP (hn3 : 3 ≤ n) (hnq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    Function.Injective (MulAut.conj : uP h n →* MulAut (uP h n)) := by
  have hs : IsSimpleGroup (uP h n) :=
    CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h hn3 hnq
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxZ : x ∈ Subgroup.center (uP h n) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun σ : MulAut (uP h n) => σ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = x * g * x⁻¹ * x := by rw [this]
      _ = x * g := by group
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (uP h n)) with hb | ht
  · rw [hb] at hxZ
    exact hxZ
  · exfalso
    have hS : Group.IsPerfect (uS h n) := CFSG.RankThree.Classical.isPerfect_gramSU_one h hn3 hnq
    have hperf : Group.IsPerfect (uP h n) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (uZ h n))
        (QuotientGroup.mk'_surjective _)
    have hcomm : ∀ a b : uP h n, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a)
    have hbot : ⁅(⊤ : Subgroup (uP h n)), (⊤ : Subgroup (uP h n))⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact hcomm b a
    have htop : ⁅(⊤ : Subgroup (uP h n)), (⊤ : Subgroup (uP h n))⁆ = ⊤ := hperf.commutator_eq_top
    rw [htop] at hbot
    obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
    apply hab
    have ha : a ∈ (⊥ : Subgroup (uP h n)) := hbot ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup (uP h n)) := hbot ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

omit [CharP K 2] in
theorem inf_inner_eq_bot_uP (hf : Even f) (hn3 : 3 ≤ n) (hnq : ¬(n = 3 ∧ 2 ^ f = 2))
    {E₀ : Subgroup (uS h n)} (hE₀3 : ∀ x ∈ E₀, x ^ 3 = 1)
    (hC2 : ∀ s : uS h n, (∀ e ∈ E₀, s * e = e * s) → ∀ k : ℕ, s ^ 2 ^ k = 1 → s = 1)
    {E T : Subgroup (MulAut (uP h n))}
    (hE₀E : ∀ e ∈ E₀, MulAut.conj (QuotientGroup.mk' (uZ h n) e) ∈ E)
    (hT : IsPGroup 2 T) (hTE : T ≤ Subgroup.centralizer (E : Set (MulAut (uP h n)))) :
    T ⊓ (MulAut.conj : uP h n →* MulAut (uP h n)).range = ⊥ := by
  obtain ⟨-, hZ3⟩ := coprime_card_uZ h hf
  have hcinj := conj_injective_uP h hn3 hnq
  rw [eq_bot_iff]
  rintro t ⟨htT, x, rfl⟩
  rw [Subgroup.mem_bot]
  have hxc : ∀ e ∈ E₀, x * QuotientGroup.mk' (uZ h n) e = QuotientGroup.mk' (uZ h n) e * x := by
    intro e he
    have h1 := Subgroup.mem_centralizer_iff.mp (hTE htT) _ (hE₀E e he)
    apply hcinj
    rw [map_mul, map_mul]
    exact h1.symm
  obtain ⟨k, hk⟩ := hT ⟨MulAut.conj x, htT⟩
  have hxk : x ^ 2 ^ k = 1 := by
    apply hcinj
    rw [map_pow, map_one]
    exact congrArg Subtype.val hk
  have hzx : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change (x ^ i) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hxk,
      _root_.one_zpow]
  obtain ⟨Q, hQ2, hQmap⟩ := exists_isPGroup_map_eq (uZ h n) hzx
  have hxQ : x ∈ Q.map (QuotientGroup.mk' (uZ h n)) := hQmap ▸ Subgroup.mem_zpowers x
  obtain ⟨s, hsQ, hsx⟩ := Subgroup.mem_map.mp hxQ
  obtain ⟨j, hj⟩ := hQ2 ⟨s, hsQ⟩
  have hsj : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hsc : ∀ e ∈ E₀, s * e = e * s := by
    intro e he
    have h1 : s * e * s⁻¹ = e := eq_of_mk_eq_of_pow_three h hZ3
      (by rw [map_mul, map_mul, map_inv, hsx, hxc e he, mul_inv_cancel_right])
      (by rw [conj_pow, hE₀3 e he, mul_one, mul_inv_cancel]) (hE₀3 e he)
    calc s * e = s * e * s⁻¹ * s := by group
      _ = e * s := by rw [h1]
  have hs1 := hC2 s hsc j hsj
  rw [← hsx, hs1, map_one, map_one]

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem eq_one_of_fieldFactor_uP (hn3 : 3 ≤ n) (hnq : ¬(n = 3 ∧ 2 ^ f = 2))
    {T : Subgroup (MulAut (uP h n))} (hT : IsPGroup 2 T)
    (hTI : T ⊓ (MulAut.conj : uP h n →* MulAut (uP h n)).range = ⊥) {t : MulAut (uP h n)}
    (ht : t ∈ T) (htD : primeFormFieldFactor h Sec4.isPrimeFormGram_one_GL hn3 hnq t = 1) :
    t = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, hdvd⟩ :=
    unitary_prime_form_full_semilinear_realization h Sec4.isPrimeFormGram_one_GL hn3 hnq
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  have htD' : t ∈ D := by
    rw [← hker]
    exact htD
  set z : D ⧸ (inner (uP h n)).subgroupOf D := ((⟨t, htD'⟩ : D) : D ⧸ (inner (uP h n)).subgroupOf D)
    with hz
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hz2 : orderOf z ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hz, ← QuotientGroup.mk_pow]
    have : (⟨t, htD'⟩ : D) ^ 2 ^ k = 1 := Subtype.ext htk
    rw [this, QuotientGroup.mk_one]
  have hzodd : orderOf z ∣ 2 ^ f + 1 := (orderOf_dvd_natCard z).trans hdvd
  have hcop : Nat.Coprime (2 ^ k) (2 ^ f + 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr
      (Even.add_one (Nat.even_pow.mpr ⟨even_two, by have := h.one_le; omega⟩)))
  have hz1 : z = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop hz2 hzodd
  have htI : t ∈ inner (uP h n) :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨t, htD'⟩ : D)).mp hz1)
  have htbot : t ∈ T ⊓ (MulAut.conj : uP h n →* MulAut (uP h n)).range := ⟨ht, htI⟩
  rw [hTI, Subgroup.mem_bot] at htbot
  exact htbot

omit [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem conjField_apply_mk (A : uU h n) (φ : K ≃+* K) (g : uS h n) :
    (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A *
        primeFormFieldHom h Sec4.isPrimeFormGram_one_GL φ : MulAut (uP h n))
        (QuotientGroup.mk' (uZ h n) g) =
      QuotientGroup.mk' (uZ h n) ⟨(A : GL (Fin n) K) *
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut φ (g : GL (Fin n) K) *
          (A : GL (Fin n) K)⁻¹,
        conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h Sec4.isPrimeFormGram_one_GL φ g.2)⟩ := by
  rw [MulAut.mul_apply]
  change primeFormConjHom h _ A (primeFormFieldAut h Sec4.isPrimeFormGram_one_GL φ
    (g : uP h n)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
