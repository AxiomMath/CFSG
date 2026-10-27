module

public import CFSG.Quasithin.EmptyFaithful.S152U21
public import CFSG.Quasithin.EmptyFaithful.S152U22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidual_mono {X Y : Subgroup G} (h : X ≤ Y) :
    oPrimeResidualOf 3 X ≤ oPrimeResidualOf 3 Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

omit [Finite G] in
theorem eq_oTwoUpper_of_eq_oPrimeResidual {X : Subgroup G} (hX : X = oPrimeResidualOf 3 X) :
    X = oTwoUpper X := by
  have h1 : oPrimeResidualOf 3 X ≤ oTwoUpper X := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxX, k, hk⟩
    exact mem_oTwoUpper_of_odd hxX (by rw [hk]; exact Odd.pow (by decide))
  exact le_antisymm (hX.le.trans h1) (oTwoUpper_le X)

theorem mem_normalizer_of_conj_mem {X : Subgroup G} {g : G} (h : ∀ y ∈ X, g * y * g⁻¹ ∈ X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  have hsub : conjSub g X ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using h y hy
  have heq : conjSub g X = X :=
    Subgroup.eq_of_le_of_card_ge hsub (by
      have : Nat.card (conjSub g X) = Nat.card X :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      omega)
  exact mem_normalizer_of_conjSub_eq152 heq

omit [Finite G] in
theorem commutator_mem_of_relIndex_le_two {N Q : Subgroup G}
    (h2 : N.relIndex Q = 1 ∨ N.relIndex Q = 2) {x : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hxQ : x ∈ Subgroup.normalizer (Q : Set G))
    {q : G} (hq : q ∈ Q) : x * q * x⁻¹ * q⁻¹ ∈ N := by
  have hxqQ : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxQ q).mp hq
  by_cases hqN : q ∈ N
  · exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN q).mp hqN) (N.inv_mem hqN)
  · rcases h2 with h | h
    · exact absurd ((Subgroup.relIndex_eq_one.mp h) hq) hqN
    · have hxqN : x * q * x⁻¹ ∉ N := fun hc => hqN ((Subgroup.mem_normalizer_iff.mp hxN q).mpr hc)
      exact mul_inv_mem_of_relIndex_two152 h hxqQ hq hxqN hqN

omit [Finite G] in
theorem mem_of_orderOf_three_pow_mul {X N : Subgroup G} (hN : IsPGroup 2 N)
    (hNX : N ≤ Subgroup.normalizer (X : Set G)) {n x : G} (hn : n ∈ N) (hx : x ∈ X) {k : ℕ}
    (hord : orderOf (n * x) = 3 ^ k) : n * x ∈ X := by
  have key : ∀ m : ℕ, ∃ x' ∈ X, (n * x) ^ m = n ^ m * x' := by
    intro m
    induction m with
    | zero => exact ⟨1, X.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨x', hx', he⟩ := ih
      have hinv : n⁻¹ * x' * n ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (hNX (N.inv_mem hn)) x').mp hx'
        simpa using this
      refine ⟨(n⁻¹ * x' * n) * x, X.mul_mem hinv hx, ?_⟩
      rw [pow_succ, he, pow_succ]
      simp [mul_assoc]
  obtain ⟨x', hx', he⟩ := key (3 ^ k)
  have h1 : (n * x) ^ 3 ^ k = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hpow : n ^ 3 ^ k ∈ X := by
    have h3 : n ^ 3 ^ k * x' = 1 := by rw [← he]; exact h1
    rw [eq_inv_of_mul_eq_one_left h3]
    exact X.inv_mem hx'
  obtain ⟨j, hj⟩ := hN ⟨n, hn⟩
  have hnj : orderOf n ∣ 2 ^ j := by
    refine orderOf_dvd_of_pow_eq_one ?_
    simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (3 ^ k) (orderOf n) :=
    Nat.Coprime.coprime_dvd_right hnj (Nat.Coprime.pow k j (by norm_num))
  exact X.mul_mem ((Subgroup.zpowers_le.mpr hpow) (A4.mem_zpowers_pow_of_coprime hcop)) hx

theorem le_normalizer_of_eq_oPrimeResidual {X Q N : Subgroup G} (hX : X = oPrimeResidualOf 3 X)
    (hN : IsPGroup 2 N) (hNX : N ≤ Subgroup.normalizer (X : Set G))
    (hc : ∀ x ∈ X, ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ N) : Q ≤ Subgroup.normalizer (X : Set G) := by
  intro q hq
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  have hy' : y ∈ oPrimeResidualOf 3 X := by rw [← hX]; exact hy
  clear hy
  induction hy' using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨hgX, k, hk⟩ := hg
    have h1 : q * g * q⁻¹ = (q * g * q⁻¹ * g⁻¹) * g := by group
    have hord : orderOf (q * g * q⁻¹) = 3 ^ k := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hk
    rw [h1] at hord ⊢
    exact mem_of_orderOf_three_pow_mul hN hNX (hc g hgX q hq) hgX hord
  | one => simp
  | mul a b _ _ ha hb => simpa [mul_assoc] using X.mul_mem ha hb
  | inv a _ ha => simpa [mul_assoc] using X.inv_mem ha

end S15223

end CFSG.Quasithin
