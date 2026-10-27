module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveThreeArith
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoE
public import CFSG.LocalAnalysis.WeakClosure81.SzStructureFacts
public import CFSG.GH74.Uniqueness.Bender.LinearOdd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

section ThreeA

variable {G : Type} [Group G]

theorem eq_one_of_inverted_of_mem_normalizer {Q : Subgroup G} (hQ : IsPGroup 2 Q) {a x : G}
    (ha : a ∈ Q) (hx : x ∈ normalizer (Q : Set G)) (hinv : a * x * a⁻¹ = x⁻¹)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have h1 : x * a⁻¹ * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hx a⁻¹).1 (Q.inv_mem ha)
  have h2 : x⁻¹ * x⁻¹ ∈ Q := by
    have h := Q.mul_mem ha h1
    have e : a * (x * a⁻¹ * x⁻¹) = x⁻¹ * x⁻¹ := by
      calc a * (x * a⁻¹ * x⁻¹) = (a * x * a⁻¹) * x⁻¹ := by group
        _ = x⁻¹ * x⁻¹ := by rw [hinv]
    rwa [e] at h
  have h3 : x * x ∈ Q := by
    have h := Q.inv_mem h2
    simpa [mul_inv_rev] using h
  obtain ⟨j, hj⟩ := hodd
  have hxQ : x ∈ Q := by
    have h0 : x ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one x
    have e : x = (x * x) ^ (j + 1) := by
      calc x = x ^ (2 * j + 1) * x := by rw [h0, one_mul]
        _ = x ^ (2 * (j + 1)) := by
          rw [← pow_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
        _ = (x * x) ^ (j + 1) := by rw [pow_mul, sq]
    rw [e]
    exact Q.pow_mem h3 _
  obtain ⟨i, hi⟩ := hQ ⟨x, hxQ⟩
  have hi' : x ^ (2 ^ i) = 1 := congrArg Subtype.val hi
  have hdvd : orderOf x ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hi'
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hl0 : l = 0 := by
    by_contra hne
    have h2l : 2 ∣ orderOf x := by rw [hl]; exact dvd_pow_self 2 hne
    have : 2 ∣ 2 * j + 1 := by rw [← hj]; exact h2l
    omega
  rw [hl0, pow_zero] at hl
  exact orderOf_eq_one_iff.1 hl

end ThreeA

section ThreeB

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {n m : ℕ}

theorem Setting12One.fixed_of_gen_eq_top {ρ : G →* LGL 2 V}
    {B A : Subgroup G} {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m) {g : G}
    (hgen : A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {v : V} (hv : v ∈ commSub ρ.range) (hfix : ρ (a * (g * a * g⁻¹)) v = v) :
    ∀ y : G, ρ y v = v := by
  haveI : Finite G := rankOne_finite h.type
  obtain ⟨-, -, -, h4⟩ := twelveOne_partOne h hgen
  have hP : ∃ a₀ ∈ A, a₀ ≠ 1 ∧ ρ a₀ = ρ a := ⟨a, ha, ha1, rfl⟩
  have hmem := h4 (ρ a) (Subgroup.mem_map_of_mem ρ ha) hP
  have hconj : ρ a * (MulAut.conj (ρ g)) (ρ a) = ρ (a * (g * a * g⁻¹)) := by
    simp [MulAut.conj_apply]
  have hvmem : v ∈ fixMod (cE ρ.range) (ρ a * (MulAut.conj (ρ g)) (ρ a)) ⊓ commSub ρ.range := by
    refine ⟨mem_fixMod.2 ?_, hv⟩
    rw [hconj, hfix, sub_self]
    exact (cE ρ.range).zero_mem
  have hvE : v ∈ cE ρ.range := hmem hvmem
  intro y
  exact (mem_cE.1 hvE).1 (ρ y) ⟨y, rfl⟩

theorem Setting12One.m_dvd_of_subgroup
    {ρ : G →* LGL 2 V} {B A : Subgroup G}
    {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m) {H : Subgroup G} (hAH : A ≤ H)
    {k : ℕ} (hk : CFSG.Quasithin.IsPSL 2 2 k ↥H ∨ CFSG.Quasithin.IsSz k ↥H)
    (hZ : Module.finrank (ZMod 2) Z ≤ m) : m ∣ k := by
  haveI : Finite G := rankOne_finite h.type
  haveI : Finite ↥H := rankOne_finite hk
  have hH := h.restrict hAH hk
  obtain ⟨L, hL⟩ := hH.exists_minimal
  rcases (twelveTwo_two_general hH hL hZ).1 with hmk | ⟨-, hmk, -⟩
  · rw [hmk]
  · exact hmk

end ThreeB

section ThreeC

variable {G : Type} [Group G]

theorem rankOne_psl_odd_order_dvd
    {k : ℕ} {Y : Type} [Group Y] (hY : CFSG.Quasithin.IsPSL 2 2 k Y) {x : Y}
    (hx : Odd (orderOf x)) : orderOf x ∣ 2 ^ k - 1 ∨ orderOf x ∣ 2 ^ k + 1 := by
  haveI : Finite Y := rankOne_finite (Or.inl hY)
  by_cases hx1 : x = 1
  · left
    rw [hx1, orderOf_one]
    exact one_dvd _
  · have hB := rankOne_benderType_psl hY
    have hcardA : Nat.card (Subgroup.zpowers x) = orderOf x := Nat.card_zpowers x
    have hA : Odd (Nat.card (Subgroup.zpowers x)) := by rw [hcardA]; exact hx
    have hA1 : Subgroup.zpowers x ≠ ⊥ := fun hbot => hx1 (Subgroup.zpowers_eq_bot.1 hbot)
    obtain ⟨T, w, hAT, -, -, hTcard, -⟩ := hB.linear_odd_subgroup hA hA1
    have hdvd : orderOf x ∣ Nat.card T := hcardA ▸ Subgroup.card_dvd_of_le hAT
    rcases hTcard with h1 | h1
    · left
      rwa [h1] at hdvd
    · right
      rwa [h1] at hdvd

theorem twelveThree_subfield
    {H : Subgroup G} {x : G} {n m k : ℕ}
    (hk : (CFSG.Quasithin.IsPSL 2 2 n G ∧ CFSG.Quasithin.IsPSL 2 2 k ↥H) ∨
      (CFSG.Quasithin.IsSz n G ∧ CFSG.Quasithin.IsSz k ↥H))
    (hk2 : 2 ≤ k) (hkn : k ∣ n) (hklt : k < n) (hm : 1 ≤ m) (hmk : m ∣ k) (hxH : x ∈ H)
    (hodd : Odd (orderOf x)) (hord : orderOf x * (2 ^ m - 1) = 2 ^ n - 1)
    (hcop : Nat.Coprime (orderOf x) (2 ^ m - 1)) :
    n = 2 * m ∧ CFSG.Quasithin.IsPSL 2 2 n G := by
  haveI hHfin : Finite ↥H := rankOne_finite (hk.imp And.right And.right)
  have hdvd1 : orderOf x ∣ Nat.card ↥H := Subgroup.orderOf_dvd_natCard H hxH
  have hdvd2 : 2 ^ m - 1 ∣ 2 ^ k - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hmk
  have hk1 : 1 ≤ k := by omega
  have hmk' : m ≤ k := Nat.le_of_dvd (by omega) hmk
  rcases hk with ⟨hGn, hHk⟩ | ⟨hGn, hHk⟩
  · have hcard := rankOne_card_psl hHk
    have hdvd3 : 2 ^ k - 1 ∣ Nat.card ↥H := by
      rw [hcard]
      exact dvd_mul_left _ _
    have hprod : orderOf x * (2 ^ m - 1) ∣ Nat.card ↥H :=
      hcop.mul_dvd_of_dvd_of_dvd hdvd1 (hdvd2.trans hdvd3)
    rw [hord, hcard] at hprod
    have hn2k : n = 2 * k := eq_two_mul_of_two_pow_sub_one_dvd_card_psl hk1 hkn hklt hprod
    have hoddH : Odd (orderOf (⟨x, hxH⟩ : ↥H)) := by
      rw [Subgroup.orderOf_mk]
      exact hodd
    have hxord := rankOne_psl_odd_order_dvd hHk hoddH
    rw [Subgroup.orderOf_mk] at hxord
    have hmeq : m = k := eq_of_mul_eq_two_pow_sub_one hm hmk' hn2k hord hxord
    exact ⟨by rw [hn2k, hmeq], hGn⟩
  · exfalso
    have hcard := rankOne_card_sz hHk
    have hdvd3 : 2 ^ k - 1 ∣ Nat.card ↥H := by
      rw [hcard]
      exact dvd_mul_left _ _
    have hprod : orderOf x * (2 ^ m - 1) ∣ Nat.card ↥H :=
      hcop.mul_dvd_of_dvd_of_dvd hdvd1 (hdvd2.trans hdvd3)
    rw [hord, hcard] at hprod
    exact SevenK.not_two_pow_sub_one_dvd_card_sz (SevenK.odd_and_three_le_of_isSz hGn).1 hkn
      hklt hprod

end ThreeC

end CFSG.LocalAnalysis.WeakClosure81
