module

public import CFSG.Permutation.UnitaryThreeRecognition.RootNormal

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem eq_centQ_or_eq_of_conj_mem [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hd3 : d ≤ 3)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    (N : Subgroup G) (hZN : centQ Q j ≤ N) (hNQ : N ≤ Q)
    (hTN : ∀ t ∈ pairStab G a b, ∀ n ∈ N, t * n * t⁻¹ ∈ N) :
    N = centQ Q j ∨ N = Q := by
  classical
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  have hZ := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard
    hΩcard hTdvd
  set q := p ^ f with hqdef
  have hq : 3 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  let T := pairStab G a b
  let X : Set G := {n | n ∈ N ∧ n ∉ centQ Q j}
  have hX : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X := by
    intro t ht x hx
    refine ⟨hTN t ht x hx.1, fun h => hx.2 ?_⟩
    have := hQ.conj_mem_centQ hcomm hj (T.inv_mem ht) h
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rw [e] at this; exact this
  let : MulAction T X := conjAction T X hX
  have hfree : ∀ x : X, stabilizer T x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro t htx
    rw [Subgroup.mem_bot]
    have htx' : (t : G) * x = x * t := (mem_stabilizer_conjAction_iff t x).mp htx
    by_contra ht1
    have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext h)
    exact x.2.2 (hQ.mem_centQ_of_commute_pairStab hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf
      hpodd hd hQcard hΩcard hTcard hsa hs2 t.property ht1' (hNQ x.2.1) htx')
  have hdvd := card_dvd_of_stabilizer_eq_bot hfree
  have hXcard : Nat.card X = Nat.card N - q := by
    have h1 : Nat.card X + Nat.card (centQ Q j) = Nat.card N := by
      let e : X ⊕ centQ Q j ≃ N :=
        { toFun := fun x => match x with
            | Sum.inl y => ⟨y.1, y.2.1⟩
            | Sum.inr y => ⟨y.1, hZN y.2⟩
          invFun := fun n => if h : n.1 ∈ centQ Q j then Sum.inr ⟨n.1, h⟩ else
            Sum.inl ⟨n.1, n.2, h⟩
          left_inv := by
            rintro (y | y)
            · simp [y.2.2]
            · simp [y.2]
          right_inv := by
            intro n
            by_cases h : n.1 ∈ centQ Q j <;> simp [h] }
      rw [← Nat.card_sum, Nat.card_congr e]
    rw [← hZ]; omega
  have hNdvd : Nat.card N ∣ p ^ (3 * f) := by rw [← hQcard]; exact Subgroup.card_dvd_of_le hNQ
  obtain ⟨k, hk3, hNk⟩ := (Nat.dvd_prime_pow hpp).mp hNdvd
  have hqN : q ∣ Nat.card N := by rw [← hZ]; exact Subgroup.card_dvd_of_le hZN
  have hkf : f ≤ k := by
    by_contra h
    push Not at h
    have hle : Nat.card N < q := by
      rw [hNk, hqdef]; exact Nat.pow_lt_pow_right (by omega) h
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact absurd (Nat.le_of_dvd hpos hqN) (by omega)
  obtain ⟨i, rfl⟩ : ∃ i, k = f + i := ⟨k - f, by omega⟩
  have hNi : Nat.card N = q * p ^ i := by rw [hNk, pow_add]
  have hTi : Nat.card T ∣ p ^ i - 1 := by
    rw [hXcard, hNi] at hdvd
    have h2 : q * p ^ i - q = q * (p ^ i - 1) := by rw [Nat.mul_sub, mul_one]
    rw [h2] at hdvd
    have hcop : Nat.Coprime (Nat.card T) q := by
      have : Nat.Coprime (p ^ (2 * f) - 1) q := by
        rw [hqdef]
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
        intro hdv
        have h4 : p ∣ p ^ (2 * f) := dvd_pow_self p (by omega)
        have h5 : p ∣ p ^ (2 * f) - (p ^ (2 * f) - 1) := Nat.dvd_sub h4 hdv
        have h6 : 1 ≤ p ^ (2 * f) := Nat.one_le_pow _ _ (by omega)
        have : p ^ (2 * f) - (p ^ (2 * f) - 1) = 1 := by omega
        rw [this] at h5
        exact hpp.one_lt.ne' (Nat.dvd_one.mp h5)
      exact Nat.Coprime.coprime_dvd_left hTdvd this
    exact hcop.dvd_of_dvd_mul_left hdvd
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  ·
    left
    refine (Subgroup.eq_of_le_of_card_ge hZN ?_).symm
    rw [hNi, hi0, pow_zero, mul_one, hZ]
  · right
    have hi : i = 2 * f := by
      have hi3 : i ≤ 2 * f := by omega
      by_contra hne
      have hlt2 : i < 2 * f := lt_of_le_of_ne hi3 hne
      have hpi : 1 < p ^ i := Nat.one_lt_pow (by omega) (by omega)
      have hle := Nat.le_of_dvd (by omega) hTi
      have hpow : p * p ^ i ≤ p ^ (2 * f) := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by omega) hlt2
      have h3 : d * (p ^ i - 1) < p ^ (2 * f) - 1 := by
        have h31 : 3 * p ^ i ≤ p ^ (2 * f) := le_trans (Nat.mul_le_mul_right _ hp) hpow
        have h32 : d * (p ^ i - 1) ≤ 3 * (p ^ i - 1) := Nat.mul_le_mul_right _ hd3
        omega
      have : Nat.card T * d ≤ (p ^ i - 1) * d := Nat.mul_le_mul_right _ hle
      rw [hTcard] at this
      have : (p ^ i - 1) * d = d * (p ^ i - 1) := mul_comm _ _
      omega
    have hNcard : Nat.card N = Nat.card Q := by
      rw [hNi, hi, hQcard, hqdef, ← pow_add]; ring_nf
    exact Subgroup.eq_of_le_of_card_ge hNQ (le_of_eq hNcard.symm)

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
