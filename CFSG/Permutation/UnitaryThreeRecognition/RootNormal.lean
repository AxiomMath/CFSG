module

public import CFSG.Permutation.UnitaryThreeRecognition.CentralTorusOrbit
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem mem_centQ_of_commute_pairStab [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {t : G} (ht : t ∈ pairStab G a b) (ht1 : t ≠ 1) {u : G} (huQ : u ∈ Q)
    (htu : t * u = u * t) : u ∈ centQ Q j := by
  by_cases hu1 : u = 1
  · rw [hu1]; exact (centQ Q j).one_mem
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]
  have hst := hQ.conj_eq_of_commute hb hsa hsb hcomm huQ hu1 ht htu
  have htW : t ∈ swapFix G a b s := by
    rw [mem_swapFix]
    refine ⟨ht, ?_⟩
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [hst]
  have hju := hQ.commute_involution_of_commute hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf
    hpodd hd hQcard hΩcard hTcard hsa hs2 htW ht1 huQ htu
  exact mem_centQ.mpr ⟨huQ, hju⟩

theorem centQ_conj_mem [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
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
    {u : G} (huQ : u ∈ Q) {z : G} (hz : z ∈ centQ Q j) : u * z * u⁻¹ ∈ centQ Q j := by
  classical
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  have hZ := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard
    hΩcard hTdvd
  set q := p ^ f with hqdef
  have hq : 3 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  have hZQ : centQ Q j ≤ Q := inf_le_left
  let Z' : Subgroup Q := (centQ Q j).subgroupOf Q
  let : Fact (Nat.Prime p) := ⟨hpp⟩
  have hQp : IsPGroup p Q := IsPGroup.of_card hQcard
  have : Group.IsNilpotent Q := hQp.isNilpotent
  by_cases htop : Z' = ⊤
  · have : (⟨u * z * u⁻¹, Q.mul_mem (Q.mul_mem huQ (hZQ hz)) (Q.inv_mem huQ)⟩ : Q) ∈ Z' := by
      rw [htop]; trivial
    exact this
  have hlt : Z' < (Subgroup.normalizer (Z' : Set Q)) :=
    Group.normalizerCondition_of_isNilpotent Z' (lt_top_iff_ne_top.mpr htop)
  let N : Subgroup G := (Subgroup.normalizer (Z' : Set Q)).map Q.subtype
  have hNQ : N ≤ Q := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact n.property
  have hZN : centQ Q j ≤ N := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hZQ hx⟩, Subgroup.le_normalizer hx, rfl⟩
  have memN : ∀ n : G, n ∈ N ↔ n ∈ Q ∧ ∀ x ∈ centQ Q j, n * x * n⁻¹ ∈ centQ Q j := by
    intro n
    constructor
    · intro hnN
      obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.mp hnN
      refine ⟨n'.property, fun x hx => ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp hn' ⟨x, hZQ hx⟩).mp hx
      exact this
    · rintro ⟨hnQ, hn⟩
      refine Subgroup.mem_map.mpr ⟨⟨n, hnQ⟩, ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx; exact hn x.1 hx
      · intro hx
        have hnx : n * x.1 * n⁻¹ ∈ centQ Q j := hx
        have hZfin : Finite (centQ Q j) := inferInstance
        have hinj : Function.Injective (fun y : centQ Q j => (⟨n * y.1 * n⁻¹, hn y.1 y.2⟩ :
            centQ Q j)) := by
          intro y₁ y₂ h
          simp only [Subtype.mk.injEq] at h
          exact Subtype.ext (by simpa using h)
        have hsurj := Finite.surjective_of_injective hinj
        obtain ⟨y, hy⟩ := hsurj ⟨n * x.1 * n⁻¹, hnx⟩
        have hyx : y.1 = x.1 := by
          have := congrArg Subtype.val hy
          simp only at this
          have := congrArg (fun w => n⁻¹ * w * n) this
          simpa [mul_assoc] using this
        change x.1 ∈ centQ Q j
        rw [← hyx]; exact y.2
  let T := pairStab G a b
  let X : Set G := {n | n ∈ N ∧ n ∉ centQ Q j}
  have hTN : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    intro t ht n hn
    rw [memN] at hn ⊢
    refine ⟨hQ.normal t ht.1 n hn.1, fun x hx => ?_⟩
    have h1 : t⁻¹ * x * t⁻¹⁻¹ ∈ centQ Q j :=
      hQ.conj_mem_centQ hcomm hj (T.inv_mem ht) hx
    have h2 := hn.2 _ h1
    have h3 := hQ.conj_mem_centQ hcomm hj ht h2
    have : t * (n * (t⁻¹ * x * t⁻¹⁻¹) * n⁻¹) * t⁻¹ = (t * n * t⁻¹) * x * (t * n * t⁻¹)⁻¹ := by
      group
    rw [← this]; exact h3
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
  have hZlt : centQ Q j < N := by
    refine lt_of_le_of_ne hZN ?_
    intro heq
    apply (lt_irrefl Z')
    calc Z' < (Subgroup.normalizer (Z' : Set Q)) := hlt
      _ ≤ Z' := by
        intro x hx
        have : (x : G) ∈ N := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        rw [← heq] at this
        exact this
  have hNgt : q < Nat.card N := by
    rw [← hZ]; exact Subgroup.card_lt_of_lt hZlt
  have hkf : f < k := by
    by_contra h
    push Not at h
    have : Nat.card N ≤ q := by rw [hNk, hqdef]; exact Nat.pow_le_pow_right (by omega) h
    omega
  obtain ⟨i, rfl⟩ : ∃ i, k = f + i := ⟨k - f, by omega⟩
  have hNi : Nat.card N = q * p ^ i := by rw [hNk, pow_add]
  have hTi : Nat.card T ∣ p ^ i - 1 := by
    rw [hXcard, hNi] at hdvd
    have h2 : q * p ^ i - q = q * (p ^ i - 1) := by rw [Nat.mul_sub, mul_one]
    rw [h2] at hdvd
    have hcop : Nat.Coprime (Nat.card T) q := by
      have hdvdT : Nat.card T ∣ p ^ (2 * f) - 1 := hTdvd
      have : Nat.Coprime (p ^ (2 * f) - 1) q := by
        rw [hqdef]
        apply Nat.Coprime.pow_right
        have h3 : p ^ (2 * f) - 1 + 1 = p ^ (2 * f) := by
          have : 1 ≤ p ^ (2 * f) := Nat.one_le_pow _ _ (by omega)
          omega
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpp]
        intro hdv
        have h4 : p ∣ p ^ (2 * f) := dvd_pow_self p (by omega)
        have h5 : p ∣ p ^ (2 * f) - (p ^ (2 * f) - 1) := Nat.dvd_sub h4 hdv
        have : p ^ (2 * f) - (p ^ (2 * f) - 1) = 1 := by omega
        rw [this] at h5
        exact hpp.one_lt.ne' (Nat.dvd_one.mp h5)
      exact Nat.Coprime.coprime_dvd_left hdvdT this
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hi : i = 2 * f := by
    have hi3 : i ≤ 2 * f := by omega
    by_contra hne
    have hlt2 : i < 2 * f := lt_of_le_of_ne hi3 hne
    have hipos : 1 ≤ i := by omega
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
  have hNcard : Nat.card N = Nat.card Q := by rw [hNi, hi, hQcard, hqdef, ← pow_add]; ring_nf
  have hNeq : N = Q := Subgroup.eq_of_le_of_card_ge hNQ (le_of_eq hNcard.symm)
  have huN : u ∈ N := by rw [hNeq]; exact huQ
  exact ((memN u).mp huN).2 z hz

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
