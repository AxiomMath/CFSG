module

public import CFSG.Permutation.UnitaryThreeRecognition.ClassTwo

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem pow_mul_eq_aux {x y c : G} (hyx : y * x = c * x * y)
    (hcy : c * y = y * c) : ∀ n : ℕ, y ^ n * x = c ^ n * x * y ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mul_eq_aux hyx hcy n
    have hcyn : c ^ n * y = y * c ^ n := ((Commute.pow_left hcy n)).eq
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (c ^ n * x * y ^ n) := by rw [ih]
      _ = (y * c ^ n) * x * y ^ n := by group
      _ = (c ^ n * y) * x * y ^ n := by rw [hcyn]
      _ = c ^ n * (y * x) * y ^ n := by group
      _ = c ^ n * (c * x * y) * y ^ n := by rw [hyx]
      _ = c ^ (n + 1) * x * y ^ (n + 1) := by group

theorem mul_pow_eq_of_commute_comm {x y c : G} (hyx : y * x = c * x * y) (hcx : c * x = x * c)
    (hcy : c * y = y * c) : ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n * c ^ n.choose 2
  | 0 => by simp
  | n + 1 => by
    have ih := mul_pow_eq_of_commute_comm hyx hcx hcy n
    have h1 := pow_mul_eq_aux hyx hcy n
    have hcN : c ^ n.choose 2 * x = x * c ^ n.choose 2 := (Commute.pow_left hcx _).eq
    have hcN' : c ^ n.choose 2 * y = y * c ^ n.choose 2 := (Commute.pow_left hcy _).eq
    have hcX : c ^ n * (x ^ (n + 1) * y ^ (n + 1)) = x ^ (n + 1) * y ^ (n + 1) * c ^ n :=
      ((Commute.pow_pow hcx n (n + 1)).mul_right (Commute.pow_pow hcy n (n + 1))).eq
    have hcxn : c ^ n * x ^ n = x ^ n * c ^ n := (Commute.pow_pow hcx n n).eq
    have hch : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * y ^ n * (c ^ n.choose 2 * x) * y := by rw [ih]; group
      _ = x ^ n * (y ^ n * x) * (c ^ n.choose 2 * y) := by rw [hcN]; group
      _ = (x ^ n * c ^ n) * x * (y ^ n * y) * c ^ n.choose 2 := by rw [h1, hcN']; group
      _ = c ^ n * (x ^ (n + 1) * y ^ (n + 1)) * c ^ n.choose 2 := by rw [← hcxn]; group
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + 1).choose 2 := by rw [hcX, hch]; group

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem pow_prime_centQ [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {z : G} (hz : z ∈ centQ Q j) : z ^ p = 1 := by
  classical
  by_cases hz1 : z = 1
  · rw [hz1, one_pow]
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  have hZ := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard
    hΩcard hTdvd
  let : Fact p.Prime := ⟨hpp⟩
  have hpZ : p ∣ Nat.card (centQ Q j) := by rw [hZ]; exact dvd_pow_self p (by omega)
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' p hpZ
  have hz₀p : (z₀ : G) ^ p = 1 := by
    have : z₀ ^ p = 1 := by rw [← hz₀]; exact pow_orderOf_eq_one z₀
    exact congrArg Subtype.val this
  have hz₀1 : (z₀ : G) ≠ 1 := by
    intro h
    have : z₀ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz₀
    exact hpp.one_lt.ne hz₀
  obtain ⟨t, _, htz⟩ := hQ.exists_conj_eq_of_mem_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp
    hf hpodd hd hQcard hΩcard hTcard hsa hs2 z₀.2 hz₀1 hz hz1
  rw [← htz, conj_pow, hz₀p, mul_one, mul_inv_cancel]

theorem mul_pow_prime [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
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
    {x : G} (hx : x ∈ Q) {y : G} (hy : y ∈ Q) : (x * y) ^ p = x ^ p * y ^ p := by
  set c := y * x * y⁻¹ * x⁻¹ with hcdef
  have hcZ : c ∈ centQ Q j := hQ.commutator_mem_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp
    hf hpodd hd hd3 hQcard hΩcard hTcard hsa hs2 hy hx
  have hcx : c * x = x * c := (hQ.centQ_commute hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf
    hpodd hd hd3 hQcard hΩcard hTcard hsa hs2 hx hcZ).symm
  have hcy : c * y = y * c := (hQ.centQ_commute hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf
    hpodd hd hd3 hQcard hΩcard hTcard hsa hs2 hy hcZ).symm
  have hyx : y * x = c * x * y := by rw [hcdef]; group
  rw [mul_pow_eq_of_commute_comm hyx hcx hcy p]
  have hcp : c ^ p = 1 := hQ.pow_prime_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd
    hd hQcard hΩcard hTcard hsa hs2 hcZ
  obtain ⟨m, hm⟩ := hpodd
  have hch : p.choose 2 = p * m := by
    rw [Nat.choose_two_right, hm]
    have : (2 * m + 1) * (2 * m + 1 - 1) = 2 * ((2 * m + 1) * m) := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hch, pow_mul, hcp, one_pow, mul_one]

theorem pow_prime_eq_one [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
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
    {x : G} (hx : x ∈ Q) : x ^ p = 1 := by
  classical
  set Z := centQ Q j with hZdef
  have hZQ : Z ≤ Q := inf_le_left
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  have hZcard := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard
    hΩcard hTdvd
  have hcen : ∀ u ∈ Q, ∀ z ∈ Z, u * z = z * u := fun u hu z hz =>
    hQ.centQ_commute hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hd3 hQcard hΩcard
      hTcard hsa hs2 hu hz
  have hmulp : ∀ u ∈ Q, ∀ v ∈ Q, (u * v) ^ p = u ^ p * v ^ p := fun u hu v hv =>
    hQ.mul_pow_prime hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hd3 hQcard hΩcard
      hTcard hsa hs2 hu hv
  have hZp : ∀ z ∈ Z, z ^ p = 1 := fun z hz =>
    hQ.pow_prime_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hQcard hΩcard
      hTcard hsa hs2 hz
  have hirr := fun N hZN hNQ hTN => hQ.eq_centQ_or_eq_of_conj_mem hb htwo hfaith hcomm hj hj2
    hj1 hsq hpp hp hf hpodd hd hd3 hQcard hΩcard hTcard hsa hs2 N hZN hNQ hTN
  have hq : 3 ≤ p ^ f := le_trans hp (Nat.le_self_pow (by omega) p)
  have hZlt : Nat.card Z < Nat.card Q := by
    rw [hZcard, hQcard]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hnotle : ¬ Q ≤ Z := fun h => by
    have := Subgroup.card_le_of_le h
    omega
  let M : Subgroup G :=
    { carrier := {y | ∃ u ∈ Q, ∃ z ∈ Z, y = u ^ p * z}
      mul_mem' := by
        rintro y₁ y₂ ⟨u₁, hu₁, z₁, hz₁, rfl⟩ ⟨u₂, hu₂, z₂, hz₂, rfl⟩
        refine ⟨u₁ * u₂, Q.mul_mem hu₁ hu₂, z₁ * z₂, Z.mul_mem hz₁ hz₂, ?_⟩
        have h1 : z₁ * u₂ ^ p = u₂ ^ p * z₁ := (hcen _ (Q.pow_mem hu₂ p) z₁ hz₁).symm
        rw [hmulp u₁ hu₁ u₂ hu₂]
        calc u₁ ^ p * z₁ * (u₂ ^ p * z₂) = u₁ ^ p * (z₁ * u₂ ^ p) * z₂ := by group
          _ = u₁ ^ p * (u₂ ^ p * z₁) * z₂ := by rw [h1]
          _ = u₁ ^ p * u₂ ^ p * (z₁ * z₂) := by group
      one_mem' := ⟨1, Q.one_mem, 1, Z.one_mem, by simp⟩
      inv_mem' := by
        rintro y ⟨u, hu, z, hz, rfl⟩
        refine ⟨u⁻¹, Q.inv_mem hu, z⁻¹, Z.inv_mem hz, ?_⟩
        have h1 : z⁻¹ * (u ^ p)⁻¹ = (u ^ p)⁻¹ * z⁻¹ :=
          (hcen _ (Q.inv_mem (Q.pow_mem hu p)) _ (Z.inv_mem hz)).symm
        rw [mul_inv_rev, h1, inv_pow] }
  have hZM : Z ≤ M := fun z hz => ⟨1, Q.one_mem, z, hz, by simp⟩
  have hMQ : M ≤ Q := by
    rintro y ⟨u, hu, z, hz, rfl⟩
    exact Q.mul_mem (Q.pow_mem hu p) (hZQ hz)
  have hTM : ∀ t ∈ pairStab G a b, ∀ n ∈ M, t * n * t⁻¹ ∈ M := by
    rintro t ht n ⟨u, hu, z, hz, rfl⟩
    refine ⟨t * u * t⁻¹, hQ.normal t ht.1 u hu, t * z * t⁻¹,
      hQ.conj_mem_centQ hcomm hj ht hz, ?_⟩
    rw [conj_pow]
    group
  have hMZ : M = Z := by
    rcases hirr M hZM hMQ hTM with h | hMQ'
    · exact h
    · exfalso
      apply hnotle
      have key : ∀ n : ℕ, ∀ y ∈ Q, ∃ u ∈ Q, ∃ z ∈ Z, y = u ^ (p ^ n) * z := by
        intro n
        induction n with
        | zero => intro y hy; exact ⟨y, hy, 1, Z.one_mem, by simp⟩
        | succ n ih =>
          intro y hy
          obtain ⟨u, hu, z, hz, rfl⟩ := ih y hy
          have huM : u ∈ M := by rw [hMQ']; exact hu
          obtain ⟨v, hv, z', hz', rfl⟩ := huM
          refine ⟨v, hv, z' ^ (p ^ n) * z, Z.mul_mem (Z.pow_mem hz' _) hz, ?_⟩
          have hc : Commute (v ^ p) z' := hcen _ (Q.pow_mem hv p) z' hz'
          rw [hc.mul_pow, ← pow_mul, ← pow_succ']
          group
      intro y hy
      obtain ⟨u, hu, z, hz, rfl⟩ := key (3 * f) y hy
      have hu1 : u ^ (p ^ (3 * f)) = 1 := by
        have h1 : (⟨u, hu⟩ : Q) ^ Nat.card Q = 1 := pow_card_eq_one'
        rw [hQcard] at h1
        exact congrArg Subtype.val h1
      rw [hu1, one_mul]
      exact hz
  have hpowZ : ∀ u ∈ Q, u ^ p ∈ Z := by
    intro u hu
    have : u ^ p ∈ M := ⟨u, hu, 1, Z.one_mem, by simp⟩
    rw [hMZ] at this
    exact this
  let K : Subgroup G :=
    { carrier := {y | y ∈ Q ∧ y ^ p = 1}
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, e₁⟩ ⟨hy₂, e₂⟩
        exact ⟨Q.mul_mem hy₁ hy₂, by rw [hmulp y₁ hy₁ y₂ hy₂, e₁, e₂, one_mul]⟩
      one_mem' := ⟨Q.one_mem, one_pow p⟩
      inv_mem' := by
        rintro y ⟨hy, e⟩
        exact ⟨Q.inv_mem hy, by rw [inv_pow, e, inv_one]⟩ }
  have hZK : Z ≤ K := fun z hz => ⟨hZQ hz, hZp z hz⟩
  have hKQ : K ≤ Q := fun y hy => hy.1
  have hTK : ∀ t ∈ pairStab G a b, ∀ n ∈ K, t * n * t⁻¹ ∈ K := by
    rintro t ht n ⟨hn, e⟩
    exact ⟨hQ.normal t ht.1 n hn, by rw [conj_pow, e, mul_one, mul_inv_cancel]⟩
  rcases hirr K hZK hKQ hTK with hKZ | hKQ'
  · exfalso
    let π : Q →* Q := MonoidHom.mk' (fun u => u ^ p) (fun u v => Subtype.ext (by
      change ((u * v : Q) : G) ^ p = (u : G) ^ p * (v : G) ^ p
      exact hmulp u u.2 v v.2))
    have hker : Nat.card π.ker ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective (fun u => ⟨u.1.1, ?_⟩) ?_
      · have hu : (u.1 : G) ∈ K := ⟨u.1.2, congrArg Subtype.val (MonoidHom.mem_ker.mp u.2)⟩
        rw [hKZ] at hu
        exact hu
      · intro u₁ u₂ h
        have h' : (u₁.1 : G) = u₂.1 := by
          have := congrArg (fun w : Z => (w : G)) h
          simpa using this
        exact Subtype.ext (Subtype.ext h')
    have hrange : Nat.card π.range ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective (fun u => ⟨u.1.1, ?_⟩) ?_
      · obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp u.2
        have : (u.1 : G) = (v : G) ^ p := by rw [← hv]; rfl
        rw [this]
        exact hpowZ v v.2
      · intro u₁ u₂ h
        have h' : (u₁.1 : G) = u₂.1 := by
          have := congrArg (fun w : Z => (w : G)) h
          simpa using this
        exact Subtype.ext (Subtype.ext h')
    have htot := Subgroup.card_ker_mul_card_range π
    have hle : Nat.card Q ≤ Nat.card Z * Nat.card Z := by
      rw [← htot]; exact Nat.mul_le_mul hker hrange
    rw [hQcard, hZcard] at hle
    have : p ^ (3 * f) = p ^ f * p ^ f * p ^ f := by ring_nf
    rw [this] at hle
    have h1 : p ^ f * p ^ f * 1 < p ^ f * p ^ f * p ^ f :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    omega
  · have : x ∈ K := by rw [hKQ']; exact hx
    exact this.2

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
