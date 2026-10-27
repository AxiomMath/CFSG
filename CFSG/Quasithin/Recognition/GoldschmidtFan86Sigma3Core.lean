module

public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open

structure Sig3 (H : Type*) [Group H] [Finite H] (S : Subgroup H) : Prop where
  two : IsPGroup 2 S
  card : Nat.card H = 3 * Nat.card S
  quot : Nonempty (H ⧸ CFSG.Open.pCore 2 H ≃* Equiv.Perm (Fin 3))

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H}

theorem oQ_two : IsPGroup 2 (CFSG.Open.pCore 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.pCore_isPGroup 2

theorem Sig3.card_Q (h : Sig3 H S) :
    Nat.card H = 6 * Nat.card (CFSG.Open.pCore 2 H) := by
  obtain ⟨e⟩ := h.quot
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 H)
  rw [h1, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card]
  simp [Nat.factorial]

theorem Sig3.card_S (h : Sig3 H S) :
    Nat.card S = 2 * Nat.card (CFSG.Open.pCore 2 H) := by
  have h1 := h.card_Q
  have h2 := h.card
  omega

theorem Sig3.index_S (h : Sig3 H S) : S.index = 3 := by
  have := Subgroup.card_mul_index S
  have hpos : 0 < Nat.card S := Nat.card_pos
  rw [h.card] at this
  exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)

theorem Sig3.Q_le_S (h : Sig3 H S) : CFSG.Open.pCore 2 H ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ¬ 2 ∣ S.index := by rw [h.index_S]; decide
  exact (oQ_two (H := H)).le_sylow_of_normal (h.two.toSylow hsyl)

theorem Sig3.exists_hom (h : Sig3 H S) :
    ∃ ψ : H →* Equiv.Perm (Fin 3), Function.Surjective ψ ∧ ψ.ker = CFSG.Open.pCore 2 H := by
  obtain ⟨e⟩ := h.quot
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 H)), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext g
    simp

theorem Sig3.exists_a (h : Sig3 H S) : ∃ a ∈ S, a ∉ CFSG.Open.pCore 2 H := by
  by_contra hcon
  push Not at hcon
  have hle : S ≤ CFSG.Open.pCore 2 H := hcon
  have := Subgroup.card_le_of_le hle
  have h2 := h.card_S
  have hpos : 0 < Nat.card (CFSG.Open.pCore 2 H) := Nat.card_pos
  omega

theorem perm3_inv : ∀ σ τ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 → τ ^ 3 = 1 → τ ≠ 1 →
    σ * τ * σ⁻¹ = τ⁻¹ := by
  decide

theorem Sig3.sq_mem (h : Sig3 H S) {a : H} (ha : a ∈ S) : a * a ∈ CFSG.Open.pCore 2 H := by
  obtain ⟨ψ, -, hker⟩ := h.exists_hom
  obtain ⟨n, hn⟩ := h.two ⟨a, ha⟩
  have han : a ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 : orderOf (ψ a) ∣ 2 ^ n := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, han, map_one]
  have h2 : orderOf (ψ a) ∣ 6 := by
    have := orderOf_dvd_natCard (ψ a)
    rwa [Nat.card_perm, Nat.card_eq_fintype_card] at this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    rw [← hj'] at h4
    have := h4.trans h2
    omega
  have hsq : (ψ a) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hj']
    exact pow_dvd_pow 2 hj1
  rw [← hker, MonoidHom.mem_ker, map_mul, ← pow_two]
  exact hsq

theorem Sig3.not_mem_Q_of_order {x : H} (hx : orderOf x = 3)
    (hS : x ∈ CFSG.Open.pCore 2 H) : False := by
  obtain ⟨n, hn⟩ := (oQ_two (H := H)) ⟨x, hS⟩
  have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 : 3 ∣ 2 ^ n := hx ▸ orderOf_dvd_of_pow_eq_one hxn
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  omega

theorem Sig3.inv_mod (h : Sig3 H S) {x : H} (hx : orderOf x = 3) {a : H} (ha : a ∈ S)
    (haQ : a ∉ CFSG.Open.pCore 2 H) :
    ∃ q ∈ CFSG.Open.pCore 2 H, a * x * a⁻¹ = q * x⁻¹ := by
  obtain ⟨ψ, -, hker⟩ := h.exists_hom
  have hsq := h.sq_mem ha
  rw [← hker, MonoidHom.mem_ker, map_mul] at hsq
  have haQ' : ψ a ≠ 1 := fun h1 => haQ (hker ▸ h1)
  have hxQ' : ψ x ≠ 1 := fun h1 => Sig3.not_mem_Q_of_order hx (hker ▸ h1)
  have hx3' : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx3 : (ψ x) ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
  have key := perm3_inv (ψ a) (ψ x) hsq haQ' hx3 hxQ'
  refine ⟨a * x * a⁻¹ * x, ?_, by group⟩
  rw [← hker, MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [key]
  group

theorem Sig3.gen (h : Sig3 H S) {x : H} (hx : orderOf x = 3) : S ⊔ Subgroup.zpowers x = ⊤ := by
  set M := S ⊔ Subgroup.zpowers x with hM
  have h1 : Nat.card S ∣ Nat.card M := Subgroup.card_dvd_of_le le_sup_left
  have h2 : 3 ∣ Nat.card M := by
    have : Nat.card (Subgroup.zpowers x) ∣ Nat.card M := Subgroup.card_dvd_of_le le_sup_right
    rwa [Nat.card_zpowers, hx] at this
  obtain ⟨k, hk⟩ := h.two.exists_card_eq
  have hcop : Nat.Coprime (Nat.card S) 3 := by
    rw [hk]
    exact Nat.Coprime.pow_left k (by decide)
  have h3 : Nat.card S * 3 ∣ Nat.card M := hcop.mul_dvd_of_dvd_of_dvd h1 h2
  have h4 : Nat.card H ∣ Nat.card M := by
    have : Nat.card H = Nat.card S * 3 := by rw [h.card]; ring
    rwa [this]
  exact Subgroup.eq_top_of_card_eq M (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card M) h4)

theorem Sig3.index_Q (h : Sig3 H S) :
    ((CFSG.Open.pCore 2 H).subgroupOf S).index = 2 := by
  have h1 := Subgroup.card_mul_index ((CFSG.Open.pCore 2 H).subgroupOf S)
  have h2 : Nat.card (((CFSG.Open.pCore 2 H).subgroupOf S)) = Nat.card (CFSG.Open.pCore 2 H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q_le_S).toEquiv
  rw [h2, h.card_S] at h1
  have hpos : 0 < Nat.card (CFSG.Open.pCore 2 H) := Nat.card_pos
  have : Nat.card (CFSG.Open.pCore 2 H) * ((CFSG.Open.pCore 2 H).subgroupOf S).index =
      Nat.card (CFSG.Open.pCore 2 H) * 2 := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem Sig3.mul_inv_mem (h : Sig3 H S) {s a : H} (hs : s ∈ S) (ha : a ∈ S)
    (haQ : a ∉ CFSG.Open.pCore 2 H) : s ∈ CFSG.Open.pCore 2 H ∨ s * a⁻¹ ∈ CFSG.Open.pCore 2 H := by
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.1 h.index_Q
  by_cases hsQ : s ∈ CFSG.Open.pCore 2 H
  · exact Or.inl hsQ
  · right
    have h1' : s * (c : H) ∈ CFSG.Open.pCore 2 H := by
      rcases hc ⟨s, hs⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Subgroup.mem_subgroupOf.1 h1
      · exact absurd (Subgroup.mem_subgroupOf.1 h1) hsQ
    have h2' : a * (c : H) ∈ CFSG.Open.pCore 2 H := by
      rcases hc ⟨a, ha⟩ with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Subgroup.mem_subgroupOf.1 h1
      · exact absurd (Subgroup.mem_subgroupOf.1 h1) haQ
    have : s * a⁻¹ = (s * c) * (a * c)⁻¹ := by group
    rw [this]
    exact (CFSG.Open.pCore 2 H).mul_mem h1' ((CFSG.Open.pCore 2 H).inv_mem h2')

end CFSG.Quasithin.Fan86.Sigma3
