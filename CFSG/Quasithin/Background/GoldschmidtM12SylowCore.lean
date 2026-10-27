module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Fam

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank AutM12Recog

namespace M12Sylow

structure TProps64 (T : Type) [Group T] : Prop where
  card : Nat.card T = 2 ^ 6
  exp : ∀ x : T, x ^ 8 = 1
  order8 : ∃ x : T, x ^ 4 ≠ 1
  rank : ∀ B : Subgroup T, IsElemAbelian 2 B → Nat.card B ≤ 8
  hasE8 : ∃ B : Subgroup T, IsElemAbelian 2 B ∧ Nat.card B = 8

theorem isElemAbelian_map {G H : Type} [Group G] [Group H] (f : G →* H)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) : IsElemAbelian 2 (B.map f) :=
  CFSG.SectionRank.isElemAbelian_map hB _

theorem TProps64.of_mulEquiv {T T' : Type} [Group T] [Group T'] (h : TProps64 T) (e : T ≃* T') :
    TProps64 T' where
  card := by rw [← Nat.card_congr e.toEquiv]; exact h.card
  exp := fun x => by
    have := h.exp (e.symm x)
    have h2 := congrArg e this
    rwa [map_pow, map_one, MulEquiv.apply_symm_apply] at h2
  order8 := by
    obtain ⟨x, hx⟩ := h.order8
    refine ⟨e x, fun h4 => hx ?_⟩
    apply e.injective
    rw [map_pow, h4, map_one]
  rank := fun B hB => by
    have h1 := h.rank (B.map e.symm.toMonoidHom) (isElemAbelian_map _ hB)
    rwa [Subgroup.card_map_of_injective e.symm.injective] at h1
  hasE8 := by
    obtain ⟨B, hB, hc⟩ := h.hasE8
    exact ⟨B.map e.toMonoidHom, isElemAbelian_map _ hB,
      by rw [Subgroup.card_map_of_injective e.injective, hc]⟩

@[expose] def Excl64 (K : Type) [Group K] [Finite K] : Prop :=
  ∀ (T : Type) [Group T] [Finite T], TProps64 T → ∀ (Q : Sylow 2 K) (n : ℕ) (N : Subgroup T),
    Nonempty (↥(Q : Subgroup K) ≃* ↥N) → Nat.card T = Nat.card N * 2 ^ n →
    Nat.card K * 2 ^ n ∣ Nat.card (MulAut K) → False

theorem Excl64.of_equiv {K' : Type} [Group K'] [Finite K'] (h : Excl64 K') {K : Type} [Group K]
    [Finite K] (e : K ≃* K') : Excl64 K := by
  intro T _ _ hT Q n N hQN hc hA
  obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv e Q
  refine h T hT Q' n N ⟨ι.symm.trans hQN.some⟩ hc ?_
  rwa [← Nat.card_congr e.toEquiv, ← Nat.card_congr (MulAut.congr e).toEquiv]

section Criteria

variable {K : Type} [Group K] {T : Type} [Group T]

theorem card_mul_two_pow (hT : TProps64 T) (Q : Subgroup K) (n : ℕ) (N : Subgroup T)
    (hQN : Nonempty (↥Q ≃* ↥N)) (hc : Nat.card T = Nat.card N * 2 ^ n) :
    Nat.card Q * 2 ^ n = 2 ^ 6 := by
  rw [← hT.card, hc, Nat.card_congr hQN.some.toEquiv]

theorem card_sylow_eq {a m : ℕ} [Finite K] (hm : Odd m) (hK : Nat.card K = 2 ^ a * m)
    (Q : Sylow 2 K) : Nat.card ↥(Q : Subgroup K) = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(Q : Subgroup K) = 2 ^ (Nat.card K).factorization 2 :=
    Sylow.card_eq_multiplicity Q
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h2 : (Nat.card K).factorization 2 = a := by
    rw [hK, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hm.not_two_dvd_nat)]
    simp
  rw [h1, h2]

end Criteria

theorem excl64_of_card {K : Type} [Group K] [Finite K] {a : ℕ} (ha : 7 ≤ a)
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ a * m) : Excl64 K := by
  intro T _ _ hT Q n N hQN hc _
  obtain ⟨m, hm, hK⟩ := hK
  have h1 := card_sylow_eq hm hK Q
  have h3 := card_mul_two_pow hT (Q : Subgroup K) n N hQN hc
  rw [h1] at h3
  have h4 : 2 ^ 7 ≤ 2 ^ 6 := by
    calc 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
      _ ≤ 2 ^ a * 2 ^ n := Nat.le_mul_of_pos_right _ (by positivity)
      _ = 2 ^ 6 := h3
  omega

theorem excl64_of_card_two_part {K : Type} [Group K] [Finite K] {m N : ℕ}
    (hK : Nat.card K = m) (hm : ∃ r : ℕ, Odd r ∧ m = 2 ^ N * r) (hN : 7 ≤ N) : Excl64 K := by
  obtain ⟨r, hr, hmr⟩ := hm
  exact excl64_of_card hN ⟨r, hr, hK.trans hmr⟩

theorem excl64_of_aut_le {K : Type} [Group K] [Finite K] {a c : ℕ}
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ a * m) (ha : a ≤ 6) (hc : c < 2 ^ (6 - a))
    (hAut : ∀ n : ℕ, Nat.card K * 2 ^ n ∣ Nat.card (MulAut K) → 2 ^ n ≤ c) : Excl64 K := by
  intro T _ _ hT Q n N hQN hcard hA
  obtain ⟨m, hm, hK⟩ := hK
  have h1 := card_sylow_eq hm hK Q
  have h3 := card_mul_two_pow hT (Q : Subgroup K) n N hQN hcard
  rw [h1, ← pow_add] at h3
  have h4 : a + n = 6 := Nat.pow_right_injective le_rfl h3
  have h5 : n = 6 - a := by omega
  have h6 : 2 ^ n ≤ c := hAut n hA
  rw [h5] at h6
  omega

theorem excl64_of_outer_le {K : Type} [Group K] [Finite K] {a c : ℕ}
    (hK : ∃ m : ℕ, Odd m ∧ Nat.card K = 2 ^ a * m) (ha : a ≤ 6) (hc : c < 2 ^ (6 - a))
    (hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) ≤ c) :
    Excl64 K := by
  refine excl64_of_aut_le hK ha hc fun n h => ?_
  have : Finite (MulAut K) := inferInstance
  have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) :=
    Nat.card_pos
  exact (Nat.le_of_dvd hpos (dvd_card_outer_of_dvd_card_mulAut h)).trans hOut

theorem excl64_of_orderOf_sixteen {K : Type} [Group K] [Finite K] {g : K} {k : ℕ} (hk : 4 ≤ k)
    (hg : orderOf g = 2 ^ k) : Excl64 K := by
  intro T _ _ hT Q n N hQN hcard hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgp : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hg])
  obtain ⟨Q', hgQ'⟩ := hgp.exists_le_sylow
  let y : ↥(Q' : Subgroup K) := ⟨g, hgQ' (Subgroup.mem_zpowers g)⟩
  let z : ↥(Q : Subgroup K) := Sylow.equiv Q' Q y
  have hz : orderOf z = 2 ^ k := by
    rw [MulEquiv.orderOf_eq]
    show orderOf y = 2 ^ k
    rw [← hg, ← Subgroup.orderOf_coe]
  have h8 : z ^ 8 = 1 := by
    have := hT.exp (embed _ N hQN z)
    rw [← map_pow] at this
    exact embed_injective _ N hQN (by rw [this, map_one])
  have h3 := orderOf_dvd_of_pow_eq_one h8
  rw [hz] at h3
  have h16 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem excl64_of_hasE16 {K : Type} [Group K] [Finite K]
    (h : ∀ Q : Sylow 2 K, ∃ B : Subgroup ↥(Q : Subgroup K), IsElemAbelian 2 B ∧ Nat.card B = 16) :
    Excl64 K := by
  intro T _ _ hT Q n N hQN hcard hA
  obtain ⟨B, hB, hc⟩ := h Q
  have h1 := hT.rank (B.map (embed (Q : Subgroup K) N hQN)) (isElemAbelian_map _ hB)
  rw [Subgroup.card_map_of_injective (embed_injective _ N hQN), hc] at h1
  omega

end M12Sylow

end CFSG.Quasithin.F6
