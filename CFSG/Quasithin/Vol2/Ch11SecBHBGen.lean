module

public import CFSG.Quasithin.Vol2.Ch5Sec1Hall

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_self (N : Subgroup G) : ⁅N, N⁆ ≤ N :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem ha hb) (N.inv_mem ha)) (N.inv_mem hb)

theorem le_normalizer_of_derived_le {N Y : Subgroup G} (hYN : Y ≤ N) (hC : ⁅N, N⁆ ≤ Y) :
    N ≤ Subgroup.normalizer (Y : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 := hC (Subgroup.commutator_mem_commutator hn (hYN hy))
    have := Y.mul_mem h1 hy
    simpa [commutatorElement_def, mul_assoc] using this
  · intro hy
    have h1 := hC (Subgroup.commutator_mem_commutator (N.inv_mem hn) (hYN hy))
    have := Y.mul_mem h1 hy
    simpa [commutatorElement_def, mul_assoc] using this

theorem mem_normalizer_of_map_conj_eq {B : Subgroup G} {g : G}
    (h : B.map (MulAut.conj g).toMonoidHom = B) : g ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom := ⟨y, hy, by simp⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨b, hb, hbe⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hbe
    have : b = y := by
      have := congrArg (fun z => g⁻¹ * z * g) hbe
      simpa [mul_assoc] using this
    exact this ▸ hb

variable [Finite G]

theorem exists_hall_of_commutator {X N T : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (h2 : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N)
    (hC : IsPGroup 2 ↥⁅N, N⁆) (hT : IsSylowTwoOf T X) :
    ∃ B : Subgroup G, Lin2.IsHallTwoPrimeOf B X ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      T ≤ pCoreOf 2 X ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := T ⊓ N with hQdef
  have hQ : IsSylowTwoOf Q N := B6.isSylowTwoOf_inf_normal hT hNX hXN
  have hQC : Q ≤ Subgroup.normalizer ((⁅N, N⁆ : Subgroup G) : Set G) :=
    hQ.1.trans ((le_sup_left : N ≤ N ⊔ N).trans (A3.sup_le_normalizer_commutator N N))
  have hQC2 : IsPGroup 2 ↥(Q ⊔ ⁅N, N⁆) := IsPGroup.to_sup_of_normal_right' hQ.2.1 hC hQC
  have hCQ : ⁅N, N⁆ ≤ Q := by
    have := F1.eq_of_isSylowTwoOf_le hQ (sup_le hQ.1 (commutator_le_self N)) hQC2 le_sup_left
    rw [this]
    exact le_sup_right
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_of_derived_le hQ.1 hCQ
  have hodd : ¬ 2 ∣ Q.relIndex N := hQ.2.2
  have hmapQ : ∀ x ∈ X, Q.map (MulAut.conj x).toMonoidHom ≤ Q := by
    intro x hx
    refine B6.le_of_isPGroup_of_odd_relIndex ?_ (hQ.2.1.map _) hQ.1 hNQ hodd
    rintro _ ⟨q, hq, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXN hx) q).mp (hQ.1 hq)
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact hmapQ x hx ⟨q, hq, rfl⟩
    · intro hq
      have := hmapQ x⁻¹ (X.inv_mem hx) ⟨_, hq, rfl⟩
      simpa [mul_assoc] using this
  have hQO : Q ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQ.1.trans hNX) hXQ hQ.2.1
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hQ.2.1
  have hoddR : Odd (Q.relIndex N) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hcop : Nat.Coprime (Nat.card Q) (Q.relIndex N) := by
    rw [ha]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hoddR)
  obtain ⟨B, hBN, hQB, hQBs, hBc, hBi⟩ := H13.exists_complement_of_coprime hQ.1 hNQ hcop
  have hBodd : Odd (Nat.card B) := hBc ▸ hoddR
  obtain ⟨b, hb⟩ := B6.exists_relIndex_eq_two_pow hXN h2
  have hBX : Lin2.IsHallTwoPrimeOf B X := by
    refine ⟨hBN.trans hNX, hBodd, a + b, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex B N X hBN hNX, hBi, ha, hb, pow_add]
  refine ⟨B, hBX, fun x hx y hy => ?_, ?_⟩
  ·
    have h1 : ⁅x, y⁆ ∈ ⁅B, B⁆ := Subgroup.commutator_mem_commutator hx hy
    have h2 : ⁅x, y⁆ ∈ Q ⊓ B :=
      ⟨hCQ (Subgroup.commutator_mono hBN hBN h1), commutator_le_self B h1⟩
    rw [hQB, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  ·
    intro t ht
    have htX : t ∈ X := hT.1 ht
    set B' := B.map (MulAut.conj t).toMonoidHom with hB'def
    have hB'N : B' ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hXN htX) y).mp (hBN hy)
    have hB'c : Nat.card B' = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    have hQB' : Q ⊓ B' = ⊥ := H13.inf_eq_bot_of_odd_of_isPGroup hQ.2.1 (hB'c ▸ hBodd)
    have hcN : Nat.card N = Nat.card Q * Nat.card B := by
      have h1 := Subgroup.relIndex_mul_card (H := B) (K := N)
      rw [inf_eq_left.mpr hBN, hBi] at h1
      rw [← h1, mul_comm]
    have hQB's : Q ⊔ B' = N := by
      refine le_antisymm (sup_le hQ.1 hB'N) (Subgroup.eq_of_le_of_card_ge (sup_le hQ.1 hB'N)
        ?_).ge
      have hd1 : Nat.card Q ∣ Nat.card ↥(Q ⊔ B') := Subgroup.card_dvd_of_le le_sup_left
      have hd2 : Nat.card B' ∣ Nat.card ↥(Q ⊔ B') := Subgroup.card_dvd_of_le le_sup_right
      have hcop' : Nat.Coprime (Nat.card Q) (Nat.card B') := by
        rw [ha, hB'c]
        exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hBodd)
      have hd := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop' hd1 hd2
      rw [hcN, ← hB'c]
      exact Nat.le_of_dvd Nat.card_pos hd
    obtain ⟨q, hqQ, hqB⟩ := H13.exists_mem_conj_of_complements hQ.1 hNQ hQ.2.1 hoddR hBN hQB
      hQBs hB'N hQB' hQB's
    have hqt : q⁻¹ * t ∈ Subgroup.normalizer (B : Set G) := by
      apply mem_normalizer_of_map_conj_eq
      have h1 : B.map (MulAut.conj (q⁻¹ * t)).toMonoidHom =
          (B.map (MulAut.conj t).toMonoidHom).map (MulAut.conj q⁻¹).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        ext y
        simp [MulAut.conj_apply, mul_assoc]
      rw [h1, ← hB'def, hqB, Subgroup.map_map]
      convert Subgroup.map_id B using 2
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    have hqT : q ∈ T := hqQ.1
    have hmem : q⁻¹ * t ∈ T ⊓ Subgroup.normalizer (B : Set G) :=
      ⟨T.mul_mem (T.inv_mem hqT) ht, hqt⟩
    have : t = q * (q⁻¹ * t) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (hQO hqQ) hmem

end CFSG.Quasithin.Vol2.Ch11.SecB
