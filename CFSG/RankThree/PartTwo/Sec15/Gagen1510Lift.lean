module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse

open scoped Pointwise

private lemma complement_facts {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K Q : Subgroup G} (hK : ¬ p ∣ Nat.card K) (hQ : IsPGroup p Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    K ⊓ Q = ⊥ ∧ (↑(K ⊔ Q) : Set G) = Q * K ∧
      Nat.card ↥(K ⊔ Q) = Nat.card K * Nat.card Q := by
  classical
  have hKQ : K ⊓ Q = ⊥ := by
    have hp : IsPGroup p ↥(K ⊓ Q) := hQ.to_le inf_le_right
    have hdvd : Nat.card ↥(K ⊓ Q) ∣ Nat.card K :=
      Subgroup.card_dvd_of_le inf_le_left
    rcases hp.card_eq_or_dvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exact absurd (h.trans hdvd) hK
  have hcoe : (↑(K ⊔ Q) : Set G) = Q * K := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right Q K hQK
  let H : Subgroup G := K ⊔ Q
  have hKH : K ≤ H := le_sup_left
  have hQH : Q ≤ H := le_sup_right
  have hcoeH : (↑H : Set G) = Q * K := by
    dsimp [H]
    exact hcoe
  have hcompl : (Q.subgroupOf H).IsComplement' (K.subgroupOf H) := by
    rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_bijective]
    constructor
    · rintro ⟨⟨q1, hq1⟩, ⟨k1, hk1⟩⟩ ⟨⟨q2, hq2⟩, ⟨k2, hk2⟩⟩ heq
      have heqG : (q1 : G) * (k1 : G) = (q2 : G) * (k2 : G) :=
        congrArg Subtype.val heq
      have hmem : (q2 : G)⁻¹ * (q1 : G) = (k2 : G) * (k1 : G)⁻¹ := by
        have h := congrArg (fun x : G => (q2 : G)⁻¹ * x * (k1 : G)⁻¹) heqG
        simpa [mul_assoc] using h
      have hQ' : (q2 : G)⁻¹ * (q1 : G) ∈ Q := Q.mul_mem (Q.inv_mem hq2) hq1
      have hK' : (q2 : G)⁻¹ * (q1 : G) ∈ K := by
        rw [hmem]
        exact K.mul_mem hk2 (K.inv_mem hk1)
      have hone : (q2 : G)⁻¹ * (q1 : G) = 1 := by
        have hbot : (q2 : G)⁻¹ * (q1 : G) ∈ (⊥ : Subgroup G) := by
          rw [← hKQ]
          exact ⟨hK', hQ'⟩
        simpa using hbot
      have hq : q1 = q2 := by
        apply Subtype.ext
        calc (q1 : G) = (q2 : G) * ((q2 : G)⁻¹ * (q1 : G)) := by group
          _ = (q2 : G) := by rw [hone, mul_one]
      have hk : k1 = k2 := by
        apply Subtype.ext
        rw [hq] at heqG
        exact mul_left_cancel heqG
      exact Prod.ext (Subtype.ext hq) (Subtype.ext hk)
    · intro z
      have hz : (z : G) ∈ (Q : Set G) * (K : Set G) := by
        rw [← hcoeH]
        exact z.2
      obtain ⟨q, hqQ, k, hkK, hqk⟩ := Set.mem_mul.mp hz
      have hqH : q ∈ H := hQH hqQ
      have hkH : k ∈ H := hKH hkK
      refine ⟨(⟨⟨q, hqH⟩, Subgroup.mem_subgroupOf.mpr hqQ⟩,
        ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hkK⟩), ?_⟩
      exact Subtype.ext hqk
  have hcardQH : Nat.card (Q.subgroupOf H) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hcardKH : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hcardH : Nat.card H = Nat.card K * Nat.card Q := by
    have h := hcompl.card_mul_card
    rw [hcardQH, hcardKH] at h
    rw [← h, Nat.mul_comm]
  exact ⟨hKQ, hcoe, by simpa [H] using hcardH⟩

private lemma exists_sylow_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K Q : Subgroup G} (hK : ¬ p ∣ Nat.card K) (hQ : IsPGroup p Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) {h : G} (f : G → G)
    (hfQ : ∀ q ∈ Q, f q ∈ Q) (hf : ∀ q ∈ Q, h * q * h⁻¹ * (f q)⁻¹ ∈ K) :
    ∃ m : ↥(K ⊔ Q),
      (Q.map (MulAut.conj h).toMonoidHom).map (MulAut.conj (m : G)).toMonoidHom = Q ∧
      ∃ q' ∈ Q, ∃ n ∈ K, q' * n = (m : G) := by
  classical
  obtain ⟨-, hcoe, hcardH⟩ := complement_facts hK hQ hQK
  let H : Subgroup G := K ⊔ Q
  have hKH : K ≤ H := le_sup_left
  have hQH : Q ≤ H := le_sup_right
  have hcoeH : (↑H : Set G) = Q * K := by
    dsimp [H]
    exact hcoe
  have hcardH' : Nat.card H = Nat.card K * Nat.card Q := by
    dsimp [H]
    exact hcardH
  have hQHp : IsPGroup p (Q.subgroupOf H) := hQ.comap_subtype
  have hcardQH : Nat.card (Q.subgroupOf H) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hQHindex : ¬ p ∣ (Q.subgroupOf H).index := by
    have h := (Q.subgroupOf H).index_mul_card
    rw [hcardQH, hcardH'] at h
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have hidx : (Q.subgroupOf H).index = Nat.card K :=
      Nat.eq_of_mul_eq_mul_right hpos h
    rw [hidx]
    exact hK
  let Pq : Sylow p ↥H := hQHp.toSylow hQHindex
  have hPq : (Pq : Subgroup ↥H) = Q.subgroupOf H := IsPGroup.toSylow_coe hQHp hQHindex
  set R : Subgroup G := Q.map (MulAut.conj h).toMonoidHom with hRdef
  have hRH : R ≤ H := by
    rintro _ ⟨q, hq, rfl⟩
    have hk : h * q * h⁻¹ * (f q)⁻¹ ∈ K := hf q hq
    have hfq : f q ∈ Q := hfQ q hq
    have hmem := (K ⊔ Q).mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hfq)
    have heq : h * q * h⁻¹ = (h * q * h⁻¹ * (f q)⁻¹) * f q := by group
    change h * q * h⁻¹ ∈ (K ⊔ Q : Subgroup G)
    rw [heq]
    exact hmem
  have hRp : IsPGroup p R := hQ.map (MulAut.conj h).toMonoidHom
  have hRHp : IsPGroup p (R.subgroupOf H) := hRp.comap_subtype
  have hcardR : Nat.card R = Nat.card Q := by
    rw [hRdef, Subgroup.card_map_of_injective (MulAut.conj h).injective]
  have hcardRH : Nat.card (R.subgroupOf H) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hRHindex : ¬ p ∣ (R.subgroupOf H).index := by
    have h := (R.subgroupOf H).index_mul_card
    rw [hcardRH, hcardR, hcardH'] at h
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have hidx : (R.subgroupOf H).index = Nat.card K :=
      Nat.eq_of_mul_eq_mul_right hpos h
    rw [hidx]
    exact hK
  let Pr : Sylow p ↥H := hRHp.toSylow hRHindex
  have hPr : (Pr : Subgroup ↥H) = R.subgroupOf H := IsPGroup.toSylow_coe hRHp hRHindex
  obtain ⟨m, hm⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥H) Pr Pq
  have hm' : (R.subgroupOf H).map (MulAut.conj m).toMonoidHom = Q.subgroupOf H := by
    have h := congrArg (fun s : Sylow p ↥H => (s : Subgroup ↥H)) hm
    rw [Sylow.coe_subgroup_smul, hPr, hPq, Subgroup.pointwise_smul_def] at h
    exact h
  have hmG : R.map (MulAut.conj (m : G)).toMonoidHom = Q := by
    have h := congrArg (Subgroup.map H.subtype) hm'
    rw [Subgroup.map_map] at h
    rw [show H.subtype.comp (MulAut.conj m).toMonoidHom =
        (MulAut.conj (m : G)).toMonoidHom.comp H.subtype by
      ext x
      simp [MulAut.conj_apply], ← Subgroup.map_map] at h
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRH,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQH] at h
    exact h
  have hmH : (m : G) ∈ (Q : Set G) * (K : Set G) := by
    rw [← hcoeH]
    exact m.2
  obtain ⟨q', hq'Q, n, hnK, hmn⟩ := Set.mem_mul.mp hmH
  exact ⟨m, by simpa [hRdef] using hmG, q', hq'Q, n, hnK, hmn⟩

theorem exists_mul_conj_eq_of_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K Q : Subgroup G} (hK : ¬ p ∣ Nat.card K) (hQ : IsPGroup p Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) {h : G} (f : G → G)
    (hfQ : ∀ q ∈ Q, f q ∈ Q) (hf : ∀ q ∈ Q, h * q * h⁻¹ * (f q)⁻¹ ∈ K) :
    ∃ n ∈ K, ∀ q ∈ Q, n * h * q * (n * h)⁻¹ = f q := by
  classical
  obtain ⟨m, hmG, q', hq'Q, n, hnK, hmn⟩ :=
    exists_sylow_conj (f := f) hK hQ hQK hfQ hf
  have hconjQ : ∀ q ∈ Q, (m : G) * h * q * ((m : G) * h)⁻¹ ∈ Q := by
    intro q hq
    have hqR : h * q * h⁻¹ ∈ Q.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hq
    have hmem : (MulAut.conj (m : G)) (h * q * h⁻¹) ∈
        (Q.map (MulAut.conj h).toMonoidHom).map (MulAut.conj (m : G)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hqR
    rw [hmG] at hmem
    simpa [MulAut.conj_apply, mul_assoc] using hmem
  have hconjNQ : ∀ q ∈ Q, n * h * q * (n * h)⁻¹ ∈ Q := by
    intro q hq
    have h1 := hconjQ q hq
    have hmq : (m : G) * h * q * ((m : G) * h)⁻¹ =
        q' * (n * h * q * (n * h)⁻¹) * q'⁻¹ := by
      rw [← hmn]
      group
    have h2 : q' * (n * h * q * (n * h)⁻¹) * q'⁻¹ ∈ Q := by
      rw [← hmq]
      exact h1
    have hiso : n * h * q * (n * h)⁻¹ =
        q'⁻¹ * (q' * (n * h * q * (n * h)⁻¹) * q'⁻¹) * q' := by group
    rw [hiso]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq'Q) h2) hq'Q
  obtain ⟨hKQ, -, -⟩ := complement_facts hK hQ hQK
  have hHnorm : K ⊔ Q ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hQK
  refine ⟨n, hnK, fun q hq => ?_⟩
  have hzQ : n * h * q * (n * h)⁻¹ ∈ Q := hconjNQ q hq
  have hzK : n * h * q * (n * h)⁻¹ * (f q)⁻¹ ∈ K := by
    have h1 : h * q * h⁻¹ * (f q)⁻¹ ∈ K := hf q hq
    have hk1 : n * (h * q * h⁻¹ * (f q)⁻¹) * n⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hnK h1) (K.inv_mem hnK)
    have hfqH : f q ∈ K ⊔ Q := Subgroup.mem_sup_right (hfQ q hq)
    have hk2 : f q * n⁻¹ * (f q)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hHnorm hfqH) n⁻¹).mp (K.inv_mem hnK)
    have hk3 : n * f q * n⁻¹ * (f q)⁻¹ ∈ K := by
      have heq : n * f q * n⁻¹ * (f q)⁻¹ = n * (f q * n⁻¹ * (f q)⁻¹) := by group
      rw [heq]
      exact K.mul_mem hnK hk2
    have heq : n * h * q * (n * h)⁻¹ * (f q)⁻¹ =
        (n * (h * q * h⁻¹ * (f q)⁻¹) * n⁻¹) * (n * f q * n⁻¹ * (f q)⁻¹) := by
      rw [mul_inv_rev]
      group
    rw [heq]
    exact K.mul_mem hk1 hk3
  have hone : n * h * q * (n * h)⁻¹ * (f q)⁻¹ = 1 := by
    have hbot : n * h * q * (n * h)⁻¹ * (f q)⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hKQ]
      exact ⟨hzK, Q.mul_mem hzQ (Q.inv_mem (hfQ q hq))⟩
    simpa using hbot
  calc n * h * q * (n * h)⁻¹ = (n * h * q * (n * h)⁻¹ * (f q)⁻¹) * f q := by group
    _ = f q := by rw [hone, one_mul]

end CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse
