module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.Quasithin.Loc442

open MulAction CFSG.Open

theorem free_card_dvd {Q α : Type*} [Group Q] [Finite Q] [MulAction Q α] [Finite α]
    (h : ∀ g : Q, g ≠ 1 → ∀ a : α, g • a ≠ a) : Nat.card Q ∣ Nat.card α := by
  classical
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite α
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Q α
  have hs : ∑ g : Q, Fintype.card (MulAction.fixedBy α g) = Fintype.card α := by
    rw [Finset.sum_eq_single (1 : Q)]
    · rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      simp [fixedBy_one_eq_univ]
    · intro g _ hg
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨a, ha⟩ => h g hg a ha⟩
    · simp
  rw [hs] at hb
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨_, by rw [hb, mul_comm]⟩

section Group8

variable {K : Type*} [Group K] (V : Subgroup K) (q : K)

def q8 (hqV : ∀ v ∈ V, q * v = v * q) (hq4 : q ^ 4 = 1) : Subgroup K where
  carrier := {g | ∃ a ∈ V, ∃ i : ℕ, g = a * q ^ i}
  mul_mem' := by
    rintro _ _ ⟨a, ha, i, rfl⟩ ⟨b, hb, j, rfl⟩
    refine ⟨a * b, V.mul_mem ha hb, i + j, ?_⟩
    have hc : q ^ i * b = b * q ^ i := (Commute.pow_left (show Commute q b from hqV b hb) i).eq
    calc a * q ^ i * (b * q ^ j) = a * (q ^ i * b) * q ^ j := by group
      _ = a * (b * q ^ i) * q ^ j := by rw [hc]
      _ = a * b * q ^ (i + j) := by rw [pow_add]; group
  one_mem' := ⟨1, V.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, ha, i, rfl⟩
    refine ⟨a⁻¹, V.inv_mem ha, 3 * i, ?_⟩
    have hc : q ^ i * a⁻¹ = a⁻¹ * q ^ i :=
      (Commute.pow_left (show Commute q a⁻¹ from hqV a⁻¹ (V.inv_mem ha)) i).eq
    have h1 : q ^ (3 * i) * q ^ i = 1 := by
      rw [← pow_add, show 3 * i + i = 4 * i by ring, pow_mul, hq4, one_pow]
    calc (a * q ^ i)⁻¹ = (q ^ i)⁻¹ * a⁻¹ := by group
      _ = q ^ (3 * i) * a⁻¹ := by
        congr 1
        exact inv_eq_of_mul_eq_one_left h1
      _ = a⁻¹ * q ^ (3 * i) := by
        have hc3 : q ^ (3 * i) * a⁻¹ = a⁻¹ * q ^ (3 * i) :=
          (Commute.pow_left (show Commute q a⁻¹ from hqV a⁻¹ (V.inv_mem ha)) (3 * i)).eq
        exact hc3

variable {V q}

theorem le_q8 {hqV : ∀ v ∈ V, q * v = v * q} {hq4 : q ^ 4 = 1} : V ≤ q8 V q hqV hq4 :=
  fun a ha => ⟨a, ha, 0, by simp⟩

theorem q_mem_q8 {hqV : ∀ v ∈ V, q * v = v * q} {hq4 : q ^ 4 = 1} : q ∈ q8 V q hqV hq4 :=
  ⟨1, V.one_mem, 1, by simp⟩

end Group8

section Cosets

variable {K : Type*} [Group K] {X L : Subgroup K}

@[expose] def deltaSet (X L : Subgroup K) : Set (K ⧸ X) :=
  {c | ∃ l ∈ L, l ∉ X ∧ c = (l : K ⧸ X)}

theorem mk_eq_one_iff (l : K) : ((l : K ⧸ X) = ((1 : K) : K ⧸ X)) ↔ l ∈ X := by
  rw [QuotientGroup.eq]
  simp

theorem smul_ne_of_stronglyEmbedded [L.Normal]
    (hSE : fusionStronglyEmbedded ((X ⊓ L).subgroupOf L)) {w : K} (hwL : w ∈ L) (hwX : w ∈ X)
    (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) {c : K ⧸ X} (hc : c ∈ deltaSet X L) : w • c ≠ c := by
  obtain ⟨l, hl, hlX, rfl⟩ := hc
  intro h
  have h' : ((w * l : K) : K ⧸ X) = (l : K ⧸ X) := h
  rw [QuotientGroup.eq] at h'
  have hmem : l⁻¹ * w⁻¹ * l ∈ X := by simpa [mul_assoc] using h'
  have hmemL : l⁻¹ * w⁻¹ * l ∈ L := by
    have := (inferInstance : L.Normal).conj_mem w⁻¹ (L.inv_mem hwL) l⁻¹
    simpa using this
  set B' := (X ⊓ L).subgroupOf L with hB'
  have hlB' : (⟨l, hl⟩ : ↥L)⁻¹ ∉ B' := by
    intro hh
    exact hlX (by simpa [hB', Subgroup.mem_subgroupOf] using (B'.inv_mem hh))
  have hodd := hSE.2.2 _ hlB'
  have hwB : (⟨w, hwL⟩ : ↥L) ∈ B' := Subgroup.mem_subgroupOf.2 ⟨hwX, hwL⟩
  have hwB2 : (⟨w, hwL⟩ : ↥L) ∈ B'.map (MulAut.conj ((⟨l, hl⟩ : ↥L)⁻¹)⁻¹).toMonoidHom := by
    refine ⟨⟨l⁻¹ * w⁻¹ * l, hmemL⟩⁻¹, ?_, ?_⟩
    · refine B'.inv_mem (Subgroup.mem_subgroupOf.2 ⟨hmem, hmemL⟩)
    · apply Subtype.ext
      simp [MulAut.conj_apply, mul_assoc]
  have hin : (⟨w, hwL⟩ : ↥L) ∈ B' ⊓ B'.map (MulAut.conj ((⟨l, hl⟩ : ↥L)⁻¹)⁻¹).toMonoidHom :=
    ⟨hwB, hwB2⟩
  have hord : orderOf (⟨w, hwL⟩ : ↥L) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hw2)
    · intro hh
      exact hw1 (congrArg Subtype.val hh)
  have hdvd : 2 ∣ Nat.card ↥(B' ⊓ B'.map (MulAut.conj ((⟨l, hl⟩ : ↥L)⁻¹)⁻¹).toMonoidHom) := by
    have := orderOf_dvd_natCard (⟨(⟨w, hwL⟩ : ↥L), hin⟩ : ↥(B' ⊓ B'.map
      (MulAut.conj ((⟨l, hl⟩ : ↥L)⁻¹)⁻¹).toMonoidHom))
    rwa [← Subgroup.orderOf_coe, show ((⟨(⟨w, hwL⟩ : ↥L), hin⟩ : ↥(B' ⊓ B'.map
      (MulAut.conj ((⟨l, hl⟩ : ↥L)⁻¹)⁻¹).toMonoidHom)) : ↥L) = ⟨w, hwL⟩ from rfl, hord] at this
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

end Cosets

section Eight

variable {K : Type*} [Group K] {X L V : Subgroup K} {q : K}

theorem q8_cases (hqV : ∀ v ∈ V, q * v = v * q) (hq4 : q ^ 4 = 1) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    (hq2 : q ^ 2 ∈ V) {g : K} (hg : g ∈ q8 V q hqV hq4) : g ∈ V ∨ g ^ 2 = q ^ 2 := by
  obtain ⟨a, ha, i, rfl⟩ := hg
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    have h : q ^ i = (q ^ 2) ^ j := by rw [hj, ← two_mul, pow_mul]
    rw [h]
    exact V.mul_mem ha (V.pow_mem hq2 j)
  · right
    have hc : Commute a (q ^ i) :=
      (Commute.pow_right (show Commute q a from (hqV a ha)).symm i)
    rw [hc.mul_pow, hV2 a ha, one_mul, ← pow_mul, hj]
    calc q ^ ((2 * j + 1) * 2) = q ^ (4 * j + 2) := by ring_nf
      _ = q ^ 2 := by rw [pow_add, pow_mul, hq4, one_pow, one_mul]

@[expose] def deltaSub [L.Normal] {Q : Subgroup K} (hQX : Q ≤ X) : SubMulAction ↥Q (K ⧸ X) where
  carrier := deltaSet X L
  smul_mem' := by
    rintro ⟨g, hg⟩ c ⟨l, hl, hlX, rfl⟩
    have hgX : g ∈ X := hQX hg
    refine ⟨g * l * g⁻¹, (inferInstance : L.Normal).conj_mem l hl g, ?_, ?_⟩
    · intro h
      apply hlX
      have := X.mul_mem (X.mul_mem (X.inv_mem hgX) h) hgX
      simpa [mul_assoc] using this
    · show ((g * l : K) : K ⧸ X) = ((g * l * g⁻¹ : K) : K ⧸ X)
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hgX

variable [Finite K]

theorem eight_dvd [L.Normal] (hSE : fusionStronglyEmbedded ((X ⊓ L).subgroupOf L))
    (hVL : V ≤ L) (hVX : V ≤ X) (hV4 : Nat.card V = 4) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    (hqX : q ∈ X) (hqV : ∀ v ∈ V, q * v = v * q) (hq2 : q ^ 2 ∈ V) (hq2' : q ^ 2 ≠ 1) :
    8 ∣ Nat.card ↥(deltaSet X L) := by
  have hq4 : q ^ 4 = 1 := by
    have := hV2 _ hq2
    rwa [← pow_mul] at this
  set Q := q8 V q hqV hq4 with hQ
  have hQX : Q ≤ X := by
    rintro _ ⟨a, ha, i, rfl⟩
    exact X.mul_mem (hVX ha) (X.pow_mem hqX i)
  have hfree : ∀ g : ↥Q, g ≠ 1 → ∀ c : ↥(deltaSub (L := L) hQX), g • c ≠ c := by
    intro g hg1 c hc
    have hgc : (g : K) • (c : K ⧸ X) = (c : K ⧸ X) := congrArg Subtype.val hc
    rcases q8_cases hqV hq4 hV2 hq2 g.2 with hgV | hg2
    · exact smul_ne_of_stronglyEmbedded hSE (hVL hgV) (hVX hgV) (hV2 _ hgV)
        (fun h => hg1 (Subtype.ext h)) c.2 hgc
    · have : (q ^ 2) • (c : K ⧸ X) = (c : K ⧸ X) := by
        rw [← hg2, pow_two, mul_smul, hgc, hgc]
      exact smul_ne_of_stronglyEmbedded hSE (hVL hq2) (hVX hq2) (hV2 _ hq2) hq2' c.2 this
  have h1 := free_card_dvd hfree
  have hpg : IsPGroup 2 ↥Q := by
    intro g
    refine ⟨2, ?_⟩
    apply Subtype.ext
    rcases q8_cases hqV hq4 hV2 hq2 g.2 with hgV | hg2
    · have := hV2 _ hgV
      show (g : K) ^ 2 ^ 2 = 1
      rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, this, one_pow]
    · show (g : K) ^ 2 ^ 2 = 1
      rw [show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, hg2, ← pow_mul]
      exact hq4
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  have hVQ : V ≤ Q := le_q8
  have hqQ : q ∈ Q := q_mem_q8
  have hqV' : q ∉ V := fun h => hq2' (hV2 q h)
  have hlt : 4 < Nat.card Q := by
    have hle : Nat.card V ≤ Nat.card Q := Subgroup.card_le_of_le hVQ
    rcases hle.lt_or_eq with h | h
    · omega
    · exact absurd (Subgroup.eq_of_le_of_card_ge hVQ h.ge ▸ hqQ) hqV'
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8 : 8 ∣ Nat.card Q := by
    rw [hk]
    exact pow_dvd_pow_of_dvd (by norm_num : 2 ∣ 2) 3 |>.trans (pow_dvd_pow 2 hk3) |> fun h => by
      simpa using h
  exact h8.trans h1

end Eight

end CFSG.Quasithin.Loc442
