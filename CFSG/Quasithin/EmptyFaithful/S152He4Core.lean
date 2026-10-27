module

public import CFSG.Quasithin.EmptyFaithful.S152He4Count
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut

public section

namespace CFSG.Quasithin.He4

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25Small

variable {Y : Type*} [Group Y] [Finite Y]

theorem card_eq_of_isSylowTwoOf {H T : Subgroup Y} (hT : IsSylowTwoOf T H) {c m : ℕ}
    (hH : Nat.card H = 2 ^ c * m) (hm : Odd m) : Nat.card T = 2 ^ c := by
  obtain ⟨b, hb⟩ := hT.2.1.exists_card_eq
  have h1 : Nat.card (T.subgroupOf H) * (T.subgroupOf H).index = Nat.card H :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (T.subgroupOf H) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
  have hidx : (T.subgroupOf H).index % 2 = 1 := by
    have := hT.2.2
    omega
  have hm2 : m % 2 = 1 := Nat.odd_iff.1 hm
  rw [h2, hb, hH] at h1
  set i := (T.subgroupOf H).index with hi
  rcases lt_trichotomy b c with hlt | heq | hgt
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, c = b + d + 1 := ⟨c - b - 1, by omega⟩
    have h3 : i = 2 ^ (d + 1) * m := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) b)
      rw [h1]; ring
    have : 2 ∣ i := ⟨2 ^ d * m, by rw [h3]; ring⟩
    omega
  · rw [hb, heq]
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, b = c + d + 1 := ⟨b - c - 1, by omega⟩
    have h3 : m = 2 ^ (d + 1) * i := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) c)
      rw [← h1]; ring
    have : 2 ∣ m := ⟨2 ^ d * i, by rw [h3]; ring⟩
    omega


theorem core_setup {Lt T H N P : Subgroup Y} (hLn : Lt.Normal)
    (hprod : ∀ y : Y, ∃ l ∈ Lt, ∃ t ∈ T, y = l * t)
    (hT : IsSylowTwoOf T ⊤) (hTH : T ≤ H)
    (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (hcard : Nat.card H = 72 * Nat.card N) (hPH : P ≤ H) :
    N ≤ T ∧ Nat.card T = 8 * Nat.card N ∧ IsSylowTwoOf (T ⊓ Lt) Lt ∧
      ∀ p ∈ P, ∀ r ∈ N ⊓ Lt, p * r * p⁻¹ ∈ N ⊓ Lt := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hN2.exists_card_eq
  have hH : Nat.card H = 2 ^ (a + 3) * 9 := by rw [hcard, ha]; ring
  have hTH' : IsSylowTwoOf T H := isSylowTwoOf_of_le hT hTH
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hnorm : H ≤ Subgroup.normalizer (N : Set Y) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro n
      refine ⟨fun hn => hNn h hh n hn, fun hn => ?_⟩
      have := hNn h⁻¹ (H.inv_mem hh) _ hn
      simpa [mul_assoc] using this
    exact (CFSG.QuasithinUnique.IsSylowTwoOf.pCoreOf_le hTH').trans' <|
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNH hnorm hN2
  · rw [card_eq_of_isSylowTwoOf hTH' hH (by norm_num : Odd 9), ha]
    ring
  · exact isSylowTwoOf_inf_of_mul (H := ⊤) hT le_top (fun h _ => hprod h)
  · intro p hp r hr
    exact ⟨hNn p (hPH hp) r hr.1, hLn.conj_mem r hr.2 p⟩

omit [Finite Y] in
theorem card_subgroupOf_eq {A Lt : Subgroup Y} (h : A ≤ Lt) :
    Nat.card (A.subgroupOf Lt) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem coreA {Lt T H N P : Subgroup Y} (hLn : Lt.Normal)
    (hprod : ∀ y : Y, ∃ l ∈ Lt, ∃ t ∈ T, y = l * t)
    (hT : IsSylowTwoOf T ⊤) (hTH : T ≤ H)
    (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (hcard : Nat.card H = 72 * Nat.card N) (hPH : P ≤ H) (hPL : P ≤ Lt) (hP9 : Nat.card P = 9)
    (hΛ : SmallFacts ↥Lt) : False := by
  obtain ⟨hNT, hT8, hS, hPn⟩ := core_setup (P := P) hLn hprod hT hTH hNH hNn hN2 hcard hPH
  obtain ⟨m, hm, hodd⟩ := hΛ.card
  have hS16 : Nat.card (T ⊓ Lt : Subgroup Y) = 16 := by
    have := card_eq_of_isSylowTwoOf hS (c := 4) (m := m) hm hodd
    simpa using this
  have hNS : N ⊓ (T ⊓ Lt) = N ⊓ Lt := by
    rw [← inf_assoc, inf_eq_left.2 hNT]
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hrel8 : N.relIndex T = 8 := by
    have h := Subgroup.relIndex_mul_card (H := N) (K := T)
    rw [inf_eq_left.2 hNT, hT8] at h
    exact Nat.eq_of_mul_eq_mul_right hNpos h
  have hrelS : N.relIndex (T ⊓ Lt) ≤ 8 := by
    rw [← hrel8]
    exact Subgroup.relIndex_le_of_le_right (H := N) (K := T ⊓ Lt) (L := T) inf_le_left
      (by rw [hrel8]; norm_num)
  have hSR : 16 ≤ 8 * Nat.card (N ⊓ Lt : Subgroup Y) := by
    have h := Subgroup.relIndex_mul_card (H := N) (K := T ⊓ Lt)
    rw [hNS, hS16] at h
    nlinarith
  have hR2 : IsPGroup 2 (N ⊓ Lt : Subgroup Y) := hN2.to_le inf_le_left
  have hRle : (N ⊓ Lt : Subgroup Y) ≤ Lt := inf_le_right
  have hPcard : Nat.card (P.subgroupOf Lt) = 9 := by rw [card_subgroupOf_eq hPL, hP9]
  have hRcard : Nat.card ((N ⊓ Lt : Subgroup Y).subgroupOf Lt) = Nat.card (N ⊓ Lt : Subgroup Y) :=
    card_subgroupOf_eq hRle
  refine lam_A hΛ (P.subgroupOf Lt) ((N ⊓ Lt : Subgroup Y).subgroupOf Lt) hPcard ?_ ?_ ?_
  · exact hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRle).symm
  · intro h
    have : Nat.card ((N ⊓ Lt : Subgroup Y).subgroupOf Lt) = 1 := by rw [h]; exact Subgroup.card_bot
    omega
  · intro p hp r hr
    have := hPn p (Subgroup.mem_subgroupOf.1 hp) r (Subgroup.mem_subgroupOf.1 hr)
    exact Subgroup.mem_subgroupOf.2 (by simpa using this)

theorem coreB {Lt T H N P : Subgroup Y} (hLn : Lt.Normal)
    (hprod : ∀ y : Y, ∃ l ∈ Lt, ∃ t ∈ T, y = l * t)
    (hT : IsSylowTwoOf T ⊤) (hTH : T ≤ H)
    (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hN2 : IsPGroup 2 N)
    (hcard : Nat.card H = 72 * Nat.card N) (hPH : P ≤ H) (hPL : P ≤ Lt) (hP9 : Nat.card P = 9)
    {j m : ℕ} (hj : 2 ≤ j) (hm : Nat.card ↥Lt = 2 ^ (2 * j) * m) (hodd : Odd m)
    (hinv : NoInvCommNine ↥Lt) : ¬ T ≤ Lt := by
  intro hTL
  obtain ⟨hNT, hT8, hS, hPn⟩ := core_setup (P := P) hLn hprod hT hTH hNH hNn hN2 hcard hPH
  have hTcard : Nat.card T = 2 ^ (2 * j) := by
    have := card_eq_of_isSylowTwoOf hS hm hodd
    rwa [inf_eq_left.2 hTL] at this
  have hNcard : Nat.card N = 2 ^ (2 * (j - 2) + 1) := by
    have h8 : (2 : ℕ) ^ (2 * j) = 8 * 2 ^ (2 * (j - 2) + 1) := by
      obtain ⟨d, rfl⟩ : ∃ d, j = d + 2 := ⟨j - 2, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [hTcard, h8] at hT8
    omega
  have hNL : N ≤ Lt := hNT.trans hTL
  have hNinf : N ⊓ Lt = N := inf_eq_left.2 hNL
  have hPcard : Nat.card (P.subgroupOf Lt) = 9 := by rw [card_subgroupOf_eq hPL, hP9]
  refine lam_B hinv (P.subgroupOf Lt) (N.subgroupOf Lt) hPcard ?_ ?_ (j - 2) ?_
  · exact hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNL).symm
  · intro p hp r hr
    have := hPn p (Subgroup.mem_subgroupOf.1 hp) r
      ⟨Subgroup.mem_subgroupOf.1 hr, hNL (Subgroup.mem_subgroupOf.1 hr)⟩
    rw [hNinf] at this
    exact Subgroup.mem_subgroupOf.2 (by simpa using this)
  · rw [card_subgroupOf_eq hNL, hNcard]


theorem nonempty_mulEquiv_mulAut {Lt T : Subgroup Y} (hLn : Lt.Normal)
    (hprod : ∀ y : Y, ∃ l ∈ Lt, ∃ t ∈ T, y = l * t) (hT2 : IsPGroup 2 T)
    (hO2 : ∀ Q : Subgroup Y, Q.Normal → IsPGroup 2 Q → Q = ⊥)
    (hZ : ∀ z ∈ Lt, (∀ l ∈ Lt, z * l = l * z) → z = 1)
    (hAut : Nat.card (MulAut ↥Lt) ≤ 2 * Nat.card ↥Lt) (hTnot : ¬ T ≤ Lt) :
    Nonempty (Y ≃* MulAut ↥Lt) := by
  classical
  have : Lt.Normal := hLn
  let φ : Y →* MulAut ↥Lt := MulAut.conjNormal
  have hφ : ∀ (y : Y) (n : ↥Lt), ((φ y n : ↥Lt) : Y) = y * n * y⁻¹ :=
    fun y n => MulAut.conjNormal_apply y n
  have hker : ∀ y : Y, φ y = 1 ↔ ∀ l ∈ Lt, y * l = l * y := by
    intro y
    rw [MulEquiv.ext_iff]
    constructor
    · intro h l hl
      have := congrArg Subtype.val (h ⟨l, hl⟩)
      rw [hφ] at this
      have h1 : y * l * y⁻¹ = l := this
      calc y * l = y * l * y⁻¹ * y := by group
        _ = l * y := by rw [h1]
    · intro h l
      apply Subtype.ext
      rw [hφ]
      calc y * (l : Y) * y⁻¹ = (l : Y) * y * y⁻¹ := by rw [h l l.2]
        _ = l := by group
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine hO2 φ.ker (MonoidHom.normal_ker φ) ?_
    intro c
    obtain ⟨l, hl, t, ht, hct⟩ := hprod c
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hmem : (c : Y) ^ 2 ^ k ∈ Lt := by
      have hmk : (QuotientGroup.mk (c : Y) : Y ⧸ Lt) = QuotientGroup.mk t := by
        rw [hct, QuotientGroup.eq]
        have := hLn.conj_mem l⁻¹ (Lt.inv_mem hl) t⁻¹
        simpa [mul_assoc] using this
      have h1 : (QuotientGroup.mk ((c : Y) ^ 2 ^ k) : Y ⧸ Lt) = 1 := by
        rw [QuotientGroup.mk_pow, hmk, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hc : (c : Y) ^ 2 ^ k ∈ φ.ker := φ.ker.pow_mem c.2 _
    have hcomm := (hker _).1 (MonoidHom.mem_ker.1 hc)
    exact Subtype.ext (hZ _ hmem hcomm)
  have hlt : Lt ≠ ⊤ := by
    intro h
    exact hTnot (h ▸ le_top)
  have hidx : 2 ≤ Lt.index := by
    have h1 : Lt.index ≠ 1 := fun h => hlt (Subgroup.index_eq_one.1 h)
    have h0 : Lt.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hcard : 2 * Nat.card ↥Lt ≤ Nat.card Y := by
    have := Subgroup.card_mul_index Lt
    nlinarith
  have hle : Nat.card (MulAut ↥Lt) ≤ Nat.card Y := hAut.trans hcard
  exact ⟨MulEquiv.ofBijective φ (hinj.bijective_of_nat_card_le hle)⟩

end CFSG.Quasithin.He4
