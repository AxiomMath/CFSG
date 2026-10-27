module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.Case4Fix

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem prime_dvd_card_of_isPSL_two {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSL 2 p 1 X) : p ∣ Nat.card X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card X = ((p ^ 1) ^ (2 * (2 - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 2, ((p ^ 1) ^ i - 1)) / Nat.gcd 2 (p ^ 1 - 1) := by
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        K).toEquiv,
      CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num), hK]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    exact Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
  rw [hg] at hcard
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton] at hcard
  have h2 : 2 ∣ p ^ 2 - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)
  rw [hcard, Nat.mul_div_assoc _ h2]
  exact Dvd.intro _ rfl

theorem card_quot_dvd_card {H L X : Subgroup G} [Finite G]
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hs : IsSimpleGroup (↥H ⧸ CFSG.pCore 2 ↥H))
    (hXL : X ≤ L) (hXH : X ≤ H) (hX : ¬ X ≤ pCoreOf 2 H) :
    Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) ∣ Nat.card ↥L := by
  have hKn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set N : Subgroup ↥H := L.subgroupOf H with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn h => ?_⟩
    show ((h * n * h⁻¹ : ↥H) : G) ∈ L
    exact (Subgroup.mem_normalizer_iff.mp (hHL h.2) n).mp hn
  have hNm : (N.map π).Normal := hNn.map π hπs
  rcases hs.eq_bot_or_eq_top_of_normal (N.map π) with hb | ht
  · exfalso
    apply hX
    intro x hx
    have hxN : (⟨x, hXH hx⟩ : ↥H) ∈ N := hXL hx
    have h1 : π ⟨x, hXH hx⟩ ∈ N.map π := Subgroup.mem_map_of_mem π hxN
    rw [hb, Subgroup.mem_bot] at h1
    have hxK : (⟨x, hXH hx⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨x, hXH hx⟩, hxK, rfl⟩
  · have h1 : Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) = Nat.card ↥(N.map π) := by
      rw [ht, Subgroup.card_top]
    have h2 : Nat.card ↥(N.map π) ∣ Nat.card ↥N := Subgroup.card_map_dvd N π
    have h3 : Nat.card ↥N = Nat.card ↥(L ⊓ H) := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective, hN, Subgroup.subgroupOf_map_subtype]
    rw [h1]
    exact h2.trans (h3 ▸ Subgroup.card_dvd_of_le inf_le_left)

theorem prime_dvd_card_quot {H L X : Subgroup G} [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpsl : IsPSL 2 p 1 (↥H ⧸ CFSG.pCore 2 ↥H)) (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hXL : X ≤ L) (hXH : X ≤ H) (hX : ¬ X ≤ pCoreOf 2 H) :
    p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hpsl).2
  have hdvd := (prime_dvd_card_of_isPSL_two hp hp2 hpsl).trans
    (card_quot_dvd_card hHL hs hXL hXH hX)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)] at hdvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  rw [hk] at hdvd
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem not_dvd_two_pow_sub_one {k p : ℕ} (hk : 1 ≤ k) (hk5 : k ≤ 5)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13) : ¬ p ∣ 2 ^ k - 1 := by
  intro h
  have hk' : 2 ^ k - 1 ∈ ({1, 3, 7, 15, 31} : Finset ℕ) := by interval_cases k <;> decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
  have hpos : 0 < 2 ^ k - 1 := by omega
  have hle := Nat.le_of_dvd hpos h
  have hp' : p = 11 ∨ p = 13 := by omega
  rcases hp' with rfl | rfl <;> rcases hk' with e | e | e | e | e <;> rw [e] at h <;>
    norm_num at h

theorem not_dvd_card_sl {n p : ℕ} (hn0 : 0 < n) (hn : n ≤ 5) (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13) :
    ¬ p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  intro hdvd
  have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
    rw [← Matrix.card_SL_mul_card_units]
    have : Nat.card (ZMod 2)ˣ = 1 := by rw [Nat.card_units, Nat.card_zmod]
    rw [this, mul_one]
  rw [hSL, Matrix.card_GL_field, ZMod.card] at hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have e : 2 ^ n - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (n - i) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' (Nat.le_of_lt i.2)]
  rw [e] at hi
  have hcop : Nat.Coprime p (2 ^ (i : ℕ)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact not_dvd_two_pow_sub_one (by have := i.2; omega) (by omega) hp24
    (hcop.dvd_of_dvd_mul_left hi)

end CFSG.Quasithin.H13.Case4Fix
