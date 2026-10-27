module

public import CFSG.Quasithin.Vol2.Ch11SecO7d
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112NotLie

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

@[expose] def InT (p : ℕ) (L : Type) [Group L] : Prop :=
  IsPSL 2 p 2 L ∨ IsPSL 3 p 1 L ∨ IsSL3 p L ∨ IsPSU 3 p 1 L ∨ IsSU3 p L

@[expose] def TOrderNe (p N : ℕ) : Prop :=
  p ^ 2 * ((p ^ 2) ^ 2 - 1) ≠ N * 2 ∧
    p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) ≠ N * Nat.gcd 3 (p - 1) ∧
    p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) ≠ N ∧
    p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) ≠ N * Nat.gcd 3 (p + 1) ∧
    p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) ≠ N

instance (p N : ℕ) : Decidable (TOrderNe p N) := by unfold TOrderNe; infer_instance

theorem card_T {L : Type} [Group L] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (h : InT p L) :
    p ^ 2 * ((p ^ 2) ^ 2 - 1) = Nat.card L * 2 ∨
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) = Nat.card L * Nat.gcd 3 (p - 1) ∨
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) = Nat.card L ∨
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) = Nat.card L * Nat.gcd 3 (p + 1) ∨
      p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) = Nat.card L := by
  rcases h with h | h | h | h | h
  · left
    have hc := H13.NotLie.card_psl2 h
    have hodd : Odd (p ^ 2) := (hp.odd_of_ne_two (by omega)).pow
    have hg : Nat.gcd 2 (p ^ 2 - 1) = 2 :=
      Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
    rw [hg] at hc
    have hev : 2 ∣ p ^ 2 * ((p ^ 2) ^ 2 - 1) :=
      Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) _
    rw [hc, Nat.div_mul_cancel hev]
  · right; left
    have hc := SecA.C11P9B.card_mul_gcd_of_isPSL3' (X := L) h
    rw [pow_one] at hc
    exact hc.symm
  · right; right; left
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    rw [Nat.card_congr (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
      3 K).symm).toEquiv, CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num),
      hK, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  · right; right; right; left
    have hc := SecA.C11P9B.card_mul_gcd_of_isPSU3 (X := L) h
    rw [pow_one] at hc
    exact hc.symm
  · right; right; right; right
    exact (SecA.C11P9B.card_of_isSU3 h).symm

theorem not_T_of_card {L : Type} [Group L] {N : ℕ} (hN : Nat.card L = N)
    (hchk : ∀ p, p.Prime → 7 ≤ p → p ^ 2 ∣ N → TOrderNe p N) :
    ∀ p, p.Prime → 7 ≤ p → ¬ InT p L := by
  intro p hp hp7 h
  have hc := card_T hp hp7 h
  rw [hN] at hc
  have hcop : ∀ d, d ∣ 3 → Nat.Coprime (p ^ 2) d := fun d hd =>
    Nat.Coprime.pow_left 2 (Nat.Coprime.coprime_dvd_right hd
      ((Nat.coprime_primes hp Nat.prime_three).mpr (by omega)))
  have hcop2 : Nat.Coprime (p ^ 2) 2 := Nat.Coprime.pow_left 2
    ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have hp3 : p ^ 2 ∣ p ^ 3 := pow_dvd_pow p (by norm_num)
  have hpN : p ^ 2 ∣ N := by
    rcases hc with hc | hc | hc | hc | hc
    · exact hcop2.dvd_of_dvd_mul_right (hc ▸ dvd_mul_right _ _)
    · exact (hcop _ (Nat.gcd_dvd_left 3 _)).dvd_of_dvd_mul_right
        (hc ▸ hp3.trans (dvd_mul_right _ _))
    · exact hc ▸ hp3.trans (dvd_mul_right _ _)
    · exact (hcop _ (Nat.gcd_dvd_left 3 _)).dvd_of_dvd_mul_right
        (hc ▸ hp3.trans (dvd_mul_right _ _))
    · exact hc ▸ hp3.trans (dvd_mul_right _ _)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hchk p hp hp7 hpN
  rcases hc with hc | hc | hc | hc | hc
  · exact h1 hc
  · exact h2 hc
  · exact h3 hc
  · exact h4 hc
  · exact h5 hc

theorem not_T_of_card' {L : Type} [Group L] {N : ℕ} (hN : Nat.card L = N) (hN0 : N ≠ 0)
    (hchk : ∀ p ∈ N.primeFactorsList, 7 ≤ p → p ^ 2 ∣ N → TOrderNe p N) :
    ∀ p, p.Prime → 7 ≤ p → ¬ InT p L :=
  not_T_of_card hN fun p hp hp7 hpN => hchk p
    ((Nat.mem_primeFactorsList hN0).mpr ⟨hp, (dvd_pow_self p two_ne_zero).trans hpN⟩) hp7 hpN

theorem normal_eq_top_or_le_center_of_T {L : Type} [Group L] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (h : InT p L) {N : Subgroup L} (hN : N.Normal) :
    N = ⊤ ∨ N ≤ Subgroup.center L := by
  have : Fact p.Prime := ⟨hp⟩
  have hsimp : IsSimpleGroup L → N = ⊤ ∨ N ≤ Subgroup.center L := fun hs => by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal L _ hs N hN with hb | ht
    · exact Or.inr (hb ▸ bot_le)
    · exact Or.inl ht
  rcases h with h | h | ⟨K, _, _, -, ⟨e⟩⟩ | h | ⟨K, _, _, hK, ⟨e⟩⟩
  · exact hsimp (CFSG.LieType.Simplicity.fam_PSL_simplicity L 2 p 2 h).2
  · exact hsimp (CFSG.LieType.Simplicity.fam_PSL_simplicity L 3 p 1 h).2
  · exact CFSG.LocalCores.quasisimple_normal_subgroups
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).trans e.symm)
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl)) hN
  · exact hsimp (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity L 3 p 1 h).2
  · have h1 := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
      (f := 1) (n := 3) (by rw [pow_one]; exact hK) le_rfl (by intro h; simp at h; omega)
    rw [pow_one] at h1
    exact CFSG.LocalCores.quasisimple_normal_subgroups
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h1.1) hN

theorem commutator_map_eq_bot {G : Type} [Group G] {L : Subgroup G} {N : Subgroup ↥L}
    (hN : N ≤ Subgroup.center ↥L) : ⁅N.map L.subtype, L⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hN hy) ⟨l, hl⟩)

theorem not_nonquasi_of_T {G : Type} [Group G] {B L : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (h : InT p ↥L) : ¬ A312Nonquasi B L := by
  intro hn
  dsimp only [A312Nonquasi] at hn
  obtain ⟨hc, q, hq2, hs⟩ : ⁅(CFSG.oddCore ↥L).map L.subtype, L⁆ ≠ ⊥ ∧
      ∃ q, 2 < q ∧ IsSL2 q (↥L ⧸ CFSG.oddCore ↥L) := by
    rcases hn with ⟨hc, -, q, hq, hq2, hs⟩ | ⟨hc, ⟨q, hq, -, h8, hs⟩, -⟩
    · exact ⟨hc, q, by have := hq.two_le; omega, hs⟩
    · exact ⟨hc, q, by omega, hs⟩
  rcases normal_eq_top_or_le_center_of_T hp hp7 h (CFSG.oddCore_normal ↥L) with ht | hz
  · obtain ⟨a, b, hab⟩ := (nontrivial_of_isSL2 hq2 hs).exists_pair_ne
    apply hab
    induction a using QuotientGroup.induction_on with
    | H x =>
    induction b using QuotientGroup.induction_on with
    | H y => exact QuotientGroup.eq.mpr (ht ▸ Subgroup.mem_top _)
  · exact hc (commutator_map_eq_bot hz)

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
