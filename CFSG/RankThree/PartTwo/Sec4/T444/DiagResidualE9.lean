module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3FDecomp

public section

namespace CFSG.RankThree.PartTwo.Sec4.ResidualGen

open CFSG.RankThree.PartTwo.Sec4.E27 (exists_mul_eq_of_mem_sup_of_comm)

section E9

variable {T : Type} [Group T] [Finite T] {a b f j : T}

theorem f_sq_conj (hfa : f * a * f⁻¹ = b) (hfb : f * b * f⁻¹ = a⁻¹) :
    f ^ 2 * a * (f ^ 2)⁻¹ = a⁻¹ ∧ f ^ 2 * b * (f ^ 2)⁻¹ = b⁻¹ := by
  have h1 : f ^ 2 * a * (f ^ 2)⁻¹ = f * (f * a * f⁻¹) * f⁻¹ := by
    rw [sq, mul_inv_rev]
    simp only [mul_assoc]
  have h2 : f ^ 2 * b * (f ^ 2)⁻¹ = f * (f * b * f⁻¹) * f⁻¹ := by
    rw [sq, mul_inv_rev]
    simp only [mul_assoc]
  refine ⟨by rw [h1, hfa, hfb], ?_⟩
  rw [h2, hfb]
  calc f * a⁻¹ * f⁻¹ = (f * a * f⁻¹)⁻¹ := by group
    _ = b⁻¹ := by rw [hfa]

theorem mem_normalizer_of_conj_mem {E : Subgroup T} {n : T} (h : ∀ x ∈ E, n * x * n⁻¹ ∈ E) :
    n ∈ Subgroup.normalizer (E : Set T) := by
  set c : T →* T := (MulAut.conj n).toMonoidHom with hc
  have hle : E.map c ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card (E.map c) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have heq : E.map c = E := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h x hx
  · intro hx
    have hx' : n * x * n⁻¹ ∈ E.map c := heq.symm ▸ hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := (MulAut.conj n).injective (by simpa [hc, MulAut.conj_apply] using hyx)
    exact this ▸ hy

theorem eq_one_or_eq_or_eq_sq_of_mem_zpowers {x y : T} (hx : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  obtain ⟨i, rfl⟩ := hy
  have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
  have hi : x ^ i = x ^ (i % 3) := zpow_eq_zpow_emod i h3
  have hlt : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  show x ^ i = 1 ∨ x ^ i = x ∨ x ^ i = x ^ 2
  rw [hi]
  rcases hlt with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; simp

theorem exists_e9_data (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hba : b ∉ Subgroup.zpowers a) (hfa : f * a * f⁻¹ = b) (hfb : f * b * f⁻¹ = a⁻¹)
    (hf4 : f ^ 4 = 1) (hja : j * a * j⁻¹ = b * a⁻¹) (hjb : j * b * j⁻¹ = a⁻¹ * b * a⁻¹) :
    ∃ E : Subgroup T, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      Nat.card E = 9 ∧
      (∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
        ∃ n ∈ Subgroup.normalizer (E : Set T), n * x * n⁻¹ = y) ∧
      ∃ s : T, s * s = 1 ∧ ∀ x ∈ E, s * x * s⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := Subgroup.zpowers a with hA
  set B := Subgroup.zpowers b with hB
  have hcab : Commute a b := hab
  have hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩
    exact (hcab.zpow_zpow i k).eq
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hAcard : Nat.card A = 3 := by
    rw [hA, Nat.card_zpowers]
    exact orderOf_eq_prime ha3 ha1
  have hBcard : Nat.card B = 3 := by
    rw [hB, Nat.card_zpowers]
    exact orderOf_eq_prime hb3 hb1
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxA : Subgroup.zpowers x = A := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx.1) ?_
      have h3 : Nat.card (Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers]
        refine orderOf_eq_prime ?_ hx1
        obtain ⟨i, hi⟩ := hx.1
        rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
      omega
    have hxB : Subgroup.zpowers x = B := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx.2) ?_
      have h3 : Nat.card (Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers]
        refine orderOf_eq_prime ?_ hx1
        obtain ⟨i, hi⟩ := hx.2
        rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
      omega
    have hBA : B = A := hxB.symm.trans hxA
    exact hba (hBA ▸ Subgroup.mem_zpowers b)
  set E := A ⊔ B with hE
  have hEcard : Nat.card E = 9 := by
    have hcomm' : ∀ (x : A) (y : B), Commute (A.subtype x) (B.subtype y) := fun x y =>
      hcomm x x.2 y y.2
    have hμrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm').range = E := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    have hμinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm') := by
      rw [injective_iff_map_eq_one]
      rintro ⟨x, y⟩ hxy
      have h1 : (x : T) * (y : T) = 1 := hxy
      have hx : (x : T) ∈ A ⊓ B := ⟨x.2, by
        have : (x : T) = (y : T)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact B.inv_mem y.2⟩
      rw [hinf, Subgroup.mem_bot] at hx
      have hy : (y : T) = 1 := by
        rw [hx, one_mul] at h1
        exact h1
      exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
    rw [← hμrange]
    calc Nat.card (MonoidHom.noncommCoprod A.subtype B.subtype hcomm').range
        = Nat.card (A × B) := (Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv).symm
      _ = 9 := by rw [Nat.card_prod, hAcard, hBcard]
  have hrep : ∀ x ∈ E, ∃ i k : ℤ, x = a ^ i * b ^ k := by
    intro x hx
    obtain ⟨u, ⟨i, rfl⟩, v, ⟨k, rfl⟩, rfl⟩ := exists_mul_eq_of_mem_sup_of_comm hcomm hx
    exact ⟨i, k, rfl⟩
  have hacomm : ∀ i k : ℤ, a ^ i * b ^ k = b ^ k * a ^ i := fun i k => (hcab.zpow_zpow i k).eq
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, k, rfl⟩ := hrep x hx
    obtain ⟨i', k', rfl⟩ := hrep y hy
    calc a ^ i * b ^ k * (a ^ i' * b ^ k') = a ^ i * (b ^ k * a ^ i') * b ^ k' := by
          simp only [mul_assoc]
      _ = a ^ i * (a ^ i' * b ^ k) * b ^ k' := by rw [← hacomm i' k]
      _ = a ^ i' * b ^ k' * (a ^ i * b ^ k) := by
          rw [show a ^ i * (a ^ i' * b ^ k) * b ^ k' = a ^ i * a ^ i' * (b ^ k * b ^ k') by
            simp only [mul_assoc], show a ^ i' * b ^ k' * (a ^ i * b ^ k) =
              a ^ i' * (b ^ k' * a ^ i) * b ^ k by simp only [mul_assoc], ← hacomm i k',
            show a ^ i' * (a ^ i * b ^ k') * b ^ k = a ^ i' * a ^ i * (b ^ k' * b ^ k) by
            simp only [mul_assoc], ← zpow_add, ← zpow_add, ← zpow_add, ← zpow_add, add_comm i i',
            add_comm k k']
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, k, rfl⟩ := hrep x hx
    have hai : (a ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
    have hbk : (b ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    rw [(hcab.zpow_zpow i k).mul_pow, hai, hbk, one_mul]
  have haE : a ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hbE : b ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hconj : ∀ n : T, n * a * n⁻¹ ∈ E → n * b * n⁻¹ ∈ E →
      n ∈ Subgroup.normalizer (E : Set T) := by
    intro n hna hnb
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨i, k, rfl⟩ := hrep x hx
    have hx' : n * (a ^ i * b ^ k) * n⁻¹ = (n * a * n⁻¹) ^ i * (n * b * n⁻¹) ^ k := by
      simp only [← MulAut.conj_apply]
      rw [map_mul, map_zpow, map_zpow]
    rw [hx']
    exact E.mul_mem (E.zpow_mem hna i) (E.zpow_mem hnb k)
  have hfN : f ∈ Subgroup.normalizer (E : Set T) :=
    hconj f (by rw [hfa]; exact hbE) (by rw [hfb]; exact E.inv_mem haE)
  have hjN : j ∈ Subgroup.normalizer (E : Set T) :=
    hconj j (by rw [hja]; exact E.mul_mem hbE (E.inv_mem haE))
      (by rw [hjb]; exact E.mul_mem (E.mul_mem (E.inv_mem haE) hbE) (E.inv_mem haE))
  have hfinv_a : f * a⁻¹ * f⁻¹ = b⁻¹ := by
    calc f * a⁻¹ * f⁻¹ = (f * a * f⁻¹)⁻¹ := by group
      _ = b⁻¹ := by rw [hfa]
  have hfinv_b : f * b⁻¹ * f⁻¹ = a := by
    calc f * b⁻¹ * f⁻¹ = (f * b * f⁻¹)⁻¹ := by group
      _ = a := by rw [hfb, inv_inv]
  have hff_a : f * f * a * (f * f)⁻¹ = a⁻¹ := by
    calc f * f * a * (f * f)⁻¹ = f * (f * a * f⁻¹) * f⁻¹ := by group
      _ = a⁻¹ := by rw [hfa, hfb]
  have hff_b : f * f * b * (f * f)⁻¹ = b⁻¹ := by
    calc f * f * b * (f * f)⁻¹ = f * (f * b * f⁻¹) * f⁻¹ := by group
      _ = b⁻¹ := by rw [hfb, hfinv_a]
  have hfff_a : f * (f * f) * a * (f * (f * f))⁻¹ = b⁻¹ := by
    calc f * (f * f) * a * (f * (f * f))⁻¹ = f * (f * f * a * (f * f)⁻¹) * f⁻¹ := by group
      _ = b⁻¹ := by rw [hff_a, hfinv_a]
  have hc1 : f * (b * a⁻¹) * f⁻¹ = a⁻¹ * b⁻¹ := by
    calc f * (b * a⁻¹) * f⁻¹ = (f * b * f⁻¹) * (f * a⁻¹ * f⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [hfb, hfinv_a]
  have hc2 : f * (a⁻¹ * b⁻¹) * f⁻¹ = b⁻¹ * a := by
    calc f * (a⁻¹ * b⁻¹) * f⁻¹ = (f * a⁻¹ * f⁻¹) * (f * b⁻¹ * f⁻¹) := by group
      _ = b⁻¹ * a := by rw [hfinv_a, hfinv_b]
  have hc3 : f * (b⁻¹ * a) * f⁻¹ = a * b := by
    calc f * (b⁻¹ * a) * f⁻¹ = (f * b⁻¹ * f⁻¹) * (f * a * f⁻¹) := by group
      _ = a * b := by rw [hfinv_b, hfa]
  have hsq_a : a ^ 2 = a⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact ha3)
  have hsq_b : b ^ 2 = b⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hb3)
  have hred : ∀ (c : T), c ^ 3 = 1 → ∀ i : ℤ, ∃ n : ℕ, n < 3 ∧ c ^ i = c ^ n := by
    intro c hc i
    have h3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc
    refine ⟨(i % 3).toNat, by omega, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_eq_zpow_emod i h3]
  have key : ∀ x ∈ E, x ≠ 1 → ∃ n ∈ Subgroup.normalizer (E : Set T), n * a * n⁻¹ = x := by
    intro x hx hx1
    obtain ⟨i, k, rfl⟩ := hrep x hx
    obtain ⟨i', hi', hi⟩ := hred a ha3 i
    obtain ⟨k', hk', hk⟩ := hred b hb3 k
    rw [hi, hk] at hx1 ⊢
    have hNm := fun {x y : T} (hx : x ∈ Subgroup.normalizer (E : Set T))
      (hy : y ∈ Subgroup.normalizer (E : Set T)) => (Subgroup.normalizer (E : Set T)).mul_mem hx hy
    have hfj1 : f * j * a * (f * j)⁻¹ = a⁻¹ * b⁻¹ := by
      calc f * j * a * (f * j)⁻¹ = f * (j * a * j⁻¹) * f⁻¹ := by group
        _ = a⁻¹ * b⁻¹ := by rw [hja, hc1]
    have hfj2 : f * (f * j) * a * (f * (f * j))⁻¹ = b⁻¹ * a := by
      calc f * (f * j) * a * (f * (f * j))⁻¹ = f * (f * (j * a * j⁻¹) * f⁻¹) * f⁻¹ := by group
        _ = b⁻¹ * a := by rw [hja, hc1, hc2]
    have hfj3 : f * (f * (f * j)) * a * (f * (f * (f * j)))⁻¹ = a * b := by
      calc f * (f * (f * j)) * a * (f * (f * (f * j)))⁻¹ =
            f * (f * (f * (j * a * j⁻¹) * f⁻¹) * f⁻¹) * f⁻¹ := by group
        _ = a * b := by rw [hja, hc1, hc2, hc3]
    interval_cases i' <;> interval_cases k'
    · exact absurd (by simp) hx1
    · exact ⟨f, hfN, by simpa using hfa⟩
    · exact ⟨f * (f * f), hNm hfN (hNm hfN hfN), by rw [hsq_b]; simpa using hfff_a⟩
    · exact ⟨1, Subgroup.one_mem _, by simp⟩
    · exact ⟨f * (f * (f * j)), hNm hfN (hNm hfN (hNm hfN hjN)), by
        rw [pow_one, pow_one]; exact hfj3⟩
    · exact ⟨f * (f * j), hNm hfN (hNm hfN hjN), by
        rw [hsq_b, pow_one, hfj2]; exact hcab.inv_right.eq.symm⟩
    · exact ⟨f * f, hNm hfN hfN, by rw [hsq_a]; simpa using hff_a⟩
    · exact ⟨j, hjN, by rw [hsq_a, pow_one, hja]; exact hcab.inv_left.eq.symm⟩
    · exact ⟨f * j, hNm hfN hjN, by rw [hsq_a, hsq_b, hfj1]⟩
  refine ⟨E, hEcomm, hE3, hEcard, ?_, f ^ 2, ?_, ?_⟩
  · intro x hx hx1 y hy hy1
    obtain ⟨n, hn, hnx⟩ := key x hx hx1
    obtain ⟨m, hm, hmy⟩ := key y hy hy1
    refine ⟨m * n⁻¹, (Subgroup.normalizer (E : Set T)).mul_mem hm
      ((Subgroup.normalizer (E : Set T)).inv_mem hn), ?_⟩
    calc m * n⁻¹ * x * (m * n⁻¹)⁻¹ = m * (n⁻¹ * x * n) * m⁻¹ := by group
      _ = m * a * m⁻¹ := by rw [← hnx]; group
      _ = y := hmy
  · rw [← pow_add]
    exact hf4
  · intro x hx
    obtain ⟨hf2a, hf2b⟩ := f_sq_conj hfa hfb
    obtain ⟨i, k, rfl⟩ := hrep x hx
    have hx' : f ^ 2 * (a ^ i * b ^ k) * (f ^ 2)⁻¹ =
        (f ^ 2 * a * (f ^ 2)⁻¹) ^ i * (f ^ 2 * b * (f ^ 2)⁻¹) ^ k := by
      simp only [← MulAut.conj_apply]
      rw [map_mul, map_zpow, map_zpow]
    rw [hx', hf2a, hf2b, mul_inv_rev, inv_zpow', inv_zpow', ← zpow_neg, ← zpow_neg]
    exact (hcab.zpow_zpow (-i) (-k)).eq

end E9

end CFSG.RankThree.PartTwo.Sec4.ResidualGen
