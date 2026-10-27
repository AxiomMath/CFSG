module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem commute_of_commutator_eq_bot {X Y : Subgroup G} (h : ⁅X, Y⁆ = ⊥) {x y : G} (hx : x ∈ X)
    (hy : y ∈ Y) : x * y = y * x := by
  have hc : ⁅x, y⁆ ∈ ⁅X, Y⁆ := commutator_mem_commutator hx hy
  rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

theorem eq_one_of_conj_eq_mul_fixed {A : Subgroup G} {p : ℕ} (hpA : ¬ p ∣ Nat.card A)
    (hp : p.Prime) {q x δ : G} (hδA : δ ∈ A) (hq : q ^ p = 1) (hδq : q * δ * q⁻¹ = δ)
    (hx : q * x * q⁻¹ = x * δ) : δ = 1 := by
  have hiter : ∀ k : ℕ, q ^ k * x * (q ^ k)⁻¹ = x * δ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hδk : q * δ ^ k * q⁻¹ = δ ^ k := by rw [← conj_pow, hδq]
      calc q ^ (k + 1) * x * (q ^ (k + 1))⁻¹ = q * (q ^ k * x * (q ^ k)⁻¹) * q⁻¹ := by
            rw [pow_succ']; group
        _ = q * x * q⁻¹ * (q * δ ^ k * q⁻¹) := by rw [ih]; group
        _ = x * δ ^ (k + 1) := by rw [hx, hδk, pow_succ']; group
  have h := hiter p
  rw [hq, one_mul, inv_one, mul_one, left_eq_mul] at h
  rw [← orderOf_eq_one_iff]
  have h1 : orderOf δ ∣ p := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf δ ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hδA
  rcases (Nat.dvd_prime hp).mp h1 with h3 | h3
  · exact h3
  · exact absurd (h3 ▸ h2) hpA

theorem pow_eq_one_of_mem_of_card_eq {Q : Subgroup G} {p : ℕ} (hQ : Nat.card Q = p) {x : G}
    (hx : x ∈ Q) : x ^ p = 1 := by
  have h := pow_card_eq_one' (G := Q) (x := ⟨x, hx⟩)
  rw [hQ] at h
  exact congrArg Subtype.val h

theorem eq_zpowers_of_card_eq_prime {Q : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hQ : Nat.card Q = p) {x : G} (hx : x ∈ Q) (hx1 : x ≠ 1) : zpowers x = Q := by
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hp.ne_zero)
  have : Fact p.Prime := ⟨hp⟩
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hx) ?_
  rw [Nat.card_zpowers, orderOf_eq_prime (pow_eq_one_of_mem_of_card_eq hQ hx) hx1, hQ]

theorem inf_centralizer_eq_of_ne_of_ne {p : ℕ} (hp : p.Prime) {A P P₁ P₂ A₁ A₂ : Subgroup G}
    (hpA : ¬ p ∣ Nat.card A) (hPsup : P₁ ⊔ P₂ = P) (hPcomm : ⁅P₁, P₂⁆ = ⊥)
    (hP₁ : Nat.card P₁ = p) (hP₂ : Nat.card P₂ = p)
    (hinv₁ : P ≤ normalizer (A₁ : Set G)) (hinv₂ : P ≤ normalizer (A₂ : Set G))
    (hA : (A : Set G) = (A₁ : Set G) * (A₂ : Set G))
    (hc₁ : ⁅A₁, P₂⁆ = ⊥) (hc₂ : ⁅A₂, P₁⁆ = ⊥)
    {Q : Subgroup G} (hQP : Q ≤ P) (hQ : Nat.card Q = p) (hQ₁ : Q ≠ P₁) (hQ₂ : Q ≠ P₂) :
    A ⊓ centralizer (Q : Set G) = A ⊓ centralizer (P : Set G) := by
  have : Finite Q := Nat.finite_of_card_ne_zero (hQ ▸ hp.ne_zero)
  have : Finite P₁ := Nat.finite_of_card_ne_zero (hP₁ ▸ hp.ne_zero)
  have : Finite P₂ := Nat.finite_of_card_ne_zero (hP₂ ▸ hp.ne_zero)
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (hQ ▸ hp.one_lt)
  refine le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hQP))
  obtain ⟨⟨q, hqQ⟩, hq1⟩ := exists_ne (1 : Q)
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hQz : zpowers q = Q := eq_zpowers_of_card_eq_prime hp hQ hqQ hq1'
  have hqp : q ^ p = 1 := pow_eq_one_of_mem_of_card_eq hQ hqQ
  have hle12 : P₁ ≤ normalizer (P₂ : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hPcomm).trans (centralizer_le_normalizer _)
  have hPmul : (P : Set G) = (P₁ : Set G) * (P₂ : Set G) := by
    rw [← hPsup]
    exact coe_mul_of_left_le_normalizer_right P₁ P₂ hle12
  have hqP : q ∈ (P₁ : Set G) * (P₂ : Set G) := hPmul ▸ hQP hqQ
  obtain ⟨q₁, hq₁, q₂, hq₂, hq⟩ := hqP
  have hq : q₁ * q₂ = q := hq
  have hq₁P : q₁ ∈ P := hPsup ▸ mem_sup_left hq₁
  have hq₂P : q₂ ∈ P := hPsup ▸ mem_sup_right hq₂
  have hq₂1 : q₂ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hq
    subst hq
    exact hQ₁ (Subgroup.eq_of_le_of_card_ge (hQz ▸ zpowers_le.mpr hq₁) (by rw [hP₁, hQ]))
  have hq₁1 : q₁ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hq
    subst hq
    exact hQ₂ (Subgroup.eq_of_le_of_card_ge (hQz ▸ zpowers_le.mpr hq₂) (by rw [hP₂, hQ]))
  have hP₁z : zpowers q₁ = P₁ := eq_zpowers_of_card_eq_prime hp hP₁ hq₁ hq₁1
  have hP₂z : zpowers q₂ = P₂ := eq_zpowers_of_card_eq_prime hp hP₂ hq₂ hq₂1
  rintro a ⟨haA, haQ⟩
  have haq : q * a = a * q := mem_centralizer_iff.mp haQ q hqQ
  have haA' : a ∈ (A₁ : Set G) * (A₂ : Set G) := hA ▸ haA
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := haA'
  have hb₁ : q * a₁ * q⁻¹ ∈ A₁ := (mem_normalizer_iff.mp (hinv₁ (hQP hqQ)) a₁).mp ha₁
  have hb₂ : q * a₂ * q⁻¹ ∈ A₂ := (mem_normalizer_iff.mp (hinv₂ (hQP hqQ)) a₂).mp ha₂
  have hconj₁ : q * a₁ * q⁻¹ = q₁ * a₁ * q₁⁻¹ := by
    have h := commute_of_commutator_eq_bot hc₁ ha₁ hq₂
    rw [← hq]
    calc q₁ * q₂ * a₁ * (q₁ * q₂)⁻¹ = q₁ * (q₂ * a₁) * q₂⁻¹ * q₁⁻¹ := by group
      _ = q₁ * (a₁ * q₂) * q₂⁻¹ * q₁⁻¹ := by rw [h]
      _ = q₁ * a₁ * q₁⁻¹ := by group
  have hconj₂ : q * a₂ * q⁻¹ = q₂ * a₂ * q₂⁻¹ := by
    have hb : q₂ * a₂ * q₂⁻¹ ∈ A₂ := (mem_normalizer_iff.mp (hinv₂ hq₂P) a₂).mp ha₂
    have h := commute_of_commutator_eq_bot hc₂ hb hq₁
    rw [← hq]
    calc q₁ * q₂ * a₂ * (q₁ * q₂)⁻¹ = q₁ * (q₂ * a₂ * q₂⁻¹) * q₁⁻¹ := by group
      _ = (q₂ * a₂ * q₂⁻¹) * q₁ * q₁⁻¹ := by rw [← h]
      _ = q₂ * a₂ * q₂⁻¹ := by group
  set δ := a₁⁻¹ * (q * a₁ * q⁻¹) with hδ
  have hfix : q * (a₁ * a₂) * q⁻¹ = a₁ * a₂ := by
    rw [haq, mul_inv_cancel_right]
  have hδ₂ : δ = a₂ * (q * a₂ * q⁻¹)⁻¹ := by
    have e : q * (a₁ * a₂) * q⁻¹ = (q * a₁ * q⁻¹) * (q * a₂ * q⁻¹) := by group
    rw [e] at hfix
    rw [hδ, eq_mul_inv_iff_mul_eq, mul_assoc, hfix, inv_mul_cancel_left]
  have hδA₁ : δ ∈ A₁ := A₁.mul_mem (A₁.inv_mem ha₁) hb₁
  have hδA₂ : δ ∈ A₂ := hδ₂ ▸ A₂.mul_mem ha₂ (A₂.inv_mem hb₂)
  have hδA : δ ∈ A := by
    have : δ ∈ (A : Set G) := by rw [hA]; exact ⟨δ, hδA₁, 1, one_mem _, mul_one δ⟩
    exact this
  have hδq : q * δ * q⁻¹ = δ := by
    have h1 := commute_of_commutator_eq_bot hc₂ hδA₂ hq₁
    have h2 := commute_of_commutator_eq_bot hc₁ hδA₁ hq₂
    rw [← hq]
    calc q₁ * q₂ * δ * (q₁ * q₂)⁻¹ = q₁ * (q₂ * δ) * q₂⁻¹ * q₁⁻¹ := by group
      _ = q₁ * (δ * q₂) * q₂⁻¹ * q₁⁻¹ := by rw [h2]
      _ = (q₁ * δ) * q₁⁻¹ := by group
      _ = (δ * q₁) * q₁⁻¹ := by rw [h1]
      _ = δ := by group
  have hxδ : q * a₁ * q⁻¹ = a₁ * δ := by rw [hδ, mul_inv_cancel_left]
  have hδ1 : δ = 1 := eq_one_of_conj_eq_mul_fixed hpA hp hδA hqp hδq hxδ
  have hfix₁ : q₁ * a₁ * q₁⁻¹ = a₁ := by rw [← hconj₁, hxδ, hδ1, mul_one]
  have hfix₂ : q₂ * a₂ * q₂⁻¹ = a₂ := by
    rw [← hconj₂]
    rw [hδ1, eq_comm, mul_inv_eq_one] at hδ₂
    exact hδ₂.symm
  have hc₁' : q₁ ∈ centralizer ({a₁} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hfix₁
  have hc₂' : q₂ ∈ centralizer ({a₂} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hfix₂
  have hP₁c : P₁ ≤ centralizer ({a₁ * a₂} : Set G) := by
    intro x hx
    have hx₁ : x ∈ centralizer ({a₁} : Set G) := (hP₁z ▸ zpowers_le.mpr hc₁') hx
    have hx₂ := commute_of_commutator_eq_bot hc₂ ha₂ hx
    rw [mem_centralizer_singleton_iff] at hx₁ ⊢
    calc x * (a₁ * a₂) = (x * a₁) * a₂ := by group
      _ = a₁ * (x * a₂) := by rw [hx₁]; group
      _ = a₁ * a₂ * x := by rw [← hx₂]; group
  have hP₂c : P₂ ≤ centralizer ({a₁ * a₂} : Set G) := by
    intro x hx
    have hx₂ : x ∈ centralizer ({a₂} : Set G) := (hP₂z ▸ zpowers_le.mpr hc₂') hx
    have hx₁ := commute_of_commutator_eq_bot hc₁ ha₁ hx
    rw [mem_centralizer_singleton_iff] at hx₂ ⊢
    calc x * (a₁ * a₂) = (x * a₁) * a₂ := by group
      _ = a₁ * (x * a₂) := by rw [← hx₁]; group
      _ = a₁ * a₂ * x := by rw [hx₂]; group
  have hPc : P ≤ centralizer ({a₁ * a₂} : Set G) := hPsup ▸ sup_le hP₁c hP₂c
  refine ⟨haA, mem_centralizer_iff.mpr fun x hx => ?_⟩
  exact mem_centralizer_singleton_iff.mp (hPc hx)

theorem inf_centralizer_le_of_conjugate {A P X : Subgroup G} {g : G}
    (hgA : g ∈ normalizer (A : Set G)) (hgP : g ∈ normalizer (P : Set G))
    (h : A ⊓ centralizer (conjugate X g : Set G) = A ⊓ centralizer (P : Set G)) :
    A ⊓ centralizer (X : Set G) ≤ A ⊓ centralizer (P : Set G) := by
  intro a ha
  obtain ⟨haA, haX⟩ := Subgroup.mem_inf.mp ha
  have hga : g⁻¹ * a * g ∈ A ⊓ centralizer (conjugate X g : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp (inv_mem hgA) a).mp haA
      simpa using h1
    · rw [mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have hxa := mem_centralizer_iff.mp haX x hx
      change g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * a * g) = g⁻¹ * a * g * (g⁻¹ * x * g⁻¹⁻¹)
      simp only [inv_inv]
      calc g⁻¹ * x * g * (g⁻¹ * a * g) = g⁻¹ * (x * a) * g := by group
        _ = g⁻¹ * (a * x) * g := by rw [hxa]
        _ = g⁻¹ * a * g * (g⁻¹ * x * g) := by group
  rw [h] at hga
  refine Subgroup.mem_inf.mpr ⟨haA, mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ P := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hgP) y).mp hy
    simpa using h1
  have h2 := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hga).2 _ hy'
  calc y * a = g * ((g⁻¹ * y * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * a * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h2]
    _ = a * y := by group

theorem commuting_supports_detect_intrinsic_prime_line_pair [Finite G] {p : ℕ} (hp : p.Prime)
    {A P P₁ P₂ A₁ A₂ : Subgroup G} (hpA : ¬ p ∣ Nat.card A) (hPsup : P₁ ⊔ P₂ = P)
    (hPinf : P₁ ⊓ P₂ = ⊥) (hPcomm : ⁅P₁, P₂⁆ = ⊥) (hP₁ : Nat.card P₁ = p)
    (hP₂ : Nat.card P₂ = p) (hinv₁ : P ≤ normalizer (A₁ : Set G))
    (hinv₂ : P ≤ normalizer (A₂ : Set G)) (hA : (A : Set G) = (A₁ : Set G) * (A₂ : Set G))
    (hc₁ : ⁅A₁, P₂⁆ = ⊥) (hc₂ : ⁅A₂, P₁⁆ = ⊥) (hn₁ : ⁅A₁, P₁⁆ ≠ ⊥) (hn₂ : ⁅A₂, P₂⁆ ≠ ⊥) :
    {Q : Subgroup G | Q ≤ P ∧ Nat.card Q = p ∧ ⁅A ⊓ centralizer (Q : Set G), P⁆ ≠ ⊥} =
        {P₁, P₂} ∧
      (∀ Q : Subgroup G, Q ≤ P → Nat.card Q = p → Q ≠ P₁ → Q ≠ P₂ →
        A ⊓ centralizer (Q : Set G) = A ⊓ centralizer (P : Set G)) ∧
      ∀ g ∈ normalizer (A : Set G) ⊓ normalizer (P : Set G),
        ({conjugate P₁ g, conjugate P₂ g} : Set (Subgroup G)) = {P₁, P₂} := by
  have hkey : ∀ Q : Subgroup G, Q ≤ P → Nat.card Q = p → Q ≠ P₁ → Q ≠ P₂ →
      A ⊓ centralizer (Q : Set G) = A ⊓ centralizer (P : Set G) := fun Q hQP hQ hQ₁ hQ₂ =>
    inf_centralizer_eq_of_ne_of_ne hp hpA hPsup hPcomm hP₁ hP₂ hinv₁ hinv₂ hA hc₁ hc₂ hQP hQ
      hQ₁ hQ₂
  have hP₁P : P₁ ≤ P := hPsup ▸ le_sup_left
  have hP₂P : P₂ ≤ P := hPsup ▸ le_sup_right
  have hA₁ : A₁ ≤ A := fun x hx => by
    have : x ∈ (A : Set G) := by rw [hA]; exact ⟨x, hx, 1, one_mem _, mul_one x⟩
    exact this
  have hA₂ : A₂ ≤ A := fun x hx => by
    have : x ∈ (A : Set G) := by rw [hA]; exact ⟨1, one_mem _, x, hx, one_mul x⟩
    exact this
  have hA₂c : A₂ ≤ A ⊓ centralizer (P₁ : Set G) :=
    le_inf hA₂ (commutator_eq_bot_iff_le_centralizer.mp hc₂)
  have hA₁c : A₁ ≤ A ⊓ centralizer (P₂ : Set G) :=
    le_inf hA₁ (commutator_eq_bot_iff_le_centralizer.mp hc₁)
  have hnot₁ : ¬ A ⊓ centralizer (P₁ : Set G) ≤ A ⊓ centralizer (P : Set G) := by
    intro h
    apply hn₂
    rw [commutator_eq_bot_iff_le_centralizer]
    exact (hA₂c.trans h).trans (inf_le_right.trans (centralizer_le hP₂P))
  have hnot₂ : ¬ A ⊓ centralizer (P₂ : Set G) ≤ A ⊓ centralizer (P : Set G) := by
    intro h
    apply hn₁
    rw [commutator_eq_bot_iff_le_centralizer]
    exact (hA₁c.trans h).trans (inf_le_right.trans (centralizer_le hP₁P))
  have hmem : ∀ X : Subgroup G, X ≤ P → (¬ A ⊓ centralizer (X : Set G) ≤
      A ⊓ centralizer (P : Set G)) → ⁅A ⊓ centralizer (X : Set G), P⁆ ≠ ⊥ := by
    intro X _ hX h
    apply hX
    refine le_inf inf_le_left ?_
    exact commutator_eq_bot_iff_le_centralizer.mp h
  refine ⟨?_, hkey, ?_⟩
  · ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hQP, hQ, hne⟩
      by_contra h
      push Not at h
      apply hne
      rw [hkey Q hQP hQ h.1 h.2, commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    · rintro (rfl | rfl)
      · exact ⟨hP₁P, hP₁, hmem _ hP₁P hnot₁⟩
      · exact ⟨hP₂P, hP₂, hmem _ hP₂P hnot₂⟩
  · rintro g ⟨hgA, hgP⟩
    have hcard : ∀ X : Subgroup G, Nat.card (conjugate X g) = Nat.card X := fun X =>
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hle : ∀ X : Subgroup G, X ≤ P → conjugate X g ≤ P := by
      rintro X hXP _ ⟨x, hx, rfl⟩
      have h1 := (mem_normalizer_iff.mp (inv_mem hgP) x).mp (hXP hx)
      simpa using h1
    have hin : ∀ X : Subgroup G, X ≤ P → Nat.card X = p →
        (¬ A ⊓ centralizer (X : Set G) ≤ A ⊓ centralizer (P : Set G)) →
        conjugate X g = P₁ ∨ conjugate X g = P₂ := by
      intro X hXP hX hnot
      by_contra h
      push Not at h
      exact hnot (inf_centralizer_le_of_conjugate hgA hgP
        (hkey _ (hle X hXP) ((hcard X).trans hX) h.1 h.2))
    have hne : conjugate P₁ g ≠ conjugate P₂ g := by
      intro h
      have h12 : P₁ = P₂ := Subgroup.map_injective (MulAut.conj g⁻¹).injective h
      have : Finite P₁ := Nat.finite_of_card_ne_zero (hP₁ ▸ hp.ne_zero)
      have hbot : P₁ = ⊥ := by rw [← inf_idem P₁]; nth_rewrite 2 [h12]; exact hPinf
      have h1 : Nat.card P₁ = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hP₁] at h1
      exact hp.one_lt.ne' h1
    rcases hin P₁ hP₁P hP₁ hnot₁ with h₁ | h₁ <;> rcases hin P₂ hP₂P hP₂ hnot₂ with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) hne
    · rw [h₁, h₂]
    · rw [h₁, h₂, Set.pair_comm]
    · exact absurd (h₁.trans h₂.symm) hne

end CFSG.Quasithin.SteinbergCD
