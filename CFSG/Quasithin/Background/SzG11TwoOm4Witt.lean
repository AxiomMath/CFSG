module

public import CFSG.Quasithin.Background.SzG11TwoDescent
public import CFSG.Quasithin.Background.SzG11TwoOm4Form

public section

namespace CFSG.Quasithin.G11.SzG11S.Two.Om4

open LinearMap (BilinForm)

section Chi

variable {K : Type} [Field K]

open Classical in
@[expose] noncomputable def chi (a : K) : ℤ := if a ^ 2 + a = 0 then 1 else -1

theorem tr_add (h2 : (2 : K) = 0) (a b : K) :
    (a + b) ^ 2 + (a + b) = (a ^ 2 + a) + (b ^ 2 + b) := by
  rw [sq_add_of_two_eq_zero h2]
  ring

theorem tr_cases (h2 : (2 : K) = 0) (h4 : ∀ κ : K, κ ^ 4 = κ) (a : K) :
    a ^ 2 + a = 0 ∨ a ^ 2 + a = 1 := by
  have h : (a ^ 2 + a) * (a ^ 2 + a - 1) = 0 := by
    linear_combination (h4 a) + a ^ 3 * h2
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

theorem chi_zero : chi (0 : K) = 1 := by simp [chi]

theorem chi_eq_one_iff (a : K) : chi a = 1 ↔ a ^ 2 + a = 0 := by
  unfold chi
  split_ifs with h <;> simp [h]

theorem chi_eq_neg_one_iff (a : K) : chi a = -1 ↔ a ^ 2 + a ≠ 0 := by
  unfold chi
  split_ifs with h <;> simp [h]

theorem chi_add (h2 : (2 : K) = 0) (h4 : ∀ κ : K, κ ^ 4 = κ) (a b : K) :
    chi (a + b) = chi a * chi b := by
  have h11 : (1 : K) + 1 = 0 := by linear_combination h2
  have hne : (1 : K) ≠ 0 := one_ne_zero
  unfold chi
  rw [tr_add h2 a b]
  rcases tr_cases h2 h4 a with ha | ha <;> rcases tr_cases h2 h4 b with hb | hb <;>
    simp [ha, hb, h11, hne]

theorem sum_eq_zero_of_mul {G : Type} [AddCommGroup G] [Fintype G] (e : G → ℤ)
    (he : ∀ a b, e (a + b) = e a * e b) (t : G) (ht : e t = -1) : ∑ a, e a = 0 := by
  have h : ∑ a, e (a + t) = ∑ a, e a :=
    Fintype.sum_equiv (Equiv.addRight t) _ _ (fun a => rfl)
  simp only [he, ht, mul_neg, mul_one, Finset.sum_neg_distrib] at h
  omega

theorem sum_chi_eq_zero [Fintype K] (h2 : (2 : K) = 0) (h4 : ∀ κ : K, κ ^ 4 = κ)
    (hK : Fintype.card K = 4) : ∑ a : K, chi a = 0 := by
  classical
  have hne : ∃ t : K, t ^ 2 + t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro t _
      have ht := hcon t
      have : t * (t + 1) = 0 := by linear_combination ht
      rcases mul_eq_zero.1 this with h | h
      · simp [h]
      · have : t = 1 := by linear_combination h - h2
        simp [this]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hK] at this
    have h2le : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨t, ht⟩ := hne
  exact sum_eq_zero_of_mul chi (chi_add h2 h4) t ((chi_eq_neg_one_iff t).2 ht)

end Chi

section Main

variable {K V : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V]

theorem sum_chi_pos (h2 : (2 : K) = 0) (hK : Fintype.card K = 4) (Q : V → K) (β : BilinForm K V)
    (hQ : ∀ u v, Q (u + v) = Q u + Q v + β u v) (hβ : ∀ u, (∀ v, β u v = 0) → u = 0)
    (x : V →+ V) (hx : ∀ (κ : K) v, x (κ • v) = κ ^ 2 • x v) (hxx : ∀ v, x (x v) = v)
    (hQx : ∀ v, Q (x v) = Q v ^ 2) : 0 < ∑ v : V, chi (Q v) := by
  classical
  have h4 : ∀ κ : K, κ ^ 4 = κ := fun κ => by
    simpa [hK] using FiniteField.pow_card κ
  have hE : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card, hK]
  have hβ_eq : ∀ u v, β u v = Q (u + v) + Q u + Q v := fun u v => by
    linear_combination (-1 : K) * hQ u v - (Q u + Q v) * h2
  have hvv : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul K v, h2, zero_smul]
  have hβx : ∀ a b, β (x a) (x b) = β a b ^ 2 := by
    intro a b
    rw [hβ_eq, hβ_eq a b, ← map_add, hQx, hQx, hQx, sq_add_of_two_eq_zero h2,
      sq_add_of_two_eq_zero h2]
  obtain ⟨L, hLmem⟩ : ∃ L : AddSubgroup V, ∀ v, v ∈ L ↔ x v = v :=
    ⟨fixAdd x, fun v => mem_fixAdd⟩
  have hLQ : ∀ l : L, Q (l : V) ^ 2 = Q l := by
    intro l
    have := hQx l
    rw [(hLmem l).1 l.2] at this
    exact this.symm
  have hchiL : ∀ l : L, chi (Q (l : V)) = 1 := by
    intro l
    rw [chi_eq_one_iff]
    linear_combination hLQ l + (Q (l : V)) * h2
  obtain ⟨ω, -, -, -, hdec⟩ := frob_decomp hE x hx hxx
  have hβL : ∀ l₀ : V, (∀ l : L, β l₀ (l : V) = 0) → l₀ = 0 := by
    intro l₀ h
    apply hβ
    intro v
    obtain ⟨l₁, h₁, l₂, h₂', rfl⟩ := hdec v
    rw [map_add, map_smul, h ⟨l₁, (hLmem l₁).2 (mem_fixAdd.1 h₁)⟩,
      h ⟨l₂, (hLmem l₂).2 (mem_fixAdd.1 h₂')⟩]
    simp
  have hchi_beta : ∀ (v : V) (l : L), chi (β v (l : V)) = 1 ↔ β (v + x v) (l : V) = 0 := by
    intro v l
    rw [chi_eq_one_iff]
    have e1 : β (x v) (l : V) = β v (l : V) ^ 2 := by
      have := hβx v l
      rwa [(hLmem l).1 l.2] at this
    rw [map_add, LinearMap.add_apply, e1]
    constructor <;> intro h <;> linear_combination h
  have horth : ∀ v : V, ∑ l : L, chi (β v (l : V)) =
      if x v = v then (Fintype.card L : ℤ) else 0 := by
    intro v
    split_ifs with hv
    · have : ∀ l : L, chi (β v (l : V)) = 1 := by
        intro l
        rw [hchi_beta, hv, hvv, map_zero, LinearMap.zero_apply]
      simp [this]
    · have hmem : v + x v ∈ L := by
        rw [hLmem, map_add, hxx, add_comm]
      have hne : v + x v ≠ 0 := by
        intro h
        apply hv
        have h1 : x v = -v := eq_neg_of_add_eq_zero_right h
        rw [h1]
        exact neg_eq_of_add_eq_zero_right (hvv v)
      obtain ⟨l, hl⟩ : ∃ l : L, β (v + x v) (l : V) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hne (hβL _ hcon)
      refine sum_eq_zero_of_mul (fun l : L => chi (β v (l : V))) (fun a b => ?_) l ?_
      · simp only [AddSubgroup.coe_add, map_add, chi_add h2 h4]
      · exact (chi_eq_neg_one_iff _).2 (fun h => hl ((hchi_beta v l).1 ((chi_eq_one_iff _).2 h)))
  have hsum : ∀ l : L, ∑ v : V, chi (Q v) = ∑ v : V, chi (Q v) * chi (β v (l : V)) := by
    intro l
    calc ∑ v : V, chi (Q v) = ∑ v : V, chi (Q (v + (l : V))) :=
          (Fintype.sum_equiv (Equiv.addRight (l : V)) (fun v => chi (Q (v + (l : V))))
            (fun v => chi (Q v)) (fun v => rfl)).symm
      _ = _ := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [hQ, chi_add h2 h4, chi_add h2 h4, hchiL l, mul_one]
  have hcard : Fintype.card L = (Finset.univ.filter (fun v : V => x v = v)).card := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun v => hLmem v))
  have hS : (Fintype.card L : ℤ) * ∑ v, chi (Q v) = (Fintype.card L : ℤ) * Fintype.card L := by
    calc (Fintype.card L : ℤ) * ∑ v, chi (Q v) = ∑ _l : L, ∑ v, chi (Q v) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ l : L, ∑ v, chi (Q v) * chi (β v (l : V)) :=
          Finset.sum_congr rfl (fun l _ => hsum l)
      _ = ∑ v, ∑ l : L, chi (Q v) * chi (β v (l : V)) := Finset.sum_comm
      _ = ∑ v, chi (Q v) * ∑ l : L, chi (β v (l : V)) := by simp only [← Finset.mul_sum]
      _ = ∑ v, chi (Q v) * (if x v = v then (Fintype.card L : ℤ) else 0) := by
          simp only [horth]
      _ = ∑ v, (if x v = v then (Fintype.card L : ℤ) else 0) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          split_ifs with hv
          · rw [hchiL ⟨v, (hLmem v).2 hv⟩, one_mul]
          · rw [mul_zero]
      _ = (Fintype.card L : ℤ) * Fintype.card L := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
            ← hcard]
  have hcZ : (0 : ℤ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hfin : ∑ v, chi (Q v) = Fintype.card L := mul_left_cancel₀ hcZ.ne' hS
  rw [hfin]
  exact hcZ

end Main

end CFSG.Quasithin.G11.SzG11S.Two.Om4
