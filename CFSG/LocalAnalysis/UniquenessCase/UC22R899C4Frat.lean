module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem uc22r899c4_frattini_step {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K H S A : Subgroup Γ} (hKH : K ≤ H) (hH : H ≤ normalizer (K : Set Γ))
    (hS : IsSylowOf q S K) (hKS : ∀ y ∈ K, y ∈ normalizer (S : Set Γ) → orderOf y ≠ p)
    (hinf : Nat.card (A ⊓ K : Subgroup Γ) ≤ p) (hA : IsElemAbelian p A) (hAH : A ≤ H) {k : ℕ}
    (hAc : p ^ (k + 1) ≤ Nat.card A) :
    ∃ D : Subgroup Γ, D ≤ H ⊓ normalizer (S : Set Γ) ∧ IsElemAbelian p D ∧
      p ^ k ≤ Nat.card D := by
  obtain ⟨D, hDH, hDel, hDc⟩ :=
    uc22r8100b_exists_elemAbelian_le_normalizer hp hq hKH hH hS hKS hA hAH
  refine ⟨D, hDH, hDel, ?_⟩
  have h : p * p ^ k ≤ p * Nat.card D :=
    calc p * p ^ k = p ^ (k + 1) := by ring
      _ ≤ Nat.card A := hAc
      _ = Nat.card (A ⊓ K : Subgroup Γ) * Nat.card D := hDc
      _ ≤ p * Nat.card D := Nat.mul_le_mul_right _ hinf
  exact Nat.le_of_mul_le_mul_left h hp.pos

theorem uc22r899c4_exists_frattini3 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K S : Fin 3 → Subgroup Γ} {A₀ : Subgroup Γ} (hS : ∀ i, IsSylowOf q (S i) (K i))
    (hKS : ∀ i, ∀ y ∈ K i, y ∈ normalizer (S i : Set Γ) → orderOf y ≠ p)
    (hinf : ∀ i, ∀ B : Subgroup Γ, IsElemAbelian p B → Nat.card (B ⊓ K i : Subgroup Γ) ≤ p)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x)
    (hA₀ : IsElemAbelian p A₀) (hA₀c : Nat.card A₀ = p ^ 4)
    (hA₀N : ∀ i, A₀ ≤ normalizer (K i : Set Γ)) :
    ∃ d : Γ, orderOf d = p ∧
      ∀ i, d ∈ normalizer (K i : Set Γ) ∧ d ∈ normalizer (S i : Set Γ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hKK : ∀ i j, K i ≤ normalizer (K j : Set Γ) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact Subgroup.le_normalizer
    · exact fun x hx => Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.2 fun y hy => (hcomm i j hij x hx y hy).symm)
  have hKS' : ∀ i j, i ≠ j → K i ≤ normalizer (S j : Set Γ) := fun i j hij x hx =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun y hy => (hcomm i j hij x hx y ((hS j).le hy)).symm)
  set H₀ : Subgroup Γ :=
    normalizer (K 0 : Set Γ) ⊓ normalizer (K 1 : Set Γ) ⊓ normalizer (K 2 : Set Γ) with hH₀def
  have hH₀ : ∀ i, H₀ ≤ normalizer (K i : Set Γ) := by
    intro i
    fin_cases i
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have hKH₀ : ∀ i, K i ≤ H₀ := fun i => le_inf (le_inf (hKK i 0) (hKK i 1)) (hKK i 2)
  obtain ⟨D₁, hD₁H, hD₁el, hD₁c⟩ := uc22r899c4_frattini_step hp hq (hKH₀ 0) (hH₀ 0) (hS 0)
    (hKS 0) (hinf 0 A₀ hA₀) hA₀ (le_inf (le_inf (hA₀N 0) (hA₀N 1)) (hA₀N 2)) (k := 3) hA₀c.ge
  obtain ⟨D₂, hD₂H, hD₂el, hD₂c⟩ := uc22r899c4_frattini_step hp hq (K := K 1)
    (H := H₀ ⊓ normalizer (S 0 : Set Γ)) (le_inf (hKH₀ 1) (hKS' 1 0 (by decide)))
    (inf_le_left.trans (hH₀ 1)) (hS 1) (hKS 1) (hinf 1 D₁ hD₁el) hD₁el hD₁H (k := 2) hD₁c
  obtain ⟨D₃, hD₃H, hD₃el, hD₃c⟩ := uc22r899c4_frattini_step hp hq (K := K 2)
    (H := H₀ ⊓ normalizer (S 0 : Set Γ) ⊓ normalizer (S 1 : Set Γ))
    (le_inf (le_inf (hKH₀ 2) (hKS' 2 0 (by decide))) (hKS' 2 1 (by decide)))
    (inf_le_left.trans (inf_le_left.trans (hH₀ 2))) (hS 2) (hKS 2) (hinf 2 D₂ hD₂el) hD₂el hD₂H
    (k := 1) hD₂c
  have hD₃1 : 1 < Nat.card D₃ := lt_of_lt_of_le (by rw [pow_one]; exact hp.one_lt) hD₃c
  obtain ⟨⟨d, hd⟩, hd1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 ((Subgroup.one_lt_card_iff_ne_bot D₃).1 hD₃1)
  have hdo : orderOf d = p := orderOf_eq_prime (hD₃el.2 d hd) fun h => hd1 (Subtype.ext h)
  obtain ⟨⟨⟨hdH₀, hdS0⟩, hdS1⟩, hdS2⟩ := hD₃H hd
  refine ⟨d, hdo, fun i => ⟨hH₀ i hdH₀, ?_⟩⟩
  fin_cases i
  exacts [hdS0, hdS1, hdS2]

end CFSG.LocalAnalysis.UniquenessCase.UC22
