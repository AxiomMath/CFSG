module

public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian

public section

open CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem exists_mul_eq_of_mem_sup_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G} (hy : y ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    hc a a.2 b b.2
  rw [← Subgroup.range_subtype A, ← Subgroup.range_subtype B,
    ← MonoidHom.noncommCoprod_range A.subtype B.subtype hcomm] at hy
  obtain ⟨⟨a, b⟩, rfl⟩ := hy
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem exists_eq_mul_zpow_of_card {G : Type*} [Group G] [Finite G] {E N : Subgroup G}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) (hcardA : Nat.card (E ⊓ N : Subgroup G) = 9)
    {φ : G} (hφE : φ ∈ E) (hφN : φ ∉ N) :
    ∀ e ∈ E, ∃ b ∈ E ⊓ N, ∃ a : ℤ, e = b * φ ^ a := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hφ1 : φ ≠ 1 := fun h => hφN (h ▸ N.one_mem)
  have hφ3 : φ ^ 3 = 1 := hE.2 φ hφE
  have hord : orderOf φ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨hp⟩
    exact orderOf_eq_prime hφ3 hφ1
  set A : Subgroup G := E ⊓ N with hA
  have hAE : A ≤ E := inf_le_left
  have hzE : Subgroup.zpowers φ ≤ E := (Subgroup.zpowers_le).2 hφE
  have hdisj : A ⊓ Subgroup.zpowers φ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, a, rfl⟩
    have hxN : φ ^ a ∈ N := hxA.2
    show φ ^ a ∈ (⊥ : Subgroup G)
    have hmod : φ ^ a = φ ^ (a % 3) := by
      rw [← zpow_mod_orderOf, hord]
      norm_cast
    have h3a : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h3a with h0 | h1 | h2
    · rw [hmod, h0, zpow_zero]
      exact Subgroup.one_mem _
    · exfalso
      rw [hmod, h1, zpow_one] at hxN
      exact hφN hxN
    · exfalso
      rw [hmod, h2] at hxN
      apply hφN
      have h4 : φ = (φ ^ (2 : ℤ)) ^ (2 : ℕ) := by
        rw [← zpow_natCast, ← _root_.zpow_mul]
        have : φ ^ (4 : ℤ) = φ := by
          have : φ ^ (4 : ℕ) = φ := by
            rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hφ3, one_mul, pow_one]
          exact_mod_cast this
        simpa using this.symm
      rw [h4]
      exact N.pow_mem hxN 2
  obtain ⟨F', hF'E, hzF, hAF, hsup⟩ :=
    CFSG.SignalizerFunctorTheorem.exists_complement_containing hp hE hAE hzE hdisj
  have hcard := CFSG.SignalizerFunctorTheorem.card_mul_card_complement hE hAE hF'E hAF hsup
  have hF'3 : Nat.card F' = 3 := by
    rw [hcardA, hc] at hcard
    omega
  have hz3 : Nat.card (Subgroup.zpowers φ) = 3 := by rw [Nat.card_zpowers, hord]
  have hF'eq : Subgroup.zpowers φ = F' :=
    Subgroup.eq_of_le_of_card_ge hzF (by rw [hF'3, hz3])
  intro e he
  have hes : e ∈ A ⊔ Subgroup.zpowers φ := by
    rw [hF'eq, hsup]
    exact he
  obtain ⟨b, hb, c, hc', rfl⟩ := exists_mul_eq_of_mem_sup_of_comm (fun a ha b hb => by
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨a, hAE ha⟩ : E) ⟨b, hzE hb⟩)) hes
  obtain ⟨a, rfl⟩ := hc'
  exact ⟨b, hb, a, rfl⟩

theorem zpow_apply_eq_of_fixes {X : Type} [Group X] {f : MulAut X} {l : X} (h : f l = l)
    (a : ℤ) : (f ^ a) l = l :=
  (MulAction.stabilizer (MulAut X) l).zpow_mem (show f ∈ MulAction.stabilizer (MulAut X) l from h) a

end CFSG.RankThree.PartTwo.Sec4.E27
