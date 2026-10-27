module

public import CFSG.Quasithin.EmptyFaithful.SzN31Top
public import CFSG.Quasithin.EmptyFaithful.SzN31CntM3p

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem counting_bound {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G11.G94Hyp Γ A m)
    (kc3 : Nat.card A ≤ 4 * Nat.card ↥(A ⊓ Subgroup.centralizer (pCoreOf 3 Γ : Set (GLV V)))) :
    m ≤ 2 := by
  by_cases hex : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
      ¬ A ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V))
  · obtain ⟨p, hp, h5, hnot⟩ := hex
    have := (counting_prime_ge_five hyp hp h5 hnot).1
    omega
  · push Not at hex
    have hbot := g94_inf_centralizer_pCoreOf_three_eq_bot hyp hex
    rw [hbot, Subgroup.card_bot, hyp.A_card] at kc3
    by_contra h
    push Not at h
    have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    omega

end Main

theorem g94Counting : G94Counting := by
  intro V _ _ _ Γ A m hyp _ hkc
  have hk := hkc 3 Nat.prime_three (by norm_num) (pCoreOf 3 Γ) A (Subgroup.map_subtype_le _)
    hyp.A_le (isPGroup_pCoreOf 3 Γ)
    (fun b hb => ⟨by rw [← pow_two]; exact hyp.A_elem.2 b hb, fun c hc =>
      G8.commute_of_isElemAbelian hyp.A_elem hb hc⟩)
    (fun b hb x hx => pCoreOf_normal_conj 3 Γ b (hyp.A_le hb) x hx)
  exact counting_bound hyp hk

end CFSG.Quasithin.SzN31
