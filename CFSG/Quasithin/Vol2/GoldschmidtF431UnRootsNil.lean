module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDefs
public import CFSG.LieType.Universal.Unitary.Extras.Unipotent

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits Matrix

section Nil

variable {F : Type} [Field F]

theorem pow_four_eq_zero {N : Matrix (Fin 4) (Fin 4) F}
    (hN : ∀ a b : Fin 4, b.val ≤ a.val → N a b = 0) : N ^ 4 = 0 := by
  have key : ∀ k : ℕ, ∀ a b : Fin 4, (N ^ k) a b ≠ 0 → a.val + k ≤ b.val := by
    intro k
    induction k with
    | zero =>
      intro a b h
      rw [pow_zero] at h
      by_contra hlt
      exact h (one_apply_ne (fun e => hlt (by simp [e])))
    | succ k ih =>
      intro a b h
      rw [pow_succ, mul_apply] at h
      obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have h1 := ih a c (left_ne_zero_of_mul hc)
      have h2 : c.val < b.val := by
        by_contra hlt
        exact right_ne_zero_of_mul hc (hN c b (by omega))
      omega
  ext a b
  by_contra h
  have := key 4 a b h
  have := b.isLt
  omega

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)

theorem isPGroup_unU : IsPGroup p (unU hF 4) := by
  intro u
  refine ⟨2, ?_⟩
  have hσ := unitaryInvolution_involutive hF
  have hid : IdBelow (lvl 1) 1
      (mat (unitaryInvolution F p f) 4 (u : SU (unitaryInvolution F p f) 4)) :=
    idBelow_of_mem_iSup hσ 1 _ (fun γ hγ => by
      have h : 0 < ht (ι := Fin (4 / 2)) γ := hγ.2
      omega) u.2
  set N : Matrix (Fin 4) (Fin 4) F := mat (unitaryInvolution F p f) 4 (u : SU _ 4) - 1 with hNdef
  have hN : ∀ a b : Fin 4, b.val ≤ a.val → N a b = 0 := by
    intro a b hab
    rw [hNdef, Matrix.sub_apply, hid a b (by simp only [lvl]; omega), sub_self]
  have h4 := pow_four_eq_zero hN
  have hp2 : 4 ≤ p ^ 2 := by
    have := (Fact.out : p.Prime).two_le
    nlinarith
  have hNp : N ^ (p ^ 2) = 0 := by
    rw [show p ^ 2 = 4 + (p ^ 2 - 4) by omega, pow_add, h4, zero_mul]
  have hu : mat (unitaryInvolution F p f) 4 (u : SU _ 4) = 1 + N := by
    rw [hNdef]
    abel
  have key : mat (unitaryInvolution F p f) 4
      ((u : SU (unitaryInvolution F p f) 4) ^ p ^ 2) = 1 := by
    rw [map_pow, hu, add_pow_char_pow_of_commute (R := Matrix (Fin 4) (Fin 4) F) p 2
      (Commute.one_left N), hNp, one_pow, add_zero]
  apply Subtype.ext
  apply mat_injective
  rw [Subgroup.coe_pow, key, Subgroup.coe_one, map_one]

theorem isNilpotent_unU : Group.IsNilpotent (unU hF 4) :=
  (isPGroup_unU hF).isNilpotent

end Nil

end CFSG.Quasithin.H13.F431.Un
