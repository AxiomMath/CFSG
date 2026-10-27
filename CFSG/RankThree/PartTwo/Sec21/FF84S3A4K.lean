module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model
public import CFSG.RankThree.PartTwo.Sec21.FF84S34K

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3A4K

open CFSG.RankThree.PartTwo.Sec21.FF84K CFSG.RankThree.PartTwo.Sec21.FF84.S3 Equiv

@[expose] noncomputable def cen3B (A B C : ℕ) (Z : List ℕ) (x : ℕ) : Bool :=
  ifB (Nat.beq (mulK x A) (mulK A x))
    (ifB (Nat.beq (mulK x B) (mulK B x))
      (ifB (Nat.beq (mulK x C) (mulK C x)) (memK x Z) true) true) true

theorem enc_f5 : enc (List.formPerm [3, 4, 5, 6, 7] : P8) = 929382928 := by decide +kernel

theorem enc_f3 : enc (List.formPerm [3, 4, 5] : P8) = 1983201808 := by decide +kernel

theorem enc_cc : enc (m₁ * m₂) = 1985229058 := by decide +kernel

theorem encZ : [enc (1 : P8), enc (m₁ * m₂), enc ((m₁ * m₂) ^ 2)] =
    [1985229328, 1985229058, 1985228833] := by
  decide +kernel

theorem check :
    allP (cen3B 929382928 1983201808 1985229058 [1985229328, 1985229058, 1985228833]) permsL =
      true := by
  decide +kernel

theorem key (g : P8)
    (h1 : g * (List.formPerm [3, 4, 5] : P8) = (List.formPerm [3, 4, 5] : P8) * g)
    (h2 : g * (List.formPerm [3, 4, 5, 6, 7] : P8) = (List.formPerm [3, 4, 5, 6, 7] : P8) * g)
    (h3 : g * (m₁ * m₂) = (m₁ * m₂) * g) :
    g = 1 ∨ g = m₁ * m₂ ∨ g = (m₁ * m₂) ^ 2 := by
  have hz := forall_perm check g
  have e1 : Nat.beq (mulK (enc g) 929382928) (mulK 929382928 (enc g)) = true := by
    rw [Nat.beq_eq, ← enc_f5, ← enc_mul, ← enc_mul, h2]
  have e2 : Nat.beq (mulK (enc g) 1983201808) (mulK 1983201808 (enc g)) = true := by
    rw [Nat.beq_eq, ← enc_f3, ← enc_mul, ← enc_mul, h1]
  have e3 : Nat.beq (mulK (enc g) 1985229058) (mulK 1985229058 (enc g)) = true := by
    rw [Nat.beq_eq, ← enc_cc, ← enc_mul, ← enc_mul, h3]
  unfold cen3B at hz
  rw [e1, ifB_true, e2, ifB_true, e3, ifB_true] at hz
  have hm := memK_sound hz
  rw [← encZ] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  exact hm.imp enc_inj (Or.imp enc_inj enc_inj)

end CFSG.RankThree.PartTwo.Sec21.FF84.S3A4K
