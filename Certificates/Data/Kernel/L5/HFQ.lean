module

public import Certificates.Data.Kernel.L5.HFC

public section

namespace CFSG.Certificates.Kernel.L5Q

open CFSG.Certificates.Kernel.PkCV CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def linV (a b c d i : Nat) : Nat :=
  Nat.xor
    (Nat.xor (nIf(Nat.beq (Nat.land i (nat_lit 1)) (nat_lit 0), nat_lit 0, a))
      (nIf(Nat.beq (Nat.land i (nat_lit 2)) (nat_lit 0), nat_lit 0, b)))
    (Nat.xor (nIf(Nat.beq (Nat.land i (nat_lit 4)) (nat_lit 0), nat_lit 0, c))
      (nIf(Nat.beq (Nat.land i (nat_lit 8)) (nat_lit 0), nat_lit 0, d)))

@[expose] noncomputable def orF (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (f i))) n

theorem testBit_orF (f : Nat → Nat) (e : Nat) :
    ∀ n, (orF f n).testBit e = true ↔ ∃ i < n, f i = e
  | 0 => by
    change (0 : Nat).testBit e = true ↔ _
    simp
  | n + 1 => by
    change (orF f n ||| 1 <<< f n).testBit e = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_orF f e n, Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hn : i = n
      · subst hn
        exact Or.inr h
      · exact Or.inl ⟨i, by omega, h⟩

theorem wC16q : wC 16 = 5 := by
  unfold wC
  rw [(Nat.log2_eq_iff (n := 17) (k := 4) (by norm_num)).2 ⟨by norm_num, by norm_num⟩]

theorem canon_of_orF {f : Nat → Nat} (h : orF f 16 = 65535) : Canon 16 (pmk 16 5 f) := by
  have hb : ∀ e, (orF f 16).testBit e = true ↔ e < 16 := by
    intro e
    rw [h, show (65535 : Nat) = 2 ^ 16 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      decide_eq_true_iff]
  have hlt : ∀ x < 16, f x < 16 := fun x hx => (hb (f x)).1 ((testBit_orF f _ 16).2 ⟨x, hx, rfl⟩)
  have hsurj : ∀ e < 16, ∃ i < 16, f i = e := fun e he => (testBit_orF f e 16).1 ((hb e).2 he)
  let F : Fin 16 → Fin 16 := fun i => ⟨f i.val, hlt i.val i.isLt⟩
  have hF : Function.Surjective F := fun e => by
    obtain ⟨i, hi, he⟩ := hsurj e.val e.isLt
    exact ⟨⟨i, hi⟩, Fin.ext he⟩
  have hinj : Function.Injective F := Finite.injective_iff_surjective.2 hF
  have c := canon_pmk (n := 16) (f := f) (by norm_num) hlt (fun a ha b hb' e => by
    have := @hinj ⟨a, ha⟩ ⟨b, hb'⟩ (Fin.ext e)
    exact congrArg Fin.val this)
  rwa [wC16q] at c

@[expose] noncomputable def permV (a b c d : Nat) : Bool :=
  Nat.beq (orF (linV a b c d) (nat_lit 16)) (nat_lit 65535)

@[expose] noncomputable def cvV (a b c d : Nat) : CV 16 :=
  if h : permV a b c d = true then
    ⟨pmk 16 5 (linV a b c d), canon_of_orF (Nat.eq_of_beq_eq_true h)⟩
  else 1

@[expose] def f16 (a : Nat) : Fin 16 := ⟨a % 16, Nat.mod_lt _ (by decide)⟩

@[expose] noncomputable def rowQ (g : Fin 16 → Fin 16 → Bool) (c : CV 16 → Bool) (k : Nat) : Bool :=
  allN 4 fun a' => strictB (Nat.add (Nat.mul 4 k) a') fun a =>
    allN 16 fun b => bIf(g (f16 a) (f16 b),
      allN 16 (fun c' => allN 16 fun d => bIf(permV a b c' d, c (cvV a b c' d), true)), true)

end CFSG.Certificates.Kernel.L5Q

end
