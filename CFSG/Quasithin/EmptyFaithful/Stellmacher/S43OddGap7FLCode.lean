module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Gap7

namespace FL

@[expose] def co (w : orth.W) (i : Fin 5) : ℕ :=
  (Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1 i).val

@[expose] def enc (w : orth.W) : ℕ :=
  co w 0 + 2 * co w 1 + 4 * co w 2 + 8 * co w 3 + 16 * co w 4

@[expose] def pY (n : ℕ) : ℕ := (n ^^^ (n >>> 2)) % 4

@[expose] def bz (n i : ℕ) : ZMod 2 := (((n >>> i) % 2 : ℕ) : ZMod 2)

@[expose] def mkV (n : ℕ) : Fin 5 → ZMod 2
  | 0 => bz n 0
  | 1 => bz n 1
  | 2 => bz n 2
  | 3 => bz n 3
  | 4 => bz n 0 + bz n 1 + bz n 2 + bz n 3

theorem mkV_mem (n : ℕ) : Multiplicative.ofAdd (mkV n) ∈ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  change ∑ i, mkV n i = 0
  rw [Fin.sum_univ_five]
  change bz n 0 + bz n 1 + bz n 2 + bz n 3 + (bz n 0 + bz n 1 + bz n 2 + bz n 3) = 0
  generalize bz n 0 = a
  generalize bz n 1 = b
  generalize bz n 2 = c
  generalize bz n 3 = d
  revert a b c d
  decide

@[expose] def mkW (n : ℕ) : orth.W := (⟨Multiplicative.ofAdd (mkV n), mkV_mem n⟩ : G6.coreMod 5)

@[expose] def pm (f g : Fin 5 → Fin 5) (h₁ : ∀ i, g (f i) = i := by decide)
    (h₂ : ∀ i, f (g i) = i := by decide) : Perm (Fin 5) :=
  ⟨f, g, h₁, h₂⟩

@[expose] def prodSel {M : Type} [Monoid M] : List Bool → List M → M
  | b :: bs, x :: xs => cond b x 1 * prodSel bs xs
  | _, _ => 1

@[expose] def xorSel : List Bool → List ℕ → ℕ
  | b :: bs, x :: xs => cond b x 0 ^^^ xorSel bs xs
  | _, _ => 0

@[expose] def qL (c : Perm (Fin 5) → Perm (Fin 5) → orth.W) : List (Perm (Fin 5)) → orth.W
  | [] => 1
  | h :: t => qL c t * (t.map (fun h' => c h h')).prod

@[expose] def fld (x p w : ℕ) : ℕ := (x >>> p) % 2 ^ w

@[expose] def nb (x i : ℕ) : ℕ := (x >>> (4 * i)) % 16

@[expose] def fnz (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cond (Nat.beq (nb x (29 - n)) 0) (fnz x n) (nb x (29 - n))

@[expose] def allIn (x v : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => (Nat.beq (nb x n) 0 || Nat.beq (nb x n) v) && allIn x v n

@[expose] def goodN (v : ℕ) : Bool := Nat.beq ((0x6ac0 >>> v) % 2) 1

@[expose] def pChk (x : ℕ) : Bool :=
  (Nat.beq (fnz x 30) 0 || goodN (fnz x 30)) && allIn x (fnz x 30) 30

@[expose] def OW : ℕ := 120

@[expose] def witAt (x n : ℕ) : Bool :=
  Nat.beq (fld x (OW + 12 * n) 5) 0 && Nat.beq (fld x (OW + 12 * n + 5) 5) 0 &&
    !Nat.beq (fld x (OW + 12 * n + 10) 2) 0

@[expose] def witAny (x : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => witAt x n || witAny x n

@[expose] def OC : ℕ := 252

@[expose] def leafN (x : ℕ) : Bool := Nat.beq (x >>> OC) 0 || witAny x 11

@[expose] def enumN : List ℕ → ℕ → Bool
  | [], acc => leafN acc
  | c :: cs, acc => enumN cs acc && enumN cs (acc ^^^ c)

@[expose] def enumP (cN : List ℕ) : List ℕ → ℕ → Bool
  | [], acc => !pChk acc || enumN cN acc
  | c :: cs, acc => enumP cN cs acc && enumP cN cs (acc ^^^ c)

end FL

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
