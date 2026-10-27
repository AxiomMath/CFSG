module

public import CFSG.Quasithin.Background.F918W0
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.D35ValChk

open Matrix

inductive InClos : Nat → Prop
  | one : InClos kid
  | mul {g : Nat} (i : Nat) : i < 3 → InClos g → InClos (kmul g (genK i))

structure D35Facts : Prop where
  conj_u0 : ∀ x ∈ tList, ∃ B B', B < 262144 ∧ B' < 262144 ∧ kmul x B = kmul B u0 ∧ kmul B B' = kid
  pair_bij : ∀ x2 ∈ tList, ∀ x3 ∈ tList, x2 ≠ u0 → x3 ≠ u0 → x2 ≠ x3 →
    isScalK (kpow3 (kmul u0 x2)) = true → isScalK (kpow3 (kmul u0 x3)) = true →
    isScalK (kpow4 (kmul x2 x3)) = true → isScalK (kpow5 (kmul (kmul u0 x2) x3)) = true →
    ∃ s P Q, s < 2 ∧ P < 2 ^ 36 ∧ Q < 2 ^ 36 ∧ bmul P (expand u0) = bmul (expand u0) P ∧
      bmul P (expand x2) = bmul (expand (refA s)) P ∧ bmul P (expand x3) = bmul (expand (refB s)) P ∧
      bmul P Q = idm
  gl_mem : kid ∈ gl ∧ u0 ∈ gl ∧ a0 ∈ gl ∧ b0 ∈ gl
  gl_nodup : gl.Nodup
  gl_length : gl.length = 1080
  gl_lt : ∀ g ∈ gl, g < 262144
  gl_closed : ∀ g ∈ gl, ∀ i, i < 3 → kmul g (genK i) ∈ gl
  gl_gen : ∀ g ∈ gl, InClos g
  scal_mem : kom ∈ gl ∧ kom2 ∈ gl
  scal_central : ∀ i, i < 3 →
    kmul kom (genK i) = kmul (genK i) kom ∧ kmul kom2 (genK i) = kmul (genK i) kom2
  center_scal : ∀ g ∈ gl, (∀ i, i < 3 → kmul g (genK i) = kmul (genK i) g) → isScalK g = true
  inv_fix : ∀ a ∈ invList, 2 * popc (fixMask a) < 64
  no_rank3 : ∀ a ∈ invList, ∀ b ∈ invList, a ≠ b → comm a b = true → ∀ c ∈ invList,
    comm a c = true → comm b c = true → c = a ∨ c = b ∨ c = kmul a b
  off_ref : (e1, e2) ∈ offPairs
  off_conj : ∀ p ∈ offPairs, ∃ γ γ', γ ∈ gl ∧ γ' ∈ gl ∧ kmul γ γ' = kid ∧
    memF p.1 p.2 (kmul (kmul γ e1) γ') = true ∧ memF p.1 p.2 (kmul (kmul γ e2) γ') = true ∧
    kmul (kmul γ e1) γ' ≠ kmul (kmul γ e2) γ'
  triple_bij : ∀ x1 x2 x3, (x1, x2, x3) ∈ presList → ∃ P Q, P < 2 ^ 36 ∧ Q < 2 ^ 36 ∧
    bmul P (expand u0) = bmul (expand x1) P ∧ bmul P (expand a0) = bmul (expand x2) P ∧
    bmul P (expand b0) = bmul (expand x3) P ∧ bmul P Q = idm

@[expose] def toM (n : Nat) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun r s => if Nat.testBit n (6 * r.val + s.val) then 1 else 0

@[expose] def vecOfBits (v : Nat) : Fin 6 → ZMod 2 := fun i => if Nat.testBit v i.val then 1 else 0

@[expose] def G0 : Subgroup (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) :=
  Subgroup.closure {g | ∃ i, i < 3 ∧
    ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand (genK i))}

@[expose] def OffF2 (E : Subgroup G0) : Prop :=
  E ≠ ⊥ ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
    64 ≤ Nat.card E * Nat.card {v : Fin 6 → ZMod 2 // ∀ e ∈ E,
      (((e : G0) : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v}

@[expose] def V4set (a b : Nat) : Set G0 :=
  {h | h = 1 ∨ ∃ c, memF a b c = true ∧
    ((h : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand c)}

structure KCoding (K : Type) [Field K] where
  dec : Nat → K
  enc : K → Nat
  enc_lt : ∀ c, enc c < 4
  dec_enc : ∀ c, dec (enc c) = c
  enc_dec : ∀ e, e < 4 → enc (dec e) = e
  dec_zero : dec 0 = 0
  dec_one : dec 1 = 1
  dec_xor : ∀ a b, a < 4 → b < 4 → dec (Nat.xor a b) = dec a + dec b
  dec_smul : ∀ a b, a < 4 → b < 4 → dec (smul a b) = dec a * dec b

@[expose] def KCoding.mc {K : Type} [Field K] (C : KCoding K) (A : Matrix (Fin 3) (Fin 3) K) : Nat :=
  C.enc (A 0 0) + 4 * C.enc (A 0 1) + 16 * C.enc (A 0 2) + 64 * C.enc (A 1 0) + 256 * C.enc (A 1 1) +
    1024 * C.enc (A 1 2) + 4096 * C.enc (A 2 0) + 16384 * C.enc (A 2 1) + 65536 * C.enc (A 2 2)

@[expose] def KCoding.vc {K : Type} [Field K] (C : KCoding K) (w : Fin 3 → K) : Nat :=
  C.enc (w 0) + 4 * C.enc (w 1) + 16 * C.enc (w 2)

end CFSG.Quasithin.D35ValChk
