module

public import CFSG.Sporadic.Co2Smith.Generators
public import CFSG.Sporadic.Co2Smith.GlDataInputs

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glLetterWords_size : Native.glLetterWords.size = 22 := rfl

theorem glLetterWords_lt : ∀ k < 22, ∀ l ∈ Native.glLetterWords[k]!, l < 4 := by
  decide +kernel

theorem glRows_size : Native.glRows.size = 22 := by
  rw [Native.glRows, Array.size_map, glLetterWords_size]

theorem glRows_get {k : ℕ} (hk : k < 22) :
    Native.glRows[k]! = Native.mRows seedRowsArr Native.glLetterWords[k]! :=
  getElem!_map_of_lt _ _ (by rw [glLetterWords_size]; exact hk)

@[expose] noncomputable def glElt (k : ℕ) : K :=
  mWord Native.glLetterWords[k]!

@[expose] noncomputable def glL : Letters where
  elt := glElt
  rows := Native.glRows
  val_eq k hk := by
    have hk' : k < 22 := glRows_size ▸ hk
    rw [glRows_get hk', glElt, mWord_val _ (glLetterWords_lt k hk')]

@[expose] noncomputable def glE (w : List ℕ) : K := lWord glL w

theorem glE_val {w : List ℕ} (hw : ∀ k ∈ w, k < 22) :
    (glE w).val.val = rowsMatrix 22 (Native.glR w) :=
  lWord_val glL w fun k hk => (show glL.rows.size = 22 from glRows_size) ▸ hw k hk

theorem glE_append (w w' : List ℕ) :
    glE (w ++ w') = glE w * glE w' :=
  lWord_append glL w w'

theorem glE_mem_of_letters {S : Subgroup K} {L : List ℕ}
    (hL : ∀ k ∈ L, glElt k ∈ S) {w : List ℕ} (hw : ∀ k ∈ w, k ∈ L) : glE w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons k w ih =>
    change glElt k * lWord glL w ∈ S
    exact S.mul_mem (hL k (hw k List.mem_cons_self))
      (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))

theorem val_mul3 {a b c : K} {A B C : Array ℕ} (ha : a.val.val = rowsMatrix 22 A)
    (hb : b.val.val = rowsMatrix 22 B) (hc : c.val.val = rowsMatrix 22 C) :
    (a * b * c).val.val = rowsMatrix 22 (mulRows 22 (mulRows 22 A B) C) := by
  rw [val_val_mul, val_val_mul, ha, hb, hc, rowsMatrix_mulRows, rowsMatrix_mulRows]

@[expose] noncomputable def α3K : K := glE [9]

@[expose] noncomputable def γ3K : K := glE [10]

@[expose] noncomputable def C0c : Subgroup K :=
  Subgroup.centralizer ({α3K, γ3K} : Set K)

theorem mem_C0c {g : K} :
    g ∈ C0c ↔ α3K * g = g * α3K ∧ γ3K * g = g * γ3K := by
  simp [C0c, Subgroup.mem_centralizer_iff]

@[expose] def glP0 : Fin 2300 := 80

@[expose] noncomputable def G1c :
    Subgroup K :=
  (MulAction.stabilizer (Equiv.Perm (Fin 2300)) glP0).comap co2PermHom

theorem mem_G1c {g : K} :
    g ∈ G1c ↔ co2PermHom g glP0 = glP0 :=
  MulAction.mem_stabilizer_iff

@[expose] noncomputable def C1c :
    Subgroup K :=
  C0c ⊓ G1c

@[expose] noncomputable def x16K : K := glE [0]

@[expose] noncomputable def x61K : K := glE Native.glX61Word

@[expose] noncomputable def δ0hK : K := glE Native.glD0hWord

@[expose] noncomputable def δ1hK : K := glE Native.glD1hWord

@[expose] noncomputable def w1K : K := x16K * x61K * x16K

@[expose] noncomputable def x25K : K := δ1hK * x16K * δ1hK

@[expose] noncomputable def x52K : K := δ1hK * x61K * δ1hK

@[expose] noncomputable def w2K : K := δ1hK * w1K * δ1hK

@[expose] noncomputable def x34K : K := δ0hK * x25K * δ0hK

@[expose] noncomputable def x43K : K := δ0hK * x52K * δ0hK

@[expose] noncomputable def w3K : K := δ0hK * w2K * δ0hK

@[expose] noncomputable def β3K : K := x34K * x43K

@[expose] noncomputable def w0K : K := w1K * w2K * w3K

@[expose] noncomputable def uK : K := glE Native.glUWord

@[expose] noncomputable def vK : K := uK * w0K * uK

@[expose] noncomputable def v1K : K := β3K * β3K * vK * β3K

@[expose] noncomputable def glFormK (t : ℕ) : K :=
  if t == 1 then uK else if t == 2 then vK else 1

@[expose] noncomputable def cPerm : Equiv.Perm (Fin 2300) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 11 => co2Strong h) (toLetters 11 Native.glCWord)

section Rows


theorem α3K_val : α3K.val.val = rowsMatrix 22 Native.glAl := glE_val (by decide)

theorem γ3K_val : γ3K.val.val = rowsMatrix 22 Native.glGa := glE_val (by decide)

theorem x16K_val : x16K.val.val = rowsMatrix 22 Native.glZ := glE_val (by decide)

theorem x16K_eq : x16K = z0 := by
  change mWord Native.glLetterWords[0]! * 1 = z0
  rw [mul_one]
  change mWord [0] = z0
  rw [mWord, lWord, lWord, mul_one]
  rfl

theorem x61K_val : x61K.val.val = rowsMatrix 22 Native.glX61 := glE_val (by decide)

theorem δ0hK_val : δ0hK.val.val = rowsMatrix 22 Native.glD0h := glE_val (by decide)

theorem δ1hK_val : δ1hK.val.val = rowsMatrix 22 Native.glD1h := glE_val (by decide)

theorem uK_val : uK.val.val = rowsMatrix 22 Native.glU := glE_val (by decide)

theorem w1K_val : w1K.val.val = rowsMatrix 22 Native.glW1 := val_mul3 x16K_val x61K_val x16K_val

theorem x25K_val : x25K.val.val = rowsMatrix 22 Native.glX25 :=
  val_mul3 δ1hK_val x16K_val δ1hK_val

theorem x52K_val : x52K.val.val = rowsMatrix 22 Native.glX52 :=
  val_mul3 δ1hK_val x61K_val δ1hK_val

theorem w2K_val : w2K.val.val = rowsMatrix 22 Native.glW2 := val_mul3 δ1hK_val w1K_val δ1hK_val

theorem x34K_val : x34K.val.val = rowsMatrix 22 Native.glX34 :=
  val_mul3 δ0hK_val x25K_val δ0hK_val

theorem x43K_val : x43K.val.val = rowsMatrix 22 Native.glX43 :=
  val_mul3 δ0hK_val x52K_val δ0hK_val

theorem w3K_val : w3K.val.val = rowsMatrix 22 Native.glW3 := val_mul3 δ0hK_val w2K_val δ0hK_val

theorem β3K_val : β3K.val.val = rowsMatrix 22 Native.glB3 := by
  rw [β3K, val_val_mul, x34K_val, x43K_val, Native.glB3, rowsMatrix_mulRows]

theorem w0K_val : w0K.val.val = rowsMatrix 22 Native.glW0 := val_mul3 w1K_val w2K_val w3K_val

theorem vK_val : vK.val.val = rowsMatrix 22 Native.glV := val_mul3 uK_val w0K_val uK_val

theorem v1K_val : v1K.val.val = rowsMatrix 22 Native.glV1 := by
  rw [v1K, val_val_mul, val_val_mul, val_val_mul, β3K_val, vK_val, Native.glV1,
    rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem glFormK_val (t : ℕ) : (glFormK t).val.val = rowsMatrix 22 (Native.glForm t) := by
  unfold glFormK Native.glForm
  split
  · exact uK_val
  · split
    · exact vK_val
    · rw [rowsMatrix_idRows]
      rfl

end Rows

end CFSG.Sporadic.Co2Smith
