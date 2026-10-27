module

public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.Code.Basis
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.Code.Basis
import Mathlib.Data.Nat.Bitwise
public import CFSG.Monster.B.TwoA.Census.SignClsInputs
public import Certificates.Certificate3015

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot

@[expose] def OM : ℕ := 2 ^ 24 - 1

theorem bvec_OM : bvec 24 OM = Ω := by decide

@[expose] def canI (n : ℕ) : ℕ := min n (n ^^^ OM)

@[expose] def permI (p : Array ℕ) (n : ℕ) : ℕ :=
  (List.range 24).foldl (fun acc j => if n.testBit j then acc + 2 ^ p[j]! else acc) 0

theorem validList_spec :
    validList.length = 2048 ∧ validList.Nodup ∧ ∀ n ∈ validList, n < 2 ^ 23 ∧ bvec 24 n ∈ C :=
  Certificates.certificate3015

@[expose] def codeCls (n : ℕ) : C ⧸ ΩLine :=
  if h : bvec 24 n ∈ C then Submodule.Quotient.mk ⟨bvec 24 n, h⟩ else 0

theorem codeCls_of_mem {n : ℕ} (h : bvec 24 n ∈ C) :
    codeCls n = Submodule.Quotient.mk ⟨bvec 24 n, h⟩ := by
  unfold codeCls
  simp only [h, ↓reduceDIte]

theorem mem_C_xor {a b : ℕ} (ha : bvec 24 a ∈ C) (hb : bvec 24 b ∈ C) :
    bvec 24 (a ^^^ b) ∈ C := by
  rw [bvec_xor]
  exact C.add_mem ha hb

theorem codeCls_xor {a b : ℕ} (ha : bvec 24 a ∈ C) (hb : bvec 24 b ∈ C) :
    codeCls (a ^^^ b) = codeCls a + codeCls b := by
  rw [codeCls_of_mem (mem_C_xor ha hb), codeCls_of_mem ha, codeCls_of_mem hb,
    ← Submodule.Quotient.mk_add]
  congr 1
  exact Subtype.ext (bvec_xor 24 a b)

theorem bvec_OM_mem : bvec 24 OM ∈ C := by
  rw [bvec_OM]
  exact Ω_mem_C

theorem codeCls_OM : codeCls OM = 0 := by
  rw [codeCls_of_mem bvec_OM_mem, Submodule.Quotient.mk_eq_zero, mem_ΩLine_iff]
  exact Or.inr (Subtype.ext bvec_OM)

theorem canI_eq (n : ℕ) : canI n = n ∨ canI n = n ^^^ OM := by
  unfold canI
  rcases le_total n (n ^^^ OM) with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

theorem mem_C_canI {n : ℕ} (h : bvec 24 n ∈ C) : bvec 24 (canI n) ∈ C := by
  rcases canI_eq n with e | e <;> rw [e]
  · exact h
  · exact mem_C_xor h bvec_OM_mem

theorem codeCls_canI {n : ℕ} (h : bvec 24 n ∈ C) : codeCls (canI n) = codeCls n := by
  rcases canI_eq n with e | e <;> rw [e]
  rw [codeCls_xor h bvec_OM_mem, codeCls_OM, add_zero]

theorem bvec_apply_23 {a : ℕ} (ha : a < 2 ^ 23) : bvec 24 a ⟨23, by norm_num⟩ = 0 := by
  rw [bvec_apply, Nat.testBit_eq_false_of_lt ha]
  rfl

theorem codeCls_inj {a b : ℕ} (ha : a < 2 ^ 23) (hb : b < 2 ^ 23) (hca : bvec 24 a ∈ C)
    (hcb : bvec 24 b ∈ C) (h : codeCls a = codeCls b) : a = b := by
  rw [codeCls_of_mem hca, codeCls_of_mem hcb, Submodule.Quotient.eq, mem_ΩLine_iff] at h
  rcases h with h | h
  · apply CFSG.Monster.VisCert.bvec_injective (by omega) (by omega)
    have := congrArg Subtype.val h
    rw [Submodule.coe_sub, ZeroMemClass.coe_zero, sub_eq_zero] at this
    exact this
  · exfalso
    have := congrFun (congrArg Subtype.val h) ⟨23, by norm_num⟩
    change bvec 24 a ⟨23, by norm_num⟩ - bvec 24 b ⟨23, by norm_num⟩ = Ω ⟨23, by norm_num⟩ at this
    rw [bvec_apply_23 ha, bvec_apply_23 hb] at this
    simp [Ω] at this

theorem codeCls_surj (x : C ⧸ ΩLine) : ∃ n ∈ validList, codeCls n = x
    := by
  have hv := validList_spec
  have hinj : Set.InjOn codeCls {n | n ∈ validList} := fun a ha b hb e =>
    codeCls_inj (hv.2.2 a ha).1 (hv.2.2 b hb).1 (hv.2.2 a ha).2 (hv.2.2 b hb).2 e
  have hcard : (codeCls '' {n | n ∈ validList}).ncard = 2 ^ 11 := by
    rw [hinj.ncard_image,
      show {n | n ∈ validList} = (validList.toFinset : Set ℕ) by ext; simp,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup hv.2.1, hv.1]
    norm_num
  have hfin : Finite (C ⧸ ΩLine) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_quot_ΩLine]; norm_num)
  have huniv : codeCls '' {n | n ∈ validList} = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, natCard_quot_ΩLine, hcard]
  have hx : x ∈ codeCls '' {n | n ∈ validList} := huniv ▸ Set.mem_univ x
  obtain ⟨n, hn, e⟩ := hx
  exact ⟨n, hn, e⟩

theorem permWord_decode {p : Array ℕ} (hp : PermArr p = true) (v : Fin 24 → ZMod 2) :
    permWord (decode p) v = v ∘ arrFun (ainv p) := by
  rw [permWord, ← decode_ainv hp, coe_decode (PermArr_ainv hp)]

theorem codeCls_permI {p : Array ℕ} (hp : PermArr p = true) (hpa : decode p ∈ AutPerm)
    {n : ℕ} (hn : bvec 24 n ∈ C) (hspec : bvec 24 (permI p n) = bvec 24 n ∘ arrFun (ainv p)) :
    codeCls (permI p n) = permQ ⟨decode p, hpa⟩ (codeCls n) := by
  have hmem : bvec 24 (permI p n) ∈ C := by
    rw [hspec, ← permWord_decode hp]
    exact permWord_mem_of_mem_AutPerm hpa hn
  rw [codeCls_of_mem hmem, codeCls_of_mem hn, permQ_mk]
  congr 1
  apply Subtype.ext
  show bvec 24 (permI p n) = _
  rw [coe_permC]
  show bvec 24 (permI p n) = permWord (decode p) (bvec 24 n)
  rw [permWord_decode hp]
  exact hspec

end CFSG.Monster.B.TwoA.Census
