module

public import CFSG.Monster.CodeAut.Affine
public import CFSG.Monster.CodeAut.Perm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Monster.Code

@[expose] def frameMask (k : ℕ) : ℕ := [0x6ca60, 0xa6ca0, 0x2222e1, 0x428e81].getD k 0

@[expose] def frameWord (k : Fin 4) : Fin 24 → ZMod 2 := bvec 24 (frameMask k)

private theorem frameWord_mem_C : ∀ k, frameWord k ∈ C := by decide

private theorem frameWord_supp : ∀ k i, frameWord k i ≠ 0 → B 0 i = 0 := by decide

theorem frameWord_mem (k : Fin 4) : frameWord k ∈ CJc (B 0) :=
  mem_CJc.2 ⟨frameWord_mem_C k, frameWord_supp k⟩

theorem frame_linearIndependent :
    LinearIndependent (ZMod 2) (Fin.cons (Ω + B 0) frameWord : Fin 5 → Fin 24 → ZMod 2) := by
  rw [Fintype.linearIndependent_iff]
  decide

@[expose] def frameLabel (i : {i // B 0 i = 0}) : Fin 4 → ZMod 2 := fun k => frameWord k i

theorem frame_affine : Function.Bijective frameLabel ∧
    ∀ a : Fin 24 → ZMod 2, a ∈ CJc (B 0) ↔ (∀ i, a i ≠ 0 → B 0 i = 0) ∧
      ∃ (c₀ : ZMod 2) (t : Fin 4 → ZMod 2), ∀ i : {i // B 0 i = 0},
        a i = c₀ + ∑ k, t k * frameWord k i :=
  affine_of_linearIndependent (B_mem_C 0) (wt_B 0) frameWord_mem frame_linearIndependent

theorem exists_affine {p : Equiv.Perm (Fin 24)} (hp : p ∈ AutPerm)
    (hs : ∀ i, B 0 (p i) = B 0 i) :
    ∃ A : GL (Fin 4) (ZMod 2), ∃ b : Fin 4 → ZMod 2, ∀ i : {i // B 0 i = 0},
      frameLabel ⟨p i, (hs i).trans i.2⟩ =
        (A : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (frameLabel i) + b := by
  have hK : ∀ k, frameWord k ∘ ⇑p ∈ CJc (B 0) := fun k =>
    mem_CJc.2 ⟨comp_mem_of_mem_AutPerm hp (frameWord_mem_C k), fun i hi => by
      rw [← hs i]
      exact frameWord_supp k (p i) hi⟩
  have hrow : ∀ k, ∃ (c₀ : ZMod 2) (t : Fin 4 → ZMod 2), ∀ i : {i // B 0 i = 0},
      (frameWord k ∘ ⇑p) i = c₀ + ∑ l, t l * frameWord l i :=
    fun k => ((frame_affine.2 _).1 (hK k)).2
  choose b t ht using hrow
  set A : Matrix (Fin 4) (Fin 4) (ZMod 2) := Matrix.of fun k l => t k l with hAdef
  have hA : ∀ i : {i // B 0 i = 0},
      frameLabel ⟨p i, (hs i).trans i.2⟩ = A.mulVec (frameLabel i) + b := by
    intro i
    funext k
    have := ht k i
    simp only [Function.comp_apply] at this
    simp only [frameLabel, Pi.add_apply, Matrix.mulVec, dotProduct, hAdef, Matrix.of_apply, this]
    ring
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    obtain ⟨i, rfl⟩ := frame_affine.1.2 x
    obtain ⟨j, rfl⟩ := frame_affine.1.2 y
    have h1 : frameLabel ⟨p i, (hs i).trans i.2⟩ = frameLabel ⟨p j, (hs j).trans j.2⟩ := by
      rw [hA, hA, hxy]
    have h2 := congrArg Subtype.val (frame_affine.1.1 h1)
    rw [Subtype.ext (p.injective h2)]
  exact ⟨(Matrix.mulVec_injective_iff_isUnit.1 hinj).unit, b, hA⟩

@[expose] def duadMask (t : ℕ) : ℕ :=
  [0xca6006, 0x6ca00a, 0x482e12, 0x4821e2, 0xa63003, 0xa9c003, 0x56c003].getD t 0

@[expose] def duadWord (t : Fin 7) : Fin 24 → ZMod 2 := bvec 24 (duadMask t)

private theorem duadWord_mem : ∀ t, duadWord t ∈ C := by decide

private theorem duadWord_ne : ∀ t, hammingNorm (duadWord t + B 0) ≠ hammingNorm (duadWord t) := by
  intro t
  rw [duadWord, B_eq_bvec, ← bvec_xor, hammingNorm_bvec, hammingNorm_bvec]
  revert t
  decide

private theorem duad_sep : ∀ j m : Fin 24, B 0 j ≠ 0 → B 0 m ≠ 0 →
    (∀ t, duadWord t m = duadWord t j) → m = j := by
  decide

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

theorem eq_one_of_fix_compl {r : Equiv.Perm (Fin 24)} (hr : r ∈ AutPerm)
    (hfix : ∀ i, B 0 i = 0 → r i = i) : r = 1 := by
  have hduad : ∀ t, duadWord t ∘ ⇑r = duadWord t := by
    intro t
    have ha := duadWord_mem t
    have he : duadWord t + duadWord t ∘ ⇑r ∈ C := C.add_mem ha (comp_mem_of_mem_AutPerm hr ha)
    have hs : ∀ i, (duadWord t + duadWord t ∘ ⇑r) i ≠ 0 → B 0 i ≠ 0 := by
      intro i hi h0
      apply hi
      simp only [Pi.add_apply, Function.comp_apply, hfix i h0, zmod2_add_self]
    rcases eq_zero_or_eq_of_supp_subset (wt_B 0) he hs with h | h
    · funext i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      rw [← sub_eq_zero, sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
      exact this
    · exfalso
      have e : duadWord t ∘ ⇑r = duadWord t + B 0 := by
        rw [← h, ← add_assoc, word_add_self, zero_add]
      have hn := hammingNorm_comp_perm (duadWord t) r
      rw [e] at hn
      exact duadWord_ne t hn
  have hJ : ∀ j, B 0 j ≠ 0 → B 0 (r j) ≠ 0 := by
    intro j hj h0
    apply hj
    rw [← r.injective (hfix _ h0)]
    exact h0
  refine Equiv.ext fun j => ?_
  by_cases hj : B 0 j = 0
  · simp [hfix j hj]
  · have := duad_sep j (r j) hj (hJ j hj) fun t => congrFun (hduad t) j
    simpa using this

attribute [local instance] arrowAction

private theorem smul_apply (p : AutPerm) (x : Fin 24 → ZMod 2) (i : Fin 24) :
    (p • x) i = x ((p : Equiv.Perm (Fin 24))⁻¹ i) := rfl

private theorem stab_fix {p : AutPerm} (hp : p ∈ MulAction.stabilizer AutPerm (B 0)) (i : Fin 24) :
    B 0 ((p : Equiv.Perm (Fin 24)) i) = B 0 i := by
  have := congrFun (MulAction.mem_stabilizer_iff.1 hp) ((p : Equiv.Perm (Fin 24)) i)
  rw [smul_apply] at this
  simpa using this.symm

private theorem card_stabilizer_le : Nat.card (MulAction.stabilizer AutPerm (B 0)) ≤ 322560 := by
  classical
  have hex : ∀ p : MulAction.stabilizer AutPerm (B 0),
      ∃ Ab : GL (Fin 4) (ZMod 2) × (Fin 4 → ZMod 2), ∀ i : {i // B 0 i = 0},
        frameLabel ⟨((p : AutPerm) : Equiv.Perm (Fin 24)) i, (stab_fix p.2 i).trans i.2⟩ =
          (Ab.1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (frameLabel i) + Ab.2 := by
    intro p
    obtain ⟨A, b, h⟩ := exists_affine (p : AutPerm).2 (stab_fix p.2)
    exact ⟨(A, b), h⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro p q hpq
    have hpt : ∀ i, B 0 i = 0 → ((p : AutPerm) : Equiv.Perm (Fin 24)) i =
        ((q : AutPerm) : Equiv.Perm (Fin 24)) i := by
      intro i hi
      have h1 := hf p ⟨i, hi⟩
      rw [hpq, ← hf q ⟨i, hi⟩] at h1
      exact congrArg Subtype.val (frame_affine.1.1 h1)
    have hr : ((q : AutPerm) : Equiv.Perm (Fin 24))⁻¹ * ((p : AutPerm) : Equiv.Perm (Fin 24)) ∈
        AutPerm := AutPerm.mul_mem (AutPerm.inv_mem (q : AutPerm).2) (p : AutPerm).2
    have h1 := eq_one_of_fix_compl hr fun i hi => by
      rw [Equiv.Perm.mul_apply, hpt i hi]
      simp
    have h2 : ((p : AutPerm) : Equiv.Perm (Fin 24)) = ((q : AutPerm) : Equiv.Perm (Fin 24)) := by
      rw [← mul_one ((q : AutPerm) : Equiv.Perm (Fin 24)), ← h1, mul_inv_cancel_left]
    exact Subtype.ext (Subtype.ext h2)
  have hcard := Nat.card_le_card_of_injective f hinj
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have hGL : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field, ZMod.card]
    simp [Fin.prod_univ_four]
  rw [Nat.card_prod, hGL, h16] at hcard
  exact hcard

private theorem card_orbit_le : Nat.card (MulAction.orbit AutPerm (B 0)) ≤ 759 := by
  classical
  set S : Finset (Fin 24 → ZMod 2) :=
    (Finset.univ.filter (· ∈ C)).filter fun x => hammingNorm x = 8 with hS
  have hsub : MulAction.orbit AutPerm (B 0) ⊆ (S : Set (Fin 24 → ZMod 2)) := by
    rintro _ ⟨p, rfl⟩
    have hmem : p • B 0 ∈ C := by
      have : p • B 0 = B 0 ∘ ⇑((p : Equiv.Perm (Fin 24))⁻¹) := rfl
      rw [this]
      exact comp_mem_of_mem_AutPerm (AutPerm.inv_mem p.2) (B_mem_C 0)
    have hwt : hammingNorm (p • B 0) = 8 := by
      have : p • B 0 = B 0 ∘ ⇑((p : Equiv.Perm (Fin 24))⁻¹) := rfl
      rw [this, hammingNorm_comp_perm, wt_B]
    simp [hS, hmem, hwt]
  have h := Nat.card_mono (Set.toFinite _) hsub
  have hS8 : Nat.card (S : Set (Fin 24 → ZMod 2)) = 759 := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hS, card_filter_wt, wtCount_eight]
  rw [hS8] at h
  exact h

theorem card_AutPerm_le : Nat.card AutPerm ≤ 244823040 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer AutPerm (B 0))
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h
  rw [← h]
  calc Nat.card (MulAction.stabilizer AutPerm (B 0)) * Nat.card (MulAction.orbit AutPerm (B 0))
      ≤ 322560 * 759 := Nat.mul_le_mul card_stabilizer_le card_orbit_le
    _ = 244823040 := by norm_num

end CFSG.Monster.Code
