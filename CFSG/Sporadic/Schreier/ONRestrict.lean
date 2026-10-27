module

public import CFSG.Sporadic.Schreier.ONGlue
public import CFSG.Perm.OrbitTree
public import CFSG.Sporadic.Schreier.ONPermArr
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Certificates
open scoped Pointwise

section Restrict

variable {G α : Type*} [Group G] [MulAction G α] (I : List α) (H : Subgroup G)
  (hH : ∀ h ∈ H, ∀ p ∈ I, h • p ∈ I)

@[expose] def listSub : SubMulAction H α where
  carrier := {p | p ∈ I}
  smul_mem' h p hp := hH h h.2 p hp

open scoped Classical in
@[expose] def listEquiv (hI : I.Nodup) : Fin I.length ≃ listSub I H hH :=
  (hI.getEquiv I).trans (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem listEquiv_apply (hI : I.Nodup) (i : Fin I.length) :
    ((listEquiv I H hH hI i : listSub I H hH) : α) = I.get i := by
  simp only [listEquiv, Equiv.trans_apply]
  rfl

@[expose] def listRestrict (hI : I.Nodup) : H →* Equiv.Perm (Fin I.length) :=
  (listEquiv I H hH hI).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom H (listSub I H hH))

theorem listRestrict_apply (hI : I.Nodup) (h : H) (i : Fin I.length) :
    listRestrict I H hH hI h i = (listEquiv I H hH hI).symm (h • listEquiv I H hH hI i) := rfl

theorem get_listRestrict (hI : I.Nodup) (h : H) (i : Fin I.length) :
    I.get (listRestrict I H hH hI h i) = (h : G) • I.get i := by
  have e : listEquiv I H hH hI (listRestrict I H hH hI h i) = h • listEquiv I H hH hI i := by
    rw [listRestrict_apply, Equiv.apply_symm_apply]
  have e' := congrArg Subtype.val e
  rw [listEquiv_apply] at e'
  exact e'

theorem listRestrict_eq_iff (hI : I.Nodup) (h : H) (i j : Fin I.length) :
    listRestrict I H hH hI h i = j ↔ (h : G) • I.get i = I.get j := by
  rw [← get_listRestrict I H hH hI h i]
  constructor
  · rintro rfl
    rfl
  · intro e
    exact (hI.get_inj_iff).1 e

theorem listRestrict_eq_one (hI : I.Nodup) (h : H) (hfix : ∀ p ∈ I, (h : G) • p = p) :
    listRestrict I H hH hI h = 1 := by
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply, listRestrict_eq_iff]
  exact hfix _ (List.get_mem I i)

end Restrict

theorem listInvariant {G α : Type*} [Group G] [MulAction G α] (I : List α) {A : Set G}
    (hA : ∀ a ∈ A, ∀ p ∈ I, a • p ∈ I) : ∀ h ∈ Subgroup.closure A, ∀ p ∈ I, h • p ∈ I :=
  fun _ hh _ hp => CFSG.Perm.smul_mem_of_finite_of_mem_closure (F := {p | p ∈ I})
    I.finite_toSet hA hh hp

variable {n : ℕ}

theorem coversOK_spec {A B : Array (Array ℕ)} (h : coversOK n A B = true) {i : ℕ}
    (hi : i < A.size) : peq n A[i]! (pid n) = true ∨ ∃ j < B.size, peq n A[i]! B[j]! = true := by
  have := allBelowN_spec h hi
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with h1 | h2
  · exact Or.inl h1
  · right
    by_contra hne
    push Not at hne
    have : allBelowN B.size (fun j => !peq n A[i]! B[j]!) = true :=
      allBelowN_iff.2 fun j hj => by simpa using hne j hj
    rw [this] at h2
    exact absurd h2 (by decide)

theorem closure_le_of_coversOK {A B : Array (Array ℕ)} {f g : ℕ → Equiv.Perm (Fin n)}
    (hf : ∀ i < A.size, PRep n A[i]! (f i)) (hg : ∀ j < B.size, PRep n B[j]! (g j))
    (h : coversOK n A B = true) :
    Subgroup.closure (f '' {i | i < A.size}) ≤ Subgroup.closure (g '' {j | j < B.size}) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rcases coversOK_spec h hi with h1 | ⟨j, hj, h2⟩
  · rw [eq_of_peq (hf i hi) prep_pid h1]
    exact one_mem _
  · rw [eq_of_peq (hf i hi) (hg j hj) h2]
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem closure_eq_of_coversOK {A B : Array (Array ℕ)} {f g : ℕ → Equiv.Perm (Fin n)}
    (hf : ∀ i < A.size, PRep n A[i]! (f i)) (hg : ∀ j < B.size, PRep n B[j]! (g j))
    (h1 : coversOK n A B = true) (h2 : coversOK n B A = true) :
    Subgroup.closure (f '' {i | i < A.size}) = Subgroup.closure (g '' {j | j < B.size}) :=
  le_antisymm (closure_le_of_coversOK hf hg h1) (closure_le_of_coversOK hg hf h2)

theorem restrictOK_spec {g R t : Array ℕ} (h : restrictOK g R t = true) {k : ℕ}
    (hk : k < R.size) : t[k]! < R.size ∧ R[t[k]!]! = g[R[k]!]! := by
  have := allBelowN_spec h hk
  simpa [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem blockImgOK_spec {g : Array ℕ} {B : Array (Array ℕ)} {t : Array ℕ}
    (h : blockImgOK g B t = true) {i : ℕ} (hi : i < B.size) :
    t[i]! < B.size ∧ inBlock B[t[i]!]! g[(B[i]!)[0]!]! = true ∧
      inBlock B[t[i]!]! g[(B[i]!)[1]!]! = true := by
  have := allBelowN_spec h hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem inBlock_iff {b : Array ℕ} {y : ℕ} : inBlock b y = true ↔ b[0]! = y ∨ b[1]! = y := by
  simp [inBlock]

theorem countBelowN_eq (m : ℕ) (p : ℕ → Bool) :
    countBelowN m p = ((Finset.range m).filter fun k => p k = true).card := by
  rw [countBelowN, ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  congr 1
  ext k
  simp

end CFSG.ONSchreier
