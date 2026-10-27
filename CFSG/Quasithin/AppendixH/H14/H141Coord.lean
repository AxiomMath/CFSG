module

public import CFSG.Quasithin.AppendixH.H14.H141Table
public import CFSG.Quasithin.AppendixH.H14.H141Lin
public import CFSG.Quasithin.AppendixH.H14.H142Conj

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Monster.Code

structure Coord64 (A : Type*) [CommGroup A] where
  code : A → ℕ
  ofCode : ℕ → A
  code_lt : ∀ a, code a < 64
  ofCode_code : ∀ a, ofCode (code a) = a
  code_ofCode : ∀ n, n < 64 → code (ofCode n) = n
  code_mul : ∀ a b, code (a * b) = code a ^^^ code b

variable {tab : Array (Array ℕ)} {A : Type*} [CommGroup A]

@[expose] noncomputable def tab64Inv (hT : tab64OK tab = true) (C : Coord64 A) :
    A →* ↥(tab64Sub tab hT) where
  toFun a := ⟨tab64Perm tab (C.code a), tab64Perm_mem_tab64Sub hT (C.code_lt a)⟩
  map_one' := by
    apply Subtype.ext
    show tab64Perm tab (C.code 1) = 1
    have h0 : C.code 1 = 0 := by
      have h := C.code_mul 1 1
      rw [mul_one] at h
      have h' : C.code 1 ^^^ C.code 1 = 0 := Nat.xor_self _
      rw [h'] at h
      simpa [Nat.xor_self] using h
    rw [h0, tab64Perm_zero hT]
  map_mul' := by
    intro a b
    apply Subtype.ext
    show tab64Perm tab (C.code (a * b)) = tab64Perm tab (C.code a) * tab64Perm tab (C.code b)
    rw [C.code_mul]
    exact (tab64Perm_mul hT (C.code_lt a) (C.code_lt b)).symm

theorem tab64Inv_ofCode (hT : tab64OK tab = true) (C : Coord64 A) {n : ℕ} (hn : n < 64) :
    tab64Inv hT C (C.ofCode n) =
      (⟨tab64Perm tab n, tab64Perm_mem_tab64Sub hT hn⟩ : ↥(tab64Sub tab hT)) := by
  apply Subtype.ext
  show tab64Perm tab (C.code (C.ofCode n)) = tab64Perm tab n
  rw [C.code_ofCode n hn]

theorem tab64Inv_bijective (hT : tab64OK tab = true) (C : Coord64 A) :
    Function.Bijective (tab64Inv hT C) := by
  constructor
  · intro a b h
    have h1 : tab64Perm tab (C.code a) = tab64Perm tab (C.code b) := congrArg Subtype.val h
    have h2 : C.code a = C.code b := tab64Perm_inj hT (C.code_lt a) (C.code_lt b) h1
    rw [← C.ofCode_code a, ← C.ofCode_code b, h2]
  · intro x
    obtain ⟨n, hn, heq⟩ := x.2
    refine ⟨C.ofCode n, ?_⟩
    apply Subtype.ext
    show (tab64Inv hT C (C.ofCode n) : S24) = (x : S24)
    rw [tab64Inv_ofCode hT C hn]
    exact heq.symm

@[expose] noncomputable def tab64Equiv (hT : tab64OK tab = true) (C : Coord64 A) :
    ↥(tab64Sub tab hT) ≃* A :=
  (MulEquiv.ofBijective (tab64Inv hT C) (tab64Inv_bijective hT C)).symm

theorem tab64Equiv_apply (hT : tab64OK tab = true) (C : Coord64 A) {n : ℕ} (hn : n < 64) :
    tab64Equiv hT C ⟨tab64Perm tab n, tab64Perm_mem_tab64Sub hT hn⟩ = C.ofCode n := by
  unfold tab64Equiv
  apply (tab64Inv_bijective hT C).1
  rw [MulEquiv.ofBijective_apply_symm_apply]
  exact (tab64Inv_ofCode hT C hn).symm

theorem actHom_tab64Equiv_state (hT : tab64OK tab = true) (C : Coord64 A) {G : Subgroup S24}
    (hGK : ∀ g ∈ G, ∀ k ∈ tab64Sub tab hT, g * k * g⁻¹ ∈ tab64Sub tab hT) (g : ↥G) {st : ℕ}
    (hst : ∀ n < 64, (g : S24) * tab64Perm tab n * (g : S24)⁻¹ = tab64Perm tab (linAct st n))
    {n : ℕ} (hn : n < 64) :
    actHom hGK (tab64Equiv hT C) g (C.ofCode n) = C.ofCode (linAct st n) := by
  calc
    actHom hGK (tab64Equiv hT C) g (C.ofCode n)
        = actHom hGK (tab64Equiv hT C) g
            (tab64Equiv hT C ⟨tab64Perm tab n, tab64Perm_mem_tab64Sub hT hn⟩) := by
          rw [tab64Equiv_apply hT C hn]
    _ = tab64Equiv hT C ⟨tab64Perm tab (linAct st n),
          tab64Perm_mem_tab64Sub hT (linAct_lt st n)⟩ := by
          rw [actHom_apply]
          exact congrArg (tab64Equiv hT C) (Subtype.ext (hst n hn))
    _ = C.ofCode (linAct st n) := tab64Equiv_apply hT C (linAct_lt st n)

end CFSG.Quasithin.AppendixH.H14
