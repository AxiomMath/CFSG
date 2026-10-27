module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.IrredClassificationFlag

public section

namespace CFSG.Quasithin.F53Mod

open Equiv Matrix

@[expose] def Tf (j ω : Fin 15) : ZMod 2 := Tm j ω

@[expose] def Tif (ω k : Fin 15) : ZMod 2 := Tim ω k

@[expose] def Rrot (j k : Fin 15) : ZMod 2 := ∑ ω, Tf j (rotTab ω) * Tif ω k

@[expose] def Rswp (j k : Fin 15) : ZMod 2 := ∑ ω, Tf j (swapTab ω) * Tif ω k

theorem Rm_rot (j k : Fin 15) : Rm (finRotate 5) j k = Rrot j k := by
  simp only [Rm, Matrix.of_apply, piF_rot]
  rfl

theorem Rm_swap (j k : Fin 15) : Rm (swap 0 1) j k = Rswp j k := by
  simp only [Rm, Matrix.of_apply, piF_swap]
  rfl

@[expose] def blockOf (j : ℕ) : ℕ :=
  if j < 1 then 0 else if j < 5 then 1 else if j < 6 then 2 else if j < 10 then 3
  else if j < 11 then 4 else 5

theorem pat_rot : ∀ j k : Fin 15, blockOf j < blockOf k → Rrot j k = 0 := by
  decide +kernel

theorem pat_swap : ∀ j k : Fin 15, blockOf j < blockOf k → Rswp j k = 0 := by
  decide +kernel

theorem blockOf_lt {d j k : ℕ} (hd : d = 1 ∨ d = 5 ∨ d = 6 ∨ d = 10 ∨ d = 11) (hj : j < d)
    (hk : d ≤ k) : blockOf j < blockOf k := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> unfold blockOf <;> split_ifs <;> omega

theorem hR_gens {d : ℕ} (hd : d = 1 ∨ d = 5 ∨ d = 6 ∨ d = 10 ∨ d = 11) :
    ∀ g ∈ gens5, ∀ j k : Fin 15, j.val < d → d ≤ k.val → Rm g j k = 0 := by
  rintro g (rfl | rfl) j k hj hk
  · rw [Rm_rot]; exact pat_rot j k (blockOf_lt hd hj hk)
  · rw [Rm_swap]; exact pat_swap j k (blockOf_lt hd hj hk)

@[expose] def Ctriv : Multiplicative (Fin 1 → ZMod 2) →* triv.W where
  toFun c := Multiplicative.ofAdd (Multiplicative.toAdd c 0)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def Cnat : Multiplicative (Fin 4 → ZMod 2) →* nat.W := MonoidHom.id _

@[expose] def orthVec (c : Fin 4 → ZMod 2) : Fin 5 → ZMod 2 :=
  ![c 1 + c 2 + c 3, c 0 + c 2 + c 3, c 0 + c 1 + c 3, c 0 + c 1 + c 2,
    c 0 + c 1 + c 2 + c 3]

theorem orthVec_add : ∀ a b : Fin 4 → ZMod 2, orthVec (a + b) = orthVec a + orthVec b := by
  decide +kernel

theorem orthVec_mem : ∀ a : Fin 4 → ZMod 2, ∑ i, orthVec a i = 0 := by decide +kernel

@[expose] def orthRaw : Multiplicative (Fin 4 → ZMod 2) →* G6.PermMod 5 where
  toFun c := Multiplicative.ofAdd (orthVec (Multiplicative.toAdd c))
  map_one' := by
    apply Multiplicative.toAdd.injective
    show orthVec 0 = 0
    decide +kernel
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    exact orthVec_add _ _

@[expose] def Corth : Multiplicative (Fin 4 → ZMod 2) →* orth.W :=
  MonoidHom.codRestrict orthRaw (G6.coreMod 5) fun c => orthVec_mem (Multiplicative.toAdd c)

instance decEqTrivW : DecidableEq triv.W := inferInstanceAs (DecidableEq (Multiplicative (ZMod 2)))

instance fintypeTrivW : Fintype triv.W := inferInstanceAs (Fintype (Multiplicative (ZMod 2)))

theorem orth_isIrred : orth.IsIrred :=
  ⟨by decide +kernel, fun U hU => irreducible_orth U fun σ y hy => hU σ (Subgroup.mem_top _) y hy⟩

theorem nat_isIrred : nat.IsIrred :=
  ⟨by decide +kernel, fun U hU => irreducible_nat U fun σ y hy => hU σ (Subgroup.mem_top _) y hy⟩

theorem step0 : Step Pm (Qd 0) (Qd 1) triv :=
  step_of_check 0 1 (by norm_num) triv triv_isIrred Ctriv (by decide +kernel)
    (by decide +kernel) (by rw [Qd_zero]; intro σ x _; trivial) (hR_gens (d := 1) (by decide))
    (by
      rintro g (rfl | rfl)
      · simp only [Rm_rot]; decide +kernel
      · simp only [Rm_swap]; decide +kernel)

theorem step1 : Step Pm (Qd 1) (Qd 5) nat :=
  step_of_check 1 4 (by norm_num) nat nat_isIrred Cnat (by decide +kernel)
    (by decide +kernel) (Qd_inv (hR_gens (d := 1) (by decide))) (hR_gens (d := 5) (by decide))
    (by
      rintro g (rfl | rfl)
      · simp only [Rm_rot]; decide +kernel
      · simp only [Rm_swap]; decide +kernel)

theorem step2 : Step Pm (Qd 5) (Qd 6) triv :=
  step_of_check 5 1 (by norm_num) triv triv_isIrred Ctriv (by decide +kernel)
    (by decide +kernel) (Qd_inv (hR_gens (d := 5) (by decide))) (hR_gens (d := 6) (by decide))
    (by
      rintro g (rfl | rfl)
      · simp only [Rm_rot]; decide +kernel
      · simp only [Rm_swap]; decide +kernel)

theorem step3 : Step Pm (Qd 6) (Qd 10) orth :=
  step_of_check 6 4 (by norm_num) orth orth_isIrred Corth (by decide +kernel)
    (by decide +kernel) (Qd_inv (hR_gens (d := 6) (by decide))) (hR_gens (d := 10) (by decide))
    (by
      rintro g (rfl | rfl)
      · simp only [Rm_rot]; decide +kernel
      · simp only [Rm_swap]; decide +kernel)

theorem step4 : Step Pm (Qd 10) (Qd 11) triv :=
  step_of_check 10 1 (by norm_num) triv triv_isIrred Ctriv (by decide +kernel)
    (by decide +kernel) (Qd_inv (hR_gens (d := 10) (by decide))) (hR_gens (d := 11) (by decide))
    (by
      rintro g (rfl | rfl)
      · simp only [Rm_rot]; decide +kernel
      · simp only [Rm_swap]; decide +kernel)

theorem step5 : Step Pm (Qd 11) (Qd 15) nat :=
  step_of_check 11 4 (by norm_num) nat nat_isIrred Cnat (by decide +kernel)
    (by decide +kernel) (Qd_inv (hR_gens (d := 11) (by decide)))
    (fun _ _ _ k _ hk => absurd k.isLt (by omega))
    (by
      rintro g (rfl | rfl)
      · simp only [Rm_rot]; decide +kernel
      · simp only [Rm_swap]; decide +kernel)

end CFSG.Quasithin.F53Mod
