module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoMoves

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] {n : ℕ} {L : Type} [Field L] [Algebra K L] {ζ : L}
  {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E)

namespace SpFrame

theorem tor_add (hζ : ζ ^ 3 = 1) (f f' : Fin F.s → ZMod 3) :
    F.tor (f + f') = F.tor f * F.tor f' :=
  ((F.tor_acts f).mul (F.tor_acts f')).eq ((F.tor_acts (f + f')).congr fun d => by
    rw [torE_add hζ]
    rfl) |>.symm

theorem tor_zero : F.tor 0 = 1 :=
  (F.tor_acts 0).eq (ActsAs.one.congr fun d => (torE_zero d).symm)

theorem tor_injective (hζo : IsPrimitiveRoot ζ 3) : Function.Injective F.tor := by
  intro f f' h
  refine torE_injective hζo fun d => F.Φ.injective ?_
  rw [← F.tor_acts f, ← F.tor_acts f', h]

theorem tor_comm (hζ : ζ ^ 3 = 1) (f f' : Fin F.s → ZMod 3) :
    F.tor f * F.tor f' = F.tor f' * F.tor f := by
  rw [← F.tor_add hζ, ← F.tor_add hζ, add_comm]

theorem tor_pow_three (hζ : ζ ^ 3 = 1) (f : Fin F.s → ZMod 3) : F.tor f ^ 3 = 1 := by
  have h3 : f + f + f = 0 := funext fun i => by
    simp only [Pi.add_apply, Pi.zero_apply]
    calc f i + f i + f i = 3 * f i := by ring
      _ = 0 := by rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
  rw [pow_succ, pow_succ, pow_one, ← F.tor_add hζ, ← F.tor_add hζ, h3, F.tor_zero]

theorem monoL_frame_isom (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool) (d d' : Fin F.s → L) :
    spForm n K (F.Φ (monoL F.σ π η d)) (F.Φ (monoL F.σ π η d')) =
      spForm n K (F.Φ d) (F.Φ d') := by
  rw [F.form, F.form]
  exact monoL_isom F.σβ π η d d'

@[expose] noncomputable def move (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool) :
    StatedSp n K :=
  Classical.choose (exists_actsAs (Φ := F.Φ) (monoL F.σ π η) (F.monoL_frame_isom π η))

theorem move_acts (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool) :
    ActsAs F.Φ (F.move π η) (monoL F.σ π η) :=
  Classical.choose_spec (exists_actsAs (Φ := F.Φ) (monoL F.σ π η) (F.monoL_frame_isom π η))

theorem move_conj (hζ : ζ ^ 3 = 1) (π : Equiv.Perm (Fin F.s)) (η : Fin F.s → Bool)
    (f : Fin F.s → ZMod 3) :
    F.move π η * F.tor f * (F.move π η)⁻¹ = F.tor (moveExp π η f) := by
  have hinv := (F.move_acts π η).inv (N := (monoL F.σ π η).symm) fun d => by simp
  refine ((F.move_acts π η).mul (F.tor_acts f) |>.mul hinv).eq
    ((F.tor_acts (moveExp π η f)).congr fun d => ?_)
  change torE ζ (moveExp π η f) d = monoL F.σ π η (torE ζ f ((monoL F.σ π η).symm d))
  rw [monoL_torE hζ F.σζ, LinearEquiv.apply_symm_apply]

@[expose] noncomputable def swap (i j : Fin F.s) (b : Bool) : StatedSp n K :=
  F.move (Equiv.swap i j) (swapSgn i j b)

theorem swap_acts (i j : Fin F.s) (b : Bool) : ActsAs F.Φ (F.swap i j b) (swapL F.σ i j b) :=
  F.move_acts _ _

theorem swap_mul_self {i j : Fin F.s} (hij : i ≠ j) (b : Bool) :
    F.swap i j b * F.swap i j b = 1 :=
  ((F.swap_acts i j b).mul (F.swap_acts i j b)).eq
    (ActsAs.one.congr fun d => (swapL_swapL F.σσ hij b d).symm)

theorem swap_comm_tor (hζ : ζ ^ 3 = 1) {i j : Fin F.s} (b : Bool) {f : Fin F.s → ZMod 3}
    (hf : f i = sgnZ b (f j)) : F.swap i j b * F.tor f = F.tor f * F.swap i j b :=
  (F.swap_acts i j b).commute (F.tor_acts f) fun d => swapL_torE hζ F.σζ b hf d

end SpFrame

theorem exists_perm_pair {s : ℕ} {z z' j j' : Fin s} (hz : z ≠ z') (hj : j ≠ j') :
    ∃ π : Equiv.Perm (Fin s), π z = j ∧ π z' = j' := by
  set a := Equiv.swap z j z' with ha
  have haj : a ≠ j := by
    intro h
    have h1 : Equiv.swap z j a = Equiv.swap z j j := by rw [h]
    rw [ha, Equiv.swap_apply_self, Equiv.swap_apply_right] at h1
    exact hz h1.symm
  refine ⟨(Equiv.swap z j).trans (Equiv.swap a j'), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm haj) hj]
  · rw [Equiv.trans_apply, ← ha, Equiv.swap_apply_left]

theorem sgnZ_sgnZ_xor (b c : Bool) (a : ZMod 3) : sgnZ b (sgnZ c a) = sgnZ (b ^^ c) a := by
  cases b <;> cases c <;> simp [sgnZ]

end ChoiceTwo

end CFSG.StandardType
