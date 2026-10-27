module

public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7AutFixPack

open Equiv CFSG.Permutation.FinPack

theorem h16 : 7 ≤ 16 := by norm_num

theorem enc_one : enc (1 : Perm (Fin 7)) = 106181136 := by decide +kernel

@[expose] noncomputable def iterK (c k x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) x (fun _ y => rd c y) k

theorem iterK_enc (σ : Perm (Fin 7)) (x : Fin 7) (k : ℕ) :
    iterK (enc σ) k x = ((σ ^ k) x : ℕ) := by
  induction k with
  | zero =>
    change (x : ℕ) = ((σ ^ 0) x : ℕ)
    rw [pow_zero, Perm.one_apply]
  | succ k ih =>
    change rd (enc σ) (iterK (enc σ) k x) = _
    rw [ih, rd_enc h16, pow_succ', Perm.mul_apply]

@[expose] noncomputable def qOrb (c : ℕ) : Bool :=
  !(allLtK (fun i => Nat.beq (iterK c 7 i) i) 7 && !Nat.beq c 106181136) ||
    allLtK (fun i => !allLtK (fun k => !Nat.beq (iterK c k 0) i) 7) 7

theorem orb_walk : walkK 7 qOrb 7 0 0 0 = true := by decide +kernel

theorem orbit_full_K : ∀ σ : Perm (Fin 7), σ ^ 7 = 1 → σ ≠ 1 →
    ∀ i : Fin 7, ∃ k : Fin 7, (σ ^ (k : ℕ)) 0 = i := by
  intro σ h7 h1 i
  have hw := walkK_sound orb_walk σ
  have hg : allLtK (fun i => Nat.beq (iterK (enc σ) 7 i) i) 7 = true := by
    refine allLtK_iff.2 fun j hj => ?_
    have e := iterK_enc σ ⟨j, hj⟩ 7
    rw [h7, Perm.one_apply] at e
    rw [Nat.beq_eq]
    exact e
  have hn : Nat.beq (enc σ) 106181136 = false := by
    rw [← enc_one]
    exact beq_enc_false h16 h1
  rw [qOrb.eq_1, hg, hn] at hw
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or] at hw
  have h2 := allLtK_iff.1 hw i i.2
  by_contra hc
  have h3 : allLtK (fun k => !Nat.beq (iterK (enc σ) k 0) i) 7 = true := by
    refine allLtK_iff.2 fun k hk => ?_
    cases hb : Nat.beq (iterK (enc σ) k 0) i
    · rfl
    · exfalso
      apply hc
      refine ⟨⟨k, hk⟩, Fin.ext ?_⟩
      have e1 : iterK (enc σ) k 0 = i := Nat.eq_of_beq_eq_true hb
      rw [← e1]
      exact (iterK_enc σ 0 k).symm
  rw [h3] at h2
  exact absurd h2 (by decide)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7AutFixPack
