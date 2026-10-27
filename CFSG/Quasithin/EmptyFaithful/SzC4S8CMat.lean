module

public import CFSG.Quasithin.Background.S1567V6a

public section

namespace CFSG.Quasithin.SzC4S8C

open CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Matrix

section Z2

@[expose] def cmZ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 0, 1, 1]

@[expose] def bmZ : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 1; 1, 0, 0; 0, 1, 0]

theorem bmZ_mul : bmZ * cmZᵀ = 1 := by decide +kernel

theorem mul_bmZ : cmZᵀ * bmZ = 1 := by decide +kernel

@[expose] def stZ (u : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := cmZ.mulVec u

theorem stZ_rel : ∀ u : Fin 3 → ZMod 2, stZ^[3] u = stZ^[2] u + u := by decide +kernel

theorem stZ_orbit : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 → ∃ n : Fin 7, stZ^[n.val] v = w := by
  decide +kernel

@[expose] def uZ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) := ⟨bmZ, cmZᵀ, bmZ_mul, mul_bmZ⟩

theorem moduleAct_true_uZ : moduleAct true uZ = cmZ := by
  simp [moduleAct, uZ]

end Z2

section Transport

variable {F : Type} [Field F] [Fintype F]

@[expose] noncomputable def cmF (hF : Fintype.card F = 2) : Matrix (Fin 3) (Fin 3) F :=
  cmZ.map (S1567.toZMod2 hF).symm

@[expose] noncomputable def trF (hF : Fintype.card F = 2) (u : Fin 3 → ZMod 2) : Fin 3 → F :=
  fun i => (S1567.toZMod2 hF).symm (u i)

theorem trF_surj (hF : Fintype.card F = 2) (v : Fin 3 → F) :
    ∃ u : Fin 3 → ZMod 2, trF hF u = v :=
  ⟨fun i => S1567.toZMod2 hF (v i), funext fun i => by simp [trF]⟩

theorem trF_add (hF : Fintype.card F = 2) (u w : Fin 3 → ZMod 2) :
    trF hF (u + w) = trF hF u + trF hF w := by
  funext i
  simp [trF]

theorem trF_eq_zero (hF : Fintype.card F = 2) (u : Fin 3 → ZMod 2) :
    trF hF u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext i
    have := congrFun h i
    simpa [trF] using this
  · rintro rfl
    funext i
    simp [trF]

theorem cmF_mulVec_trF (hF : Fintype.card F = 2) (u : Fin 3 → ZMod 2) :
    (cmF hF).mulVec (trF hF u) = trF hF (stZ u) :=
  S1567.mulVec_map_ring (S1567.toZMod2 hF).symm cmZ u

theorem cmF_iter_trF (hF : Fintype.card F = 2) (n : ℕ) (u : Fin 3 → ZMod 2) :
    (fun v => (cmF hF).mulVec v)^[n] (trF hF u) = trF hF (stZ^[n] u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, cmF_mulVec_trF, ih]

theorem cmF_rel (hF : Fintype.card F = 2) (u : Fin 3 → F) :
    (fun v => (cmF hF).mulVec v)^[3] u = (fun v => (cmF hF).mulVec v)^[2] u + u := by
  obtain ⟨u', rfl⟩ := trF_surj hF u
  rw [cmF_iter_trF, cmF_iter_trF, stZ_rel, trF_add]

theorem cmF_orbit (hF : Fintype.card F = 2) (v w : Fin 3 → F) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ n : ℕ, (fun v => (cmF hF).mulVec v)^[n] v = w := by
  obtain ⟨v', rfl⟩ := trF_surj hF v
  obtain ⟨w', rfl⟩ := trF_surj hF w
  have hv' : v' ≠ 0 := fun h => hv ((trF_eq_zero hF v').2 h)
  have hw' : w' ≠ 0 := fun h => hw ((trF_eq_zero hF w').2 h)
  obtain ⟨n, hn⟩ := stZ_orbit v' w' hv' hw'
  exact ⟨n.val, by rw [cmF_iter_trF, hn]⟩

theorem exists_gl (hF : Fintype.card F = 2) :
    ∃ u : Matrix.GeneralLinearGroup (Fin 3) F, moduleAct true u = cmF hF :=
  ⟨S1567.glMap (S1567.toZMod2 hF).symm uZ, by
    rw [S1567.moduleAct_glMap, moduleAct_true_uZ]
    rfl⟩

omit [Field F] in
theorem natCard_mult (hF : Fintype.card F = 2) (k : ℕ) :
    Nat.card (Multiplicative (Fin k → Fin 3 → F)) = 2 ^ (3 * k) := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_fin, hF]
  exact (pow_mul 2 3 k).symm

theorem add_self (hF : Fintype.card F = 2) (a : F) : a + a = 0 := by
  have h1 : ∀ b : ZMod 2, b + b = 0 := by decide
  exact (S1567.toZMod2 hF).injective (by simpa using h1 (S1567.toZMod2 hF a))

theorem mul_self_eq_one (hF : Fintype.card F = 2) {k : ℕ} {ι : Type}
    (y : Multiplicative (Fin k → ι → F)) : y * y = 1 := by
  apply Multiplicative.toAdd.injective
  funext i j
  simpa using add_self hF (Multiplicative.toAdd y i j)

end Transport

end CFSG.Quasithin.SzC4S8C
