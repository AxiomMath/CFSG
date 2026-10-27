module

public import CFSG.RankThree.PartOne.CTP.StrongPNoncentral
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.RankThree.PartOne.StrongP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

section Heis

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] def heisUnit {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    (a b : F) : GL (Fin n) F where
  val := heisenbergMatrix σ i k a b
  inv := heisenbergMatrix σ i k (-a) (-b - a * σ a)
  val_inv := by
    rw [heisenbergMatrix_mul σ hi hik hk, map_neg]
    have h1 : a + -a = 0 := add_neg_cancel a
    have h2 : b + (-b - a * σ a) - a * -σ a = 0 := by ring
    rw [h1, h2, heisenbergMatrix_zero]
  inv_val := by
    rw [heisenbergMatrix_mul σ hi hik hk]
    have h1 : -a + a = 0 := neg_add_cancel a
    have h2 : -b - a * σ a + b - -a * σ a = 0 := by ring
    rw [h1, h2, heisenbergMatrix_zero]

theorem coe_heisUnit {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) :
    ((heisUnit σ hi hik hk a b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      heisenbergMatrix σ i k a b := rfl

theorem heisUnit_mem (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {i k : Fin n} (hi : i ≠ Fin.rev i)
    (hik : i ≠ k) (hk : Fin.rev k = k) {a b : F} (hab : b + σ b + σ a * a = 0) :
    heisUnit σ hi hik hk a b ∈ SU σ n :=
  ⟨det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk hab⟩

@[expose] def rkFin (n : ℕ) : Fin n → ℕ := fun i => i.val

theorem rkFin_lt (n : ℕ) (i : Fin n) : rkFin n i < n := i.isLt

theorem heisUnit_unitri3 (a b : F) :
    IsUnitri (rkFin 3) (heisUnit σ (i := 0) (k := 1) (by decide) (by decide) (by decide) a b) := by
  intro i j h
  change (heisenbergMatrix σ (0 : Fin 3) 1 a b - 1) i j ≠ 0 at h
  have e0 : Fin.rev (0 : Fin 3) = 2 := rfl
  fin_cases i <;> fin_cases j <;>
    simp [heisenbergMatrix, e0, rkFin] at h ⊢

theorem heisenbergMatrix_entry3 (a b : F) :
    heisenbergMatrix σ (0 : Fin 3) 1 a b 0 2 = b := by
  have e0 : Fin.rev (0 : Fin 3) = 2 := rfl
  simp [heisenbergMatrix, e0]

theorem noncentralPair_su3 (hσ : ∀ c, σ (σ c) = c) {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : 3 ≤ p) (hex : ∀ a : F, σ a = a → ∃ c : F, c + σ c = a) {a' : F} (ha' : σ a' ≠ a') :
    NoncentralPair p (SU σ 3) := by
  obtain ⟨b, hb⟩ := hex (-1) (by simp)
  have hfix : σ (-(σ a' * a')) = -(σ a' * a') := by
    rw [map_neg, map_mul, hσ]; ring
  obtain ⟨b', hb'⟩ := hex _ hfix
  have hb1 : b + σ b + σ 1 * 1 = 0 := by rw [map_one]; linear_combination hb
  have hb2 : b' + σ b' + σ a' * a' = 0 := by linear_combination hb'
  have h0 : (0 : Fin 3) ≠ Fin.rev 0 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hk : Fin.rev (1 : Fin 3) = 1 := by decide
  refine noncentralPair_of_unitri (r := rkFin 3) (m := 3) (rkFin_lt 3) hp
    (heisUnit_mem σ hσ h0 h01 hk hb1) (heisUnit_mem σ hσ h0 h01 hk hb2)
    (heisUnit_unitri3 σ 1 b) (heisUnit_unitri3 σ a' b') ?_
  intro h
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [Units.val_mul, coe_heisUnit] at h'
  rw [heisenbergMatrix_mul σ h0 h01 hk, heisenbergMatrix_mul σ h0 h01 hk] at h'
  have := congrFun (congrFun h' 0) 2
  rw [heisenbergMatrix_entry3, heisenbergMatrix_entry3] at this
  apply ha'
  rw [map_one] at this
  linear_combination -this

end Heis

section FourDim

variable {F : Type} [Field F] (σ : F ≃+* F)

theorem noncentralPair_su4 (hσ : ∀ c, σ (σ c) = c) {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : 4 ≤ p) {c : F} (hc0 : c ≠ 0) (hc : c + σ c = 0) :
    NoncentralPair p (SU σ 4) := by
  have hij : (0 : Fin 4) ≠ 1 := by decide
  have hi : (0 : Fin 4) ≠ Fin.rev 0 := by decide
  have hj : (1 : Fin 4) ≠ Fin.rev 1 := by decide
  let x : SU σ 4 := rootHom σ hσ hij hi hj (Multiplicative.ofAdd 1)
  let y : SU σ 4 := longRootHom σ (i := 1) hj (Multiplicative.ofAdd ⟨c, hc⟩)
  have e0 : Fin.rev (0 : Fin 4) = 3 := rfl
  have e1 : Fin.rev (1 : Fin 4) = 2 := rfl
  have hxm : ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = rootMatrix σ 0 1 1 :=
    coe_rootHom σ hσ hij hi hj _
  have hym : ((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = longRootMatrix 1 c :=
    coe_longRootHom σ hj _
  refine noncentralPair_of_unitri (r := rkFin 4) (m := 4) (rkFin_lt 4) hp x.2 y.2 ?_ ?_ ?_
  · intro i j h
    change (((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) - 1) i j ≠ 0 at h
    rw [hxm] at h
    fin_cases i <;> fin_cases j <;>
      simp [rootMatrix, e0, e1, rkFin] at h ⊢
  · intro i j h
    change (((y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) - 1) i j ≠ 0 at h
    rw [hym] at h
    fin_cases i <;> fin_cases j <;>
      simp [longRootMatrix, e1, rkFin] at h ⊢
  · intro h
    have h' := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h
    simp only [Units.val_mul] at h'
    rw [hxm, hym] at h'
    have := congrFun (congrFun h' 0) 2
    simp [rootMatrix, longRootMatrix, e0, e1, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.single_apply, Matrix.one_apply] at this
    exact hc0 this

end FourDim

section Transport

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem noncentralPair_statedSU (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ)
    (h : NoncentralPair p (SU (unitaryInvolution F p f) n)) :
    NoncentralPair p (StatedSU n (p ^ f) F) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  refine NoncentralPair.conj P (fun g hg => ?_) h
  rw [← SUid_eq_statedSU hF n]
  exact (conjEquiv P hP ⟨g, hg⟩).2

theorem hasNoncommPair_statedSU (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : n = 3 ∨ n = 4)
    (hp : 5 ≤ p) : HasNoncommPair p (StatedProj (StatedSU n (p ^ f) F)) := by
  have hσ := unitaryInvolution_involutive hF
  refine NoncentralPair.hasNoncommPair (noncentralPair_statedSU hF n ?_)
  rcases hn with rfl | rfl
  · obtain ⟨a', ha'⟩ := exists_unitaryInvolution_ne hF
    exact noncentralPair_su3 _ hσ (by omega) (fun a ha => exists_add_unitaryInvolution_eq hF ha) ha'
  · obtain ⟨c, hc0, hc⟩ := exists_unitaryInvolution_eq_neg hF
    exact noncentralPair_su4 _ hσ (by omega) hc0 (by rw [hc]; ring)

end Transport

end CFSG.RankThree.PartOne.StrongP
