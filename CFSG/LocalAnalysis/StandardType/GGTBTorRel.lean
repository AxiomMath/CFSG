module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRest

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

def ggFoldD (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ :=
  Matrix.of fun i j =>
    if j.val + 2 = n then
      CartanMatrix.D n ⟨i.val, by have := i.isLt; omega⟩ ⟨n - 2, by have := i.isLt; omega⟩ +
        CartanMatrix.D n ⟨i.val, by have := i.isLt; omega⟩ ⟨n - 1, by have := i.isLt; omega⟩
    else CartanMatrix.D n ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩

theorem ggFoldD_eq {n : ℕ} (hn : 4 ≤ n) : ggFoldD n = CartanMatrix.B (n - 1) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [ggFoldD, CartanMatrix.D, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

def ggFoldCartan {n k : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (rep : Fin k → Fin n)
    (orb : Fin n → Fin k) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => ∑ j' ∈ Finset.univ.filter (fun j' => orb j' = j), C (rep i) j'

theorem ggFoldE₆_eq : ggFoldCartan CartanMatrix.E₆ ![1, 3, 2, 0] ![3, 0, 2, 1, 2, 3] =
    CartanMatrix.F₄ := by
  decide

theorem ggFoldA₅_eq : ggFoldCartan (CartanMatrix.A 5) ![0, 1, 2] ![0, 1, 2, 1, 0] =
    CartanMatrix.C 3 := by
  decide

def GGTBTorRelD : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    ((lab.tag = .D ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank) ∨
      (lab.tag = .twD ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank)))) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - 1) (ggTorMpm p lab) (lab.rank - 1)
          (CartanMatrix.B (lab.rank - 1)) (CoxeterMatrix.B (lab.rank - 1)) R I

def GGTBTorRelE6 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    ((lab.tag = .E6 ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p 4 (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄ R I

def GGTBTorRelE6Split : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    lab.tag = .E6 → p ∣ 2 ^ lab.n + 1 →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p 4 (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄ R I

theorem GGTBTorRelE6.split (h : GGTBTorRelE6) : GGTBTorRelE6Split := by
  intro p hp hp2 hp3 lab hlab htag hpm
  exact h p hp hp2 hp3 lab hlab (Or.inl ⟨htag, hpm⟩)

def GGTBTorRelA5 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.rank = 5 →
    ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1)) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p 3 (ggTorMpm p lab) 3 (CartanMatrix.C 3) (CoxeterMatrix.B 3) R I

theorem ggCartanB_ker_zero {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) :
    ∀ c : Fin n → ZMod p, (∀ j, ∑ k, (CartanMatrix.B n j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.B_det hn]; exact ggTor_not_dvd_small hp.out hp2 (by norm_num))

end CFSG.StandardType
