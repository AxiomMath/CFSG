module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

def ggTorMpm (p : ℕ) (lab : LargeEvenLabel) : ℕ :=
  if p ∣ 2 ^ lab.n - 1 then 2 ^ lab.n - 1 else 2 ^ lab.n + 1

def GGTBTorAInd : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .A ∨ lab.tag = .twA) → ¬ p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorM lab) lab.rank
          (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I

def GGTBTorC : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .B ∨ lab.tag = .C) → p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorMpm p lab) lab.rank
          (CartanMatrix.C lab.rank) (CoxeterMatrix.B lab.rank) R I

def GGTBTorD : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    ((lab.tag = .D ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank))) ∨
      (lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank)) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorMpm p lab) lab.rank
          (CartanMatrix.D lab.rank) (ggCoxeterMatrixD lab.rank) R I

def GGTBTorDHigh : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    4 ≤ lab.rank →
    ((lab.tag = .D ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank))) ∨
      (lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank)) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorMpm p lab) lab.rank
          (CartanMatrix.D lab.rank) (ggCoxeterMatrixD lab.rank) R I

theorem GGTBTorD.high (h : GGTBTorD) : GGTBTorDHigh :=
  fun p hp hp2 lab hlab _ hrow => h p hp hp2 lab hlab hrow

def GGTBTorDHighNonsplit : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    4 ≤ lab.rank → p ∣ 2 ^ lab.n + 1 →
    ((lab.tag = .D ∧ Even lab.rank) ∨ (lab.tag = .twD ∧ Odd lab.rank)) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorMpm p lab) lab.rank
          (CartanMatrix.D lab.rank) (ggCoxeterMatrixD lab.rank) R I

theorem GGTBTorD.highNonsplit (h : GGTBTorD) : GGTBTorDHighNonsplit := by
  intro p hp hp2 lab hlab _ hplus htag
  apply h p hp hp2 lab hlab
  rcases htag with ⟨ht, heven⟩ | ⟨ht, hodd⟩
  · exact Or.inl ⟨ht, Or.inr ⟨hplus, heven⟩⟩
  · exact Or.inr ⟨ht, hplus, hodd⟩

def GGTBTorE6Ind : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    (lab.tag = .E6 ∨ lab.tag = .twE6) → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (6 - ggTorEnn p lab) (ggTorM lab) 6 (CartanMatrix.E 6) CoxeterMatrix.E₆ R I

def GGTBTorE6IndTwist : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    lab.tag = .twE6 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (6 - ggTorEnn p lab) (ggTorM lab) 6 (CartanMatrix.E 6) CoxeterMatrix.E₆ R I

theorem GGTBTorE6Ind.twist (h : GGTBTorE6Ind) : GGTBTorE6IndTwist :=
  fun p hp hp2 hp3 lab hlab ht hm => h p hp hp2 hp3 lab hlab (Or.inr ht) hm

def GGTBTorE7 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .E7 →
    p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (7 - ggTorEnn p lab) (ggTorMpm p lab) 7 (CartanMatrix.E 7)
          CoxeterMatrix.E₇ R I

def GGTBTorE8Ind : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    lab.tag = .E8 → p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (8 - ggTorEnn p lab) (ggTorMpm p lab) 8 (CartanMatrix.E 8)
          CoxeterMatrix.E₈ R I

def GGTBTorF4 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .F4 →
    p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) → ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1) →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (4 - ggTorEnn p lab) (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄ R I

def GGTBTorG2 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .G2 →
    p ∣ 2 ^ lab.n - 1 →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p 2 (2 ^ lab.n - 1) 2 CartanMatrix.G₂ CoxeterMatrix.G₂ R I

theorem ggCartan_ker_zero_of_not_dvd_det {ι : Type} [Fintype ι] [DecidableEq ι] {p : ℕ}
    [Fact p.Prime] (C : Matrix ι ι ℤ) (hC : ¬ (p : ℤ) ∣ C.det) :
    ∀ c : ι → ZMod p, (∀ j, ∑ k, (C j k : ZMod p) * c k = 0) → c = 0 := by
  intro c hc
  set Cp : Matrix ι ι (ZMod p) := (Int.castRingHom (ZMod p)).mapMatrix C
  have hdet : Cp.det = (C.det : ZMod p) := by
    simp only [Cp, ← RingHom.map_det]
    rfl
  have hu : IsUnit Cp.det := by
    rw [hdet, isUnit_iff_ne_zero]
    exact fun h => hC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h)
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det Cp).2 hu)
  apply hinj
  ext j
  simp only [Matrix.mulVec, dotProduct, Cp, RingHom.mapMatrix_apply, Matrix.map_apply,
    eq_intCast, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  exact hc j

theorem ggTor_not_dvd_small {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℤ}
    (hd : d = 1 ∨ d = 2 ∨ d = 4) : ¬ (p : ℤ) ∣ d := by
  rintro h
  have h4 : (p : ℤ) ∣ 4 := by
    rcases hd with rfl | rfl | rfl
    · exact h.trans (by norm_num)
    · exact h.trans (by norm_num)
    · exact h
  have h4' : p ∣ 2 * 2 := by exact_mod_cast h4
  rcases hp.dvd_mul.1 h4' with h2 | h2 <;>
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem ggCartanAInd_ker_zero {p N : ℕ} [hp : Fact p.Prime] (hpN : ¬ p ∣ N + 1) :
    ∀ c : Fin N → ZMod p, (∀ j, ∑ k, (CartanMatrix.A N j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.A_det]
    exact_mod_cast hpN)

theorem ggCartanC_ker_zero {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n) :
    ∀ c : Fin n → ZMod p, (∀ j, ∑ k, (CartanMatrix.C n j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.C_det hn]; exact ggTor_not_dvd_small hp.out hp2 (by norm_num))

theorem ggCartanD_ker_zero {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : 2 ≤ n) :
    ∀ c : Fin n → ZMod p, (∀ j, ∑ k, (CartanMatrix.D n j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.D_det hn]; exact ggTor_not_dvd_small hp.out hp2 (by norm_num))

theorem ggCartanE6Ind_ker_zero {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3) :
    ∀ c : Fin 6 → ZMod p, (∀ j, ∑ k, (CartanMatrix.E 6 j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.E_det (by norm_num)]
    intro h
    have h3 : p ∣ 3 := by
      exact_mod_cast (show (p : ℤ) ∣ 3 by simpa using h)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h3))

theorem ggCartanE7_ker_zero {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ c : Fin 7 → ZMod p, (∀ j, ∑ k, (CartanMatrix.E 7 j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.E_det (by norm_num)]; exact ggTor_not_dvd_small hp.out hp2 (by norm_num))

theorem ggCartanE8_ker_zero {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ c : Fin 8 → ZMod p, (∀ j, ∑ k, (CartanMatrix.E 8 j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.E_det (by norm_num)]; exact ggTor_not_dvd_small hp.out hp2 (by norm_num))

theorem ggCartanF4_ker_zero {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ c : Fin 4 → ZMod p, (∀ j, ∑ k, (CartanMatrix.F₄ j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.F₄_det]; exact ggTor_not_dvd_small hp.out hp2 (by norm_num))

theorem ggCartanG2_ker_zero {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ c : Fin 2 → ZMod p, (∀ j, ∑ k, (CartanMatrix.G₂ j k : ZMod p) * c k = 0) → c = 0 :=
  ggCartan_ker_zero_of_not_dvd_det _ (by
    rw [CartanMatrix.G₂_det]; exact ggTor_not_dvd_small hp.out hp2 (by norm_num))

end CFSG.StandardType
