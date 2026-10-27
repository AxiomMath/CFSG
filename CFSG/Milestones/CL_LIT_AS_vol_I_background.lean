module

public import Mathlib
public import CFSG.Open.Catalog
public import CFSG.Open.Defs
public import CFSG.Open.QuasithinDefs
public import CFSG.Open.QuasithinH1NaturalModulesMilestoneDefs
public import CFSG.Milestones.ASVolI.Bundle
public import CFSG.Quasithin.Background.ASVolIRegistered

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_as_vol_i_background_1
    (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (H : Subgroup PSL(2, GaloisField p f)) :
    (IsElemAbelian p H ∧ ∃ m : ℕ, m ≤ f ∧ Nat.card H = p ^ m) ∨
    (IsCyclic H ∧ (Nat.card H ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      Nat.card H ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1))) ∨
    (∃ z : ℕ, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    (16 ∣ p ^ (2 * f) - 1 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (P : Subgroup H) (_ : P.Normal), IsElemAbelian p P ∧
      Nat.card P = p ^ m ∧ IsCyclic (H ⧸ P) ∧ Nat.card (H ⧸ P) = t ∧ t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∨
    (∃ m : ℕ, m ∣ f ∧ Nonempty (H ≃* PSL(2, GaloisField p m))) ∨
    (∃ m : ℕ, 2 * m ∣ f ∧ Nonempty (H ≃* PGL(2, GaloisField p m))) := by
  exact CFSG.Open.ASVolIRegistered.red_1 p f hf H


end CFSG.Open

namespace CFSG.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_as_vol_i_background_2 :
    (∀ n : ℕ, 2 ≤ n → quasithinH1CardSL 2 (GaloisField 2 n) = 2 ^ n) ∧
    (∀ n : ℕ, 2 ≤ n → quasithinH1CardSL 3 (GaloisField 2 n) = 1) ∧
    quasithinH1CardSL 3 (ZMod 2) = 2 ∧
    (∀ n : ℕ, 2 ≤ n →
      Nat.card (groupCohomology (Rep.of (quasithinH1MatrixRep
        (Matrix.symplecticGroup (Fin 2) (GaloisField 2 n)).subtype)) 1) = 2 ^ n) ∧
    quasithinH1CardSL 4 (ZMod 2) = 1 ∧
    quasithinH1CardSL 5 (ZMod 2) = 1 :=
  CFSG.Open.ASVolIRegistered.red_2


end CFSG.Open

namespace CFSG.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_as_vol_i_background_3 :
    quasithinMultiplierCyclic (alternatingGroup (Fin 9)) 2 ∧
    (∀ (p k : ℕ) [Fact p.Prime], p ≠ 2 → 9 < p ^ k →
      quasithinMultiplierCyclic PSL(2, GaloisField p k) 2) ∧
    quasithinMultiplierCyclic (quasithinPSU 4 2 1) 2 ∧
    quasithinMultiplierCyclic PSL(4, ZMod 3) 2 ∧
    quasithinMultiplierCyclic quasithinJ3 3 ∧
    quasithinMultiplierCyclic quasithinMcL 3 ∧
    quasithinMultiplierCyclic (quasithinG2 (ZMod 3)) 3 ∧
    (∀ (p k : ℕ) [Fact p.Prime], p ≠ 2 → 0 < k → 3 ∣ p ^ k - 1 →
      quasithinMultiplierCyclic PSL(3, GaloisField p k) 3) ∧
    (∀ (p k : ℕ) [Fact p.Prime], p ≠ 2 → 0 < k → 3 ∣ p ^ k + 1 →
      quasithinMultiplierCyclic (PSU3 p k) 3) ∧
    (∀ (r m : ℕ) [Fact r.Prime], r = 2 ^ 2 ^ m + 1 → 3 < r →
      quasithinMultiplierCyclic PSL(4, ZMod r) 4) ∧
    (∀ (s m : ℕ) [Fact s.Prime], s = 2 ^ m - 1 → 3 < s →
      quasithinMultiplierCyclic (quasithinPSU 4 s 1) 4) ∧
    quasithinMultiplierCyclic (quasithinPSU 5 2 2) 5 ∧
    Nonempty (quasithinHopfMultiplier (quasithinPSU 4 3 1) ≃*
      Multiplicative (ZMod 3 × ZMod 3 × ZMod 4)) ∧
    quasithinMultiplierCyclic (Matrix.symplecticGroup (Fin 3) (ZMod 2)) 2 ∧
    (∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → quasithinMultiplierCyclic (quasithinPSp 2 (ZMod p)) 2) :=
  CFSG.Open.ASVolIRegistered.red_3


end CFSG.Open

namespace CFSG.Open

open CFSG.Open in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_as_vol_i_background_4 :
    quasithinMultiplierCyclic PSL(4, ZMod 2) 2 ∧
    quasithinMultiplierCyclic (quasithinG2 (GaloisField 2 2)) 2 ∧
    quasithinMultiplierCyclic quasithinM12 2 ∧
    quasithinMultiplierCyclic quasithinJ2 2 ∧
    quasithinMultiplierCyclic quasithinHS 2 ∧
    quasithinMultiplierCyclic quasithinRu 2 ∧
    (∀ (p k : ℕ) [Fact p.Prime], p ≠ 2 → 0 < k → p ^ k ≠ 3 → p ^ k ≠ 9 →
      quasithinMultiplierCyclic PSL(2, GaloisField p k) 2) ∧
    (∀ (p k : ℕ) [Fact p.Prime], 0 < k → 3 ∣ p ^ k - 1 → p ^ k ≠ 4 →
      quasithinMultiplierCyclic PSL(3, GaloisField p k) 3) ∧
    (∀ (p k : ℕ) [Fact p.Prime], 0 < k → 3 ∣ p ^ k + 1 → p ^ k ≠ 2 →
      quasithinMultiplierCyclic (PSU3 p k) 3) ∧
    quasithinMultiplierCyclic (alternatingGroup (Fin 6)) 6 ∧
    quasithinMultiplierCyclic (alternatingGroup (Fin 7)) 6 ∧
    quasithinMultiplierCyclic quasithinM22 12 ∧
    Nonempty (quasithinHopfMultiplier (Sz 1) ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
    Nonempty (quasithinHopfMultiplier PSL(3, GaloisField 2 2) ≃*
      Multiplicative (ZMod 4 × ZMod 4 × ZMod 3)) :=
  CFSG.Open.ASVolIRegistered.red_4


end CFSG.Open

namespace CFSG.Open

section

theorem _root_.CFSG.Milestones.cl_lit_as_vol_i_background_partial
    : CFSG.ASVolI.Statement :=
  CFSG.ASVolI.statement_holds
end

section

theorem _root_.CFSG.Milestones.cl_lit_as_vol_i_background
    : CFSG.ASVolI.Statement :=
  CFSG.ASVolI.statement_holds
end

end CFSG.Open
