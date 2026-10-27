module

public import CFSG.LocalAnalysis.StandardType.FS81.AutMat
public import CFSG.GroupTheory.SupCommute
import Mathlib.Tactic.Ring

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup

namespace Basis3

theorem not_mem_zpowers_b_of_ne {G : Type} [Group G] {k : ℕ}
    (B : Basis3 G k) {i j : Fin k} (hij : i ≠ j) : B.b i ∉ zpowers (B.b j) := by
  classical
  intro h
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp h
  have hs : (B.bS j) ^ m = B.bS i := Subtype.ext hm
  have he := congrArg B.equiv.symm hs
  rw [map_zpow] at he
  change (Multiplicative.ofAdd (B.coords (B.bS j))) ^ m =
    Multiplicative.ofAdd (B.coords (B.bS i)) at he
  rw [B.coords_bS, B.coords_bS] at he
  have hvec := congrArg Multiplicative.toAdd he
  change m • (Pi.single j (1 : ZMod 3) : Coords k) = Pi.single i 1 at hvec
  have hv := congrFun hvec i
  simp [Pi.smul_apply, hij] at hv

theorem not_mem_sup_zpowers_of_not_dvd_card {G : Type} [Group G] {k : ℕ}
    (B : Basis3 G k) (R : Subgroup G) [Finite R] (hR3 : ¬ 3 ∣ Nat.card R)
    (hRC : R ≤ centralizer (B.span : Set G)) {i j : Fin k} (hij : i ≠ j) :
    B.b i ∉ R ⊔ zpowers (B.b j) := by
  have hZE : zpowers (B.b j) ≤ B.span := zpowers_le.mpr (B.b_mem_span j)
  have hcomm : ∀ r ∈ R, ∀ z ∈ zpowers (B.b j), Commute r z := fun r hr z hz =>
    (mem_centralizer_iff.mp (hRC hr) z (hZE hz)).symm
  intro hi
  obtain ⟨r, hr, z, hz, hrz⟩ := (CFSG.mem_sup_of_commute hcomm).mp hi
  have hrE : r ∈ B.span := by
    have heq : r = B.b i * z⁻¹ := by rw [← hrz]; group
    rw [heq]
    exact B.span.mul_mem (B.b_mem_span i) (B.span.inv_mem (hZE hz))
  let v : Coords k := B.coords ⟨r, hrE⟩
  have hv : B.vec v = r := B.vec_coords ⟨r, hrE⟩
  have hv3 : v + v + v = 0 := by
    funext a
    change v a + v a + v a = 0
    calc v a + v a + v a = (3 : ZMod 3) * v a := by ring
      _ = 0 := by
        change ((3 : ℕ) : ZMod 3) * v a = 0
        rw [ZMod.natCast_self, zero_mul]
  have hr3 : r ^ 3 = 1 := by
    have hprod : B.vec v * B.vec v * B.vec v = 1 := by
      rw [← B.vec_add, ← B.vec_add, hv3, B.vec_zero]
    rw [hv] at hprod
    simpa only [pow_succ, pow_zero, one_mul] using hprod
  have hr1 : r = 1 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf r)
      (orderOf_dvd_of_pow_eq_one hr3) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact False.elim (hR3 (h ▸ Subgroup.orderOf_dvd_natCard R hr))
  have hiZ : B.b i ∈ zpowers (B.b j) := by
    rw [hr1, one_mul] at hrz
    exact hrz ▸ hz
  exact B.not_mem_zpowers_b_of_ne hij hiZ

end Basis3

end CFSG.StandardType.FrameRoute.FS81
