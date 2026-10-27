module

public import CFSG.Permutation.UnitaryThreeRecognition.DThreeInvol
public import CFSG.Permutation.UnitaryThreeRecognition.DThreeSign
public import CFSG.Permutation.UnitaryThreeRecognition.Bridge3Perm
public import CFSG.Permutation.UnitaryThreeRecognition.BridgeHyp4

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

theorem two_ne_zero_of_card {K : Type*} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : Odd q) : (2 : K) ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  intro h2
  have hchar : ringChar K = 2 := by
    have := ringChar.dvd (show ((2 : ℕ) : K) = 0 by exact_mod_cast h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, hK, hchar] at hn
  have hev : Even (q ^ 2) := by rw [hn]; exact (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  exact (Nat.not_even_iff_odd.mpr hq.pow) hev

theorem tPerm_eq_one_iff {K : Type*} [Field K] [Finite K] {J : HermitianForm 3 K} {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : Odd q) (hconj : ∀ x : K, J.conj x = x ^ q) (h3 : 3 ∣ q + 1)
    (m : Kˣ) : tPerm J m = 1 ↔ (m : K) ^ 3 = 1 := by
  have h2 := two_ne_zero_of_card hK hq
  obtain ⟨w, hw⟩ := DThree.exists_fst_one (J := J) h2
  have hw1 : w ≠ 1 := DThree.ne_one_of_fst (by rw [hw]; exact one_ne_zero)
  rw [← DThree.t_eq_one_iff h2 hw1 hconj h3 m]
  exact Equiv.ext_iff

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
include S

theorem torusPerm_j [Finite G] [Finite Ω] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : Odd q) (hconj : ∀ x : K, J.conj x = x ^ q) (h3 : 3 ∣ q + 1) :
    C.torusPerm S ⟨j, S.hj⟩ = tPerm J (-1) := by
  set m := C.kOf ⟨j, S.hj⟩ with hmdef
  have key := tPerm_eq_one_iff (J := J) hK hq hconj h3
  have hjj : (⟨j, S.hj⟩ : pairStab G a b) * ⟨j, S.hj⟩ = 1 := Subtype.ext S.hj2
  have hm2 : tPerm J (m * m) = 1 := by
    rw [map_mul, hmdef, ← torusPerm_apply C S, ← map_mul, hjj, map_one]
  have hm6 : ((m : K) ^ 3) ^ 2 = 1 := by
    have := (key (m * m)).mp hm2
    rw [Units.val_mul] at this
    linear_combination this
  have hm3 : (m : K) ^ 3 ≠ 1 := by
    intro e
    have h1 : C.torusPerm S ⟨j, S.hj⟩ = 1 := (key m).mpr e
    have : (⟨j, S.hj⟩ : pairStab G a b) = 1 := C.torusPerm_injective S (by rw [map_one]; exact h1)
    exact S.hj1 (congrArg Subtype.val this)
  have hm3' : (m : K) ^ 3 = -1 := by
    have : ((m : K) ^ 3 - 1) * ((m : K) ^ 3 + 1) = 0 := by linear_combination hm6
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hm3
    · linear_combination h
  have h1 : tPerm J (m * (-1)⁻¹) = 1 := by
    rw [key, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one, inv_neg,
      inv_one]
    linear_combination (-1 : K) * hm3'
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [torusPerm_apply, ← hmdef, h1]

theorem sLeft_eq_of_fix {u : Q} (hu : (u : G) ≠ 1) (hF : S.sMapCoord φ (φ u) = φ u) :
    sLeft Q a b s u = u := by
  rw [S.sMapCoord_apply φ u hu] at hF
  exact congrArg Subtype.val (φ.injective hF)

theorem hmap3_fix [Finite G] [Finite Ω] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : Odd q) (hconj : ∀ x : K, J.conj x = x ^ q) (h3 : 3 ∣ q + 1) {c : Coord J}
    (hc : c ≠ 1) (hF : S.sMapCoord φ c = c) : tPerm J (C.hmap3 S c) = tPerm J (-1) := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have hu1 : (u : G) ≠ 1 := phi_ne_one.mpr hc
  obtain ⟨hτ, -⟩ := S.sTor_sRight_of_sLeft_eq u.2 hu1 (sLeft_eq_of_fix S hu1 hF)
  rw [C.hmap3_apply S u hu1, ← C.torusPerm_j S hK hq hconj h3, torusPerm_apply]
  congr 2
  exact Subtype.ext hτ

include C in
theorem sMapCoord_fix_inv [Finite G] [Finite Ω] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : Odd q) (hconj : ∀ x : K, J.conj x = x ^ q) (h3 : 3 ∣ q + 1) {c : Coord J}
    (hc : c ≠ 1) (hF : S.sMapCoord φ c = c) :
    hermitianTorusAction J (-1) (S.sMapCoord φ c⁻¹)⁻¹ = S.sMapCoord φ c⁻¹ := by
  obtain ⟨u, rfl⟩ := φ.surjective c
  have hu1 : (u : G) ≠ 1 := phi_ne_one.mpr hc
  obtain ⟨-, hr⟩ := S.sTor_sRight_of_sLeft_eq u.2 hu1 (sLeft_eq_of_fix S hu1 hF)
  have hrQ := S.root.sRight_mem S.hb S.hsa S.hs2 u.2 hu1
  have e := sMapCoord_inv_inv (φ := φ) S u hu1
  have e' : S.sMapCoord φ (φ u)⁻¹ = (φ ⟨sRight Q a b s u, hrQ⟩)⁻¹ := by rw [← e, inv_inv]
  rw [e, e', ← tPerm_apply, ← C.torusPerm_j S hK hq hconj h3, torusPerm_apply, tPerm_apply,
    C.kOf_conj ⟨j, S.hj⟩ _ (S.root.normal j S.hj.1 _ hrQ), ← map_inv]
  congr 1
  apply Subtype.ext
  have hji : j⁻¹ = j := inv_eq_of_mul_eq_one_right S.hj2
  change j * sRight Q a b s u * j⁻¹ = (sRight Q a b s u)⁻¹
  rw [hji, hr]

theorem exists_sMapCoord_fix {k : G} (hk : s = k⁻¹ * j * k) :
    ∃ c : Coord J, c ≠ 1 ∧ S.sMapCoord φ c = c := by
  obtain ⟨u, hu, hu1, hfix⟩ := S.exists_sLeft_eq_self hk
  refine ⟨φ ⟨u, hu⟩, phi_ne_one.mp hu1, ?_⟩
  rw [S.sMapCoord_apply φ ⟨u, hu⟩ hu1]
  congr 1
  exact Subtype.ext hfix

end CoordHyp

end CFSG.UnitaryThreeRecognition
