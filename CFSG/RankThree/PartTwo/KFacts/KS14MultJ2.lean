module

public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Gen
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public meta import CFSG.RankThree.Native.PermEnumeration
public import CFSG.RankThree.PartTwo.KFacts.KS14MultJ2Inputs
public import Certificates.Certificate8166
public import Certificates.Certificate3139
public import Certificates.Certificate10019

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (GJ okA keyPts eltOf rep_eltOf eq_of_rep rep_mul
  rep_pow rep_conj commute_of_commA subOf gElt subOf_eq_closure_gElt card_subOf okA_spec card_GJ)

theorem j2_mult5_check : chkMult5 = true :=
  Certificates.certificate8166

theorem chkMult5_parts :
    okA j2x5Arr = true ∧ okA j2y5Arr = true ∧ okA j2g5Arr = true ∧
    eqA 315 (powArr 315 j2x5Arr 5) (idA 315) = true ∧ commA j2x5Arr j2y5Arr = true ∧
    eqA 315 (conjA 315 j2g5Arr j2x5Arr) (powArr 315 j2x5Arr 4) = true ∧
    eqA 315 (conjA 315 j2g5Arr j2y5Arr) (compA 315 (powArr 315 j2x5Arr 3) j2y5Arr) = true ∧
    enumOK 315 gensE25 keyPts cE25 = true ∧ cE25.pts.size = 25 := by
  have h := j2_mult5_check
  simp only [chkMult5, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

noncomputable def j2x5 :
    GJ := eltOf j2x5Arr chkMult5_parts.1

noncomputable def j2y5 :
    GJ := eltOf j2y5Arr chkMult5_parts.2.1

noncomputable def j2g5 :
    GJ := eltOf j2g5Arr chkMult5_parts.2.2.1

theorem j2x5_pow_five :
    j2x5 ^ 5 = 1 :=
  eq_of_rep (rep_pow (rep_eltOf _) 5) (Sec4.Sporadic.J2.rep_one) chkMult5_parts.2.2.2.1

theorem j2x5_mul_comm :
    j2x5 * j2y5 = j2y5 * j2x5 :=
  (commute_of_commA (rep_eltOf _) (rep_eltOf _) chkMult5_parts.2.2.2.2.1).eq

theorem j2g5_conj_x :
    j2g5 * j2x5 * j2g5⁻¹ = j2x5 ^ 4 :=
  eq_of_rep (rep_conj (rep_eltOf _) (okA_spec chkMult5_parts.2.2.1).1 (rep_eltOf _))
    (rep_pow (rep_eltOf _) 4) chkMult5_parts.2.2.2.2.2.1

theorem j2g5_conj_y :
    j2g5 * j2y5 * j2g5⁻¹ = j2x5 ^ 3 * j2y5 :=
  eq_of_rep (rep_conj (rep_eltOf _) (okA_spec chkMult5_parts.2.2.1).1 (rep_eltOf _))
    (rep_mul (rep_pow (rep_eltOf _) 3) (rep_eltOf _)) chkMult5_parts.2.2.2.2.2.2.1

theorem card_closure_j2xy :
    Nat.card (Subgroup.closure ({j2x5, j2y5} : Set GJ)) = 25 := by
  have hgs : ∀ k < gensE25.size, validA 315 gensE25[k]! = true ∧ inP gensE25[k]! = true := by
    intro k hk
    have hk2 : k < 2 := hk
    interval_cases k
    · exact okA_spec chkMult5_parts.1
    · exact okA_spec chkMult5_parts.2.1
  have hcard := card_subOf (by decide) chkMult5_parts.2.2.2.2.2.2.2.1 hgs
  rw [chkMult5_parts.2.2.2.2.2.2.2.2] at hcard
  rw [subOf_eq_closure_gElt gensE25 hgs] at hcard
  have hset : {g | ∃ k, ∃ hk : k < gensE25.size, gElt gensE25 hgs k hk = g} =
      ({j2x5, j2y5} : Set GJ) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := hk
      interval_cases k
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
  rwa [hset] at hcard

theorem factorization_card_GJ :
    (Nat.card GJ).factorization 5 = 2 := by
  rw [card_GJ, show (604800 : ℕ) = 5 ^ 2 * 24192 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow (by norm_num),
    Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num),
    add_zero]

theorem ks18Mult_j2
    (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hX : Group.IsPerfect X) (hZc : Z ≤ Subgroup.center X) (hcop : Nat.Coprime 6 (Nat.card Z))
    (hS : Nonempty (X ⧸ Z ≃* NativeSporadic.J2)) : Z = ⊥ := by
  obtain ⟨φ⟩ := hS
  set e : X ⧸ Z ≃* GJ := φ.trans nativeEquivP with he
  refine eq_bot_of_isPerfect_of_sylow_comm hZc fun p hp hpZ P => ?_
  have : Fact p.Prime := ⟨hp⟩
  have hp6 : Nat.Coprime 6 p := Nat.Coprime.coprime_dvd_right hpZ hcop
  by_cases hp5 : p = 5
  · subst hp5
    exact sylow_five_comm_of_witness hZc e j2x5_pow_five j2x5_mul_comm j2g5_conj_x j2g5_conj_y
      card_closure_j2xy factorization_card_GJ P
  · refine sylow_comm_of_not_sq_dvd hZc ?_ P
    rw [Nat.card_congr e.toEquiv, card_GJ]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have hp778 : p < 778 := by
      by_contra h
      have : 778 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
      omega
    have hcheck : ∀ q < 778, Nat.Coprime 6 q → q ≠ 5 → 2 ≤ q → ¬ q ^ 2 ∣ 604800 := by
      decide +kernel
    exact hcheck p hp778 hp6 hp5 hp.two_le hd

end CFSG.RankThree.PartTwo.KFacts.KS14
