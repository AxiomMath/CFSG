module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSylow
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSmallAlternating
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonNonsplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonPSL2Partition
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonCounting
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonCase823
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_11
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonUnipotent
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Transfer

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.8.27

Dickson's subgroup classification for subgroups of PSL(2,p^f).
-/

namespace CFSG.Glauberman
namespace Dickson

open BenderSuzuki.MatrixGroups
open BenderSuzuki.External
open scoped Pointwise
open scoped LinearAlgebra.Projectivization

universe u v

set_option maxHeartbeats 1600000 in
/-- Huppert II.8.24: the Dickson case in which p does not divide the subgroup order. -/
public theorem huppert_II_8_24_dickson_case_no_p_part
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (hp_not_dvd_card_H : ¬ p ∣ Nat.card H) :
    (∃ z : ℕ,
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = z ∧ IsCyclic H) ∨
    (∃ z : ℕ,
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) := by
  classical
  let P : Sylow p H := default
  have hPcard : Nat.card P = p ^ 0 := by
    rw [P.card_eq_multiplicity,
      Nat.factorization_eq_zero_of_not_dvd hp_not_dvd_card_H, pow_zero]
  rcases huppert_II_8_22_dickson_counting
      (m := 0) hFcard H P hPcard with
    ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
      hrepresentative, hdistinct, hs, hnormalizerZ, hdihedral,
      _hnormalizerP, hdivides, _hcounting⟩
  let NZ : Fin r → Subgroup H := fun i => Subgroup.normalizer (Z i : Set H)
  have h824_partition_count :
      Nat.card H =
        1 + ∑ i, (Nat.card (Z i) - 1) * (NZ i).index := by
    have hraw :
        Nat.card H =
          1 + (p ^ 0 - 1) *
              (Subgroup.normalizer (P : Set H)).index +
            ∑ i, (Nat.card (Z i) - 1) *
              (Subgroup.normalizer (Z i : Set H)).index := by
      apply huppert_II_8_22_partition_count_of_unique_family P hPcard Z
      intro x hx
      convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
        hcoprime hmaximal hrepresentative hdistinct x hx using 1
      funext A
      rcases A with Q | z <;> rfl
    simpa only [pow_zero, Nat.reduceSubDiff, zero_mul, add_zero, NZ] using hraw
  have h824_z_index_factor :
      ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
    intro i
    have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
      dsimp only [NZ]
      exact hnormalizerZ i
    calc
      (Nat.card (Z i) * s i) * (NZ i).index =
          Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
      _ = Nat.card H := (NZ i).card_mul_index
  have h824_family_bound : r ≤ 3 := by
    let T := ∑ i, (Nat.card (Z i) - 1) * (NZ i).index
    have hterm (i : Fin r) :
        Nat.card H ≤ 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by
      have hzbound :
          Nat.card (Z i) * s i ≤ 4 * (Nat.card (Z i) - 1) := by
        calc
          Nat.card (Z i) * s i ≤ Nat.card (Z i) * 2 :=
            Nat.mul_le_mul_left (Nat.card (Z i)) (hs i).2
          _ ≤ (2 * (Nat.card (Z i) - 1)) * 2 :=
            Nat.mul_le_mul_right 2 (by
              have hzi := hnontrivial i
              omega)
          _ = 4 * (Nat.card (Z i) - 1) := by ring
      calc
        Nat.card H = (Nat.card (Z i) * s i) * (NZ i).index :=
          (h824_z_index_factor i).symm
        _ ≤ (4 * (Nat.card (Z i) - 1)) * (NZ i).index :=
          Nat.mul_le_mul_right (NZ i).index hzbound
        _ = 4 * ((Nat.card (Z i) - 1) * (NZ i).index) := by ring
    have hrs : r * Nat.card H ≤ 4 * T := by
      calc
        r * Nat.card H = Finset.univ.sum fun _ : Fin r => Nat.card H := by simp
        _ ≤ Finset.univ.sum fun i : Fin r =>
            4 * ((Nat.card (Z i) - 1) * (NZ i).index) :=
          Finset.sum_le_sum fun i _hi => hterm i
        _ = 4 * T := by simp [T, Finset.mul_sum]
    have hcountT : Nat.card H = 1 + T := by
      simpa only [T] using h824_partition_count
    have hTlt : T < Nat.card H := by omega
    have hcancel : r * Nat.card H < 4 * Nat.card H :=
      hrs.trans_lt
        ((Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hTlt)
    have hrlt : r < 4 :=
      (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
    omega
  have h824_shape :
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
    by_cases hr_zero : r = 0
    · subst r
      have hHcard : Nat.card H = 1 := by
        simpa using h824_partition_count
      have hHcyclic : IsCyclic H := by
        let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hHcard).1
        exact isCyclic_of_subsingleton
      exact Or.inl ⟨1, Or.inl (one_dvd _), hHcard, hHcyclic⟩
    · have h824_positive_shape :
          (∃ z : ℕ,
            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
            Nat.card H = z ∧ IsCyclic H) ∨
          (∃ z : ℕ,
            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
            Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
          Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
          Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (H ≃* alternatingGroup (Fin 5)) := by
        by_cases hr_one : r = 1
        · subst r
          have hs0_one : s 0 = 1 := by
            have hs0 := hs 0
            rcases (show s 0 = 1 ∨ s 0 = 2 by omega) with hs0_one | hs0_two
            · exact hs0_one
            · have hkpos : 0 < (NZ 0).index :=
                Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
              have hzpos : 0 < Nat.card (Z 0) := Nat.card_pos
              have hle :
                  1 + (Nat.card (Z 0) - 1) * (NZ 0).index ≤
                    Nat.card (Z 0) * (NZ 0).index := by
                calc
                  1 + (Nat.card (Z 0) - 1) * (NZ 0).index ≤
                      (NZ 0).index +
                        (Nat.card (Z 0) - 1) * (NZ 0).index := by omega
                  _ = (Nat.card (Z 0) - 1) * (NZ 0).index +
                      (NZ 0).index := Nat.add_comm _ _
                  _ = (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by ring
                  _ = Nat.card (Z 0) * (NZ 0).index := by
                    rw [Nat.sub_add_cancel (hnontrivial 0).le]
              have hlt :
                  Nat.card (Z 0) * (NZ 0).index <
                    (Nat.card (Z 0) * 2) * (NZ 0).index := by
                have hprodpos :
                    0 < Nat.card (Z 0) * (NZ 0).index :=
                  Nat.mul_pos hzpos hkpos
                calc
                  Nat.card (Z 0) * (NZ 0).index <
                      2 * (Nat.card (Z 0) * (NZ 0).index) := by omega
                  _ = (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
              have hbad : Nat.card H < Nat.card H := by
                calc
                  Nat.card H =
                      1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
                    simpa using h824_partition_count
                  _ ≤ Nat.card (Z 0) * (NZ 0).index := hle
                  _ < (Nat.card (Z 0) * 2) * (NZ 0).index := hlt
                  _ = Nat.card H := by
                    calc
                      (Nat.card (Z 0) * 2) * (NZ 0).index =
                          (Nat.card (Z 0) * s 0) * (NZ 0).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 0) * a) * (NZ 0).index) hs0_two.symm
                      _ = Nat.card H := h824_z_index_factor 0
              exact (Nat.lt_irrefl _ hbad).elim
          have hcount0 :
              Nat.card H =
                1 + (Nat.card (Z 0) - 1) * (NZ 0).index := by
            simpa using h824_partition_count
          have hfactor0 :
              Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
            simpa [hs0_one] using h824_z_index_factor 0
          have hk_one : (NZ 0).index = 1 := by
            have hzsplit :
                Nat.card (Z 0) * (NZ 0).index =
                  (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
              calc
                Nat.card (Z 0) * (NZ 0).index =
                    (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by
                  rw [Nat.sub_add_cancel (hnontrivial 0).le]
                _ = (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index := by
                  ring
            have hcancel :
                (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                  (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by
              calc
                (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                    Nat.card (Z 0) * (NZ 0).index := hzsplit.symm
                _ = Nat.card H := hfactor0
                _ = 1 + (Nat.card (Z 0) - 1) * (NZ 0).index := hcount0
                _ = (Nat.card (Z 0) - 1) * (NZ 0).index + 1 := by omega
            exact Nat.add_left_cancel hcancel
          have hHcard : Nat.card H = Nat.card (Z 0) := by
            calc
              Nat.card H = Nat.card (Z 0) * (NZ 0).index := hfactor0.symm
              _ = Nat.card (Z 0) := by rw [hk_one, mul_one]
          have hZtop : Z 0 = ⊤ :=
            Subgroup.eq_top_of_card_eq (H := Z 0) hHcard.symm
          have hHcyclic : IsCyclic H := by
            have htopcyclic : IsCyclic (⊤ : Subgroup H) :=
              (MulEquiv.subgroupCongr hZtop).isCyclic.mp (hcyclic 0)
            exact (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).isCyclic.mp htopcyclic
          exact Or.inl ⟨Nat.card (Z 0), hdivides 0, hHcard, hHcyclic⟩
        · have h824_two_or_three_shape :
              (∃ z : ℕ,
                ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                  (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                Nat.card H = z ∧ IsCyclic H) ∨
              (∃ z : ℕ,
                ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                  (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
              Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
              Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
              Nonempty (H ≃* alternatingGroup (Fin 5)) := by
            by_cases hr_two : r = 2
            · have h824_two_shape :
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = z ∧ IsCyclic H) ∨
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
                  Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                subst r
                have hnot_one_one (hs0 : s 0 = 1) (hs1 : s 1 = 1) : False := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index := by
                    simpa [add_assoc] using h824_partition_count
                  have hfactor0 :
                      Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
                    simpa [hs0] using h824_z_index_factor 0
                  have hfactor1 :
                      Nat.card (Z 1) * (NZ 1).index = Nat.card H := by
                    simpa [hs1] using h824_z_index_factor 1
                  have hrel0 :
                      (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z 0) - 1) * (NZ 0).index + (NZ 0).index =
                          (Nat.card (Z 0) - 1 + 1) * (NZ 0).index := by ring
                      _ = Nat.card (Z 0) * (NZ 0).index := by
                        rw [Nat.sub_add_cancel (hnontrivial 0).le]
                      _ = Nat.card H := hfactor0
                  have hrel1 :
                      (Nat.card (Z 1) - 1) * (NZ 1).index + (NZ 1).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z 1) - 1) * (NZ 1).index + (NZ 1).index =
                          (Nat.card (Z 1) - 1 + 1) * (NZ 1).index := by ring
                      _ = Nat.card (Z 1) * (NZ 1).index := by
                        rw [Nat.sub_add_cancel (hnontrivial 1).le]
                      _ = Nat.card H := hfactor1
                  have hbound0 : 2 * (NZ 0).index ≤ Nat.card H := by
                    calc
                      2 * (NZ 0).index ≤ Nat.card (Z 0) * (NZ 0).index :=
                        Nat.mul_le_mul_right (NZ 0).index (by
                          have hz := hnontrivial 0
                          omega)
                      _ = Nat.card H := hfactor0
                  have hbound1 : 2 * (NZ 1).index ≤ Nat.card H := by
                    calc
                      2 * (NZ 1).index ≤ Nat.card (Z 1) * (NZ 1).index :=
                        Nat.mul_le_mul_right (NZ 1).index (by
                          have hz := hnontrivial 1
                          omega)
                      _ = Nat.card H := hfactor1
                  omega
                have hnot_two_two (hs0 : s 0 = 2) (hs1 : s 1 = 2) : False := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index := by
                    simpa [add_assoc] using h824_partition_count
                  have hfactor0 :
                      2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z 0) * (NZ 0).index) =
                          (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
                      _ = (Nat.card (Z 0) * s 0) * (NZ 0).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 0) * a) * (NZ 0).index) hs0.symm
                      _ = Nat.card H := h824_z_index_factor 0
                  have hfactor1 :
                      2 * (Nat.card (Z 1) * (NZ 1).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z 1) * (NZ 1).index) =
                          (Nat.card (Z 1) * 2) * (NZ 1).index := by ring
                      _ = (Nat.card (Z 1) * s 1) * (NZ 1).index :=
                        congrArg (fun a =>
                          (Nat.card (Z 1) * a) * (NZ 1).index) hs1.symm
                      _ = Nat.card H := h824_z_index_factor 1
                  have hrel0 :
                      2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) +
                          2 * (NZ 0).index = Nat.card H := by
                    calc
                      2 * ((Nat.card (Z 0) - 1) * (NZ 0).index) +
                          2 * (NZ 0).index =
                          2 * ((Nat.card (Z 0) - 1 + 1) * (NZ 0).index) := by
                            ring
                      _ = 2 * (Nat.card (Z 0) * (NZ 0).index) := by
                        rw [Nat.sub_add_cancel (hnontrivial 0).le]
                      _ = Nat.card H := hfactor0
                  have hrel1 :
                      2 * ((Nat.card (Z 1) - 1) * (NZ 1).index) +
                          2 * (NZ 1).index = Nat.card H := by
                    calc
                      2 * ((Nat.card (Z 1) - 1) * (NZ 1).index) +
                          2 * (NZ 1).index =
                          2 * ((Nat.card (Z 1) - 1 + 1) * (NZ 1).index) := by
                            ring
                      _ = 2 * (Nat.card (Z 1) * (NZ 1).index) := by
                        rw [Nat.sub_add_cancel (hnontrivial 1).le]
                      _ = Nat.card H := hfactor1
                  have hk0pos : 0 < (NZ 0).index :=
                    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
                  have hk1pos : 0 < (NZ 1).index :=
                    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
                  omega
                have hmixed (i j : Fin 2) (hij : i ≠ j)
                    (hsi : s i = 1) (hsj : s j = 2) :
                    (∃ z : ℕ,
                      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                    Nonempty (H ≃* alternatingGroup (Fin 4)) := by
                  have hsum :
                      (∑ k, (Nat.card (Z k) - 1) * (NZ k).index) =
                        (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                    fin_cases i <;> fin_cases j
                    · exact (hij rfl).elim
                    · simp
                    · simp [add_comm]
                    · exact (hij rfl).elim
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                    calc
                      Nat.card H =
                          1 + ∑ k, (Nat.card (Z k) - 1) * (NZ k).index :=
                        h824_partition_count
                      _ = 1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index := by
                        rw [hsum]
                        simp [add_assoc]
                  have hfactor_i :
                      Nat.card (Z i) * (NZ i).index = Nat.card H := by
                    simpa [hsi] using h824_z_index_factor i
                  have hfactor_j :
                      2 * (Nat.card (Z j) * (NZ j).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z j) * (NZ j).index) =
                          (Nat.card (Z j) * 2) * (NZ j).index := by ring
                      _ = (Nat.card (Z j) * s j) * (NZ j).index :=
                        congrArg (fun a =>
                          (Nat.card (Z j) * a) * (NZ j).index) hsj.symm
                      _ = Nat.card H := h824_z_index_factor j
                  have hrel_i :
                      (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
                        Nat.card H := by
                    calc
                      (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
                          (Nat.card (Z i) - 1 + 1) * (NZ i).index := by ring
                      _ = Nat.card (Z i) * (NZ i).index := by
                        rw [Nat.sub_add_cancel (hnontrivial i).le]
                      _ = Nat.card H := hfactor_i
                  have hindex_eq :
                      (NZ i).index =
                        1 + (Nat.card (Z j) - 1) * (NZ j).index := by
                    omega
                  by_cases hzi_two : Nat.card (Z i) = 2
                  · have hdihedral_case :
                        ∃ z : ℕ,
                          ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                            (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                          Nat.card H = 2 * z ∧
                            Nonempty (H ≃* DihedralGroup z) := by
                      have hfactor_i_two : 2 * (NZ i).index = Nat.card H := by
                        calc
                          2 * (NZ i).index = Nat.card (Z i) * (NZ i).index :=
                            congrArg (fun a => a * (NZ i).index) hzi_two.symm
                          _ = Nat.card H := hfactor_i
                      have hindex_i_eq :
                          (NZ i).index = Nat.card (Z j) * (NZ j).index := by
                        apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                        exact hfactor_i_two.trans hfactor_j.symm
                      have hzsplit :
                          Nat.card (Z j) * (NZ j).index =
                            (Nat.card (Z j) - 1) * (NZ j).index +
                              (NZ j).index := by
                        calc
                          Nat.card (Z j) * (NZ j).index =
                              (Nat.card (Z j) - 1 + 1) * (NZ j).index := by
                            rw [Nat.sub_add_cancel (hnontrivial j).le]
                          _ = (Nat.card (Z j) - 1) * (NZ j).index +
                              (NZ j).index := by ring
                      have hk_j_one : (NZ j).index = 1 := by
                        have hcancel :
                            (Nat.card (Z j) - 1) * (NZ j).index +
                                (NZ j).index =
                              (Nat.card (Z j) - 1) * (NZ j).index + 1 := by
                          calc
                            (Nat.card (Z j) - 1) * (NZ j).index +
                                (NZ j).index =
                                Nat.card (Z j) * (NZ j).index := hzsplit.symm
                            _ = (NZ i).index := hindex_i_eq.symm
                            _ = 1 + (Nat.card (Z j) - 1) * (NZ j).index :=
                              hindex_eq
                            _ = (Nat.card (Z j) - 1) * (NZ j).index + 1 := by
                              omega
                        exact Nat.add_left_cancel hcancel
                      have hHcard : Nat.card H = 2 * Nat.card (Z j) := by
                        calc
                          Nat.card H =
                              2 * (Nat.card (Z j) * (NZ j).index) :=
                            hfactor_j.symm
                          _ = 2 * Nat.card (Z j) := by rw [hk_j_one, mul_one]
                      have hNZtop : NZ j = ⊤ :=
                        Subgroup.index_eq_one.mp hk_j_one
                      obtain ⟨eD⟩ := hdihedral j hsj
                      let eH : NZ j ≃* H :=
                        (MulEquiv.subgroupCongr hNZtop).trans
                          (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
                      exact
                        ⟨Nat.card (Z j), hdivides j, hHcard,
                          ⟨eH.symm.trans eD⟩⟩
                    exact Or.inl hdihedral_case
                  · have hA4_case :
                        Nonempty (H ≃* alternatingGroup (Fin 4)) := by
                      have hzi_ge_three : 3 ≤ Nat.card (Z i) := by
                        have hzi := hnontrivial i
                        omega
                      have hterm_lt :
                          (Nat.card (Z j) - 1) * (NZ j).index < (NZ i).index := by
                        omega
                      have hfactor_eq :
                          Nat.card (Z i) * (NZ i).index =
                            2 * (Nat.card (Z j) * (NZ j).index) :=
                        hfactor_i.trans hfactor_j.symm
                      have hzi_lt_four : Nat.card (Z i) < 4 := by
                        by_contra hnot
                        have hzi_ge_four : 4 ≤ Nat.card (Z i) := by omega
                        have hcoeff :
                            2 * Nat.card (Z j) ≤
                              Nat.card (Z i) * (Nat.card (Z j) - 1) := by
                          calc
                            2 * Nat.card (Z j) ≤
                                4 * (Nat.card (Z j) - 1) := by
                              have hzj := hnontrivial j
                              omega
                            _ ≤ Nat.card (Z i) * (Nat.card (Z j) - 1) :=
                              Nat.mul_le_mul_right (Nat.card (Z j) - 1) hzi_ge_four
                        have hbad :
                            2 * (Nat.card (Z j) * (NZ j).index) <
                              2 * (Nat.card (Z j) * (NZ j).index) := by
                          calc
                            2 * (Nat.card (Z j) * (NZ j).index) =
                                (2 * Nat.card (Z j)) * (NZ j).index := by ring
                            _ ≤ (Nat.card (Z i) * (Nat.card (Z j) - 1)) *
                                (NZ j).index :=
                              Nat.mul_le_mul_right (NZ j).index hcoeff
                            _ = Nat.card (Z i) *
                                ((Nat.card (Z j) - 1) * (NZ j).index) := by ring
                            _ < Nat.card (Z i) * (NZ i).index :=
                              (Nat.mul_lt_mul_left (by omega : 0 < Nat.card (Z i))).2
                                hterm_lt
                            _ = 2 * (Nat.card (Z j) * (NZ j).index) := hfactor_eq
                        exact (Nat.lt_irrefl _ hbad).elim
                      have hzi_three : Nat.card (Z i) = 3 := by omega
                      have hfactor_eq_three :
                          3 * (NZ i).index =
                            2 * (Nat.card (Z j) * (NZ j).index) := by
                        calc
                          3 * (NZ i).index = Nat.card (Z i) * (NZ i).index :=
                            congrArg (fun a => a * (NZ i).index) hzi_three.symm
                          _ = 2 * (Nat.card (Z j) * (NZ j).index) := hfactor_eq
                      have hzj_two : Nat.card (Z j) = 2 := by
                        by_contra hzj_ne_two
                        have hzj_ge_three : 3 ≤ Nat.card (Z j) := by
                          have hzj := hnontrivial j
                          omega
                        have hcoeff :
                            2 * Nat.card (Z j) ≤
                              3 * (Nat.card (Z j) - 1) := by omega
                        have hbad :
                            2 * (Nat.card (Z j) * (NZ j).index) <
                              2 * (Nat.card (Z j) * (NZ j).index) := by
                          calc
                            2 * (Nat.card (Z j) * (NZ j).index) =
                                (2 * Nat.card (Z j)) * (NZ j).index := by ring
                            _ ≤ (3 * (Nat.card (Z j) - 1)) * (NZ j).index :=
                              Nat.mul_le_mul_right (NZ j).index hcoeff
                            _ = 3 * ((Nat.card (Z j) - 1) * (NZ j).index) := by ring
                            _ < 3 * (NZ i).index :=
                              (Nat.mul_lt_mul_left (by norm_num : 0 < 3)).2 hterm_lt
                            _ = 2 * (Nat.card (Z j) * (NZ j).index) :=
                              hfactor_eq_three
                        exact (Nat.lt_irrefl _ hbad).elim
                      have hindex' : (NZ i).index = 1 + (NZ j).index := by
                        simpa [hzj_two] using hindex_eq
                      have hfactor' : 3 * (NZ i).index = 4 * (NZ j).index := by
                        calc
                          3 * (NZ i).index =
                              2 * (Nat.card (Z j) * (NZ j).index) :=
                            hfactor_eq_three
                          _ = 4 * (NZ j).index := by rw [hzj_two]; ring
                      have hkj_three : (NZ j).index = 3 := by omega
                      have hki_four : (NZ i).index = 4 := by omega
                      have hHcard12 : Nat.card H = 12 := by
                        calc
                          Nat.card H = Nat.card (Z i) * (NZ i).index :=
                            hfactor_i.symm
                          _ = 12 := by rw [hzi_three, hki_four]
                      have hZiIndex4 : (Z i).index = 4 := by
                        have hmul := (Z i).card_mul_index
                        rw [hzi_three, hHcard12] at hmul
                        omega
                      let hZiP : IsPGroup 3 (Z i) :=
                        IsPGroup.of_card (n := 1) (by simpa using hzi_three)
                      let Q : Sylow 3 H := hZiP.toSylow (by
                        rw [hZiIndex4]
                        norm_num)
                      have hSylow4 : Nat.card (Sylow 3 H) = 4 := by
                        calc
                          Nat.card (Sylow 3 H) =
                              (Subgroup.normalizer (Q : Set H)).index :=
                            Q.card_eq_index_normalizer
                          _ = (NZ i).index := by rfl
                          _ = 4 := hki_four
                      exact
                        huppert_II_8_17_b_order_twelve_four_sylow_three
                          hHcard12 hSylow4
                    exact Or.inr hA4_case
                have hs0_cases : s 0 = 1 ∨ s 0 = 2 := by
                  have h := hs 0
                  omega
                have hs1_cases : s 1 = 1 ∨ s 1 = 2 := by
                  have h := hs 1
                  omega
                rcases hs0_cases with hs0 | hs0 <;>
                  rcases hs1_cases with hs1 | hs1
                · exact (hnot_one_one hs0 hs1).elim
                · rcases hmixed 0 1 (by decide) hs0 hs1 with hdih | hA4
                  · exact Or.inr (Or.inl hdih)
                  · exact Or.inr (Or.inr (Or.inl hA4))
                · rcases hmixed 1 0 (by decide) hs1 hs0 with hdih | hA4
                  · exact Or.inr (Or.inl hdih)
                  · exact Or.inr (Or.inr (Or.inl hA4))
                · exact (hnot_two_two hs0 hs1).elim
              exact h824_two_shape
            · have hr_three : r = 3 := by omega
              have h824_three_shape :
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = z ∧ IsCyclic H) ∨
                  (∃ z : ℕ,
                    ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                      (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                    Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
                  Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                  Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                subst r
                have hs_all_two : ∀ i, s i = 2 := by
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z 0) - 1) * (NZ 0).index +
                          (Nat.card (Z 1) - 1) * (NZ 1).index +
                            (Nat.card (Z 2) - 1) * (NZ 2).index := by
                    simpa only [Fin.sum_univ_three, add_assoc] using
                      h824_partition_count
                  have hquarter (a : Fin 3) :
                      Nat.card H ≤
                        4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                    have hzbound :
                        Nat.card (Z a) * s a ≤ 4 * (Nat.card (Z a) - 1) := by
                      calc
                        Nat.card (Z a) * s a ≤ Nat.card (Z a) * 2 :=
                          Nat.mul_le_mul_left (Nat.card (Z a)) (hs a).2
                        _ ≤ (2 * (Nat.card (Z a) - 1)) * 2 :=
                          Nat.mul_le_mul_right 2 (by
                            have hza := hnontrivial a
                            omega)
                        _ = 4 * (Nat.card (Z a) - 1) := by ring
                    calc
                      Nat.card H =
                          (Nat.card (Z a) * s a) * (NZ a).index :=
                        (h824_z_index_factor a).symm
                      _ ≤ (4 * (Nat.card (Z a) - 1)) * (NZ a).index :=
                        Nat.mul_le_mul_right (NZ a).index hzbound
                      _ = 4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                  have hhalf (a : Fin 3) (hsa : s a = 1) :
                      2 * Nat.card H ≤
                        4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                    have hfactor :
                        Nat.card (Z a) * (NZ a).index = Nat.card H := by
                      simpa [hsa] using h824_z_index_factor a
                    have hzbound :
                        Nat.card (Z a) ≤ 2 * (Nat.card (Z a) - 1) := by
                      have hza := hnontrivial a
                      omega
                    have hle :
                        Nat.card H ≤
                          2 * ((Nat.card (Z a) - 1) * (NZ a).index) := by
                      calc
                        Nat.card H = Nat.card (Z a) * (NZ a).index :=
                          hfactor.symm
                        _ ≤ (2 * (Nat.card (Z a) - 1)) * (NZ a).index :=
                          Nat.mul_le_mul_right (NZ a).index hzbound
                        _ = 2 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                    calc
                      2 * Nat.card H ≤
                          2 * (2 * ((Nat.card (Z a) - 1) * (NZ a).index)) :=
                        Nat.mul_le_mul_left 2 hle
                      _ = 4 * ((Nat.card (Z a) - 1) * (NZ a).index) := by ring
                  intro i
                  have hsi := hs i
                  rcases (show s i = 1 ∨ s i = 2 by omega) with hsi_one | hsi_two
                  · exfalso
                    fin_cases i
                    · have hh := hhalf 0 hsi_one
                      have hq1 := hquarter 1
                      have hq2 := hquarter 2
                      omega
                    · have hq0 := hquarter 0
                      have hh := hhalf 1 hsi_one
                      have hq2 := hquarter 2
                      omega
                    · have hq0 := hquarter 0
                      have hq1 := hquarter 1
                      have hh := hhalf 2 hsi_one
                      omega
                  · exact hsi_two
                have hordered (i j k : Fin 3)
                    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
                    (hji : Nat.card (Z j) ≤ Nat.card (Z i))
                    (hkj : Nat.card (Z k) ≤ Nat.card (Z j)) :
                    (∃ z : ℕ,
                      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                    Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                    Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                  have hsum :
                      (∑ a, (Nat.card (Z a) - 1) * (NZ a).index) =
                        (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                    have huniv :
                        ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                      apply (Finset.card_eq_iff_eq_univ ({i, j, k} : Finset (Fin 3))).mp
                      simp [hij, hik, hjk]
                    calc
                      (∑ a, (Nat.card (Z a) - 1) * (NZ a).index) =
                          ∑ a ∈ ({i, j, k} : Finset (Fin 3)),
                            (Nat.card (Z a) - 1) * (NZ a).index := by
                              rw [huniv]
                      _ = (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                              simp [hij, hik, hjk, add_assoc]
                  have hcount :
                      Nat.card H =
                        1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                    calc
                      Nat.card H =
                          1 + ∑ a, (Nat.card (Z a) - 1) * (NZ a).index :=
                        h824_partition_count
                      _ = 1 + (Nat.card (Z i) - 1) * (NZ i).index +
                          (Nat.card (Z j) - 1) * (NZ j).index +
                            (Nat.card (Z k) - 1) * (NZ k).index := by
                        rw [hsum]
                        simp [add_assoc]
                  have hfactor (a : Fin 3) :
                      2 * (Nat.card (Z a) * (NZ a).index) = Nat.card H := by
                    calc
                      2 * (Nat.card (Z a) * (NZ a).index) =
                          (Nat.card (Z a) * 2) * (NZ a).index := by ring
                      _ = (Nat.card (Z a) * s a) * (NZ a).index :=
                        congrArg (fun b =>
                          (Nat.card (Z a) * b) * (NZ a).index)
                          (hs_all_two a).symm
                      _ = Nat.card H := h824_z_index_factor a
                  have hqj :
                      Nat.card (Z i) * (NZ i).index =
                        Nat.card (Z j) * (NZ j).index := by
                    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                    exact (hfactor i).trans (hfactor j).symm
                  have hqk :
                      Nat.card (Z i) * (NZ i).index =
                        Nat.card (Z k) * (NZ k).index := by
                    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
                    exact (hfactor i).trans (hfactor k).symm
                  have hrel (a : Fin 3) :
                      (Nat.card (Z a) - 1) * (NZ a).index + (NZ a).index =
                        Nat.card (Z a) * (NZ a).index := by
                    calc
                      (Nat.card (Z a) - 1) * (NZ a).index + (NZ a).index =
                          (Nat.card (Z a) - 1 + 1) * (NZ a).index := by ring
                      _ = Nat.card (Z a) * (NZ a).index := by
                        rw [Nat.sub_add_cancel (hnontrivial a).le]
                  have hindex_sum :
                      (NZ i).index + (NZ j).index + (NZ k).index =
                        Nat.card (Z i) * (NZ i).index + 1 := by
                    have hri := hrel i
                    have hrj :
                        (Nat.card (Z j) - 1) * (NZ j).index + (NZ j).index =
                          Nat.card (Z i) * (NZ i).index :=
                      (hrel j).trans hqj.symm
                    have hrk :
                        (Nat.card (Z k) - 1) * (NZ k).index + (NZ k).index =
                          Nat.card (Z i) * (NZ i).index :=
                      (hrel k).trans hqk.symm
                    have htwice :
                        2 * (Nat.card (Z i) * (NZ i).index) =
                          1 + (Nat.card (Z i) - 1) * (NZ i).index +
                            (Nat.card (Z j) - 1) * (NZ j).index +
                              (Nat.card (Z k) - 1) * (NZ k).index :=
                      (hfactor i).trans hcount
                    omega
                  have hclassification :
                      (∃ z : ℕ,
                        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
                      Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                    have hki_le_kj : (NZ i).index ≤ (NZ j).index := by
                      by_contra hnot
                      have hlt : (NZ j).index < (NZ i).index := by omega
                      have hprod_lt :
                          Nat.card (Z j) * (NZ j).index <
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          Nat.card (Z j) * (NZ j).index ≤
                              Nat.card (Z i) * (NZ j).index :=
                            Nat.mul_le_mul_right (NZ j).index hji
                          _ < Nat.card (Z i) * (NZ i).index :=
                            (Nat.mul_lt_mul_left
                              (Nat.card_pos (α := Z i))).2 hlt
                      exact (Nat.lt_irrefl _ (hprod_lt.trans_eq hqj)).elim
                    have hqjk :
                        Nat.card (Z j) * (NZ j).index =
                          Nat.card (Z k) * (NZ k).index :=
                      hqj.symm.trans hqk
                    have hkj_le_kk : (NZ j).index ≤ (NZ k).index := by
                      by_contra hnot
                      have hlt : (NZ k).index < (NZ j).index := by omega
                      have hprod_lt :
                          Nat.card (Z k) * (NZ k).index <
                            Nat.card (Z j) * (NZ j).index := by
                        calc
                          Nat.card (Z k) * (NZ k).index ≤
                              Nat.card (Z j) * (NZ k).index :=
                            Nat.mul_le_mul_right (NZ k).index hkj
                          _ < Nat.card (Z j) * (NZ j).index :=
                            (Nat.mul_lt_mul_left
                              (Nat.card_pos (α := Z j))).2 hlt
                      exact (Nat.lt_irrefl _ (hprod_lt.trans_eq hqjk)).elim
                    have hzk_two : Nat.card (Z k) = 2 := by
                      by_contra hne
                      have hzk_ge_three : 3 ≤ Nat.card (Z k) := by
                        have hzk := hnontrivial k
                        omega
                      have hsum_le :
                          (NZ i).index + (NZ j).index + (NZ k).index ≤
                            3 * (NZ k).index := by omega
                      have hthree_le :
                          3 * (NZ k).index ≤
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          3 * (NZ k).index ≤
                              Nat.card (Z k) * (NZ k).index :=
                            Nat.mul_le_mul_right (NZ k).index hzk_ge_three
                          _ = Nat.card (Z i) * (NZ i).index := hqk.symm
                      omega
                    have hzj_lt_four : Nat.card (Z j) < 4 := by
                      by_contra hnot
                      have hzj_ge_four : 4 ≤ Nat.card (Z j) := by omega
                      have hfour_le :
                          4 * (NZ j).index ≤
                            Nat.card (Z i) * (NZ i).index := by
                        calc
                          4 * (NZ j).index ≤
                              Nat.card (Z j) * (NZ j).index :=
                            Nat.mul_le_mul_right (NZ j).index hzj_ge_four
                          _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                      have htwo_kj_le_kk :
                          2 * (NZ j).index ≤ (NZ k).index := by
                        have hqk_two :
                            Nat.card (Z i) * (NZ i).index =
                              2 * (NZ k).index := by
                          calc
                            Nat.card (Z i) * (NZ i).index =
                                Nat.card (Z k) * (NZ k).index := hqk
                            _ = 2 * (NZ k).index := by rw [hzk_two]
                        omega
                      have hsum_le :
                          (NZ i).index + (NZ j).index + (NZ k).index ≤
                            2 * (NZ k).index := by omega
                      have hqk_two :
                          Nat.card (Z i) * (NZ i).index =
                            2 * (NZ k).index := by
                        calc
                          Nat.card (Z i) * (NZ i).index =
                              Nat.card (Z k) * (NZ k).index := hqk
                          _ = 2 * (NZ k).index := by rw [hzk_two]
                      omega
                    have hzj_cases :
                        Nat.card (Z j) = 2 ∨ Nat.card (Z j) = 3 := by
                      have hzj_ge_two : 2 ≤ Nat.card (Z j) := by
                        have hzj := hnontrivial j
                        omega
                      omega
                    rcases hzj_cases with hzj_two | hzj_three
                    · have hdihedral_ordered :
                          ∃ z : ℕ,
                            ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
                              (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
                            Nat.card H = 2 * z ∧
                              Nonempty (H ≃* DihedralGroup z) := by
                        have hkj_eq_kk : (NZ j).index = (NZ k).index := by
                          have htwo_kj_eq_two_kk :
                              2 * (NZ j).index = 2 * (NZ k).index := by
                            calc
                              2 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_two]
                              _ = Nat.card (Z k) * (NZ k).index := hqjk
                              _ = 2 * (NZ k).index := by rw [hzk_two]
                          omega
                        have hki_one : (NZ i).index = 1 := by
                          have htwo_kj :
                              2 * (NZ j).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              2 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_two]
                              _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                          omega
                        have hHcard :
                            Nat.card H = 2 * Nat.card (Z i) := by
                          calc
                            Nat.card H =
                                2 * (Nat.card (Z i) * (NZ i).index) :=
                              (hfactor i).symm
                            _ = 2 * Nat.card (Z i) := by rw [hki_one, mul_one]
                        have hNZtop : NZ i = ⊤ :=
                          Subgroup.index_eq_one.mp hki_one
                        obtain ⟨eD⟩ := hdihedral i (hs_all_two i)
                        let eH : NZ i ≃* H :=
                          (MulEquiv.subgroupCongr hNZtop).trans
                            (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H)
                        exact
                          ⟨Nat.card (Z i), hdivides i, hHcard,
                            ⟨eH.symm.trans eD⟩⟩
                      exact Or.inl hdihedral_ordered
                    · have hexceptional :
                          Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
                            Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                        have hzi_lt_six : Nat.card (Z i) < 6 := by
                          by_contra hnot
                          have hzi_ge_six : 6 ≤ Nat.card (Z i) := by omega
                          have hsix_le_q :
                              6 * (NZ i).index ≤
                                Nat.card (Z i) * (NZ i).index :=
                            Nat.mul_le_mul_right (NZ i).index hzi_ge_six
                          have hthree_j :
                              3 * (NZ j).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              3 * (NZ j).index =
                                  Nat.card (Z j) * (NZ j).index := by
                                rw [hzj_three]
                              _ = Nat.card (Z i) * (NZ i).index := hqj.symm
                          have htwo_k :
                              2 * (NZ k).index =
                                Nat.card (Z i) * (NZ i).index := by
                            calc
                              2 * (NZ k).index =
                                  Nat.card (Z k) * (NZ k).index := by
                                rw [hzk_two]
                              _ = Nat.card (Z i) * (NZ i).index := hqk.symm
                          omega
                        have hzi_cases :
                            Nat.card (Z i) = 3 ∨ Nat.card (Z i) = 4 ∨
                              Nat.card (Z i) = 5 := by
                          have hzi_ge_three : 3 ≤ Nat.card (Z i) := by
                            rw [← hzj_three]
                            exact hji
                          omega
                        rcases hzi_cases with hzi_three | hzi_four | hzi_five
                        · have hindices_three :
                              (NZ i).index = 2 ∧ (NZ j).index = 2 ∧
                                (NZ k).index = 3 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_three, hzj_three] at hijq
                            rw [hzi_three, hzk_two] at hikq
                            rw [hzi_three] at hsumq
                            omega
                          have hHcard12 : Nat.card H = 12 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 12 := by rw [hzi_three, hindices_three.1]
                          have hZiIndex4 : (Z i).index = 4 := by
                            have hmul := (Z i).card_mul_index
                            rw [hzi_three, hHcard12] at hmul
                            omega
                          have hZjIndex4 : (Z j).index = 4 := by
                            have hmul := (Z j).card_mul_index
                            rw [hzj_three, hHcard12] at hmul
                            omega
                          let hZiP : IsPGroup 3 (Z i) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzi_three)
                          let hZjP : IsPGroup 3 (Z j) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzj_three)
                          let Qi : Sylow 3 H := hZiP.toSylow (by
                            rw [hZiIndex4]
                            norm_num)
                          let Qj : Sylow 3 H := hZjP.toSylow (by
                            rw [hZjIndex4]
                            norm_num)
                          obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Qi Qj
                          have hconj :
                              (Z i).map (MulAut.conj g).toMonoidHom = Z j := by
                            have hg' := congrArg
                              (fun Q : Sylow 3 H => (Q : Subgroup H)) hg
                            exact hg'
                          exact (hij (hdistinct i j g hconj)).elim
                        · left
                          have hindices_four :
                              (NZ i).index = 3 ∧ (NZ j).index = 4 ∧
                                (NZ k).index = 6 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_four, hzj_three] at hijq
                            rw [hzi_four, hzk_two] at hikq
                            rw [hzi_four] at hsumq
                            omega
                          have hHcard24 : Nat.card H = 24 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 24 := by rw [hzi_four, hindices_four.1]
                          have hZjIndex8 : (Z j).index = 8 := by
                            have hmul := (Z j).card_mul_index
                            rw [hzj_three, hHcard24] at hmul
                            omega
                          let hZjP : IsPGroup 3 (Z j) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzj_three)
                          let Q : Sylow 3 H := hZjP.toSylow (by
                            rw [hZjIndex8]
                            norm_num)
                          have hSylow4 : Nat.card (Sylow 3 H) = 4 := by
                            calc
                              Nat.card (Sylow 3 H) =
                                  (Subgroup.normalizer (Q : Set H)).index :=
                                Q.card_eq_index_normalizer
                              _ = (NZ j).index := by rfl
                              _ = 4 := hindices_four.2.1
                          let Ω := Sylow 3 H
                          let := Fintype.ofFinite Ω
                          have hΩcard : Fintype.card Ω = 4 := by
                            simpa [Ω, Nat.card_eq_fintype_card] using hSylow4
                          let act := MulAction.toPermHom H Ω
                          have hact_inj : Function.Injective act := by
                            rw [← MonoidHom.ker_eq_bot_iff]
                            have hker_le_normalizer (R : Sylow 3 H) :
                                act.ker ≤ Subgroup.normalizer (R : Set H) := by
                              intro x hx
                              have hxperm : act x = 1 := hx
                              have hxfix : x • R = R := by
                                have h := DFunLike.congr_fun hxperm R
                                simpa [act] using h
                              exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
                            have hnormalizer_card_six :
                                Nat.card (Subgroup.normalizer (Q : Set H)) = 6 := by
                              have hQindex :
                                  (Subgroup.normalizer (Q : Set H)).index = 4 := by
                                calc
                                  (Subgroup.normalizer (Q : Set H)).index =
                                      Nat.card (Sylow 3 H) :=
                                    Q.card_eq_index_normalizer.symm
                                  _ = 4 := hSylow4
                              have hmul :=
                                (Subgroup.normalizer (Q : Set H)).card_mul_index
                              rw [hQindex, hHcard24] at hmul
                              omega
                            have hker_card_dvd_six : Nat.card act.ker ∣ 6 := by
                              simpa [hnormalizer_card_six] using
                                Subgroup.card_dvd_of_le (hker_le_normalizer Q)
                            have hno_sylow_le_ker (R : Sylow 3 H) :
                                ¬ (R : Subgroup H) ≤ act.ker := by
                              intro hRker
                              obtain ⟨S, hSR⟩ :=
                                Fintype.exists_ne_of_one_lt_card
                                  (by omega : 1 < Fintype.card Ω) R
                              have hRnormalizesS :
                                  (R : Subgroup H) ≤
                                    Subgroup.normalizer (S : Set H) := by
                                intro x hx
                                exact hker_le_normalizer S (hRker hx)
                              have hsupP :
                                  IsPGroup 3
                                    ((R : Subgroup H) ⊔ (S : Subgroup H) :
                                      Subgroup H) :=
                                R.isPGroup'.to_sup_of_normal_right'
                                  S.isPGroup' hRnormalizesS
                              have hsup_eq :
                                  (R : Subgroup H) ⊔ (S : Subgroup H) = S :=
                                S.is_maximal' hsupP le_sup_right
                              have hRleS : (R : Subgroup H) ≤ S := by
                                calc
                                  (R : Subgroup H) ≤
                                      (R : Subgroup H) ⊔ (S : Subgroup H) :=
                                    le_sup_left
                                  _ = S := hsup_eq
                              have hS_eq_R : (S : Subgroup H) = R :=
                                R.is_maximal' S.isPGroup' hRleS
                              exact hSR (Sylow.ext hS_eq_R)
                            have hthree_not_dvd_ker : ¬ 3 ∣ Nat.card act.ker := by
                              intro hthree
                              obtain ⟨x, hxorder⟩ :=
                                exists_prime_orderOf_dvd_card' 3 hthree
                              have hxHorder : orderOf (x : H) = 3 :=
                                (Subgroup.orderOf_coe x).trans hxorder
                              have hXisP :
                                  IsPGroup 3 (Subgroup.zpowers (x : H)) :=
                                IsPGroup.of_card
                                  (((Nat.card_zpowers (x : H)).trans hxHorder).trans
                                    (pow_one 3).symm)
                              obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
                              have hXcard :
                                  Nat.card (Subgroup.zpowers (x : H)) = 3 :=
                                (Nat.card_zpowers (x : H)).trans hxHorder
                              have hRcard : Nat.card R = 3 := by
                                calc
                                  Nat.card R = Nat.card Q :=
                                    Nat.card_congr (Sylow.equiv R Q).toEquiv
                                  _ = 3 := by
                                    change Nat.card (Z j) = 3
                                    exact hzj_three
                              have hXR_eq :
                                  Subgroup.zpowers (x : H) = (R : Subgroup H) :=
                                Subgroup.eq_of_le_of_card_ge hXR (by
                                  rw [hXcard, hRcard])
                              apply hno_sylow_le_ker R
                              rw [← hXR_eq]
                              intro y hy
                              rcases hy with ⟨n, rfl⟩
                              exact act.ker.zpow_mem x.2 n
                            have hker_card_cases :
                                Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
                              have hpos : 0 < Nat.card act.ker := Nat.card_pos
                              have hle : Nat.card act.ker ≤ 6 :=
                                Nat.le_of_dvd (by norm_num) hker_card_dvd_six
                              interval_cases Nat.card act.ker <;> norm_num at *
                            rcases hker_card_cases with hker_one | hker_two
                            · exact Subgroup.card_eq_one.mp hker_one
                            · have horder_six : ∃ x : H, orderOf x = 6 := by
                                obtain ⟨y, hyorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 3 (by
                                    rw [hzj_three])
                                have hyHorder : orderOf (y : H) = 3 :=
                                  (Subgroup.orderOf_coe y).trans hyorder
                                obtain ⟨c, hcorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 2 (by
                                    rw [hker_two])
                                have hcne : c ≠ 1 := by
                                  intro hc
                                  rw [hc, orderOf_one] at hcorder
                                  norm_num at hcorder
                                obtain ⟨c', hc'ne, hc'unique⟩ :=
                                  (Nat.card_eq_two_iff' (1 : act.ker)).mp hker_two
                                have hc_eq : c = c' := hc'unique c hcne
                                have hc_central :
                                    (c : H) ∈ Subgroup.center H := by
                                  rw [Subgroup.mem_center_iff]
                                  intro g
                                  let d : act.ker :=
                                    ⟨g * (c : H) * g⁻¹,
                                      (inferInstance : act.ker.Normal).conj_mem
                                        (c : H) c.2 g⟩
                                  have hdne : d ≠ 1 := by
                                    intro hd
                                    have hdval := congrArg Subtype.val hd
                                    change g * (c : H) * g⁻¹ = 1 at hdval
                                    apply hcne
                                    apply Subtype.ext
                                    calc
                                      (c : H) =
                                          g⁻¹ * (g * (c : H) * g⁻¹) * g := by
                                        group
                                      _ = 1 := by rw [hdval]; simp
                                  have hd_eq : d = c := by
                                    rw [hc_eq]
                                    exact hc'unique d hdne
                                  have hdval := congrArg Subtype.val hd_eq
                                  change g * (c : H) * g⁻¹ = (c : H) at hdval
                                  calc
                                    g * (c : H) =
                                        (g * (c : H) * g⁻¹) * g := by group
                                    _ = (c : H) * g := by rw [hdval]
                                have hcHorder : orderOf (c : H) = 2 :=
                                  (Subgroup.orderOf_coe c).trans hcorder
                                have hcomm : Commute (c : H) (y : H) :=
                                  (Subgroup.mem_center_iff.mp hc_central (y : H)).symm
                                have hcop :
                                    Nat.Coprime (orderOf (c : H))
                                      (orderOf (y : H)) := by
                                  rw [hcHorder, hyHorder]
                                  norm_num
                                refine ⟨(c : H) * (y : H), ?_⟩
                                rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop,
                                  hcHorder, hyHorder]
                              have hno_order_six : ∀ x : H, orderOf x ≠ 6 := by
                                intro x hxorder
                                have hxne : x ≠ 1 := by
                                  intro hx
                                  rw [hx, orderOf_one] at hxorder
                                  norm_num at hxorder
                                obtain ⟨A, hxA, _hAunique⟩ :=
                                  huppert_II_8_22_unique_family hFcard H Z
                                    hcyclic hnontrivial hcoprime hmaximal
                                    hrepresentative hdistinct x hxne
                                rcases A with Qp | z
                                · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                    (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                  have hQpcard : Nat.card Qp = 1 := by
                                    calc
                                      Nat.card Qp = Nat.card P :=
                                        Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                      _ = 1 := by simpa using hPcard
                                  rw [hxorder, hQpcard] at hxdvd
                                  norm_num at hxdvd
                                · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                                    z.2.1.orderOf_dvd_natCard hxA
                                  obtain ⟨g, hg⟩ := z.2.2
                                  have hzcard :
                                      Nat.card z.2.1 = Nat.card (Z z.1) := by
                                    rw [hg, Subgroup.card_map_of_injective
                                      (MulAut.conj g).injective]
                                  have huniv :
                                      ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                                    apply
                                      (Finset.card_eq_iff_eq_univ
                                        ({i, j, k} : Finset (Fin 3))).mp
                                    simp [hij, hik, hjk]
                                  have hz_cases : z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                    have hzmem :
                                        z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                      rw [huniv]
                                      simp
                                    simpa [Finset.mem_insert, Finset.mem_singleton]
                                      using hzmem
                                  rw [hxorder, hzcard] at hxdvd
                                  rcases hz_cases with hzi | hzj | hzk
                                  · rw [hzi, hzi_four] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzj, hzj_three] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzk, hzk_two] at hxdvd
                                    norm_num at hxdvd
                              obtain ⟨x, hx⟩ := horder_six
                              exact (hno_order_six x hx).elim
                          let eΩ : Ω ≃ Fin 4 := Fintype.equivFinOfCardEq hΩcard
                          let actFin : H →* Equiv.Perm (Fin 4) :=
                            (Equiv.permCongrHom eΩ).toMonoidHom.comp act
                          have hactFin_inj : Function.Injective actFin := by
                            intro x y hxy
                            apply hact_inj
                            apply (Equiv.permCongrHom eΩ).injective
                            simpa [actFin] using hxy
                          let K : Subgroup (Equiv.Perm (Fin 4)) := actFin.range
                          have hrange_inj : Function.Injective actFin.rangeRestrict := by
                            intro x y hxy
                            exact hactFin_inj (congrArg Subtype.val hxy)
                          let eRange : H ≃* K :=
                            MulEquiv.ofBijective actFin.rangeRestrict
                              ⟨hrange_inj,
                                MonoidHom.rangeRestrict_surjective actFin⟩
                          have hKcard : Nat.card K = 24 := by
                            calc
                              Nat.card K = Nat.card H :=
                                (Nat.card_congr eRange.toEquiv).symm
                              _ = 24 := hHcard24
                          have hpermcard :
                              Nat.card (Equiv.Perm (Fin 4)) = 24 := by
                            norm_num [Fintype.card_perm, Nat.factorial]
                          have hKtop : K = ⊤ :=
                            Subgroup.eq_top_of_card_eq (H := K)
                              (hKcard.trans hpermcard.symm)
                          exact
                            ⟨eRange.trans (MulEquiv.subgroupCongr hKtop) |>.trans
                              (Subgroup.topEquiv :
                                (⊤ : Subgroup (Equiv.Perm (Fin 4))) ≃*
                                  Equiv.Perm (Fin 4))⟩
                        · right
                          have hindices_five :
                              (NZ i).index = 6 ∧ (NZ j).index = 10 ∧
                                (NZ k).index = 15 := by
                            have hijq := hqj
                            have hikq := hqk
                            have hsumq := hindex_sum
                            rw [hzi_five, hzj_three] at hijq
                            rw [hzi_five, hzk_two] at hikq
                            rw [hzi_five] at hsumq
                            omega
                          have hHcard60 : Nat.card H = 60 := by
                            calc
                              Nat.card H =
                                  2 * (Nat.card (Z i) * (NZ i).index) :=
                                (hfactor i).symm
                              _ = 60 := by rw [hzi_five, hindices_five.1]
                          have hZiIndex12 : (Z i).index = 12 := by
                            have hmul := (Z i).card_mul_index
                            rw [hzi_five, hHcard60] at hmul
                            omega
                          let : Fact (Nat.Prime 5) := ⟨by decide⟩
                          let hZiP : IsPGroup 5 (Z i) :=
                            IsPGroup.of_card (n := 1) (by simpa using hzi_five)
                          let Q : Sylow 5 H := hZiP.toSylow (by
                            rw [hZiIndex12]
                            norm_num)
                          have hSylow6 : Nat.card (Sylow 5 H) = 6 := by
                            calc
                              Nat.card (Sylow 5 H) =
                                  (Subgroup.normalizer (Q : Set H)).index :=
                                Q.card_eq_index_normalizer
                              _ = (NZ i).index := by rfl
                              _ = 6 := hindices_five.1
                          let Ω := Sylow 5 H
                          let := Fintype.ofFinite Ω
                          have hΩcard : Fintype.card Ω = 6 := by
                            simpa [Ω, Nat.card_eq_fintype_card] using hSylow6
                          let act := MulAction.toPermHom H Ω
                          have hact_inj : Function.Injective act := by
                            rw [← MonoidHom.ker_eq_bot_iff]
                            have hker_le_normalizer (R : Sylow 5 H) :
                                act.ker ≤ Subgroup.normalizer (R : Set H) := by
                              intro x hx
                              have hxperm : act x = 1 := hx
                              have hxfix : x • R = R := by
                                have h := DFunLike.congr_fun hxperm R
                                simpa [act] using h
                              exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
                            have hnormalizer_card_ten :
                                Nat.card (Subgroup.normalizer (Q : Set H)) = 10 := by
                              have hQindex :
                                  (Subgroup.normalizer (Q : Set H)).index = 6 := by
                                calc
                                  (Subgroup.normalizer (Q : Set H)).index =
                                      Nat.card (Sylow 5 H) :=
                                    Q.card_eq_index_normalizer.symm
                                  _ = 6 := hSylow6
                              have hmul :=
                                (Subgroup.normalizer (Q : Set H)).card_mul_index
                              rw [hQindex, hHcard60] at hmul
                              omega
                            have hker_card_dvd_ten : Nat.card act.ker ∣ 10 := by
                              simpa [hnormalizer_card_ten] using
                                Subgroup.card_dvd_of_le (hker_le_normalizer Q)
                            have hno_sylow_le_ker (R : Sylow 5 H) :
                                ¬ (R : Subgroup H) ≤ act.ker := by
                              intro hRker
                              obtain ⟨S, hSR⟩ :=
                                Fintype.exists_ne_of_one_lt_card
                                  (by omega : 1 < Fintype.card Ω) R
                              have hRnormalizesS :
                                  (R : Subgroup H) ≤
                                    Subgroup.normalizer (S : Set H) := by
                                intro x hx
                                exact hker_le_normalizer S (hRker hx)
                              have hsupP :
                                  IsPGroup 5
                                    ((R : Subgroup H) ⊔ (S : Subgroup H) :
                                      Subgroup H) :=
                                R.isPGroup'.to_sup_of_normal_right'
                                  S.isPGroup' hRnormalizesS
                              have hsup_eq :
                                  (R : Subgroup H) ⊔ (S : Subgroup H) = S :=
                                S.is_maximal' hsupP le_sup_right
                              have hRleS : (R : Subgroup H) ≤ S := by
                                calc
                                  (R : Subgroup H) ≤
                                      (R : Subgroup H) ⊔ (S : Subgroup H) :=
                                    le_sup_left
                                  _ = S := hsup_eq
                              have hS_eq_R : (S : Subgroup H) = R :=
                                R.is_maximal' S.isPGroup' hRleS
                              exact hSR (Sylow.ext hS_eq_R)
                            have hfive_not_dvd_ker : ¬ 5 ∣ Nat.card act.ker := by
                              intro hfive
                              obtain ⟨x, hxorder⟩ :=
                                exists_prime_orderOf_dvd_card' 5 hfive
                              have hxHorder : orderOf (x : H) = 5 :=
                                (Subgroup.orderOf_coe x).trans hxorder
                              have hXisP :
                                  IsPGroup 5 (Subgroup.zpowers (x : H)) :=
                                IsPGroup.of_card
                                  (((Nat.card_zpowers (x : H)).trans hxHorder).trans
                                    (pow_one 5).symm)
                              obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
                              have hXcard :
                                  Nat.card (Subgroup.zpowers (x : H)) = 5 :=
                                (Nat.card_zpowers (x : H)).trans hxHorder
                              have hRcard : Nat.card R = 5 := by
                                calc
                                  Nat.card R = Nat.card Q :=
                                    Nat.card_congr (Sylow.equiv R Q).toEquiv
                                  _ = 5 := by
                                    change Nat.card (Z i) = 5
                                    exact hzi_five
                              have hXR_eq :
                                  Subgroup.zpowers (x : H) = (R : Subgroup H) :=
                                Subgroup.eq_of_le_of_card_ge hXR (by
                                  rw [hXcard, hRcard])
                              apply hno_sylow_le_ker R
                              rw [← hXR_eq]
                              intro y hy
                              rcases hy with ⟨n, rfl⟩
                              exact act.ker.zpow_mem x.2 n
                            have hker_card_cases :
                                Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
                              have hpos : 0 < Nat.card act.ker := Nat.card_pos
                              have hle : Nat.card act.ker ≤ 10 :=
                                Nat.le_of_dvd (by norm_num) hker_card_dvd_ten
                              interval_cases Nat.card act.ker <;> norm_num at *
                            rcases hker_card_cases with hker_one | hker_two
                            · exact Subgroup.card_eq_one.mp hker_one
                            · have horder_ten : ∃ x : H, orderOf x = 10 := by
                                obtain ⟨y, hyorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 5 (by
                                    rw [hzi_five])
                                have hyHorder : orderOf (y : H) = 5 :=
                                  (Subgroup.orderOf_coe y).trans hyorder
                                obtain ⟨c, hcorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 2 (by
                                    rw [hker_two])
                                have hcne : c ≠ 1 := by
                                  intro hc
                                  rw [hc, orderOf_one] at hcorder
                                  norm_num at hcorder
                                obtain ⟨c', hc'ne, hc'unique⟩ :=
                                  (Nat.card_eq_two_iff' (1 : act.ker)).mp hker_two
                                have hc_eq : c = c' := hc'unique c hcne
                                have hc_central :
                                    (c : H) ∈ Subgroup.center H := by
                                  rw [Subgroup.mem_center_iff]
                                  intro g
                                  let d : act.ker :=
                                    ⟨g * (c : H) * g⁻¹,
                                      (inferInstance : act.ker.Normal).conj_mem
                                        (c : H) c.2 g⟩
                                  have hdne : d ≠ 1 := by
                                    intro hd
                                    have hdval := congrArg Subtype.val hd
                                    change g * (c : H) * g⁻¹ = 1 at hdval
                                    apply hcne
                                    apply Subtype.ext
                                    calc
                                      (c : H) =
                                          g⁻¹ * (g * (c : H) * g⁻¹) * g := by
                                        group
                                      _ = 1 := by rw [hdval]; simp
                                  have hd_eq : d = c := by
                                    rw [hc_eq]
                                    exact hc'unique d hdne
                                  have hdval := congrArg Subtype.val hd_eq
                                  change g * (c : H) * g⁻¹ = (c : H) at hdval
                                  calc
                                    g * (c : H) =
                                        (g * (c : H) * g⁻¹) * g := by group
                                    _ = (c : H) * g := by rw [hdval]
                                have hcHorder : orderOf (c : H) = 2 :=
                                  (Subgroup.orderOf_coe c).trans hcorder
                                have hcomm : Commute (c : H) (y : H) :=
                                  (Subgroup.mem_center_iff.mp hc_central (y : H)).symm
                                have hcop :
                                    Nat.Coprime (orderOf (c : H))
                                      (orderOf (y : H)) := by
                                  rw [hcHorder, hyHorder]
                                  norm_num
                                refine ⟨(c : H) * (y : H), ?_⟩
                                rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop,
                                  hcHorder, hyHorder]
                              have hno_order_ten : ∀ x : H, orderOf x ≠ 10 := by
                                intro x hxorder
                                have hxne : x ≠ 1 := by
                                  intro hx
                                  rw [hx, orderOf_one] at hxorder
                                  norm_num at hxorder
                                obtain ⟨A, hxA, _hAunique⟩ :=
                                  huppert_II_8_22_unique_family hFcard H Z
                                    hcyclic hnontrivial hcoprime hmaximal
                                    hrepresentative hdistinct x hxne
                                rcases A with Qp | z
                                · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                    (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                  have hQpcard : Nat.card Qp = 1 := by
                                    calc
                                      Nat.card Qp = Nat.card P :=
                                        Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                      _ = 1 := by simpa using hPcard
                                  rw [hxorder, hQpcard] at hxdvd
                                  norm_num at hxdvd
                                · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                                    z.2.1.orderOf_dvd_natCard hxA
                                  obtain ⟨g, hg⟩ := z.2.2
                                  have hzcard :
                                      Nat.card z.2.1 = Nat.card (Z z.1) := by
                                    rw [hg, Subgroup.card_map_of_injective
                                      (MulAut.conj g).injective]
                                  have huniv :
                                      ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                                    apply
                                      (Finset.card_eq_iff_eq_univ
                                        ({i, j, k} : Finset (Fin 3))).mp
                                    simp [hij, hik, hjk]
                                  have hz_cases : z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                    have hzmem :
                                        z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                      rw [huniv]
                                      simp
                                    simpa [Finset.mem_insert, Finset.mem_singleton]
                                      using hzmem
                                  rw [hxorder, hzcard] at hxdvd
                                  rcases hz_cases with hzi | hzj | hzk
                                  · rw [hzi, hzi_five] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzj, hzj_three] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzk, hzk_two] at hxdvd
                                    norm_num at hxdvd
                              obtain ⟨x, hx⟩ := horder_ten
                              exact (hno_order_ten x hx).elim
                          have hA5_via_sylow_two :
                              Nonempty (H ≃* alternatingGroup (Fin 5)) := by
                            have hNZkcard4 : Nat.card (NZ k) = 4 := by
                              dsimp only [NZ]
                              rw [hnormalizerZ k, hzk_two, hs_all_two k]
                            let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
                            let hNZkP : IsPGroup 2 (NZ k) :=
                              IsPGroup.of_card (n := 2) (by
                                simpa using hNZkcard4)
                            let P2 : Sylow 2 H := hNZkP.toSylow (by
                              rw [hindices_five.2.2]
                              norm_num)
                            have hSylow2_data :
                                Nat.card (Sylow 2 H) = 5 ∧
                                  ∀ x : H, orderOf x = 2 →
                                    ∃! R : Sylow 2 H,
                                      x ∈ (R : Subgroup H) := by
                              have hSylow2card4 (R : Sylow 2 H) :
                                  Nat.card R = 4 := by
                                calc
                                  Nat.card R = Nat.card P2 :=
                                    Nat.card_congr (Sylow.equiv R P2).toEquiv
                                  _ = 4 := by
                                    change Nat.card (NZ k) = 4
                                    exact hNZkcard4
                              have hno_order_four :
                                  ∀ x : H, orderOf x ≠ 4 := by
                                intro x hxorder
                                have hxne : x ≠ 1 := by
                                  intro hx
                                  rw [hx, orderOf_one] at hxorder
                                  norm_num at hxorder
                                obtain ⟨A, hxA, _hAunique⟩ :=
                                  huppert_II_8_22_unique_family hFcard H Z
                                    hcyclic hnontrivial hcoprime hmaximal
                                    hrepresentative hdistinct x hxne
                                rcases A with Qp | z
                                · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                    (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                  have hQpcard : Nat.card Qp = 1 := by
                                    calc
                                      Nat.card Qp = Nat.card P :=
                                        Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                      _ = 1 := by simpa using hPcard
                                  rw [hxorder, hQpcard] at hxdvd
                                  norm_num at hxdvd
                                · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                                    z.2.1.orderOf_dvd_natCard hxA
                                  obtain ⟨g, hg⟩ := z.2.2
                                  have hzcard :
                                      Nat.card z.2.1 = Nat.card (Z z.1) := by
                                    rw [hg, Subgroup.card_map_of_injective
                                      (MulAut.conj g).injective]
                                  have huniv :
                                      ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
                                    apply
                                      (Finset.card_eq_iff_eq_univ
                                        ({i, j, k} : Finset (Fin 3))).mp
                                    simp [hij, hik, hjk]
                                  have hz_cases : z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                    have hzmem :
                                        z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                      rw [huniv]
                                      simp
                                    simpa [Finset.mem_insert, Finset.mem_singleton]
                                      using hzmem
                                  rw [hxorder, hzcard] at hxdvd
                                  rcases hz_cases with hzi | hzj | hzk
                                  · rw [hzi, hzi_five] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzj, hzj_three] at hxdvd
                                    norm_num at hxdvd
                                  · rw [hzk, hzk_two] at hxdvd
                                    norm_num at hxdvd
                              have hsylow2_order_two (R : Sylow 2 H)
                                  {x : H} (hxR : x ∈ (R : Subgroup H))
                                  (hxne : x ≠ 1) : orderOf x = 2 := by
                                have hdvd : orderOf x ∣ 4 := by
                                  simpa [hSylow2card4 R] using
                                    (R : Subgroup H).orderOf_dvd_natCard hxR
                                have hpos : 0 < orderOf x := orderOf_pos x
                                have hne_one : orderOf x ≠ 1 :=
                                  fun h => hxne (orderOf_eq_one_iff.mp h)
                                have hne_four : orderOf x ≠ 4 := hno_order_four x
                                have hle : orderOf x ≤ 4 :=
                                  Nat.le_of_dvd (by norm_num) hdvd
                                interval_cases orderOf x <;> norm_num at *
                              have hinvolution_unique_sylow (x : H)
                                  (hxorder : orderOf x = 2) :
                                  ∃! R : Sylow 2 H, x ∈ (R : Subgroup H) := by
                                have hxne : x ≠ 1 := by
                                  intro hx
                                  rw [hx, orderOf_one] at hxorder
                                  norm_num at hxorder
                                let X : Subgroup H := Subgroup.zpowers x
                                have hXcard : Nat.card X = 2 := by
                                  simpa [X] using
                                    (Nat.card_zpowers x).trans hxorder
                                have hXisP : IsPGroup 2 X :=
                                  IsPGroup.of_card (n := 1) (by simpa using hXcard)
                                obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
                                have hxR : x ∈ (R : Subgroup H) :=
                                  hXR (by exact Subgroup.mem_zpowers x)
                                have hnormalizerXcard4 :
                                    Nat.card (Subgroup.normalizer (X : Set H)) = 4 := by
                                  obtain ⟨A, hxA, _hAunique⟩ :=
                                    huppert_II_8_22_unique_family hFcard H Z
                                      hcyclic hnontrivial hcoprime hmaximal
                                      hrepresentative hdistinct x hxne
                                  rcases A with Qp | z
                                  · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                      (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                    have hQpcard : Nat.card Qp = 1 := by
                                      calc
                                        Nat.card Qp = Nat.card P :=
                                          Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                        _ = 1 := by simpa using hPcard
                                    rw [hxorder, hQpcard] at hxdvd
                                    norm_num at hxdvd
                                  · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                                      z.2.1.orderOf_dvd_natCard hxA
                                    obtain ⟨g, hg⟩ := z.2.2
                                    have hzcard :
                                        Nat.card z.2.1 = Nat.card (Z z.1) := by
                                      rw [hg, Subgroup.card_map_of_injective
                                        (MulAut.conj g).injective]
                                    have huniv :
                                        ({i, j, k} : Finset (Fin 3)) =
                                          Finset.univ := by
                                      apply
                                        (Finset.card_eq_iff_eq_univ
                                          ({i, j, k} : Finset (Fin 3))).mp
                                      simp [hij, hik, hjk]
                                    have hz_cases :
                                        z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                      have hzmem :
                                          z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                        rw [huniv]
                                        simp
                                      simpa [Finset.mem_insert,
                                        Finset.mem_singleton] using hzmem
                                    rcases hz_cases with hza | hza | hza
                                    · rw [hxorder, hzcard, hza, hzi_five] at hxdvd
                                      norm_num at hxdvd
                                    · rw [hxorder, hzcard, hza, hzj_three] at hxdvd
                                      norm_num at hxdvd
                                    · have hgk :
                                          z.2.1 = (Z k).map
                                            (MulAut.conj g).toMonoidHom := by
                                        simpa [hza] using hg
                                      have hWcard : Nat.card z.2.1 = 2 := by
                                        rw [hzcard, hza, hzk_two]
                                      have hXeqW : X = z.2.1 :=
                                        Subgroup.eq_of_le_of_card_ge (by
                                          exact Subgroup.zpowers_le.2 hxA) (by
                                            rw [hXcard, hWcard])
                                      rw [hXeqW, hgk]
                                      rw [← Subgroup.map_normalizer_eq_of_bijective
                                        (Z k) (MulAut.conj g).bijective,
                                        Subgroup.card_map_of_injective
                                          (MulAut.conj g).injective]
                                      simpa [NZ] using hNZkcard4
                                have hSylow_eq_normalizer (S : Sylow 2 H)
                                    (hxS : x ∈ (S : Subgroup H)) :
                                    (S : Subgroup H) =
                                      Subgroup.normalizer (X : Set H) := by
                                  have hScard : Nat.card S = 2 ^ 2 := by
                                    norm_num [hSylow2card4 S]
                                  let : CommGroup S :=
                                    IsPGroup.commGroupOfCardEqPrimeSq hScard
                                  have hXleS : X ≤ (S : Subgroup H) := by
                                    exact Subgroup.zpowers_le.2 hxS
                                  have hnormal :
                                      (X.subgroupOf (S : Subgroup H)).Normal :=
                                    inferInstance
                                  have hSle :
                                      (S : Subgroup H) ≤
                                        Subgroup.normalizer (X : Set H) :=
                                    (Subgroup.normal_subgroupOf_iff_le_normalizer
                                      hXleS).mp hnormal
                                  exact Subgroup.eq_of_le_of_card_ge hSle (by
                                    rw [hSylow2card4 S, hnormalizerXcard4])
                                refine ⟨R, hxR, ?_⟩
                                intro S hxS
                                apply Sylow.ext
                                exact (hSylow_eq_normalizer S hxS).trans
                                  (hSylow_eq_normalizer R hxR).symm
                              let Zodd : Fin 2 → Subgroup H := ![Z i, Z j]
                              have hunique2 : ∀ x : H, x ≠ 1 →
                                  ∃! A : (Sylow 2 H) ⊕
                                      (Σ a : Fin 2,
                                        {W : Subgroup H // ∃ g : H,
                                          W = (Zodd a).map
                                            (MulAut.conj g).toMonoidHom}),
                                    x ∈ match A with
                                      | Sum.inl R => (R : Subgroup H)
                                      | Sum.inr z => (z.2.1 : Subgroup H) := by
                                intro x hxne
                                obtain ⟨A, hxA, hAunique⟩ :=
                                  huppert_II_8_22_unique_family hFcard H Z
                                    hcyclic hnontrivial hcoprime hmaximal
                                    hrepresentative hdistinct x hxne
                                rcases A with Qp | z
                                · have hxdvd : orderOf x ∣ Nat.card Qp :=
                                    (Qp : Subgroup H).orderOf_dvd_natCard hxA
                                  have hQpcard : Nat.card Qp = 1 := by
                                    calc
                                      Nat.card Qp = Nat.card P :=
                                        Nat.card_congr (Sylow.equiv Qp P).toEquiv
                                      _ = 1 := by simpa using hPcard
                                  have hxorder_one : orderOf x = 1 :=
                                    Nat.eq_one_of_dvd_one (by
                                      simpa [hQpcard] using hxdvd)
                                  exact
                                    (hxne (orderOf_eq_one_iff.mp hxorder_one)).elim
                                · obtain ⟨g, hg⟩ := z.2.2
                                  have hzcard :
                                      Nat.card z.2.1 = Nat.card (Z z.1) := by
                                    rw [hg, Subgroup.card_map_of_injective
                                      (MulAut.conj g).injective]
                                  have huniv :
                                      ({i, j, k} : Finset (Fin 3)) =
                                        Finset.univ := by
                                    apply
                                      (Finset.card_eq_iff_eq_univ
                                        ({i, j, k} : Finset (Fin 3))).mp
                                    simp [hij, hik, hjk]
                                  have hz_cases :
                                      z.1 = i ∨ z.1 = j ∨ z.1 = k := by
                                    have hzmem :
                                        z.1 ∈ ({i, j, k} : Finset (Fin 3)) := by
                                      rw [huniv]
                                      simp
                                    simpa [Finset.mem_insert,
                                      Finset.mem_singleton] using hzmem
                                  rcases hz_cases with hza | hza | hza
                                  · let W0 :
                                        {W : Subgroup H // ∃ g : H,
                                          W = (![Z i, Z j] 0).map
                                            (MulAut.conj g).toMonoidHom} :=
                                      ⟨z.2.1, by simpa [hza] using z.2.2⟩
                                    refine ⟨Sum.inr ⟨0, W0⟩, hxA, ?_⟩
                                    intro B hxB
                                    rcases B with R | ⟨b, V⟩
                                    · have hxorder : orderOf x = 2 :=
                                        hsylow2_order_two R hxB hxne
                                      have hxdvd :
                                          orderOf x ∣ Nat.card z.2.1 :=
                                        z.2.1.orderOf_dvd_natCard hxA
                                      rw [hxorder, hzcard, hza, hzi_five]
                                        at hxdvd
                                      norm_num at hxdvd
                                    · fin_cases b
                                      · let V0 :
                                            {W : Subgroup H // ∃ g : H,
                                              W = (Z i).map
                                                (MulAut.conj g).toMonoidHom} :=
                                          ⟨V.1, by simpa [Zodd] using V.2⟩
                                        have heq :=
                                          hAunique (Sum.inr ⟨i, V0⟩) hxB
                                        cases heq
                                        rfl
                                      · let V1 :
                                            {W : Subgroup H // ∃ g : H,
                                              W = (Z j).map
                                                (MulAut.conj g).toMonoidHom} :=
                                          ⟨V.1, by simpa [Zodd] using V.2⟩
                                        have heq :=
                                          hAunique (Sum.inr ⟨j, V1⟩) hxB
                                        have hjza : j = z.1 :=
                                          congrArg (fun C => match C with
                                            | Sum.inl _ => i
                                            | Sum.inr w => w.1) heq
                                        have hij' : j = i := hjza.trans hza
                                        exact (hij hij'.symm).elim
                                  · let W1 :
                                        {W : Subgroup H // ∃ g : H,
                                          W = (![Z i, Z j] 1).map
                                            (MulAut.conj g).toMonoidHom} :=
                                      ⟨z.2.1, by simpa [hza] using z.2.2⟩
                                    refine ⟨Sum.inr ⟨1, W1⟩, hxA, ?_⟩
                                    intro B hxB
                                    rcases B with R | ⟨b, V⟩
                                    · have hxorder : orderOf x = 2 :=
                                        hsylow2_order_two R hxB hxne
                                      have hxdvd :
                                          orderOf x ∣ Nat.card z.2.1 :=
                                        z.2.1.orderOf_dvd_natCard hxA
                                      rw [hxorder, hzcard, hza, hzj_three]
                                        at hxdvd
                                      norm_num at hxdvd
                                    · fin_cases b
                                      · let V0 :
                                            {W : Subgroup H // ∃ g : H,
                                              W = (Z i).map
                                                (MulAut.conj g).toMonoidHom} :=
                                          ⟨V.1, by simpa [Zodd] using V.2⟩
                                        have heq :=
                                          hAunique (Sum.inr ⟨i, V0⟩) hxB
                                        have hiza : i = z.1 :=
                                          congrArg (fun C => match C with
                                            | Sum.inl _ => j
                                            | Sum.inr w => w.1) heq
                                        have hji' : i = j := hiza.trans hza
                                        exact (hij hji').elim
                                      · let V1 :
                                            {W : Subgroup H // ∃ g : H,
                                              W = (Z j).map
                                                (MulAut.conj g).toMonoidHom} :=
                                          ⟨V.1, by simpa [Zodd] using V.2⟩
                                        have heq :=
                                          hAunique (Sum.inr ⟨j, V1⟩) hxB
                                        cases heq
                                        rfl
                                  · have hxdvd :
                                        orderOf x ∣ Nat.card z.2.1 :=
                                      z.2.1.orderOf_dvd_natCard hxA
                                    have hxorder : orderOf x = 2 := by
                                      have hpos : 0 < orderOf x := orderOf_pos x
                                      have hne_one : orderOf x ≠ 1 :=
                                        fun h => hxne (orderOf_eq_one_iff.mp h)
                                      have hdvd2 : orderOf x ∣ 2 := by
                                        simpa [hzcard, hza, hzk_two] using hxdvd
                                      have hle : orderOf x ≤ 2 :=
                                        Nat.le_of_dvd (by norm_num) hdvd2
                                      omega
                                    obtain ⟨R, hxR, hRunique⟩ :=
                                      hinvolution_unique_sylow x hxorder
                                    refine ⟨Sum.inl R, hxR, ?_⟩
                                    intro B hxB
                                    rcases B with S | ⟨b, V⟩
                                    · exact congrArg Sum.inl (hRunique S hxB)
                                    · fin_cases b
                                      · have hxdvdV :
                                            orderOf x ∣ Nat.card V.1 :=
                                          V.1.orderOf_dvd_natCard hxB
                                        obtain ⟨a, ha⟩ := V.2
                                        have hVcard :
                                            Nat.card V.1 = Nat.card (Z i) := by
                                          rw [ha, Subgroup.card_map_of_injective
                                            (MulAut.conj a).injective]
                                          simp [Zodd]
                                        rw [hxorder, hVcard, hzi_five] at hxdvdV
                                        norm_num at hxdvdV
                                      · have hxdvdV :
                                            orderOf x ∣ Nat.card V.1 :=
                                          V.1.orderOf_dvd_natCard hxB
                                        obtain ⟨a, ha⟩ := V.2
                                        have hVcard :
                                            Nat.card V.1 = Nat.card (Z j) := by
                                          rw [ha, Subgroup.card_map_of_injective
                                            (MulAut.conj a).injective]
                                          simp [Zodd]
                                        rw [hxorder, hVcard, hzj_three] at hxdvdV
                                        norm_num at hxdvdV
                              have hP2card : Nat.card P2 = 2 ^ 2 := by
                                change Nat.card (NZ k) = 2 ^ 2
                                norm_num [hNZkcard4]
                              have hcount2 :
                                  Nat.card H =
                                    1 + (2 ^ 2 - 1) *
                                        (Subgroup.normalizer (P2 : Set H)).index +
                                      ∑ a, (Nat.card (Zodd a) - 1) *
                                        (Subgroup.normalizer
                                          (Zodd a : Set H)).index := by
                                apply
                                  huppert_II_8_22_partition_count_of_unique_family
                                    P2 hP2card Zodd
                                intro x hx
                                convert hunique2 x hx using 1
                                funext A
                                rcases A with R | z <;> rfl
                              have hP2normalizer_index :
                                  (Subgroup.normalizer (P2 : Set H)).index =
                                    Nat.card (Sylow 2 H) :=
                                P2.card_eq_index_normalizer.symm
                              rw [hP2normalizer_index] at hcount2
                              simp [Zodd, Fin.sum_univ_two, NZ, hHcard60,
                                hzi_five, hzj_three, hindices_five.1,
                                hindices_five.2.1] at hcount2
                              constructor
                              · omega
                              · exact hinvolution_unique_sylow
                            have hSylow2card5 : Nat.card (Sylow 2 H) = 5 :=
                              hSylow2_data.1
                            have hinvolution_unique_sylow :
                                ∀ x : H, orderOf x = 2 →
                                  ∃! R : Sylow 2 H,
                                    x ∈ (R : Subgroup H) :=
                              hSylow2_data.2
                            let Ω2 := Sylow 2 H
                            let := Fintype.ofFinite Ω2
                            have hΩ2card : Fintype.card Ω2 = 5 := by
                              simpa [Ω2, Nat.card_eq_fintype_card] using hSylow2card5
                            let act2 := MulAction.toPermHom H Ω2
                            have hact2_inj : Function.Injective act2 := by
                              rw [← MonoidHom.ker_eq_bot_iff]
                              have hker_le_normalizer (R : Sylow 2 H) :
                                  act2.ker ≤
                                    Subgroup.normalizer (R : Set H) := by
                                intro x hx
                                have hxperm : act2 x = 1 := hx
                                have hxfix : x • R = R := by
                                  have h := DFunLike.congr_fun hxperm R
                                  simpa [act2] using h
                                exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
                              have hnormalizer_card_twelve :
                                  Nat.card
                                      (Subgroup.normalizer (P2 : Set H)) = 12 := by
                                have hP2index :
                                    (Subgroup.normalizer (P2 : Set H)).index = 5 := by
                                  calc
                                    (Subgroup.normalizer (P2 : Set H)).index =
                                        Nat.card (Sylow 2 H) :=
                                      P2.card_eq_index_normalizer.symm
                                    _ = 5 := hSylow2card5
                                have hmul :=
                                  (Subgroup.normalizer
                                    (P2 : Set H)).card_mul_index
                                rw [hP2index, hHcard60] at hmul
                                omega
                              have hker_card_dvd_twelve :
                                  Nat.card act2.ker ∣ 12 := by
                                simpa [hnormalizer_card_twelve] using
                                  Subgroup.card_dvd_of_le
                                    (hker_le_normalizer P2)
                              have hker_has_no_involution :
                                  ∀ x : act2.ker, orderOf x ≠ 2 := by
                                intro x hxorder
                                have hxHorder : orderOf (x : H) = 2 :=
                                  (Subgroup.orderOf_coe x).trans hxorder
                                obtain ⟨R, hxR, hRunique⟩ :=
                                  hinvolution_unique_sylow (x : H) hxHorder
                                obtain ⟨S, hSR⟩ :=
                                  Fintype.exists_ne_of_one_lt_card
                                    (by omega : 1 < Fintype.card Ω2) R
                                let X : Subgroup H :=
                                  Subgroup.zpowers (x : H)
                                have hXcard : Nat.card X = 2 := by
                                  simpa [X] using
                                    (Nat.card_zpowers (x : H)).trans hxHorder
                                have hXisP : IsPGroup 2 X :=
                                  IsPGroup.of_card (n := 1) (by
                                    simpa using hXcard)
                                have hXnormalizesS :
                                    X ≤ Subgroup.normalizer (S : Set H) := by
                                  exact Subgroup.zpowers_le.2
                                    (hker_le_normalizer S x.2)
                                have hsupP :
                                    IsPGroup 2
                                      (X ⊔ (S : Subgroup H) : Subgroup H) :=
                                  hXisP.to_sup_of_normal_right'
                                    S.isPGroup' hXnormalizesS
                                have hsup_eq :
                                    X ⊔ (S : Subgroup H) = S :=
                                  S.is_maximal' hsupP le_sup_right
                                have hxS : (x : H) ∈ (S : Subgroup H) := by
                                  have hxjoin :
                                      (x : H) ∈ X ⊔ (S : Subgroup H) :=
                                    (show X ≤ X ⊔ (S : Subgroup H) from
                                      le_sup_left) (by
                                        exact Subgroup.mem_zpowers (x : H))
                                  rw [hsup_eq] at hxjoin
                                  exact hxjoin
                                exact hSR (hRunique S hxS)
                              have htwo_not_dvd_ker :
                                  ¬ 2 ∣ Nat.card act2.ker := by
                                intro htwo
                                obtain ⟨x, hxorder⟩ :=
                                  exists_prime_orderOf_dvd_card' 2 htwo
                                exact hker_has_no_involution x hxorder
                              have hker_card_cases :
                                  Nat.card act2.ker = 1 ∨
                                    Nat.card act2.ker = 3 := by
                                have hpos : 0 < Nat.card act2.ker := Nat.card_pos
                                have hle : Nat.card act2.ker ≤ 12 :=
                                  Nat.le_of_dvd (by norm_num)
                                    hker_card_dvd_twelve
                                interval_cases h : Nat.card act2.ker
                                · omega
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · omega
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · norm_num [h] at hker_card_dvd_twelve
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · norm_num [h] at hker_card_dvd_twelve
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · norm_num [h] at hker_card_dvd_twelve
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                                · norm_num [h] at hker_card_dvd_twelve
                                · exfalso
                                  apply htwo_not_dvd_ker
                                  norm_num [h]
                              rcases hker_card_cases with hker_one | hker_three
                              · exact Subgroup.card_eq_one.mp hker_one
                              · have hSylow3card10 :
                                    Nat.card (Sylow 3 H) = 10 := by
                                  let : Fact (Nat.Prime 3) := ⟨by decide⟩
                                  have hZjIndex20 : (Z j).index = 20 := by
                                    have hmul := (Z j).card_mul_index
                                    rw [hzj_three, hHcard60] at hmul
                                    omega
                                  let hZjP : IsPGroup 3 (Z j) :=
                                    IsPGroup.of_card (n := 1) (by
                                      simpa using hzj_three)
                                  let Q3 : Sylow 3 H := hZjP.toSylow (by
                                    rw [hZjIndex20]
                                    norm_num)
                                  calc
                                    Nat.card (Sylow 3 H) =
                                        (Subgroup.normalizer
                                          (Q3 : Set H)).index :=
                                      Q3.card_eq_index_normalizer
                                    _ = (NZ j).index := by rfl
                                    _ = 10 := hindices_five.2.1
                                have hker_is_sylow_three :
                                    ∃ R : Sylow 3 H,
                                      (R : Subgroup H) = act2.ker := by
                                  let : Fact (Nat.Prime 3) := ⟨by decide⟩
                                  have hkerP : IsPGroup 3 act2.ker :=
                                    IsPGroup.of_card (n := 1) (by
                                      simpa using hker_three)
                                  have hkerIndex20 : act2.ker.index = 20 := by
                                    have hmul := act2.ker.card_mul_index
                                    rw [hker_three, hHcard60] at hmul
                                    omega
                                  let R3 : Sylow 3 H := hkerP.toSylow (by
                                    rw [hkerIndex20]
                                    norm_num)
                                  exact ⟨R3, rfl⟩
                                obtain ⟨R3, hR3⟩ := hker_is_sylow_three
                                have hR3normal : (R3 : Subgroup H).Normal := by
                                  rw [hR3]
                                  exact inferInstance
                                let : Unique (Sylow 3 H) :=
                                  Sylow.unique_of_normal R3 hR3normal
                                have hSylow3card1 :
                                    Nat.card (Sylow 3 H) = 1 := Nat.card_unique
                                omega
                            let eΩ2 : Ω2 ≃ Fin 5 :=
                              Fintype.equivFinOfCardEq hΩ2card
                            let actFin2 : H →* Equiv.Perm (Fin 5) :=
                              (Equiv.permCongrHom eΩ2).toMonoidHom.comp act2
                            have hactFin2_inj : Function.Injective actFin2 := by
                              intro x y hxy
                              apply hact2_inj
                              apply (Equiv.permCongrHom eΩ2).injective
                              simpa [actFin2] using hxy
                            let K2 : Subgroup (Equiv.Perm (Fin 5)) := actFin2.range
                            have hrange2_inj :
                                Function.Injective actFin2.rangeRestrict := by
                              intro x y hxy
                              exact hactFin2_inj (congrArg Subtype.val hxy)
                            let eRange2 : H ≃* K2 :=
                              MulEquiv.ofBijective actFin2.rangeRestrict
                                ⟨hrange2_inj,
                                  MonoidHom.rangeRestrict_surjective actFin2⟩
                            have hK2card : Nat.card K2 = 60 := by
                              calc
                                Nat.card K2 = Nat.card H :=
                                  (Nat.card_congr eRange2.toEquiv).symm
                                _ = 60 := hHcard60
                            have hperm5card :
                                Nat.card (Equiv.Perm (Fin 5)) = 120 := by
                              norm_num [Fintype.card_perm, Nat.factorial]
                            have hK2index : K2.index = 2 := by
                              have hmul := K2.index_mul_card
                              rw [hK2card, hperm5card] at hmul
                              omega
                            have hK2alt : K2 = alternatingGroup (Fin 5) :=
                              Equiv.Perm.eq_alternatingGroup_of_index_eq_two hK2index
                            exact ⟨eRange2.trans (MulEquiv.subgroupCongr hK2alt)⟩
                          exact hA5_via_sylow_two
                      exact Or.inr hexceptional
                  exact hclassification
                by_cases h01 : Nat.card (Z 0) ≤ Nat.card (Z 1)
                · by_cases h12 : Nat.card (Z 1) ≤ Nat.card (Z 2)
                  · rcases hordered 2 1 0 (by decide) (by decide) (by decide)
                        h12 h01 with hdih | hS4 | hA5
                    · exact Or.inr (Or.inl hdih)
                    · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                  · by_cases h02 : Nat.card (Z 0) ≤ Nat.card (Z 2)
                    · rcases hordered 1 2 0 (by decide) (by decide) (by decide)
                          (by omega) h02 with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                    · rcases hordered 1 0 2 (by decide) (by decide) (by decide)
                          h01 (by omega) with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                · by_cases h02 : Nat.card (Z 0) ≤ Nat.card (Z 2)
                  · rcases hordered 2 0 1 (by decide) (by decide) (by decide)
                        h02 (by omega) with hdih | hS4 | hA5
                    · exact Or.inr (Or.inl hdih)
                    · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                  · by_cases h12 : Nat.card (Z 1) ≤ Nat.card (Z 2)
                    · rcases hordered 0 2 1 (by decide) (by decide) (by decide)
                          (by omega) h12 with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
                    · rcases hordered 0 1 2 (by decide) (by decide) (by decide)
                          (by omega) (by omega) with hdih | hS4 | hA5
                      · exact Or.inr (Or.inl hdih)
                      · exact Or.inr (Or.inr (Or.inr (Or.inl hS4)))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr hA5)))
              exact h824_three_shape
          exact h824_two_or_three_shape
      exact h824_positive_shape
  have h824_A4_restriction
      (hA4 : Nonempty (H ≃* alternatingGroup (Fin 4))) :
      p ≠ 2 ∨ Even f := by
    left
    intro hp2
    subst p
    apply hp_not_dvd_card_H
    have hc := Nat.card_congr hA4.some.toEquiv
    have hA4card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc, hA4card]
    norm_num
  have h824_S4_restriction
      (hS4 : Nonempty (H ≃* Equiv.Perm (Fin 4))) :
      16 ∣ p ^ (2 * f) - 1 := by
    have hS4_p_ne_two : p ≠ 2 := by
      intro hp2
      subst p
      apply hp_not_dvd_card_H
      have hHcard : Nat.card H = 24 := by
        calc
          Nat.card H = Nat.card (Equiv.Perm (Fin 4)) :=
            Nat.card_congr hS4.some.toEquiv
          _ = 24 := by norm_num [Fintype.card_perm, Nat.factorial]
      rw [hHcard]
      norm_num
    have hS4_cycle_four : ∃ x : H, orderOf x = 4 := by
      refine ⟨hS4.some.symm (Fin.cycleRange (3 : Fin 4)), ?_⟩
      rw [hS4.some.symm.orderOf_eq]
      rw [← Equiv.Perm.lcm_cycleType,
        Fin.cycleType_cycleRange (by decide : (3 : Fin 4) ≠ 0)]
      norm_num
    have hS4_cycle_four_family :
        ∃ a : Fin r, 4 ∣ Nat.card (Z a) := by
      obtain ⟨x, hxorder⟩ := hS4_cycle_four
      have hxne : x ≠ 1 := by
        intro hx
        rw [hx, orderOf_one] at hxorder
        norm_num at hxorder
      obtain ⟨A, hxA, _hAunique⟩ :=
        huppert_II_8_22_unique_family hFcard H Z
          hcyclic hnontrivial hcoprime hmaximal
          hrepresentative hdistinct x hxne
      rcases A with Qp | z
      · have hxdvd : orderOf x ∣ Nat.card Qp :=
          (Qp : Subgroup H).orderOf_dvd_natCard hxA
        have hQpcard : Nat.card Qp = 1 := by
          calc
            Nat.card Qp = Nat.card P :=
              Nat.card_congr (Sylow.equiv Qp P).toEquiv
            _ = 1 := by simpa using hPcard
        rw [hxorder, hQpcard] at hxdvd
        norm_num at hxdvd
      · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
          z.2.1.orderOf_dvd_natCard hxA
        obtain ⟨g, hg⟩ := z.2.2
        have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
        refine ⟨z.1, ?_⟩
        simpa [hxorder, hzcard] using hxdvd
    have hS4_four_torus :
        4 ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∨
          4 ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
      obtain ⟨a, ha⟩ := hS4_cycle_four_family
      rcases hdivides a with hsplit | hnonsplit
      · exact Or.inl (dvd_trans ha hsplit)
      · exact Or.inr (dvd_trans ha hnonsplit)
    have hS4_q_odd : Odd (Nat.card F) := by
      rw [hFcard]
      exact ((Fact.out : p.Prime).odd_of_ne_two hS4_p_ne_two).pow
    have hS4_two_dvd_sub : 2 ∣ Nat.card F - 1 := by
      rcases hS4_q_odd with ⟨k, hk⟩
      use k
      omega
    have hS4_two_dvd_add : 2 ∣ Nat.card F + 1 := by
      exact hS4_q_odd.add_one.two_dvd
    have hS4_gcd_two : Nat.gcd (Nat.card F - 1) 2 = 2 := by
      exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        (Nat.dvd_gcd hS4_two_dvd_sub (dvd_refl 2))
    have hS4_eight_torus :
        8 ∣ Nat.card F - 1 ∨ 8 ∣ Nat.card F + 1 := by
      rw [hS4_gcd_two] at hS4_four_torus
      rcases hS4_four_torus with hminus | hplus
      · left
        obtain ⟨a, ha⟩ := hminus
        use a
        calc
          Nat.card F - 1 = (Nat.card F - 1) / 2 * 2 :=
            (Nat.div_mul_cancel hS4_two_dvd_sub).symm
          _ = (4 * a) * 2 := by rw [ha]
          _ = 8 * a := by ring
      · right
        obtain ⟨a, ha⟩ := hplus
        use a
        calc
          Nat.card F + 1 = (Nat.card F + 1) / 2 * 2 :=
            (Nat.div_mul_cancel hS4_two_dvd_add).symm
          _ = (4 * a) * 2 := by rw [ha]
          _ = 8 * a := by ring
    have hS4_sixteen_q_sq_sub_one :
        16 ∣ Nat.card F ^ 2 - 1 := by
      have hfactor :
          Nat.card F ^ 2 - 1 =
            (Nat.card F - 1) * (Nat.card F + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
      rw [hfactor]
      rcases hS4_eight_torus with hminus | hplus
      · have hmul := Nat.mul_dvd_mul hminus hS4_two_dvd_add
        norm_num at hmul
        exact hmul
      · have hmul := Nat.mul_dvd_mul hS4_two_dvd_sub hplus
        norm_num at hmul
        exact hmul
    rw [hFcard, ← pow_mul] at hS4_sixteen_q_sq_sub_one
    simpa [mul_comm] using hS4_sixteen_q_sq_sub_one
  have h824_A5_restriction
      (hA5 : Nonempty (H ≃* alternatingGroup (Fin 5))) :
      p = 5 ∨ 5 ∣ p ^ (2 * f) - 1 := by
    have hA5_cycle_five : ∃ x : H, orderOf x = 5 := by
      let y : alternatingGroup (Fin 5) :=
        ⟨Fin.cycleRange (4 : Fin 5), by
          rw [Equiv.Perm.mem_alternatingGroup, Fin.sign_cycleRange]
          decide⟩
      refine ⟨hA5.some.symm y, ?_⟩
      rw [hA5.some.symm.orderOf_eq, ← Subgroup.orderOf_coe y]
      change orderOf (Fin.cycleRange (4 : Fin 5)) = 5
      rw [← Equiv.Perm.lcm_cycleType,
        Fin.cycleType_cycleRange (by decide : (4 : Fin 5) ≠ 0)]
      norm_num
    have hA5_cycle_five_family :
        ∃ a : Fin r, 5 ∣ Nat.card (Z a) := by
      obtain ⟨x, hxorder⟩ := hA5_cycle_five
      have hxne : x ≠ 1 := by
        intro hx
        rw [hx, orderOf_one] at hxorder
        norm_num at hxorder
      obtain ⟨A, hxA, _hAunique⟩ :=
        huppert_II_8_22_unique_family hFcard H Z
          hcyclic hnontrivial hcoprime hmaximal
          hrepresentative hdistinct x hxne
      rcases A with Qp | z
      · have hxdvd : orderOf x ∣ Nat.card Qp :=
          (Qp : Subgroup H).orderOf_dvd_natCard hxA
        have hQpcard : Nat.card Qp = 1 := by
          calc
            Nat.card Qp = Nat.card P :=
              Nat.card_congr (Sylow.equiv Qp P).toEquiv
            _ = 1 := by simpa using hPcard
        rw [hxorder, hQpcard] at hxdvd
        norm_num at hxdvd
      · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
          z.2.1.orderOf_dvd_natCard hxA
        obtain ⟨g, hg⟩ := z.2.2
        have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
          rw [hg, Subgroup.card_map_of_injective
            (MulAut.conj g).injective]
        refine ⟨z.1, ?_⟩
        simpa [hxorder, hzcard] using hxdvd
    have hA5_five_torus_quotient :
        5 ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∨
          5 ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
      obtain ⟨a, ha⟩ := hA5_cycle_five_family
      rcases hdivides a with hsplit | hnonsplit
      · exact Or.inl (dvd_trans ha hsplit)
      · exact Or.inr (dvd_trans ha hnonsplit)
    have hA5_five_torus_factor :
        5 ∣ Nat.card F - 1 ∨ 5 ∣ Nat.card F + 1 := by
      have hq : 1 ≤ Nat.card F :=
        (Finite.one_lt_card (α := F)).le
      have hdvd_sub : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F - 1 :=
        Nat.gcd_dvd_left _ _
      have hdvd_two : Nat.gcd (Nat.card F - 1) 2 ∣ 2 :=
        Nat.gcd_dvd_right _ _
      have hdvd_add : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
        have h := Nat.dvd_add hdvd_sub hdvd_two
        convert h using 1
        all_goals omega
      rcases hA5_five_torus_quotient with hminus | hplus
      · exact Or.inl
          (dvd_trans hminus (Nat.div_dvd_of_dvd hdvd_sub))
      · exact Or.inr
          (dvd_trans hplus (Nat.div_dvd_of_dvd hdvd_add))
    have hA5_five_q_sq_sub_one :
        5 ∣ Nat.card F ^ 2 - 1 := by
      have hfactor :
          Nat.card F ^ 2 - 1 =
            (Nat.card F - 1) * (Nat.card F + 1) := by
        simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
      rw [hfactor]
      rcases hA5_five_torus_factor with hminus | hplus
      · exact dvd_mul_of_dvd_left hminus _
      · exact dvd_mul_of_dvd_right hplus _
    right
    rw [hFcard, ← pow_mul] at hA5_five_q_sq_sub_one
    simpa [mul_comm] using hA5_five_q_sq_sub_one
  rcases h824_shape with hcyc | hdih | hA4 | hS4 | hA5
  · exact Or.inl hcyc
  · exact Or.inr (Or.inl hdih)
  · exact Or.inr (Or.inr (Or.inl ⟨h824_A4_restriction hA4, hA4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h824_S4_restriction hS4, hS4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h824_A5_restriction hA5, hA5⟩)))

/-- Huppert II.4.7, in the degree-six, order-sixty case used by II.8.25:
a faithful primitive permutation group of degree six and order sixty is `A5`. -/
public theorem huppert_II_4_7_primitive_degree_six_order_sixty
    {G Ω : Type u} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω]
    (hprimitive : MulAction.IsPreprimitive G Ω)
    (hΩcard : Nat.card Ω = 6) (hGcard : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype Ω := Fintype.ofFinite Ω
  have : MulAction.IsPreprimitive G Ω := hprimitive
  have hΩfcard : Fintype.card Ω = 6 := by
    simpa [Nat.card_eq_fintype_card] using hΩcard
  let : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hΩfcard]; norm_num)
  have hnormal_transitive
      (N : Subgroup G) [N.Normal] (hN_ne_bot : N ≠ ⊥) :
      MulAction.IsPretransitive N Ω := by
    apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    intro hfixed
    apply hN_ne_bot
    apply le_antisymm
    · intro g hg
      have hg_one : g = 1 :=
        (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G Ω)) g fun x =>
          (show x ∈ MulAction.fixedPoints N Ω by simp [hfixed]) ⟨g, hg⟩
      simp [hg_one]
    · exact bot_le
  have hnormal_card_dvd_six
      (N : Subgroup G) [N.Normal] (hN_ne_bot : N ≠ ⊥) :
      6 ∣ Nat.card N := by
    let : MulAction.IsPretransitive N Ω := hnormal_transitive N hN_ne_bot
    let a : Ω := Classical.arbitrary Ω
    have hdiv := (MulAction.stabilizer N a).index_dvd_card
    rw [MulAction.index_stabilizer_of_transitive, hΩcard] at hdiv
    exact hdiv
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := default
  have hfac60_two : (Nat.factorization 60) 2 = 2 := by
    have hle : 2 ≤ (Nat.factorization 60) 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp
        (by norm_num)
    have hnle : ¬ 3 ≤ (Nat.factorization 60) 2 := by
      intro h
      have hdvd :=
        (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mpr h
      norm_num at hdvd
    omega
  have hPcard : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hGcard]
    rw [hfac60_two]
    norm_num
  have hPindex : P.index = 15 := by
    have hmul := P.card_mul_index
    rw [hPcard, hGcard] at hmul
    omega
  have hSylow2_dvd : Nat.card (Sylow 2 G) ∣ 15 := by
    simpa [hPindex] using P.card_dvd_index
  have hSylow2_not_even : ¬ 2 ∣ Nat.card (Sylow 2 G) :=
    not_dvd_card_sylow 2 G
  have hSylow2_cases :
      Nat.card (Sylow 2 G) = 1 ∨
        Nat.card (Sylow 2 G) = 3 ∨
        Nat.card (Sylow 2 G) = 5 ∨
        Nat.card (Sylow 2 G) = 15 := by
    have hpos : 0 < Nat.card (Sylow 2 G) := Nat.card_pos
    have hle : Nat.card (Sylow 2 G) ≤ 15 :=
      Nat.le_of_dvd (by norm_num) hSylow2_dvd
    interval_cases h : Nat.card (Sylow 2 G) <;> norm_num [h] at *
  have hSylow2card5 : Nat.card (Sylow 2 G) = 5 := by
    rcases hSylow2_cases with hcard1 | hcard3 | hcard5 | hcard15
    · have : Subsingleton (Sylow 2 G) :=
        (Nat.card_eq_one_iff_unique.mp hcard1).1
      let : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
      have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hPcard]
        norm_num
      have hdiv := hnormal_card_dvd_six (P : Subgroup G) hP_ne_bot
      rw [hPcard] at hdiv
      norm_num at hdiv
    · let act3 := MulAction.toPermHom G (Sylow 2 G)
      have hker_le_normalizer (Q : Sylow 2 G) :
          act3.ker ≤
            Subgroup.normalizer (Q : Set G) := by
        intro x hx
        have hxperm : act3 x = 1 := hx
        have hxfix : x • Q = Q := by
          have h := DFunLike.congr_fun hxperm Q
          simpa [act3] using h
        exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
      have hnormalizer_card_twenty :
          Nat.card (Subgroup.normalizer (P : Set G)) = 20 := by
        have hindex :
            (Subgroup.normalizer (P : Set G)).index = 3 := by
          calc
            (Subgroup.normalizer (P : Set G)).index =
                Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
            _ = 3 := hcard3
        have hmul :=
          (Subgroup.normalizer (P : Set G)).card_mul_index
        rw [hindex, hGcard] at hmul
        omega
      have hker_card_dvd_twenty : Nat.card act3.ker ∣ 20 := by
        have hcard := Subgroup.card_dvd_of_le (hker_le_normalizer P)
        rw [hnormalizer_card_twenty] at hcard
        exact hcard
      have hker_bot : act3.ker = ⊥ := by
        by_contra hker
        have hdiv6 := hnormal_card_dvd_six act3.ker hker
        have : 6 ∣ 20 := dvd_trans hdiv6 hker_card_dvd_twenty
        norm_num at this
      have hact3_inj : Function.Injective act3 := by
        rw [← MonoidHom.ker_eq_bot_iff]
        exact hker_bot
      let : Fintype (Sylow 2 G) := Fintype.ofFinite (Sylow 2 G)
      have hSylow2fcard : Fintype.card (Sylow 2 G) = 3 := by
        simpa [Nat.card_eq_fintype_card] using hcard3
      have hcard_le := Nat.card_le_card_of_injective act3 hact3_inj
      have hperm_card : Nat.card (Equiv.Perm (Sylow 2 G)) = 6 := by
        rw [Nat.card_eq_fintype_card]
        simp [Fintype.card_perm, hSylow2fcard, Nat.factorial]
      rw [hGcard, hperm_card] at hcard_le
      omega
    · exact hcard5
    · have hnormalizer_card_four :
          Nat.card (Subgroup.normalizer (P : Set G)) = 4 := by
        have hindex :
            (Subgroup.normalizer (P : Set G)).index = 15 := by
          calc
            (Subgroup.normalizer (P : Set G)).index =
                Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
            _ = 15 := hcard15
        have hmul :=
          (Subgroup.normalizer (P : Set G)).card_mul_index
        rw [hindex, hGcard] at hmul
        omega
      have hnormalizer_eq :
          Subgroup.normalizer (P : Set G) =
            (P : Subgroup G) := by
        symm
        apply Subgroup.eq_of_le_of_card_ge
          (show (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G) from
            Subgroup.le_normalizer)
        rw [hnormalizer_card_four, hPcard]
      have hnormalizer_le_centralizer :
          Subgroup.normalizer (P : Set G) ≤
            Subgroup.centralizer (P : Set G) := by
        rw [hnormalizer_eq]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        let xP : P := ⟨x, hx⟩
        let yP : P := ⟨y, hy⟩
        let : IsMulCommutative P :=
          IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by
            calc
              Nat.card P = 4 := by simpa only [P.coe_coe] using hPcard
              _ = 2 ^ 2 := by norm_num)
        exact congrArg Subtype.val
          ((@IsMulCommutative.is_comm P _ inferInstance).comm yP xP)
      let K : Subgroup G :=
        (MonoidHom.transferSylow P hnormalizer_le_centralizer).ker
      let : K.Normal := inferInstance
      have hcomp : K.IsComplement' P := by
        exact MonoidHom.ker_transferSylow_isComplement'
          P hnormalizer_le_centralizer
      have hKcard : Nat.card K = 15 := by
        have hmul := hcomp.card_mul_card
        rw [hPcard, hGcard] at hmul
        omega
      have hK_ne_bot : K ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hKcard]
        norm_num
      have hdiv := hnormal_card_dvd_six K hK_ne_bot
      rw [hKcard] at hdiv
      norm_num at hdiv
  let act2 := MulAction.toPermHom G (Sylow 2 G)
  have hker_le_normalizer (Q : Sylow 2 G) :
      act2.ker ≤ Subgroup.normalizer (Q : Set G) := by
    intro x hx
    have hxperm : act2 x = 1 := hx
    have hxfix : x • Q = Q := by
      have h := DFunLike.congr_fun hxperm Q
      simpa [act2] using h
    exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
  have hnormalizer_card_twelve :
      Nat.card (Subgroup.normalizer (P : Set G)) = 12 := by
    have hindex :
        (Subgroup.normalizer (P : Set G)).index = 5 := by
      calc
        (Subgroup.normalizer (P : Set G)).index =
            Nat.card (Sylow 2 G) := P.card_eq_index_normalizer.symm
        _ = 5 := hSylow2card5
    have hmul :=
      (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hindex, hGcard] at hmul
    omega
  have hker_card_dvd_twelve : Nat.card act2.ker ∣ 12 := by
    have hcard := Subgroup.card_dvd_of_le (hker_le_normalizer P)
    rw [hnormalizer_card_twelve] at hcard
    exact hcard
  have hker_bot : act2.ker = ⊥ := by
    by_contra hker_ne_bot
    have hdiv6 := hnormal_card_dvd_six act2.ker hker_ne_bot
    have hker_cases : Nat.card act2.ker = 6 ∨ Nat.card act2.ker = 12 := by
      have hpos : 0 < Nat.card act2.ker := Nat.card_pos
      have hle : Nat.card act2.ker ≤ 12 :=
        Nat.le_of_dvd (by norm_num) hker_card_dvd_twelve
      interval_cases h : Nat.card act2.ker <;> norm_num [h] at *
    rcases hker_cases with hker6 | hker12
    · let K : Subgroup G := act2.ker
      let : K.Normal := inferInstance
      let : Fact (Nat.Prime 3) := ⟨by decide⟩
      let Q : Sylow 3 K := default
      have hfac6_three : (Nat.factorization 6) 3 = 1 := by
        rw [show 6 = 3 * 2 by norm_num,
          Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 2),
          Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
      have hQcard : Nat.card Q = 3 := by
        rw [Q.card_eq_multiplicity, show Nat.card K = 6 from hker6]
        rw [hfac6_three]
        norm_num
      have hQindex : Q.index = 2 := by
        have hmul := Q.card_mul_index
        rw [hQcard, show Nat.card K = 6 from hker6] at hmul
        omega
      have hSylow3_dvd : Nat.card (Sylow 3 K) ∣ 2 := by
        simpa [hQindex] using Q.card_dvd_index
      have hSylow3_mod := card_sylow_modEq_one 3 K
      have hSylow3card1 : Nat.card (Sylow 3 K) = 1 := by
        have hpos : 0 < Nat.card (Sylow 3 K) := Nat.card_pos
        have hle : Nat.card (Sylow 3 K) ≤ 2 :=
          Nat.le_of_dvd (by norm_num) hSylow3_dvd
        interval_cases h : Nat.card (Sylow 3 K)
        · rfl
        · have hfalse : ¬(2 : ℕ) ≡ 1 [MOD 3] := by decide
          exact (hfalse (h ▸ hSylow3_mod)).elim
      have : Subsingleton (Sylow 3 K) :=
        (Nat.card_eq_one_iff_unique.mp hSylow3card1).1
      let : (Q : Subgroup K).Characteristic :=
        Sylow.characteristic_of_subsingleton Q
      let QG : Subgroup G := (Q : Subgroup K).map K.subtype
      let : QG.Normal := inferInstance
      have hQGcard : Nat.card QG = 3 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hQcard]
      have hQG_ne_bot : QG ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hQGcard]
        norm_num
      have hdiv := hnormal_card_dvd_six QG hQG_ne_bot
      rw [hQGcard] at hdiv
      norm_num at hdiv
    · let K : Subgroup G := act2.ker
      let : K.Normal := inferInstance
      let Q : Sylow 2 K := default
      have hfac12_two : (Nat.factorization 12) 2 = 2 := by
        have hle : 2 ≤ (Nat.factorization 12) 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mp
            (by norm_num)
        have hnle : ¬ 3 ≤ (Nat.factorization 12) 2 := by
          intro h
          have hdvd :=
            (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num)).mpr h
          norm_num at hdvd
        omega
      have hQcard : Nat.card Q = 4 := by
        rw [Q.card_eq_multiplicity, show Nat.card K = 12 from hker12]
        rw [hfac12_two]
        norm_num
      obtain ⟨R, hQR⟩ := Q.exists_comap_subtype_eq
      have hK_le_normalizer : K ≤ Subgroup.normalizer (R : Set G) :=
        hker_le_normalizer R
      have hQnormal : (Q : Subgroup K).Normal := by
        rw [← hQR]
        change (R.subgroupOf K).Normal
        exact Subgroup.normal_subgroupOf_of_le_normalizer hK_le_normalizer
      let : (Q : Subgroup K).Characteristic :=
        Sylow.characteristic_of_normal Q hQnormal
      let QG : Subgroup G := (Q : Subgroup K).map K.subtype
      let : QG.Normal := inferInstance
      have hQGcard : Nat.card QG = 4 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hQcard]
      have hQG_ne_bot : QG ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hQGcard]
        norm_num
      have hdiv := hnormal_card_dvd_six QG hQG_ne_bot
      rw [hQGcard] at hdiv
      norm_num at hdiv
  have hact2_inj : Function.Injective act2 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hker_bot
  let : Fintype (Sylow 2 G) := Fintype.ofFinite (Sylow 2 G)
  have hSylow2fcard : Fintype.card (Sylow 2 G) = 5 := by
    simpa [Nat.card_eq_fintype_card] using hSylow2card5
  let eΩ2 : Sylow 2 G ≃ Fin 5 := Fintype.equivFinOfCardEq hSylow2fcard
  let actFin2 : G →* Equiv.Perm (Fin 5) :=
    (Equiv.permCongrHom eΩ2).toMonoidHom.comp act2
  have hactFin2_inj : Function.Injective actFin2 := by
    intro x y hxy
    apply hact2_inj
    apply (Equiv.permCongrHom eΩ2).injective
    simpa [actFin2] using hxy
  let A : Subgroup (Equiv.Perm (Fin 5)) := actFin2.range
  let eRange : G ≃* A :=
    MulEquiv.ofBijective actFin2.rangeRestrict
      ⟨fun x y hxy => hactFin2_inj (congrArg Subtype.val hxy),
        MonoidHom.rangeRestrict_surjective actFin2⟩
  have hAcard : Nat.card A = 60 := by
    rw [← Nat.card_congr eRange.toEquiv, hGcard]
  have hperm5card : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Fintype.card_perm, Nat.factorial]
  have hAindex : A.index = 2 := by
    have hmul := A.index_mul_card
    rw [hAcard, hperm5card] at hmul
    omega
  have hAalt : A = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hAindex
  exact ⟨eRange.trans (MulEquiv.subgroupCongr hAalt)⟩

/-- Huppert II.8.25: a faithful transitive permutation group of degree six
and order sixty is `A5`. -/
public theorem huppert_II_8_25_transitive_degree_six_order_sixty
    {G Ω : Type u} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [FaithfulSMul G Ω]
    (htransitive : MulAction.IsPretransitive G Ω)
    (hΩcard : Nat.card Ω = 6) (hGcard : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2 := by
    classical
    let := Fintype.ofFinite Ω
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hΩfcard : Fintype.card Ω = 6 := by
      simpa [Nat.card_eq_fintype_card] using hΩcard
    have hfive : 5 ∣ Nat.card G := by
      rw [hGcard]
      norm_num
    obtain ⟨g, hgorder⟩ := exists_prime_orderOf_dvd_card' 5 hfive
    let σ : Equiv.Perm Ω := MulAction.toPerm g
    have hσorder : orderOf σ = 5 := by
      calc
        orderOf σ = orderOf g :=
          orderOf_injective (MulAction.toPermHom G Ω)
            (MulAction.toPerm_injective : Function.Injective
              (MulAction.toPerm : G → Equiv.Perm Ω)) g
        _ = 5 := hgorder
    have hσcycle : σ.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order'
        (by simpa [hσorder] using (Fact.out : Nat.Prime 5))
        (by rw [hΩfcard, hσorder]; norm_num)
    have hfixed_card : Nat.card (Function.fixedPoints σ) = 1 := by
      rw [Nat.card_eq_fintype_card, σ.card_fixedPoints, hσcycle.cycleType,
        Multiset.sum_singleton, ← hσcycle.orderOf, hσorder, hΩfcard]
    have hfixed_nonempty : Nonempty (Function.fixedPoints σ) :=
      Finite.card_pos_iff.mp (by rw [hfixed_card]; norm_num)
    obtain ⟨x, hx⟩ := hfixed_nonempty
    have hσx : σ x = x := hx
    have hfixed_unique {y : Ω} (hy : σ y = y) : y = x := by
      have hsub : Subsingleton (Function.fixedPoints σ) :=
        (Nat.card_eq_one_iff_unique.mp hfixed_card).1
      exact congrArg Subtype.val
        (hsub.elim (⟨y, hy⟩ : Function.fixedPoints σ) ⟨x, hx⟩)
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨u, hu⟩ := htransitive.exists_smul_eq a x
    obtain ⟨v, hv⟩ := htransitive.exists_smul_eq x c
    have hub_ne : u • b ≠ x := by
      intro hub
      exact hab (smul_left_cancel u (hu.trans hub.symm))
    have hvd_ne : v⁻¹ • d ≠ x := by
      intro hvd
      apply hcd
      calc
        c = v • x := hv.symm
        _ = v • (v⁻¹ • d) := by rw [hvd]
        _ = d := smul_inv_smul v d
    have hσub : σ (u • b) ≠ u • b := by
      intro hfix
      exact hub_ne (hfixed_unique hfix)
    have hσvd : σ (v⁻¹ • d) ≠ v⁻¹ • d := by
      intro hfix
      exact hvd_ne (hfixed_unique hfix)
    obtain ⟨n, hn⟩ := hσcycle.exists_pow_eq hσub hσvd
    have hperm_pow : MulAction.toPerm (g ^ n) = σ ^ n := by
      change (MulAction.toPermHom G Ω) (g ^ n) = σ ^ n
      rw [map_pow]
      rfl
    have hgpow_b : (g ^ n) • (u • b) = v⁻¹ • d := by
      change (MulAction.toPerm (g ^ n)) (u • b) = v⁻¹ • d
      rw [hperm_pow]
      exact hn
    have hσpow_x (k : ℕ) : (σ ^ k) x = x := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, Equiv.Perm.mul_apply, hσx, ih]
    have hgpow_x : (g ^ n) • x = x := by
      change (MulAction.toPerm (g ^ n)) x = x
      rw [hperm_pow]
      exact hσpow_x n
    refine ⟨v * g ^ n * u, ?_, ?_⟩
    · simp only [mul_smul]
      rw [hu, hgpow_x, hv]
    · simp only [mul_smul]
      rw [hgpow_b, smul_inv_smul]
  have hprimitive : MulAction.IsPreprimitive G Ω :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo_transitive
  exact huppert_II_4_7_primitive_degree_six_order_sixty
    hprimitive hΩcard hGcard

/-- The II.8.2(a) consequence used in II.8.26: a Sylow subgroup of a
subgroup of `PSL(2,p^f)` is elementary abelian. -/
private theorem h826_sylow_elementary
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) :
    IsElementaryAbelian p P := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p :=
    charP_of_card_eq_prime_pow (by simpa using hFcard)
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  have hPmemQ (x : P) :
      (((x : P) : H) : PSL2MatrixGroup F) ∈ (Q : Subgroup _) := by
    have hx :
        (x : H) ∈ (Q : Subgroup (PSL2MatrixGroup F)).comap H.subtype := by
      rw [hQcomap]
      exact x.property
    exact hx
  have hFieldElementary : IsElementaryAbelian p (Multiplicative F) := by
    refine
      { toIsMulCommutative :=
          { is_comm := ⟨fun x y => mul_comm x y⟩ }
        exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    change Multiplicative.ofAdd x.toAdd ^ p = 1
    rw [← ofAdd_nsmul]
    simp
  obtain ⟨eQ⟩ := huppert_II_8_2_a_sylow_equiv_additive hFcard Q
  have hQElementary : IsElementaryAbelian p Q := by
    refine
      { toIsMulCommutative :=
          { is_comm := ⟨fun x y => ?_⟩ }
        exponent_dvd_p := ?_ }
    · apply eQ.symm.injective
      simpa using
        hFieldElementary.toIsMulCommutative.is_comm.comm
          (eQ.symm x) (eQ.symm y)
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply eQ.symm.injective
      have hx : (eQ.symm x) ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          hFieldElementary.exponent_dvd_p (eQ.symm x)
      simpa using hx
  refine
    { toIsMulCommutative :=
        { is_comm := ⟨fun x y => ?_⟩ }
      exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    let xQ : Q := ⟨((x : H) : PSL2MatrixGroup F), hPmemQ x⟩
    let yQ : Q := ⟨((y : H) : PSL2MatrixGroup F), hPmemQ y⟩
    have hxy := congrArg Subtype.val
      (hQElementary.toIsMulCommutative.is_comm.comm xQ yQ)
    simpa [xQ, yQ] using hxy
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    apply Subtype.ext
    let xQ : Q := ⟨((x : H) : PSL2MatrixGroup F), hPmemQ x⟩
    have hxpow : xQ ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        hQElementary.exponent_dvd_p xQ
    simpa [xQ] using congrArg Subtype.val hxpow

private theorem h826_card_actor_dvd_two_mul_card_of_stabilizer_card_le_two
    {A X : Type*} [Group A] [MulAction A X] [Finite A] [Finite X]
    (hstab : ∀ x : X, Nat.card (MulAction.stabilizer A x) ≤ 2) :
    Nat.card A ∣ 2 * Nat.card X := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype X := Fintype.ofFinite X
  let Ω := Quotient (MulAction.orbitRel A X)
  let : Fintype Ω := Fintype.ofFinite Ω
  have hterm (ω : Ω) :
      Nat.card A ∣
        2 * (Nat.card A /
          Nat.card (MulAction.stabilizer A ω.out)) := by
    have hspos : 0 < Nat.card (MulAction.stabilizer A ω.out) :=
      Nat.card_pos
    have hsle := hstab ω.out
    have hscases :
        Nat.card (MulAction.stabilizer A ω.out) = 1 ∨
          Nat.card (MulAction.stabilizer A ω.out) = 2 := by
      omega
    rcases hscases with hs | hs
    · rw [hs]
      simp
    · rw [hs]
      have hdS :
          Nat.card (MulAction.stabilizer A ω.out) ∣ Nat.card A :=
        Subgroup.card_subgroup_dvd_card (MulAction.stabilizer A ω.out)
      have hd : 2 ∣ Nat.card A := by
        rw [hs] at hdS
        exact hdS
      obtain ⟨k, hk⟩ := hd
      rw [hk]
      simp
  have hsum : Nat.card A ∣
      ∑ ω : Ω, 2 * (Nat.card A /
        Nat.card (MulAction.stabilizer A ω.out)) :=
    Finset.dvd_sum fun ω _hω => hterm ω
  have hformula : Nat.card X =
      ∑ ω : Ω, Nat.card A /
        Nat.card (MulAction.stabilizer A ω.out) := by
    simpa [Nat.card_eq_fintype_card] using
      MulAction.card_eq_sum_card_group_div_card_stabilizer A X
  rw [← Finset.mul_sum, ← hformula] at hsum
  exact hsum

private theorem h826_subgroup_card_le_two_of_disjoint_le_normalizer
    {G : Type*} [Group G] [Finite G] (Q S : Subgroup G)
    (hSle : S ≤ Subgroup.normalizer (Q : Set G))
    (hdisjoint : Disjoint S Q)
    (hNcard : Nat.card (Subgroup.normalizer (Q : Set G)) =
      2 * Nat.card Q) :
    Nat.card S ≤ 2 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let QN : Subgroup N := Q.subgroupOf N
  let SN : Subgroup N := S.subgroupOf N
  let : QN.Normal := by
    dsimp only [QN]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (by
      simp [N])
  let φ : SN →* N ⧸ QN :=
    (QuotientGroup.mk' QN).comp SN.subtype
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hker : φ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hQmem : (x : N) * (y : N)⁻¹ ∈ QN :=
      (QuotientGroup.eq_one_iff ((x : N) * (y : N)⁻¹)).mp hker
    have hQmemG : (x : G) * (y : G)⁻¹ ∈ Q := hQmem
    have hSmemG : (x : G) * (y : G)⁻¹ ∈ S :=
      S.mul_mem x.property (S.inv_mem y.property)
    have honeG : (x : G) * (y : G)⁻¹ = 1 :=
      Subgroup.disjoint_def.mp hdisjoint hSmemG hQmemG
    apply Subtype.ext
    apply Subtype.ext
    exact mul_inv_eq_one.mp honeG
  have hcardSN_dvd : Nat.card SN ∣ Nat.card (N ⧸ QN) :=
    Subgroup.card_dvd_of_injective φ hφinj
  have hQNcard : Nat.card QN = Nat.card Q := by
    dsimp only [QN]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have hSNcard : Nat.card SN = Nat.card S := by
    dsimp only [SN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv
  have hquotient_card : Nat.card (N ⧸ QN) = 2 := by
    have hfactor := Subgroup.card_eq_card_quotient_mul_card_subgroup QN
    change Nat.card N = Nat.card (N ⧸ QN) * Nat.card QN at hfactor
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q))
    calc
      Nat.card (N ⧸ QN) * Nat.card Q = Nat.card N := by
        rw [← hQNcard]
        exact hfactor.symm
      _ = 2 * Nat.card Q := by simpa [N] using hNcard
  rw [hSNcard, hquotient_card] at hcardSN_dvd
  exact Nat.le_of_dvd (by norm_num) hcardSN_dvd

private theorem h826_conjugacy_class_card_divisibility
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G)
    (hA_normalizer : Nat.card (Subgroup.normalizer (A : Set G)) =
      2 * Nat.card A)
    (hdisjoint : ∀ g : G,
      Disjoint B (A.map (MulAut.conj g).toMonoidHom)) :
    Nat.card B ∣ 2 * (Subgroup.normalizer (A : Set G)).index := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  have hsmul_normalizer (g : G) (Q : Subgroup G) :
      g • Q = Q ↔ g ∈ Subgroup.normalizer (Q : Set G) := by
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer Q),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h => iff_congr Iff.rfl
      ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
        fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
          MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  have hstabA : MulAction.stabilizer G A =
      Subgroup.normalizer (A : Set G) := by
    ext g
    change g • A = A ↔ g ∈ Subgroup.normalizer (A : Set G)
    exact hsmul_normalizer g A
  let q : MulAction.orbitRel.Quotient G (Subgroup G) := Quotient.mk'' A
  let C := MulAction.orbitRel.Quotient.orbit q
  let : MulAction B C := MulAction.compHom C B.subtype
  have hCcard : Nat.card C =
      (Subgroup.normalizer (A : Set G)).index := by
    change Nat.card ↥(MulAction.orbitRel.Quotient.orbit q) = _
    rw [show MulAction.orbitRel.Quotient.orbit q = MulAction.orbit G A by
      simp [q], Nat.card_coe_set_eq, ← MulAction.index_stabilizer G A, hstabA]
  have hstabilizer (x : C) :
      Nat.card (MulAction.stabilizer B x) ≤ 2 := by
    let St : Subgroup B := MulAction.stabilizer B x
    let S : Subgroup G := St.map B.subtype
    have hQconj : ∃ g : G,
        (x : Subgroup G) = A.map (MulAut.conj g).toMonoidHom := by
      have hx := x.property
      change (x : Subgroup G) ∈
        MulAction.orbitRel.Quotient.orbit q at hx
      rw [show MulAction.orbitRel.Quotient.orbit q = MulAction.orbit G A by
        simp [q]] at hx
      rcases hx with ⟨g, hg⟩
      exact ⟨g, hg.symm⟩
    have hSleN : S ≤
        Subgroup.normalizer ((x : Subgroup G) : Set G) := by
      rintro y ⟨z, hz, rfl⟩
      have hfix : z • x = x := MulAction.mem_stabilizer_iff.mp hz
      have hfix' : (z : G) • (x : Subgroup G) = (x : Subgroup G) :=
        congrArg Subtype.val hfix
      exact (hsmul_normalizer (z : G) (x : Subgroup G)).mp hfix'
    have hSleB : S ≤ B := by
      rintro y ⟨z, _hz, rfl⟩
      exact z.property
    obtain ⟨g, hg⟩ := hQconj
    have hdisjBQ : Disjoint B (x : Subgroup G) := by
      rw [hg]
      exact hdisjoint g
    have hdisjSQ : Disjoint S (x : Subgroup G) :=
      hdisjBQ.mono hSleB le_rfl
    have hQnormalizer :
        Nat.card (Subgroup.normalizer ((x : Subgroup G) : Set G)) =
          2 * Nat.card (x : Subgroup G) := by
      rw [hg,
        ← Subgroup.map_normalizer_eq_of_bijective A (MulAut.conj g).bijective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hA_normalizer
    calc
      Nat.card St = Nat.card S := by
        symm
        exact Subgroup.card_map_of_injective B.subtype_injective
      _ ≤ 2 := h826_subgroup_card_le_two_of_disjoint_le_normalizer
        (x : Subgroup G) S hSleN hdisjSQ hQnormalizer
  have hdiv :=
    h826_card_actor_dvd_two_mul_card_of_stabilizer_card_le_two hstabilizer
  rwa [hCcard] at hdiv

private theorem h826_punctured_conjugacy_class_card_divisibility
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (hA_normalizer : Nat.card (Subgroup.normalizer (A : Set G)) =
      2 * Nat.card A)
    (hdisjoint : ∀ g : G,
      A.map (MulAut.conj g).toMonoidHom ≠ A →
        Disjoint A (A.map (MulAut.conj g).toMonoidHom)) :
    Nat.card A ∣
      2 * ((Subgroup.normalizer (A : Set G)).index - 1) := by
  classical
  let : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  have hsmul_normalizer (g : G) (Q : Subgroup G) :
      g • Q = Q ↔ g ∈ Subgroup.normalizer (Q : Set G) := by
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer Q),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h => iff_congr Iff.rfl
      ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
        fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
          MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  have hstabA : MulAction.stabilizer G A =
      Subgroup.normalizer (A : Set G) := by
    ext g
    change g • A = A ↔ g ∈ Subgroup.normalizer (A : Set G)
    exact hsmul_normalizer g A
  let q : MulAction.orbitRel.Quotient G (Subgroup G) := Quotient.mk'' A
  let C := MulAction.orbitRel.Quotient.orbit q
  let base : C := ⟨A, by simp [C, q]⟩
  let X := {x : C // x ≠ base}
  let : MulAction A C := MulAction.compHom C A.subtype
  have hbase_fixed (a : A) : a • base = base := by
    apply Subtype.ext
    change (a : G) • A = A
    exact (hsmul_normalizer (a : G) A).mpr
      (Subgroup.le_normalizer a.property)
  let : MulAction A X :=
    { smul := fun a x => ⟨a • (x : C), by
        intro h
        apply x.2
        have hax : a • (x : C) = base := h
        calc
          (x : C) = a⁻¹ • (a • (x : C)) :=
            (inv_smul_smul a (x : C)).symm
          _ = a⁻¹ • base := congrArg (fun y : C => a⁻¹ • y) hax
          _ = base := hbase_fixed a⁻¹⟩
      one_smul := by
        intro x
        apply Subtype.ext
        exact one_smul A (x : C)
      mul_smul := by
        intro a b x
        apply Subtype.ext
        exact mul_smul a b (x : C) }
  have hCcard : Nat.card C =
      (Subgroup.normalizer (A : Set G)).index := by
    change Nat.card ↥(MulAction.orbitRel.Quotient.orbit q) = _
    rw [show MulAction.orbitRel.Quotient.orbit q = MulAction.orbit G A by
      simp [q], Nat.card_coe_set_eq, ← MulAction.index_stabilizer G A, hstabA]
  have hXcard : Nat.card X = Nat.card C - 1 := by
    let : Fintype C := Fintype.ofFinite C
    let : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {x : C // x ≠ base} = Fintype.card C - 1
    simp
  have hstabilizer (x : X) :
      Nat.card (MulAction.stabilizer A x) ≤ 2 := by
    let St : Subgroup A := MulAction.stabilizer A x
    let S : Subgroup G := St.map A.subtype
    have hQconj : ∃ g : G,
        (((x : X) : C) : Subgroup G) =
          A.map (MulAut.conj g).toMonoidHom := by
      have hx := ((x : X) : C).property
      change (((x : X) : C) : Subgroup G) ∈
        MulAction.orbitRel.Quotient.orbit q at hx
      rw [show MulAction.orbitRel.Quotient.orbit q = MulAction.orbit G A by
        simp [q]] at hx
      rcases hx with ⟨g, hg⟩
      exact ⟨g, hg.symm⟩
    have hSleN : S ≤ Subgroup.normalizer
        ((((x : X) : C) : Subgroup G) : Set G) := by
      rintro y ⟨z, hz, rfl⟩
      have hfix : z • x = x := MulAction.mem_stabilizer_iff.mp hz
      have hfixC : z • ((x : X) : C) = ((x : X) : C) :=
        congrArg Subtype.val hfix
      have hfix' : (z : G) • (((x : X) : C) : Subgroup G) =
          (((x : X) : C) : Subgroup G) := congrArg Subtype.val hfixC
      exact (hsmul_normalizer (z : G)
        (((x : X) : C) : Subgroup G)).mp hfix'
    have hSleA : S ≤ A := by
      rintro y ⟨z, _hz, rfl⟩
      exact z.property
    obtain ⟨g, hg⟩ := hQconj
    have hQne : (((x : X) : C) : Subgroup G) ≠ A := by
      intro heq
      apply x.2
      apply Subtype.ext
      exact heq
    have hmap_ne : A.map (MulAut.conj g).toMonoidHom ≠ A := by
      rw [← hg]
      exact hQne
    have hdisjAQ : Disjoint A (((x : X) : C) : Subgroup G) := by
      rw [hg]
      exact hdisjoint g hmap_ne
    have hdisjSQ : Disjoint S (((x : X) : C) : Subgroup G) :=
      hdisjAQ.mono hSleA le_rfl
    have hQnormalizer : Nat.card (Subgroup.normalizer
        ((((x : X) : C) : Subgroup G) : Set G)) =
        2 * Nat.card (((x : X) : C) : Subgroup G) := by
      rw [hg,
        ← Subgroup.map_normalizer_eq_of_bijective A (MulAut.conj g).bijective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hA_normalizer
    calc
      Nat.card St = Nat.card S := by
        symm
        exact Subgroup.card_map_of_injective A.subtype_injective
      _ ≤ 2 := h826_subgroup_card_le_two_of_disjoint_le_normalizer
        (((x : X) : C) : Subgroup G) S hSleN hdisjSQ hQnormalizer
  have hdiv :=
    h826_card_actor_dvd_two_mul_card_of_stabilizer_card_le_two hstabilizer
  rwa [hXcard, hCcard] at hdiv

private theorem h826_distinct_torus_conjugates_disjoint
    {F : Type*} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j)
    {i j : Fin r} {A B : Subgroup H}
    (hA : ∃ g, A = (Z i).map (MulAut.conj g).toMonoidHom)
    (hB : ∃ g, B = (Z j).map (MulAut.conj g).toMonoidHom)
    (hAB : A ≠ B) :
    Disjoint A B := by
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  by_contra hx
  have hu := huppert_II_8_22_unique_family hFcard H Z hcyclic
    hnontrivial hcoprime hmaximal hrepresentative hdistinct x hx
  let a : (Sylow p H) ⊕
      (Σ k : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z k).map (MulAut.conj g).toMonoidHom}) :=
    Sum.inr ⟨i, ⟨A, hA⟩⟩
  let b : (Sylow p H) ⊕
      (Σ k : Fin r, {W : Subgroup H // ∃ g : H,
        W = (Z k).map (MulAut.conj g).toMonoidHom}) :=
    Sum.inr ⟨j, ⟨B, hB⟩⟩
  have ha : x ∈ match a with
      | Sum.inl Q => (Q : Subgroup H)
      | Sum.inr z => (z.2.1 : Subgroup H) := hxA
  have hb : x ∈ match b with
      | Sum.inl Q => (Q : Subgroup H)
      | Sum.inr z => (z.2.1 : Subgroup H) := hxB
  have hab : a = b := hu.unique ha hb
  have hab' := Sum.inr.inj hab
  have hsub : A = B := congrArg
    (fun z : Σ k : Fin r, {W : Subgroup H // ∃ g : H,
      W = (Z k).map (MulAut.conj g).toMonoidHom} =>
        (z.2.1 : Subgroup H)) hab'
  exact hAB hsub

private theorem h826_card_actor_dvd_group_card_sub_one
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [MulDistribMulAction A E]
    (hfree : ∀ a : A, a ≠ 1 → ∀ e : E, a • e = e → e = 1) :
    Nat.card A ∣ Nat.card E - 1 := by
  classical
  let X := {e : E // e ≠ 1}
  let : MulAction A X :=
    { smul := fun a e => ⟨a • (e : E), by
        intro h
        apply e.2
        have h' := congrArg (fun x : E => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro e
        apply Subtype.ext
        change (1 : A) • (e : E) = (e : E)
        exact one_smul A (e : E)
      mul_smul := by
        intro a b e
        apply Subtype.ext
        change (a * b) • (e : E) = a • (b • (e : E))
        exact mul_smul a b (e : E) }
  have hstab : ∀ e : X, MulAction.stabilizer A e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    intro a ha
    have hae : a • e = e := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_ne_one
    have hfix : a • (e : E) = (e : E) := congrArg Subtype.val hae
    exact e.2 (hfree a ha_ne_one (e : E) hfix)
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hXcard : Nat.card X = Nat.card E - 1 := by
    let : Fintype E := Fintype.ofFinite E
    let : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {e : E // e ≠ 1} = Fintype.card E - 1
    simp
  rw [hXcard, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A X)), by
    rw [mul_comm]
    exact hcard⟩

private theorem h826_card_actor_dvd_two_mul_card
    {A X : Type*} [Group A] [Finite A] [Finite X] [MulAction A X]
    (hstab : ∀ x : X, Nat.card (MulAction.stabilizer A x) ≤ 2) :
    Nat.card A ∣ 2 * Nat.card X := by
  classical
  let Ω := Quotient (MulAction.orbitRel A X)
  let : Fintype Ω := Fintype.ofFinite Ω
  have horbit (ω : Ω) :
      Nat.card A ∣ 2 * Nat.card (MulAction.orbit A ω.out) := by
    let : Fintype A := Fintype.ofFinite A
    let : Fintype (MulAction.orbit A ω.out) := Fintype.ofFinite _
    let : Fintype (MulAction.stabilizer A ω.out) := Fintype.ofFinite _
    have hmul :
        Nat.card (MulAction.orbit A ω.out) *
            Nat.card (MulAction.stabilizer A ω.out) = Nat.card A := by
      simpa [Nat.card_eq_fintype_card] using
        MulAction.card_orbit_mul_card_stabilizer_eq_card_group A ω.out
    have hstab_cases :
        Nat.card (MulAction.stabilizer A ω.out) = 1 ∨
          Nat.card (MulAction.stabilizer A ω.out) = 2 := by
      have hpos : 0 < Nat.card (MulAction.stabilizer A ω.out) := Nat.card_pos
      have hle := hstab ω.out
      omega
    rcases hstab_cases with hs | hs
    · rw [hs, mul_one] at hmul
      rw [← hmul]
      exact ⟨2, by ring⟩
    · rw [hs] at hmul
      rw [← hmul]
      exact ⟨1, by ring⟩
  have hcardX :
      Nat.card X = ∑ ω : Ω, Nat.card (MulAction.orbit A ω.out) := by
    calc
      Nat.card X =
          Nat.card (Σ ω : Ω, MulAction.orbit A ω.out) :=
        Nat.card_congr (MulAction.selfEquivSigmaOrbits A X)
      _ = ∑ ω : Ω, Nat.card (MulAction.orbit A ω.out) := Nat.card_sigma
  have hsum :
      Nat.card A ∣
        ∑ ω : Ω, 2 * Nat.card (MulAction.orbit A ω.out) := by
    exact Finset.dvd_sum fun ω _hω => horbit ω
  simpa only [hcardX, Finset.mul_sum] using hsum

private theorem h826_card_pgl2
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let GL2 := GL (Fin 2) K
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 =>
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range =
          Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalar_inj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card PGL2 := by
    calc
      centerGL.index = mkPGL.ker.index := by
        rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card PGL2 := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card PGL2 =
        Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) *
        (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) *
        (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

@[expose] public def h826_pglMap
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) :
    Matrix.ProjGenLinGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F := by
  let f : GL (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjGenLinGroup.mk.comp
      (Matrix.GeneralLinearGroup.map e)
  apply Matrix.ProjGenLinGroup.lift f
  ext a
  change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.map e
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.map e a, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map,
      Matrix.GeneralLinearGroup.scalar]

set_option backward.isDefEq.respectTransparency false in
public theorem h826_pglMap_mk
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) (A : GL (Fin 2) K) :
    h826_pglMap e (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.map e A) := by
  unfold h826_pglMap
  exact Matrix.ProjGenLinGroup.lift_mk _ A

public theorem h826_pglMap_injective
    {K : Type u} {F : Type v} [Field K] [Field F]
    (e : K →+* F) (he : Function.Injective e) :
    Function.Injective (h826_pglMap e) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rcases Matrix.ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, h826_pglMap_mk] at hx
    have hcenterF :
        Matrix.GeneralLinearGroup.map e A ∈
          Subgroup.center (GL (Fin 2) F) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hx
    rcases
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
          hcenterF with ⟨c, hc⟩
    have hc00 :
        c = e ((A : Matrix (Fin 2) (Fin 2) K) 0 0) := by
      have h := congrFun (congrFun hc (0 : Fin 2)) (0 : Fin 2)
      simpa [Matrix.GeneralLinearGroup.map_apply] using h
    have hcenterK : A ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      refine ⟨(A : Matrix (Fin 2) (Fin 2) K) 0 0, ?_⟩
      ext i j
      apply he
      have h := congrFun (congrFun hc i) j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.map_apply, hc00] at h ⊢ <;>
        exact h
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker,
      Matrix.ProjGenLinGroup.ker_mk]
    exact hcenterK
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]

@[expose] public def h826_pslToPGL
    {K : Type u} [Field K] :
    PSL2MatrixGroup K →*
      Matrix.ProjGenLinGroup (Fin 2) K := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.ProjGenLinGroup (Fin 2) K :=
    Matrix.ProjGenLinGroup.mk.comp
      Matrix.SpecialLinearGroup.toGL
  apply QuotientGroup.lift
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) f
  intro A hA
  rw [MonoidHom.mem_ker]
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL A) = 1
  rw [← MonoidHom.mem_ker, Matrix.ProjGenLinGroup.ker_mk]
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2
  rcases Matrix.SpecialLinearGroup.mem_center_iff.mp hA with
    ⟨c, _, hc⟩
  exact ⟨c, by simpa using hc⟩

public theorem h826_pslToPGL_mk
    {K : Type u} [Field K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    h826_pslToPGL
        (QuotientGroup.mk'
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) A) =
      Matrix.ProjGenLinGroup.mk
        (Matrix.SpecialLinearGroup.toGL A) := by
  rfl

public theorem h826_pslToPGL_injective
    {K : Type u} [Field K] :
    Function.Injective (h826_pslToPGL (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rcases QuotientGroup.mk'_surjective
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K)) x with ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, h826_pslToPGL_mk] at hx
    have hcenterGL :
        Matrix.SpecialLinearGroup.toGL A ∈
          Subgroup.center (GL (Fin 2) K) := by
      rw [← Matrix.ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hx
    rcases
        Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
          hcenterGL with ⟨c, hc⟩
    have hc_sq : c ^ 2 = 1 := by
      have hc' :
          Matrix.scalar (Fin 2) c =
            (A : Matrix (Fin 2) (Fin 2) K) := by
        simpa using hc
      have hdet := A.property
      rw [← hc'] at hdet
      simpa [Matrix.det_diagonal, Fin.prod_univ_two, pow_two] using hdet
    have hcenterSL :
        A ∈ Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K) := by
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      exact ⟨c, by simpa using hc_sq, by simpa using hc⟩
    exact (QuotientGroup.eq_one_iff A).mpr hcenterSL
  · intro hx
    rw [Subgroup.mem_bot] at hx
    simp [hx]

/-- The concrete subfield retained by the large-normalizer branch of
Dickson's classification.  After one projective conjugation, the ambient
inclusion of `H` is the scalar-extension of a faithful projective
representation over `K`. -/
public structure SubfieldConjugacyWitness
    {F : Type u} [Field F] (p m : ℕ)
    (H : Subgroup (PSL2MatrixGroup F)) where
  K : Subfield F
  card_eq : Nat.card K = p ^ m
  phi : H →* Matrix.ProjGenLinGroup (Fin 2) K
  phi_injective : Function.Injective phi
  conjugator : Matrix.ProjGenLinGroup (Fin 2) F
  map_phi (h : H) :
    h826_pglMap K.subtype (phi h) =
      conjugator * h826_pslToPGL (h : PSL2MatrixGroup F) * conjugator⁻¹

private def h826_slEquiv
    {K : Type u} {L : Type v} [Field K] [Field L]
    (e : K ≃+* L) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) L := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.SpecialLinearGroup (Fin 2) L :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  let g : Matrix.SpecialLinearGroup (Fin 2) L →*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]
  · apply MonoidHom.ext
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]

public def h826_pslEquiv
    {K : Type u} {L : Type v} [Field K] [Field L]
    (e : K ≃+* L) :
    PSL2MatrixGroup K ≃* PSL2MatrixGroup L := by
  let eSL := h826_slEquiv e
  apply QuotientGroup.congr
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) L)) eSL
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (MulEquivClass.apply_mem_center_iff eSL).2 hB
  · intro hA
    refine ⟨eSL.symm A, ?_, eSL.apply_symm_apply A⟩
    exact (MulEquivClass.apply_mem_center_iff eSL.symm).2 hA

set_option backward.isDefEq.respectTransparency false in
private theorem h826_pslToPGL_range_le_of_index_two
    {K : Type u} [Field K] [Finite K]
    (htwo : (2 : K) ≠ 0)
    (M : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K))
    (hMindex : M.index = 2) :
    (h826_pslToPGL (K := K)).range ≤ M := by
  classical
  intro x hx
  rcases hx with ⟨y, rfl⟩
  induction y using QuotientGroup.induction_on with
  | _ A =>
      change h826_pslToPGL
          (QuotientGroup.mk'
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) K)) A) ∈ M
      rw [h826_pslToPGL_mk]
      let PMatrix : Matrix (Fin 2) (Fin 2) K → Prop := fun B =>
        ∃ hB : Matrix.det B = 1,
          Matrix.ProjGenLinGroup.mk
            (Matrix.SpecialLinearGroup.toGL
              (⟨B, hB⟩ : Matrix.SpecialLinearGroup (Fin 2) K)) ∈ M
      have hP : PMatrix (A : Matrix (Fin 2) (Fin 2) K) := by
        apply Matrix.diagonal_transvection_induction PMatrix
        · intro D hdet
          have hDdet : Matrix.det (Matrix.diagonal D) = 1 :=
            hdet.trans A.property
          let AD : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨Matrix.diagonal D, hDdet⟩
          have hDprod : D 0 * D 1 = 1 := by
            simpa [Matrix.det_diagonal, Fin.prod_univ_two] using hDdet
          have hD0ne : D 0 ≠ 0 := by
            intro hzero
            rw [hzero, zero_mul] at hDprod
            exact zero_ne_one hDprod
          let B : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![D 0, 0; 0, 1]
              (by simp [Matrix.det_fin_two, hD0ne])
          let d0 : Kˣ := Units.mk0 (D 0) hD0ne
          have hmat :
              B * B =
                Matrix.GeneralLinearGroup.scalar (Fin 2) d0 *
                  Matrix.SpecialLinearGroup.toGL AD := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [B, d0, AD, Matrix.GeneralLinearGroup.scalar,
                Matrix.mul_apply, hDprod]
          refine ⟨hDdet, ?_⟩
          have hsquare :=
            Subgroup.sq_mem_of_index_two hMindex
              (Matrix.ProjGenLinGroup.mk B)
          rw [pow_two, ← map_mul, hmat, map_mul,
            Matrix.ProjGenLinGroup.mk_scalar, one_mul] at hsquare
          exact hsquare
        · intro t
          let thalf : Matrix.TransvectionStruct (Fin 2) K :=
            ⟨t.i, t.j, t.hij, t.c / 2⟩
          let B : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨thalf.toMatrix, thalf.det⟩
          let C : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨t.toMatrix, t.det⟩
          have hc : t.c / 2 + t.c / 2 = t.c := by
            field_simp
            ring
          have hBC : B * B = C := by
            apply Subtype.ext
            change Matrix.transvection t.i t.j (t.c / 2) *
                Matrix.transvection t.i t.j (t.c / 2) =
              Matrix.transvection t.i t.j t.c
            rw [Matrix.transvection_mul_transvection_same
              t.i t.j t.hij, hc]
          refine ⟨t.det, ?_⟩
          have hsquare :=
            Subgroup.sq_mem_of_index_two hMindex
              (Matrix.ProjGenLinGroup.mk
                (Matrix.SpecialLinearGroup.toGL B))
          rw [pow_two, ← map_mul, ← map_mul, hBC] at hsquare
          exact hsquare
        · rintro B C ⟨hBdet, hB⟩ ⟨hCdet, hC⟩
          have hBCdet : Matrix.det (B * C) = 1 := by
            simp [hBdet, hCdet]
          let Bs : Matrix.SpecialLinearGroup (Fin 2) K := ⟨B, hBdet⟩
          let Cs : Matrix.SpecialLinearGroup (Fin 2) K := ⟨C, hCdet⟩
          let BCs : Matrix.SpecialLinearGroup (Fin 2) K :=
            ⟨B * C, hBCdet⟩
          have hmul : Bs * Cs = BCs := by rfl
          refine ⟨hBCdet, ?_⟩
          change Matrix.ProjGenLinGroup.mk
              (Matrix.SpecialLinearGroup.toGL BCs) ∈ M
          rw [← hmul, map_mul, map_mul]
          exact M.mul_mem hB hC
      rcases hP with ⟨hdet, hmem⟩
      have hAeq :
          (⟨(A : Matrix (Fin 2) (Fin 2) K), hdet⟩ :
            Matrix.SpecialLinearGroup (Fin 2) K) = A :=
        Subtype.ext rfl
      rw [hAeq] at hmem
      exact hmem

public theorem h826_pslToPGL_range_index_eq_two
    {K : Type u} [Field K] [Finite K]
    (hneg : (-1 : K) ≠ 1) :
    (h826_pslToPGL (K := K)).range.index = 2 := by
  let iota := h826_pslToPGL (K := K)
  have hcenter :
      Nat.card
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) = 2 :=
    huppert614_card_center_of_neg_one_ne_one hneg
  have hPSLmul := huppert614_card_psl_mul_center (K := K)
  rw [hcenter] at hPSLmul
  have hPGLcard := h826_card_pgl2 (K := K)
  have hrangeCard :
      Nat.card (PSL2MatrixGroup K) = Nat.card iota.range :=
    Nat.card_congr (MonoidHom.ofInjective h826_pslToPGL_injective).toEquiv
  have hindex := iota.range.index_mul_card
  rw [← hrangeCard, hPGLcard, ← hPSLmul] at hindex
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := PSL2MatrixGroup K))
  calc
    iota.range.index * Nat.card (PSL2MatrixGroup K) =
        Nat.card (PSL2MatrixGroup K) * 2 := hindex
    _ = 2 * Nat.card (PSL2MatrixGroup K) := by ring

private theorem h826_index_two_subgroup_eq_pslRange
    {K : Type u} [Field K] [Finite K]
    (htwo : (2 : K) ≠ 0)
    (M : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K))
    (hMindex : M.index = 2)
    (hPSLindex : (h826_pslToPGL (K := K)).range.index = 2) :
    M = (h826_pslToPGL (K := K)).range := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let R := (h826_pslToPGL (K := K)).range
  let : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite M := Finite.of_injective M.subtype M.subtype_injective
  let : Finite R := Finite.of_injective R.subtype R.subtype_injective
  have hRleM : R ≤ M :=
    h826_pslToPGL_range_le_of_index_two htwo M hMindex
  have hMcard := M.card_mul_index
  have hRcard := R.card_mul_index
  rw [hMindex] at hMcard
  rw [hPSLindex] at hRcard
  have hcardEq : Nat.card M = Nat.card R := by
    apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2)
    exact hMcard.trans hRcard.symm
  exact (Subgroup.eq_of_le_of_card_ge hRleM (by rw [hcardEq])).symm

private def h826_scalarStabilizer
    {F : Type*} [Field F] [Finite F] (W : AddSubgroup F) :
    Subfield F where
  carrier := {a | ∀ x : F, x ∈ W → a * x ∈ W}
  zero_mem' := by
    intro x hx
    simp
  one_mem' := by
    intro x hx
    simpa using hx
  add_mem' := by
    intro a b ha hb x hx
    rw [add_mul]
    exact W.add_mem (ha x hx) (hb x hx)
  neg_mem' := by
    intro a ha x hx
    rw [neg_mul]
    exact W.neg_mem (ha x hx)
  mul_mem' := by
    intro a b ha hb x hx
    rw [mul_assoc]
    exact ha (b * x) (hb x hx)
  inv_mem' := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      intro x hx
      simp
    · let φ : W → W := fun x => ⟨a * (x : F), ha x x.property⟩
      have hφinj : Function.Injective φ := by
        intro x y hxy
        apply Subtype.ext
        have hval := congrArg Subtype.val hxy
        exact mul_left_cancel₀ ha0 hval
      have hφsurj : Function.Surjective φ :=
        Finite.injective_iff_surjective.mp hφinj
      intro x hx
      obtain ⟨y, hy⟩ := hφsurj ⟨x, hx⟩
      have hyval : a * (y : F) = x := congrArg Subtype.val hy
      have heq : a⁻¹ * x = (y : F) := by
        rw [← hyval]
        field_simp
      rw [heq]
      exact y.property

public theorem h826_exponent_dvd_of_pow_sub_one_dvd
    {p m f : ℕ} (hp : 2 ≤ p)
    (h : p ^ m - 1 ∣ p ^ f - 1) :
    m ∣ f := by
  have hgcd :
      Nat.gcd (p ^ m - 1) (p ^ f - 1) = p ^ m - 1 :=
    Nat.gcd_eq_left_iff_dvd.mpr h
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hgcd
  have hleft : 1 ≤ p ^ Nat.gcd m f := one_le_pow₀ (by omega)
  have hright : 1 ≤ p ^ m := one_le_pow₀ (by omega)
  have hpow : p ^ Nat.gcd m f = p ^ m := by omega
  have heq : Nat.gcd m f = m := Nat.pow_right_injective hp hpow
  rw [← heq]
  exact Nat.gcd_dvd_right m f

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
private theorem h826_group_order_cases
    (q a b n u v w : ℕ)
    (hq : 1 < q) (ha : 1 < a) (hb : 1 < b)
    (hqa : Nat.Coprime q a) (hqb : Nat.Coprime q b)
    (hadiv : a ∣ q - 1) (hgcd : Nat.gcd a b ∣ 2)
    (hnlcm : n = Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)))
    (hqu : (q * a) * u = n)
    (hav : (2 * a) * v = n)
    (hbw : (2 * b) * w = n)
    (hcount :
      n = 1 + (q - 1) * u + (a - 1) * v + (b - 1) * w) :
    (q = 3 ∧ a = 2 ∧ b = 5 ∧ n = 60) ∨
      (a = q - 1 ∧ b = q + 1 ∧
        n = (q + 1) * q * (q - 1)) ∨
      (Nat.Coprime q 2 ∧
        a = (q - 1) / 2 ∧ b = (q + 1) / 2 ∧
        n = ((q + 1) * q * (q - 1)) / Nat.gcd (q - 1) 2) := by
  have hqpos : 0 < q := by omega
  have hap : 0 < a := by omega
  have hbp : 0 < b := by omega
  have hab_dvd_inner : a * b ∣ Nat.lcm (2 * a) (2 * b) := by
    calc
      a * b = Nat.gcd a b * Nat.lcm a b := (Nat.gcd_mul_lcm a b).symm
      _ ∣ 2 * Nat.lcm a b :=
        Nat.mul_dvd_mul_right hgcd (Nat.lcm a b)
      _ = Nat.lcm (2 * a) (2 * b) := (Nat.lcm_mul_left 2 a b).symm
  have hab_dvd_c :
      a * b ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    dvd_trans hab_dvd_inner (Nat.dvd_lcm_right _ _)
  have hq_dvd_c :
      q ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    dvd_trans (dvd_mul_right q a) (Nat.dvd_lcm_left _ _)
  have hqab_dvd_c :
      q * (a * b) ∣ Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) :=
    (hqa.mul_right hqb).mul_dvd_of_dvd_of_dvd hq_dvd_c hab_dvd_c
  have hc_dvd_twoqab :
      Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) ∣
        2 * q * a * b := by
    apply Nat.lcm_dvd
    · exact ⟨2 * b, by ring⟩
    · apply Nat.lcm_dvd
      · exact ⟨q * b, by ring⟩
      · exact ⟨q * a, by ring⟩
  have hnshape : n = q * a * b ∨ n = 2 * q * a * b := by
    let c := Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b))
    have hqab_dvd : q * a * b ∣ c := by
      simpa [c, mul_assoc] using hqab_dvd_c
    obtain ⟨k, hk⟩ := hqab_dvd
    have hc_dvd : c ∣ 2 * (q * a * b) := by
      simpa [c, mul_assoc] using hc_dvd_twoqab
    have hk_dvd_two : k ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_left
        (by positivity : 0 < q * a * b)
      have : (q * a * b) * k ∣ (q * a * b) * 2 := by
        rw [← hk]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hc_dvd
      exact this
    have hcpos : 0 < c :=
      Nat.lcm_pos (by positivity)
        (Nat.lcm_pos (by positivity) (by positivity))
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      rw [hkzero, mul_zero] at hk
      exact (Nat.ne_of_gt hcpos) hk
    have hkcases : k = 1 ∨ k = 2 := by
      have hkle : k ≤ 2 := Nat.le_of_dvd (by norm_num) hk_dvd_two
      omega
    rcases hkcases with rfl | rfl
    · left
      rw [hnlcm]
      simpa [c, mul_assoc] using hk
    · right
      rw [hnlcm]
      convert hk using 1
      all_goals ring
  rcases hnshape with hn | hn
  · have hu : u = b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q * a)
      calc
        (q * a) * u = n := hqu
        _ = (q * a) * b := by simpa [mul_assoc] using hn
    have hv : 2 * v = q * b := by
      apply Nat.eq_of_mul_eq_mul_left hap
      calc
        a * (2 * v) = (2 * a) * v := by ring
        _ = n := hav
        _ = a * (q * b) := by rw [hn]; ring
    have hw : 2 * w = q * a := by
      apply Nat.eq_of_mul_eq_mul_left hbp
      calc
        b * (2 * w) = (2 * b) * w := by ring
        _ = n := hbw
        _ = b * (q * a) := by rw [hn]; ring
    have hrel : q * a + 2 * (b - 1) = q * b := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have hasub : a - 1 + 1 = a := Nat.sub_add_cancel ha.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hn hu hv hw hcount hqsub hasub hbsub htwosub ⊢
      nlinarith
    have hab : a < b := by
      by_contra hnot
      have hle : b ≤ a := by omega
      have hmul_le := Nat.mul_le_mul_left q hle
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hrel hle hmul_le hbsub ⊢
      nlinarith
    have hrel' : (b - a) * q = 2 * (b - 1) := by
      have hsub : b - a + a = b := Nat.sub_add_cancel hab.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hrel hsub hbsub ⊢
      nlinarith
    have hq_dvd_twice : q ∣ 2 * (b - 1) :=
      ⟨b - a, by simpa [mul_comm] using hrel'.symm⟩
    have hq_dvd_bsub : q ∣ b - 1 := by
      rcases Nat.coprime_or_dvd_of_prime Nat.prime_two q with h2q | h2q
      · exact h2q.symm.dvd_of_dvd_mul_left hq_dvd_twice
      · have ha_not_even : ¬ Even a := by
          intro hae
          have htwo_one : 2 ∣ 1 := by
            rw [← hqa.gcd_eq_one]
            exact Nat.dvd_gcd h2q (even_iff_two_dvd.mp hae)
          norm_num at htwo_one
        have hb_not_even : ¬ Even b := by
          intro hbe
          have htwo_one : 2 ∣ 1 := by
            rw [← hqb.gcd_eq_one]
            exact Nat.dvd_gcd h2q (even_iff_two_dvd.mp hbe)
          norm_num at htwo_one
        have hdelta_even : 2 ∣ b - a := by
          rw [← even_iff_two_dvd, Nat.even_sub hab.le]
          constructor
          · exact fun hbe => (hb_not_even hbe).elim
          · exact fun hae => (ha_not_even hae).elim
        obtain ⟨k, hk⟩ := hdelta_even
        refine ⟨k, ?_⟩
        have hcancel : k * q = b - 1 := by
          rw [hk] at hrel'
          have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
          zify at hrel' hbsub ⊢
          nlinarith
        simpa [mul_comm] using hcancel.symm
    obtain ⟨k, hk⟩ := hq_dvd_bsub
    have hbk : b = 1 + q * k := by
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      zify at hk hbsub ⊢
      nlinarith
    have hdelta : b - a = 2 * k := by
      apply Nat.eq_of_mul_eq_mul_right hqpos
      calc
        (b - a) * q = 2 * (b - 1) := hrel'
        _ = 2 * (q * k) := by rw [hk]
        _ = (2 * k) * q := by ring
    have hale : a ≤ q - 1 := Nat.le_of_dvd (by omega) hadiv
    have hq3 : 3 ≤ q := by omega
    have hqsub_two : q - 2 + 2 = q :=
      Nat.sub_add_cancel (by omega : 2 ≤ q)
    have hak : a = 1 + k * (q - 2) := by
      zify at hbk hdelta hqsub_two ⊢
      nlinarith
    have hkpos : 0 < k := by omega
    have hk_le_one : k ≤ 1 := by
      have hmul_le : k * (q - 2) ≤ 1 * (q - 2) := by
        have hqsub_one : q - 2 + 1 = q - 1 := by omega
        zify at hak hale hqsub_one ⊢
        nlinarith
      exact (Nat.mul_le_mul_right_iff (by omega : 0 < q - 2)).mp hmul_le
    have hkone : k = 1 := by omega
    right
    left
    have haeq : a = q - 1 := by
      simp [hkone] at hak
      omega
    have hbeq : b = q + 1 := by omega
    refine ⟨haeq, hbeq, ?_⟩
    rw [hn, haeq, hbeq]
    ring
  · have hqodd : Nat.Coprime q 2 := by
      rcases Nat.coprime_or_dvd_of_prime Nat.prime_two q with h2q | h2q
      · exact h2q.symm
      · exfalso
        have hc_dvd_qab :
            Nat.lcm (q * a) (Nat.lcm (2 * a) (2 * b)) ∣
              q * a * b := by
          apply Nat.lcm_dvd
          · exact ⟨b, by ring⟩
          · apply Nat.lcm_dvd
            · obtain ⟨q2, hq2⟩ := h2q
              exact ⟨q2 * b, by rw [hq2]; ring⟩
            · obtain ⟨q2, hq2⟩ := h2q
              exact ⟨q2 * a, by rw [hq2]; ring⟩
        have hdiv : 2 * q * a * b ∣ q * a * b := by
          rw [← hn, hnlcm]
          exact hc_dvd_qab
        have hpos : 0 < q * a * b := by positivity
        have hle := Nat.le_of_dvd hpos hdiv
        have hdouble : 2 * (q * a * b) ≤ q * a * b := by
          simpa [mul_assoc] using hle
        omega
    have hu : u = 2 * b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q * a)
      calc
        (q * a) * u = n := hqu
        _ = (q * a) * (2 * b) := by rw [hn]; ring
    have hv : v = q * b := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * a)
      calc
        (2 * a) * v = n := hav
        _ = (2 * a) * (q * b) := by rw [hn]; ring
    have hw : w = q * a := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * b)
      calc
        (2 * b) * w = n := hbw
        _ = (2 * b) * (q * a) := by rw [hn]; ring
    have hrel : q * a + (2 * b - 1) = q * b := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have hasub : a - 1 + 1 = a := Nat.sub_add_cancel ha.le
      have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel hb.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hn hu hv hw hcount hqsub hasub hbsub htwosub ⊢
      nlinarith
    have hab : a < b := by
      by_contra hnot
      have hle : b ≤ a := by omega
      have hmul_le := Nat.mul_le_mul_left q hle
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at hrel hle hmul_le htwosub ⊢
      nlinarith
    have hrel' : (b - a) * q = 2 * b - 1 := by
      have hsub : b - a + a = b := Nat.sub_add_cancel hab.le
      have htwob : 1 ≤ 2 * b := by omega
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel htwob
      zify at hrel hsub htwosub ⊢
      nlinarith
    have hq_dvd : q ∣ 2 * b - 1 :=
      ⟨b - a, by simpa [mul_comm] using hrel'.symm⟩
    obtain ⟨k, hk⟩ := hq_dvd
    have htwo_b : 2 * b = 1 + q * k := by omega
    have hdelta : b - a = k := by
      apply Nat.eq_of_mul_eq_mul_right hqpos
      calc
        (b - a) * q = 2 * b - 1 := hrel'
        _ = q * k := hk
        _ = k * q := by ring
    have hak : a + k = b := by omega
    have hale : a ≤ q - 1 := Nat.le_of_dvd (by omega) hadiv
    have hkpos : 0 < k := by omega
    have hqodd' : Odd q := hqodd.odd_of_right
    have hkodd : Odd k := by
      rw [← Nat.not_even_iff_odd]
      intro hkeven
      have hqkeven : Even (q * k) := hkeven.mul_left q
      rcases hqkeven with ⟨r, hr⟩
      omega
    have hkle : k ≤ 3 := by
      have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
      have htwosub : 2 * b - 1 + 1 = 2 * b :=
        Nat.sub_add_cancel (by omega : 1 ≤ 2 * b)
      zify at htwo_b hak hale hqsub htwosub ⊢
      nlinarith
    have hkcases : k = 1 ∨ k = 3 := by
      rcases hkodd with ⟨j, hj⟩
      omega
    rcases hkcases with hk1 | hk3
    · right
      right
      have hqgcd : Nat.gcd (q - 1) 2 = 2 := by
        apply Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
        apply Nat.dvd_gcd
        · rcases hqodd' with ⟨r, hr⟩
          exact ⟨r, by simp [hr]⟩
        · exact dvd_refl 2
      have htwoa : 2 * a = q - 1 := by
        have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
        zify at hk1 hak htwo_b hqsub ⊢
        nlinarith
      have htwobb : 2 * b = q + 1 := by
        zify at hk1 htwo_b ⊢
        nlinarith
      have hqsub_even : 2 ∣ q - 1 := ⟨a, htwoa.symm⟩
      have hqadd_even : 2 ∣ q + 1 := ⟨b, htwobb.symm⟩
      have haeq : a = (q - 1) / 2 := by
        rw [← htwoa]
        simp
      have hbeq : b = (q + 1) / 2 := by
        rw [← htwobb]
        simp
      refine ⟨hqodd, haeq, hbeq, ?_⟩
      rw [hn, hqgcd, haeq, hbeq]
      obtain ⟨x, hx⟩ := hqsub_even
      obtain ⟨y, hy⟩ := hqadd_even
      rw [hx, hy]
      simp
      rw [show 2 * y * q * (2 * x) = (2 * q * x * y) * 2 by ring]
      simp
    · left
      have hqle : q ≤ 3 := by
        have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.le
        have hqsub_two : q - 2 + 2 = q :=
          Nat.sub_add_cancel (by omega : 2 ≤ q)
        simp [hk3] at hak htwo_b
        zify at hak htwo_b hale hqsub hqsub_two ⊢
        nlinarith
      have hqeq : q = 3 := by omega
      subst q
      have haeq : a = 2 := by omega
      have hbeq : b = 5 := by omega
      exact ⟨rfl, haeq, hbeq, by simp [hn, haeq, hbeq]⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
/-- Huppert II.8.26: the Dickson case with a larger Sylow p-normalizer. -/
public theorem huppert_II_8_26_dickson_case_p_part_normalizer_large_with_subfield
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hP_nontrivial : Nat.card P ≠ 1)
    (hnormalizer : Subgroup.normalizer (P : Set H) ≠ (P : Subgroup H)) :
    (∃ m t : ℕ,
      t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
      ∃ N C : Subgroup H,
        N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
        IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
    (∃ m : ℕ, p ^ m = 3 ∧
      (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) ∧
      Nonempty (SubfieldConjugacyWitness p m H)) ∨
    (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
      Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m)) ∧
      Nonempty (SubfieldConjugacyWitness p m H)) := by
  obtain ⟨m, hPm⟩ := P.isPGroup'.exists_card_eq
  have hm_ne_zero : m ≠ 0 := by
    intro hm
    subst m
    apply hP_nontrivial
    simpa using hPm
  have h826_counting_shapes :
      Nat.card H = Nat.card (Subgroup.normalizer (P : Set H)) ∨
      (p ^ m = 3 ∧ Nat.card H = 60 ∧
        (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nat.card (Sylow 5 H) = 6 ∧
        Function.Injective (MulAction.toPermHom H (Sylow 5 H))) ∨
      (2 * m ∣ f ∧ Nonempty
        (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) ∧
        Nonempty (SubfieldConjugacyWitness p m H)) ∨
      (m ∣ f ∧ Nonempty
        (H ≃* PSL2MatrixGroup (GaloisField p m)) ∧
        Nonempty (SubfieldConjugacyWitness p m H)) := by
    classical
    let : Fintype F := Fintype.ofFinite F
    let : CharP F p :=
      charP_of_card_eq_prime_pow (by simpa using hFcard)
    rcases huppert_II_8_22_dickson_counting hFcard H P hPm with
      ⟨r, Z, s, hcyclic, hnontrivial, hcoprime, hmaximal,
        hrepresentative, hdistinct, hs, hnormalizerZ, _hdihedral,
        hnormalizerP, hdivides, _hcounting⟩
    let NP : Subgroup H := Subgroup.normalizer (P : Set H)
    let NZ : Fin r → Subgroup H := fun i =>
      Subgroup.normalizer (Z i : Set H)
    let term : Fin r → ℕ := fun i =>
      (Nat.card (Z i) - 1) * (NZ i).index
    have hpartition_count :
        Nat.card H =
          1 + (p ^ m - 1) * NP.index + ∑ i, term i := by
      dsimp only [NP, NZ, term]
      apply huppert_II_8_22_partition_count_of_unique_family P hPm Z
      intro x hx
      convert huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
        hcoprime hmaximal hrepresentative hdistinct x hx using 1
      funext A
      rcases A with Q | z <;> rfl
    have hz_index_factor :
        ∀ i, (Nat.card (Z i) * s i) * (NZ i).index = Nat.card H := by
      intro i
      have hNZcard : Nat.card (NZ i) = Nat.card (Z i) * s i := by
        dsimp only [NZ]
        exact hnormalizerZ i
      calc
        (Nat.card (Z i) * s i) * (NZ i).index =
            Nat.card (NZ i) * (NZ i).index := by rw [hNZcard]
        _ = Nat.card H := (NZ i).card_mul_index
    have hterm_factor (i : Fin r) :
        term i + (NZ i).index =
          Nat.card (Z i) * (NZ i).index := by
      dsimp only [term]
      calc
        (Nat.card (Z i) - 1) * (NZ i).index + (NZ i).index =
            (Nat.card (Z i) - 1 + 1) * (NZ i).index := by ring
        _ = Nat.card (Z i) * (NZ i).index := by
          rw [Nat.sub_add_cancel (hnontrivial i).le]
    have hterm_bound (i : Fin r) :
        Nat.card H ≤ 4 * term i := by
      have hzbound :
          Nat.card (Z i) * s i ≤ 4 * (Nat.card (Z i) - 1) := by
        calc
          Nat.card (Z i) * s i ≤ Nat.card (Z i) * 2 :=
            Nat.mul_le_mul_left (Nat.card (Z i)) (hs i).2
          _ ≤ (2 * (Nat.card (Z i) - 1)) * 2 :=
            Nat.mul_le_mul_right 2 (by
              have hzi := hnontrivial i
              omega)
          _ = 4 * (Nat.card (Z i) - 1) := by ring
      calc
        Nat.card H = (Nat.card (Z i) * s i) * (NZ i).index :=
          (hz_index_factor i).symm
        _ ≤ (4 * (Nat.card (Z i) - 1)) * (NZ i).index :=
          Nat.mul_le_mul_right (NZ i).index hzbound
        _ = 4 * term i := by simp only [term]; ring
    have hfamily_bound : r ≤ 3 := by
      let T := ∑ i, term i
      have hrs : r * Nat.card H ≤ 4 * T := by
        calc
          r * Nat.card H = Finset.univ.sum fun _ : Fin r => Nat.card H := by simp
          _ ≤ Finset.univ.sum fun i : Fin r => 4 * term i :=
            Finset.sum_le_sum fun i _hi => hterm_bound i
          _ = 4 * T := by simp [T, Finset.mul_sum]
      have hTlt : T < Nat.card H := by
        have hcount : Nat.card H =
            1 + (p ^ m - 1) * NP.index + T := by
          simpa only [T] using hpartition_count
        omega
      have hcancel : r * Nat.card H < 4 * Nat.card H :=
        hrs.trans_lt ((Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hTlt)
      have hrlt : r < 4 :=
        (Nat.mul_lt_mul_right (Nat.card_pos (α := H))).mp hcancel
      omega
    have hpm_gt : 1 < p ^ m := by
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero,
          fun h => hP_nontrivial (hPm.trans h)⟩
    obtain ⟨i0, hNPcard⟩ :
        ∃ i, Nat.card NP = p ^ m * Nat.card (Z i) := by
      rcases hnormalizerP hpm_gt with hsmall | hlarge
      · exfalso
        have hPN : (P : Subgroup H) = NP := by
          apply Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer
          have hsmall' : Nat.card NP = p ^ m := by
            simpa only [NP] using hsmall
          have hcard_ge : Nat.card NP ≤ Nat.card (P : Subgroup H) := by
            rw [hsmall', hPm]
          exact hcard_ge
        exact hnormalizer (by simpa [NP] using hPN.symm)
      · exact hlarge
    have hNP_index_factor :
        (p ^ m * Nat.card (Z i0)) * NP.index = Nat.card H := by
      calc
        (p ^ m * Nat.card (Z i0)) * NP.index =
            Nat.card NP * NP.index := by rw [hNPcard]
        _ = Nat.card H := NP.card_mul_index
    have hpre_shape :
        Nat.card H = Nat.card NP ∨ (r = 2 ∧ ∀ i, s i = 2) := by
      let rest : Fin r → ℕ := fun i =>
        ∑ j ∈ Finset.univ.erase i, term j
      have hsum_rest (i : Fin r) :
          (∑ j, term j) = term i + rest i := by
        simpa only [rest, add_comm] using
          (Finset.sum_erase_add Finset.univ term (Finset.mem_univ i)).symm
      have hNPindex_pos : 0 < NP.index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hNZindex_pos (i : Fin r) : 0 < (NZ i).index :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have hq_ge_two : 2 ≤ p ^ m := hpm_gt
      have hindex_one (hsi : s i0 = 1) :
          (NZ i0).index = p ^ m * NP.index := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z i0))
        calc
          Nat.card (Z i0) * (NZ i0).index = Nat.card H := by
            simpa [hsi] using hz_index_factor i0
          _ = (p ^ m * Nat.card (Z i0)) * NP.index :=
            hNP_index_factor.symm
          _ = Nat.card (Z i0) * (p ^ m * NP.index) := by ring
      have hindex_two (hsi : s i0 = 2) :
          p ^ m * NP.index = 2 * (NZ i0).index := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z i0))
        calc
          Nat.card (Z i0) * (p ^ m * NP.index) = Nat.card H := by
            rw [← hNP_index_factor]
            ring
          _ = (Nat.card (Z i0) * 2) * (NZ i0).index := by
            simpa [hsi] using (hz_index_factor i0).symm
          _ = Nat.card (Z i0) * (2 * (NZ i0).index) := by ring
      have hq_term :
          (p ^ m - 1) * NP.index + NP.index = p ^ m * NP.index := by
        calc
          (p ^ m - 1) * NP.index + NP.index =
              (p ^ m - 1 + 1) * NP.index := by ring
          _ = p ^ m * NP.index := by
            rw [Nat.sub_add_cancel hpm_gt.le]
      have hrest_eq_of_one (hsi : s i0 = 1) :
          NP.index = 1 + rest i0 := by
        have hcount := hpartition_count
        rw [hsum_rest i0] at hcount
        have hzfactor :
            Nat.card (Z i0) * (NZ i0).index = Nat.card H := by
          simpa [hsi] using hz_index_factor i0
        have hidx := hindex_one hsi
        have hrel := hterm_factor i0
        omega
      have hrest_lt_of_two (hsi : s i0 = 2) :
          rest i0 < Nat.card (Z i0) * (NZ i0).index := by
        have hcount := hpartition_count
        rw [hsum_rest i0] at hcount
        have hzfactor :
            2 * (Nat.card (Z i0) * (NZ i0).index) = Nat.card H := by
          calc
            2 * (Nat.card (Z i0) * (NZ i0).index) =
                (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
            _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by rw [hsi]
            _ = Nat.card H := hz_index_factor i0
        have hidx := hindex_two hsi
        have hNPindex_le : NP.index ≤ (NZ i0).index := by
          have hmul := Nat.mul_le_mul_right NP.index hq_ge_two
          rw [hidx] at hmul
          omega
        have hrel := hterm_factor i0
        omega
      have hother_lower_one (hsi : s i0 = 1)
          (j : Fin r) (hji : j ≠ i0) : NP.index ≤ term j := by
        have hfour_le :
            4 * NP.index ≤ Nat.card H := by
          have hqz : 4 ≤ p ^ m * Nat.card (Z i0) :=
            Nat.mul_le_mul hq_ge_two (hnontrivial i0)
          calc
            4 * NP.index ≤
                (p ^ m * Nat.card (Z i0)) * NP.index :=
              Nat.mul_le_mul_right NP.index hqz
            _ = Nat.card H := hNP_index_factor
        have hj := hterm_bound j
        omega
      have hother_lower_two (hsi : s i0 = 2)
          (j : Fin r) (hji : j ≠ i0) :
          Nat.card (Z i0) * (NZ i0).index ≤ 2 * term j := by
        have hzfactor :
            2 * (Nat.card (Z i0) * (NZ i0).index) = Nat.card H := by
          calc
            2 * (Nat.card (Z i0) * (NZ i0).index) =
                (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
            _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by rw [hsi]
            _ = Nat.card H := hz_index_factor i0
        have hj := hterm_bound j
        omega
      have hr_pos : 0 < r := Nat.zero_lt_of_lt i0.isLt
      have hr_cases : r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases hr_cases with hr_one | hr_two | hr_three
      · subst r
        have hi0 : i0 = (0 : Fin 1) := Subsingleton.elim _ _
        subst i0
        rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
          hs0 | hs0
        · left
          have hrest : rest 0 = 0 := by simp [rest]
          have hindex : NP.index = 1 := by
            have h : NP.index = 1 + rest 0 := by
              simpa using hrest_eq_of_one hs0
            omega
          calc
            Nat.card H = Nat.card NP * NP.index := NP.card_mul_index.symm
            _ = Nat.card NP := by rw [hindex, mul_one]
        · exfalso
          have hcount := hpartition_count
          rw [hsum_rest 0] at hcount
          have hrest : rest 0 = 0 := by simp [rest]
          have hzfactor :
              2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
            calc
              2 * (Nat.card (Z 0) * (NZ 0).index) =
                  (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
              _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by rw [hs0]
              _ = Nat.card H := hz_index_factor 0
          have hidx : p ^ m * NP.index = 2 * (NZ 0).index := by
            simpa using hindex_two hs0
          have hNPindex_le : NP.index ≤ (NZ 0).index := by
            have hmul := Nat.mul_le_mul_right NP.index hq_ge_two
            rw [hidx] at hmul
            omega
          have hrel := hterm_factor 0
          have hz_lower :
              2 * (NZ 0).index ≤ Nat.card (Z 0) * (NZ 0).index :=
            Nat.mul_le_mul_right (NZ 0).index (hnontrivial 0)
          omega
      · right
        refine ⟨hr_two, ?_⟩
        subst r
        fin_cases i0
        · have hs0_two : s 0 = 2 := by
            rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
              hs0 | hs0
            · have hrest : NP.index = 1 + rest 0 := by
                simpa using hrest_eq_of_one hs0
              have hlower := hother_lower_one hs0 1 (by decide)
              have hrest_term : rest 0 = term 1 := by
                change (∑ j ∈ Finset.univ.erase (0 : Fin 2), term j) = term 1
                rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide]
                simp
              omega
            · exact hs0
          have hs1_two : s 1 = 2 := by
            rcases (show s 1 = 1 ∨ s 1 = 2 by have h := hs 1; omega) with
              hs1 | hs1
            · have hrest_lt :
                  rest 0 < Nat.card (Z 0) * (NZ 0).index := by
                simpa using hrest_lt_of_two hs0_two
              have hrest_term : rest 0 = term 1 := by
                change (∑ j ∈ Finset.univ.erase (0 : Fin 2), term j) = term 1
                rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide]
                simp
              have hzfactor0 :
                  2 * (Nat.card (Z 0) * (NZ 0).index) = Nat.card H := by
                calc
                  2 * (Nat.card (Z 0) * (NZ 0).index) =
                      (Nat.card (Z 0) * 2) * (NZ 0).index := by ring
                  _ = (Nat.card (Z 0) * s 0) * (NZ 0).index := by rw [hs0_two]
                  _ = Nat.card H := hz_index_factor 0
              have hzfactor1 :
                  Nat.card (Z 1) * (NZ 1).index = Nat.card H := by
                simpa [hs1] using hz_index_factor 1
              have hrel1 := hterm_factor 1
              have hk1_bound :
                  2 * (NZ 1).index ≤ Nat.card H := by
                calc
                  2 * (NZ 1).index ≤
                      Nat.card (Z 1) * (NZ 1).index :=
                    Nat.mul_le_mul_right (NZ 1).index (hnontrivial 1)
                  _ = Nat.card H := hzfactor1
              omega
            · exact hs1
          intro i
          fin_cases i
          · exact hs0_two
          · exact hs1_two
        · have hs1_two : s 1 = 2 := by
            rcases (show s 1 = 1 ∨ s 1 = 2 by have h := hs 1; omega) with
              hs1 | hs1
            · have hrest : NP.index = 1 + rest 1 := by
                simpa using hrest_eq_of_one hs1
              have hlower := hother_lower_one hs1 0 (by decide)
              have hrest_term : rest 1 = term 0 := by
                change (∑ j ∈ Finset.univ.erase (1 : Fin 2), term j) = term 0
                rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide]
                simp
              omega
            · exact hs1
          have hs0_two : s 0 = 2 := by
            rcases (show s 0 = 1 ∨ s 0 = 2 by have h := hs 0; omega) with
              hs0 | hs0
            · have hrest_lt :
                  rest 1 < Nat.card (Z 1) * (NZ 1).index := by
                simpa using hrest_lt_of_two hs1_two
              have hrest_term : rest 1 = term 0 := by
                change (∑ j ∈ Finset.univ.erase (1 : Fin 2), term j) = term 0
                rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide]
                simp
              have hzfactor1 :
                  2 * (Nat.card (Z 1) * (NZ 1).index) = Nat.card H := by
                calc
                  2 * (Nat.card (Z 1) * (NZ 1).index) =
                      (Nat.card (Z 1) * 2) * (NZ 1).index := by ring
                  _ = (Nat.card (Z 1) * s 1) * (NZ 1).index := by rw [hs1_two]
                  _ = Nat.card H := hz_index_factor 1
              have hzfactor0 :
                  Nat.card (Z 0) * (NZ 0).index = Nat.card H := by
                simpa [hs0] using hz_index_factor 0
              have hrel0 := hterm_factor 0
              have hk0_bound :
                  2 * (NZ 0).index ≤ Nat.card H := by
                calc
                  2 * (NZ 0).index ≤
                      Nat.card (Z 0) * (NZ 0).index :=
                    Nat.mul_le_mul_right (NZ 0).index (hnontrivial 0)
                  _ = Nat.card H := hzfactor0
              omega
            · exact hs0
          intro i
          fin_cases i
          · exact hs0_two
          · exact hs1_two
      · exfalso
        subst r
        rcases (show s i0 = 1 ∨ s i0 = 2 by have h := hs i0; omega) with
          hsi | hsi
        · have hrest := hrest_eq_of_one hsi
          have hlower : 2 * NP.index ≤ rest i0 := by
            calc
              2 * NP.index =
                  ∑ j ∈ Finset.univ.erase i0, NP.index := by simp
              _ ≤ ∑ j ∈ Finset.univ.erase i0, term j :=
                Finset.sum_le_sum fun j hj =>
                  hother_lower_one hsi j (Finset.ne_of_mem_erase hj)
              _ = rest i0 := rfl
          omega
        · have hrest := hrest_lt_of_two hsi
          have hlower :
              Nat.card (Z i0) * (NZ i0).index ≤ rest i0 := by
            have hsum :
                2 * (Nat.card (Z i0) * (NZ i0).index) ≤
                  2 * rest i0 := by
              calc
                2 * (Nat.card (Z i0) * (NZ i0).index) =
                    ∑ j ∈ Finset.univ.erase i0,
                      Nat.card (Z i0) * (NZ i0).index := by simp
                _ ≤ ∑ j ∈ Finset.univ.erase i0, 2 * term j :=
                  Finset.sum_le_sum fun j hj =>
                    hother_lower_two hsi j (Finset.ne_of_mem_erase hj)
                _ = 2 * rest i0 := by simp [rest, Finset.mul_sum]
            omega
          omega
    rcases hpre_shape with hnormal | ⟨hr, hs_two⟩
    · exact Or.inl (by simpa [NP] using hnormal)
    · subst r
      have hP_ne_bot : (P : Subgroup H) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hPm]
        exact hpm_gt
      let PN : Subgroup NP := (P : Subgroup H).subgroupOf NP
      let : PN.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (by
          simp [NP])
      obtain ⟨hquotient_cyclic, hquotient_card_dvd,
          hNormalizer_fixedPointFree, U, T, conjH, hconjH_injective,
          hconjH_conj,
          hU_commutative, hT_cyclic, hTcard, hT_fixedPointFree,
          hP_map_conjH_le_U, hB_le_normalizer, hB_conjugate_torus,
          hNP_maps_B, hU_preimage, unipotent, splitTorus,
          h_unipotent_injective, hU_range, hT_range, hsplit_conj,
          hunipotent_matrix, hsplitTorus_matrix⟩ :=
        h821_borel_quotient_data hFcard H P hP_ne_bot NP rfl PN rfl
      have hi0_divisors :
          Nat.card (Z i0) ∣ p ^ m - 1 ∧
          Nat.card (Z i0) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
        have hquotient_card_dvd_sub_one :
            Nat.card (NP ⧸ PN) ∣ Nat.card F - 1 :=
          dvd_trans hquotient_card_dvd
            (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
        have hf_ne_zero : f ≠ 0 :=
          huppert_II_8_27_field_exponent_ne_zero hFcard
        have hp_dvd_cardF : p ∣ Nat.card F := by
          rw [hFcard]
          exact dvd_pow_self p hf_ne_zero
        have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
          intro hp_sub
          have hp_one : p ∣ 1 := by
            have hd := Nat.dvd_sub hp_dvd_cardF hp_sub
            have hsub : Nat.card F - (Nat.card F - 1) = 1 := by
              have hcard_pos : 0 < Nat.card F := Nat.card_pos
              omega
            rwa [hsub] at hd
          exact (Fact.out : p.Prime).not_dvd_one hp_one
        have hcop_p_quotient : Nat.Coprime p (Nat.card (NP ⧸ PN)) :=
          Nat.Coprime.of_dvd_right hquotient_card_dvd_sub_one
            ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
              hp_not_dvd_cardF_sub_one)
        have hPNcard : Nat.card PN = p ^ m := by
          calc
            Nat.card PN = Nat.card P :=
              Nat.card_congr
                (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
            _ = p ^ m := hPm
        have hPNindex : PN.index = Nat.card (NP ⧸ PN) := rfl
        have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
          rw [hPNcard, hPNindex]
          exact hcop_p_quotient.pow_left m
        obtain ⟨C, hcomp⟩ :=
          Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
        have hCcard : Nat.card C = Nat.card (Z i0) := by
          have hmul := hcomp.card_mul_card
          rw [hPNcard, hNPcard] at hmul
          exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hpm_gt) hmul
        let : MulDistribMulAction C PN :=
          MulDistribMulAction.compHom PN
            ((MulAut.conjNormal (H := PN)).comp C.subtype)
        have hfree :
            ∀ c : C, c ≠ 1 → ∀ x : PN, c • x = x → x = 1 := by
          intro c hc x hfix
          by_contra hx
          have hc_not_PN : (c : NP) ∉ PN := by
            intro hcPN
            have hc_one : (c : NP) = 1 :=
              Subgroup.disjoint_def.mp hcomp.disjoint hcPN c.property
            apply hc
            apply Subtype.ext
            exact hc_one
          have hx_mem_P : ((x : NP) : H) ∈ (P : Subgroup H) := by
            have hx_mem := x.property
            change ((x : NP) : H) ∈ (P : Subgroup H) at hx_mem
            exact hx_mem
          let xP : P := ⟨((x : NP) : H), hx_mem_P⟩
          have hxP_ne : xP ≠ 1 := by
            intro hxP
            apply hx
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun y : P => (y : H)) hxP
          have hfixNP := congrArg Subtype.val hfix
          change (c : NP) * (x : NP) * (c : NP)⁻¹ = (x : NP) at hfixNP
          have hfixH := congrArg Subtype.val hfixNP
          exact (hNormalizer_fixedPointFree (c : NP) hc_not_PN xP hxP_ne hfixH).elim
        have hCdiv : Nat.card C ∣ p ^ m - 1 := by
          have hdiv := h826_card_actor_dvd_group_card_sub_one hfree
          rwa [hPNcard] at hdiv
        have hCquotient : Nat.card C = Nat.card (NP ⧸ PN) := by
          calc
            Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
            _ = Nat.card (NP ⧸ PN) := rfl
        constructor
        · rwa [← hCcard]
        · rw [← hCcard, hCquotient]
          exact hquotient_card_dvd
      have hi0_dvd_sub_one := hi0_divisors.1
      have hi0_dvd_ambient := hi0_divisors.2
      let i1 : Fin 2 := if i0 = 0 then 1 else 0
      have hi1_ne_i0 : i1 ≠ i0 := by
        fin_cases i0 <;> simp [i1]
      have hi0_ne_i1 : i0 ≠ i1 := Ne.symm hi1_ne_i0
      have huniv_pair : ({i0, i1} : Finset (Fin 2)) = Finset.univ := by
        ext j
        fin_cases i0 <;> fin_cases j <;> simp [i1]
      have htorus_inf_eq_bot (i j : Fin 2) (g : H)
          (hne : Z i ≠ (Z j).map (MulAut.conj g).toMonoidHom) :
          Z i ⊓ (Z j).map (MulAut.conj g).toMonoidHom = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        by_cases hx_one : x = 1
        · simp [hx_one]
        · exfalso
          obtain ⟨A, hxA, hAunique⟩ :=
            huppert_II_8_22_unique_family hFcard H Z hcyclic hnontrivial
              hcoprime hmaximal hrepresentative hdistinct x hx_one
          let Ai : (Sylow p H) ⊕
              (Σ k : Fin 2, {W : Subgroup H // ∃ a : H,
                W = (Z k).map (MulAut.conj a).toMonoidHom}) :=
            Sum.inr ⟨i, ⟨Z i, ⟨1, by ext y; simp⟩⟩⟩
          let Aj : (Sylow p H) ⊕
              (Σ k : Fin 2, {W : Subgroup H // ∃ a : H,
                W = (Z k).map (MulAut.conj a).toMonoidHom}) :=
            Sum.inr ⟨j, ⟨(Z j).map (MulAut.conj g).toMonoidHom, ⟨g, rfl⟩⟩⟩
          have hxAi : x ∈ match Ai with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H) := by
            simpa [Ai] using hx.1
          have hxAj : x ∈ match Aj with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H) := by
            simpa [Aj] using hx.2
          have hAiAj : Ai = Aj :=
            (hAunique Ai hxAi).trans (hAunique Aj hxAj).symm
          have hcarrier := congrArg
            (fun B => match B with
              | Sum.inl Q => (Q : Subgroup H)
              | Sum.inr z => (z.2.1 : Subgroup H)) hAiAj
          exact hne (by simpa [Ai, Aj] using hcarrier)
      let : MulAction H (Subgroup H) := MulAction.compHom _ MulAut.conj
      let X := MulAction.orbit H (Z i0)
      let base : X := ⟨Z i0, MulAction.mem_orbit_self (Z i0)⟩
      let : Nonempty X := ⟨base⟩
      have hbase_fixed (a : Z i0) : a • base = base := by
        apply Subtype.ext
        change MulAut.conj (a : H) • Z i0 = Z i0
        exact Subgroup.conj_smul_eq_self_of_mem a.property
      let X0 : SubMulAction (Z i0) X :=
        { carrier := {W | W ≠ base}
          smul_mem' := by
            intro a W hW haW
            apply hW
            calc
              W = a⁻¹ • (a • W) := (inv_smul_smul a W).symm
              _ = a⁻¹ • base := congrArg (fun Y : X => a⁻¹ • Y) haW
              _ = base := hbase_fixed a⁻¹ }
      have hstab_normalizer (W : Subgroup H) :
          MulAction.stabilizer H W =
            Subgroup.normalizer (W : Set H) := by
        ext g
        change g • W = W ↔ g ∈ Subgroup.normalizer (W : Set H)
        rw [eq_comm, SetLike.ext_iff,
          ← inv_mem_iff (G := H) (H := Subgroup.normalizer W),
          Subgroup.mem_normalizer_iff, inv_inv]
        exact
          forall_congr' fun h =>
            iff_congr Iff.rfl
              ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
                fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
                  MulAut.apply_inv_self H (MulAut.conj g) h⟩⟩
      have horbit_normalizer_card (W : X) :
          Nat.card (Subgroup.normalizer ((W : Subgroup H) : Set H)) =
            2 * Nat.card (W : Subgroup H) := by
        rcases W.property with ⟨g, hg⟩
        have hgmap :
            (W : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change (W : Subgroup H) = g • Z i0
          exact hg.symm
        calc
          Nat.card (Subgroup.normalizer ((W : Subgroup H) : Set H)) =
              Nat.card (Subgroup.normalizer (Z i0 : Set H)) := by
            rw [hgmap, ← Subgroup.map_equiv_normalizer_eq,
              Subgroup.card_map_of_injective (MulAut.conj g).injective]
          _ = Nat.card (Z i0) * 2 := by rw [hnormalizerZ i0, hs_two i0]
          _ = 2 * Nat.card (W : Subgroup H) := by
            rw [hgmap,
              Subgroup.card_map_of_injective (MulAut.conj g).injective]
            ring
      have hrestricted_stabilizer_card_le_two
          (A : Subgroup H) (W : X)
          (hAW : A ⊓ (W : Subgroup H) = ⊥) :
          Nat.card (MulAction.stabilizer A W) ≤ 2 := by
        let B : Subgroup H :=
          A ⊓ Subgroup.normalizer (((W : Subgroup H)) : Set H)
        have hWB :
            (W : Subgroup H) ⊓ B = ⊥ := by
          calc
            (W : Subgroup H) ⊓ B =
                (A ⊓ (W : Subgroup H)) ⊓
                  Subgroup.normalizer (((W : Subgroup H)) : Set H) := by
              dsimp only [B]
              ac_rfl
            _ = ⊥ := by simp [hAW]
        have hWindex :
            (W : Subgroup H).relIndex
                (Subgroup.normalizer (((W : Subgroup H)) : Set H)) = 2 :=
          relIndex_eq_two_of_card_eq_two_mul
            (W : Subgroup H)
            (Subgroup.normalizer (((W : Subgroup H)) : Set H))
            Subgroup.le_normalizer (horbit_normalizer_card W)
        have hBrel : (⊥ : Subgroup H).relIndex B ≤ 2 :=
          relIndex_le_two_of_inter_eq
            (W : Subgroup H) B
            (Subgroup.normalizer (((W : Subgroup H)) : Set H)) ⊥
            inf_le_right hWB hWindex
        have hBcard : Nat.card B ≤ 2 := by
          simpa only [Subgroup.relIndex_bot_left] using hBrel
        have hstab_eq :
            MulAction.stabilizer A W =
              (Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A := by
          ext a
          rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
          constructor
          · intro ha
            have haval := congrArg Subtype.val ha
            change (a : H) • (W : Subgroup H) = (W : Subgroup H) at haval
            have hamem :
                (a : H) ∈ MulAction.stabilizer H (W : Subgroup H) := by
              simpa [MulAction.mem_stabilizer_iff] using haval
            rwa [hstab_normalizer] at hamem
          · intro ha
            apply Subtype.ext
            change (a : H) • (W : Subgroup H) = (W : Subgroup H)
            have hamem :
                (a : H) ∈ MulAction.stabilizer H (W : Subgroup H) := by
              rwa [hstab_normalizer]
            simpa [MulAction.mem_stabilizer_iff] using hamem
        rw [hstab_eq]
        calc
          Nat.card
                ((Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A) =
              Nat.card
                (((Subgroup.normalizer (((W : Subgroup H)) : Set H)).subgroupOf A).map
                  A.subtype) :=
            (Subgroup.card_map_of_injective A.subtype_injective).symm
          _ = Nat.card
                ↥((Subgroup.normalizer (((W : Subgroup H)) : Set H) : Subgroup H) ⊓ A) := by
            rw [Subgroup.subgroupOf_map_subtype]
          _ = Nat.card B := by
            apply congrArg (fun K : Subgroup H => Nat.card K)
            dsimp only [B]
            exact inf_comm _ _
          _ ≤ 2 := hBcard
      have hstab_X0 (W : X0) :
          Nat.card (MulAction.stabilizer (Z i0) W) ≤ 2 := by
        have hW_ne : (W : X) ≠ base := W.property
        rcases (W : X).property with ⟨g, hg⟩
        have hgmap :
            ((W : X) : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change ((W : X) : Subgroup H) = g • Z i0
          exact hg.symm
        have hinter :
            Z i0 ⊓ ((W : X) : Subgroup H) = ⊥ := by
          rw [hgmap]
          apply htorus_inf_eq_bot
          intro heq
          apply hW_ne
          apply Subtype.ext
          exact (heq.trans hgmap.symm).symm
        have hle :=
          hrestricted_stabilizer_card_le_two (Z i0) (W : X) hinter
        have hstab_eq :
            MulAction.stabilizer (Z i0) W =
              MulAction.stabilizer (Z i0) (W : X) := by
          ext a
          simp only [MulAction.mem_stabilizer_iff]
          constructor
          · exact fun h => congrArg Subtype.val h
          · exact fun h => Subtype.ext h
        rwa [hstab_eq]
      have hi0_dvd_orbit_punctured :
          Nat.card (Z i0) ∣ 2 * Nat.card X0 :=
        h826_card_actor_dvd_two_mul_card hstab_X0
      have hX0card : Nat.card X0 = Nat.card X - 1 := by
        change Nat.card {W : X // W ≠ base} = Nat.card X - 1
        let : Fintype X := Fintype.ofFinite X
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        simp
      have hi0_dvd_orbit :
          Nat.card (Z i0) ∣ 2 * (Nat.card X - 1) := by
        rwa [hX0card] at hi0_dvd_orbit_punctured
      have hstab_i1 (W : X) :
          Nat.card (MulAction.stabilizer (Z i1) W) ≤ 2 := by
        rcases W.property with ⟨g, hg⟩
        have hgmap :
            (W : Subgroup H) =
              (Z i0).map (MulAut.conj g).toMonoidHom := by
          change (W : Subgroup H) = g • Z i0
          exact hg.symm
        have hne : Z i1 ≠
            (Z i0).map (MulAut.conj g).toMonoidHom := by
          intro heq
          apply hi0_ne_i1
          exact hdistinct i0 i1 g heq.symm
        have hinter : Z i1 ⊓ (W : Subgroup H) = ⊥ := by
          rw [hgmap]
          exact htorus_inf_eq_bot i1 i0 g hne
        exact hrestricted_stabilizer_card_le_two (Z i1) W hinter
      have hi1_dvd_orbit :
          Nat.card (Z i1) ∣ 2 * Nat.card X :=
        h826_card_actor_dvd_two_mul_card hstab_i1
      have htorus_gcd :
          Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣ 2 := by
        have hleft :
            Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣
              2 * (Nat.card X - 1) :=
          dvd_trans (Nat.gcd_dvd_left _ _) hi0_dvd_orbit
        have hright :
            Nat.gcd (Nat.card (Z i0)) (Nat.card (Z i1)) ∣
              2 * Nat.card X :=
          dvd_trans (Nat.gcd_dvd_right _ _) hi1_dvd_orbit
        have hsub := Nat.dvd_sub hright hleft
        have hXpos : 0 < Nat.card X := Nat.card_pos
        have hdiff : 2 * Nat.card X - 2 * (Nat.card X - 1) = 2 := by
          omega
        rwa [hdiff] at hsub
      let c := Nat.lcm (p ^ m * Nat.card (Z i0))
        (Nat.lcm (2 * Nat.card (Z i0)) (2 * Nat.card (Z i1)))
      have hi0_factor :
          (2 * Nat.card (Z i0)) * (NZ i0).index = Nat.card H := by
        calc
          (2 * Nat.card (Z i0)) * (NZ i0).index =
              (Nat.card (Z i0) * 2) * (NZ i0).index := by ring
          _ = (Nat.card (Z i0) * s i0) * (NZ i0).index := by
            rw [hs_two i0]
          _ = Nat.card H := hz_index_factor i0
      have hi1_factor :
          (2 * Nat.card (Z i1)) * (NZ i1).index = Nat.card H := by
        calc
          (2 * Nat.card (Z i1)) * (NZ i1).index =
              (Nat.card (Z i1) * 2) * (NZ i1).index := by ring
          _ = (Nat.card (Z i1) * s i1) * (NZ i1).index := by
            rw [hs_two i1]
          _ = Nat.card H := hz_index_factor i1
      have hqa_dvd_c : p ^ m * Nat.card (Z i0) ∣ c := by
        exact Nat.dvd_lcm_left _ _
      have h2a_dvd_c : 2 * Nat.card (Z i0) ∣ c := by
        exact dvd_trans (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_right _ _)
      have h2b_dvd_c : 2 * Nat.card (Z i1) ∣ c := by
        exact dvd_trans (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_right _ _)
      have hc_dvd_H : c ∣ Nat.card H := by
        apply Nat.lcm_dvd
        · exact ⟨NP.index, hNP_index_factor.symm⟩
        · apply Nat.lcm_dvd
          · exact ⟨(NZ i0).index, hi0_factor.symm⟩
          · exact ⟨(NZ i1).index, hi1_factor.symm⟩
      have hquotient_dvd_NP : Nat.card H / c ∣ NP.index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H hqa_dvd_c
        have hindex : NP.index =
            Nat.card H / (p ^ m * Nat.card (Z i0)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
              (Nat.card_pos (α := Z i0)))) hNP_index_factor
        rwa [← hindex] at hdiv
      have hquotient_dvd_NZi0 : Nat.card H / c ∣ (NZ i0).index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H h2a_dvd_c
        have hindex : (NZ i0).index =
            Nat.card H / (2 * Nat.card (Z i0)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (by norm_num)
              (Nat.card_pos (α := Z i0)))) hi0_factor
        rwa [← hindex] at hdiv
      have hquotient_dvd_NZi1 : Nat.card H / c ∣ (NZ i1).index := by
        have hdiv := Nat.div_dvd_div_left hc_dvd_H h2b_dvd_c
        have hindex : (NZ i1).index =
            Nat.card H / (2 * Nat.card (Z i1)) :=
          Nat.eq_div_of_mul_eq_right
            (Nat.ne_of_gt (Nat.mul_pos (by norm_num)
              (Nat.card_pos (α := Z i1)))) hi1_factor
        rwa [← hindex] at hdiv
      have hsum_pair :
          (∑ i, term i) = term i0 + term i1 := by
        rw [← huniv_pair]
        simp [hi0_ne_i1]
      have hcount_pair : Nat.card H =
          1 + (p ^ m - 1) * NP.index +
            (Nat.card (Z i0) - 1) * (NZ i0).index +
            (Nat.card (Z i1) - 1) * (NZ i1).index := by
        rw [hpartition_count, hsum_pair]
        simp only [term]
        ring
      have hquotient_dvd_tail : Nat.card H / c ∣
          (p ^ m - 1) * NP.index +
            (Nat.card (Z i0) - 1) * (NZ i0).index +
            (Nat.card (Z i1) - 1) * (NZ i1).index := by
        exact Nat.dvd_add
          (Nat.dvd_add
            (dvd_mul_of_dvd_right hquotient_dvd_NP _)
            (dvd_mul_of_dvd_right hquotient_dvd_NZi0 _))
          (dvd_mul_of_dvd_right hquotient_dvd_NZi1 _)
      have hquotient_dvd_H : Nat.card H / c ∣ Nat.card H :=
        Nat.div_dvd_of_dvd hc_dvd_H
      have hquotient_dvd_one : Nat.card H / c ∣ 1 := by
        have hsub := Nat.dvd_sub hquotient_dvd_H hquotient_dvd_tail
        have htail_eq : Nat.card H -
            ((p ^ m - 1) * NP.index +
              (Nat.card (Z i0) - 1) * (NZ i0).index +
              (Nat.card (Z i1) - 1) * (NZ i1).index) = 1 := by
          omega
        rwa [htail_eq] at hsub
      have hquotient_one : Nat.card H / c = 1 :=
        Nat.eq_one_of_dvd_one hquotient_dvd_one
      have hH_eq_c : Nat.card H = c := by
        have hmul := Nat.div_mul_cancel hc_dvd_H
        rw [hquotient_one, one_mul] at hmul
        exact hmul.symm
      have hPNcard : Nat.card PN = p ^ m := by
        calc
          Nat.card PN = Nat.card P :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
          _ = p ^ m := hPm
      have hPNindex : PN.index = Nat.card (Z i0) := by
        have hmul := PN.card_mul_index
        rw [hPNcard, hNPcard] at hmul
        exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hpm_gt) hmul
      have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
        rw [hPNcard, hPNindex]
        exact (hcoprime i0).pow_left m
      obtain ⟨C, hcomp⟩ :=
        Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
      have hCcyclic : IsCyclic C := by
        let eC : NP ⧸ PN ≃* C := hcomp.symm.QuotientMulEquiv
        let : IsCyclic (NP ⧸ PN) := hquotient_cyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      have hCcard : Nat.card C = Nat.card (Z i0) := by
        calc
          Nat.card C = PN.index := hcomp.symm.index_eq_card.symm
          _ = Nat.card (Z i0) := hPNindex
      let : IsCyclic C := hCcyclic
      obtain ⟨cgen, hcgen⟩ := IsCyclic.exists_generator (α := C)
      have hcgen_ne_one : cgen ≠ 1 := by
        intro hc
        have hsub : Subsingleton C := by
          constructor
          intro x y
          rcases hcgen x with ⟨i, hi⟩
          rcases hcgen y with ⟨j, hj⟩
          rw [hc] at hi hj
          simp only [one_zpow] at hi hj
          exact hi.symm.trans hj
        have hcard_one : Nat.card C = 1 := Nat.card_eq_one_iff_unique.mpr
          ⟨hsub, ⟨1⟩⟩
        rw [hCcard] at hcard_one
        exact (hnontrivial i0).ne hcard_one.symm
      let cN : NP := (cgen : C)
      have hcN_not_PN : cN ∉ PN := by
        intro hcPN
        have hcC : cN ∈ C := cgen.property
        have hc_one : cN = 1 :=
          Subgroup.disjoint_def.mp hcomp.disjoint hcPN hcC
        exact hcgen_ne_one (Subtype.ext hc_one)
      have hcN_not_U : conjH (cN : H) ∉ U := by
        intro hcU
        exact hcN_not_PN ((hU_preimage cN).mp hcU)
      obtain ⟨u, huU, hc_torus⟩ :=
        hB_conjugate_torus (conjH (cN : H))
          (hNP_maps_B cN) hcN_not_U
      rcases hc_torus with ⟨t, htT, ht⟩
      change u * t * u⁻¹ = conjH (cN : H) at ht
      let conjH' : H →* PSL2MatrixGroup F :=
        (MulAut.conj u⁻¹).toMonoidHom.comp conjH
      have hconjH'_injective : Function.Injective conjH' :=
        (MulAut.conj u⁻¹).injective.comp hconjH_injective
      have hP_map_conjH'_le_U : (P : Subgroup H).map conjH' ≤ U := by
        rintro y ⟨x, hxP, rfl⟩
        change u⁻¹ * conjH x * (u⁻¹)⁻¹ ∈ U
        exact U.mul_mem
          (U.mul_mem (U.inv_mem huU)
            (hP_map_conjH_le_U (Subgroup.mem_map_of_mem conjH hxP)))
          (by simpa using huU)
      have hcgen_image : conjH' (cN : H) = t := by
        dsimp only [conjH']
        change u⁻¹ * conjH (cN : H) * (u⁻¹)⁻¹ = t
        rw [← ht]
        group
      rw [hT_range] at htT
      rcases htT with ⟨r, hr⟩
      have hcgen_split : conjH' (cN : H) = splitTorus r := by
        rw [hcgen_image, hr]
      let P0 : Subgroup (PSL2MatrixGroup F) :=
        (P : Subgroup H).map conjH'
      let W : AddSubgroup F :=
        { carrier := {x | unipotent x ∈ P0}
          zero_mem' := by
            change unipotent 0 ∈ P0
            simp
          add_mem' := by
            intro x y hx hy
            change unipotent (x + y) ∈ P0
            rw [unipotent.map_add_eq_mul]
            exact P0.mul_mem hx hy
          neg_mem' := by
            intro x hx
            change unipotent (-x) ∈ P0
            rw [unipotent.map_neg_eq_inv]
            exact P0.inv_mem hx }
      have hWcard : Nat.card W = p ^ m := by
        let eW : W ≃ P0 := Equiv.ofBijective
          (fun x : W => (⟨unipotent (x : F), x.property⟩ : P0)) (by
            constructor
            · intro x y hxy
              apply Subtype.ext
              apply h_unipotent_injective
              exact congrArg Subtype.val hxy
            · intro y
              have hyU : (y : PSL2MatrixGroup F) ∈ U := by
                apply hP_map_conjH'_le_U
                exact y.property
              rw [hU_range] at hyU
              rcases hyU with ⟨x, hx⟩
              refine ⟨⟨x, ?_⟩, ?_⟩
              · change unipotent.toMonoidHom x ∈ P0
                rw [hx]
                exact y.property
              · apply Subtype.ext
                exact hx)
        calc
          Nat.card W = Nat.card P0 := Nat.card_congr eW
          _ = Nat.card P :=
            Subgroup.card_map_of_injective hconjH'_injective
          _ = p ^ m := hPm
      have hW_ne_bot : W ≠ ⊥ := by
        rw [← AddSubgroup.one_lt_card_iff_ne_bot, hWcard]
        exact hpm_gt
      obtain ⟨x0, hx0_ne_zero⟩ :=
        AddSubgroup.ne_bot_iff_exists_ne_zero.mp hW_ne_bot
      have hx0_val_ne_zero : (x0 : F) ≠ 0 := by
        intro hx
        exact hx0_ne_zero (Subtype.ext hx)
      have hx0_unipotent_ne_one : unipotent (x0 : F) ≠ 1 := by
        intro hx
        have hxzero := h_unipotent_injective
          (hx.trans unipotent.map_zero_eq_one.symm)
        exact hx0_ne_zero (Subtype.ext hxzero)
      have hlambda_mem_W :
          ∀ x : F, x ∈ W → (r : F) ^ 2 * x ∈ W := by
        intro x hxW
        change unipotent ((r : F) ^ 2 * x) ∈ P0
        rw [← hsplit_conj]
        rcases hxW with ⟨y, hyP, hy⟩
        have hc_normalizes :
            (cN : H) ∈ Subgroup.normalizer (P : Set H) := cN.property
        have hcyP :
            (cN : H) * y * (cN : H)⁻¹ ∈ (P : Subgroup H) :=
          (Subgroup.mem_normalizer_iff.mp hc_normalizes y).mp hyP
        refine ⟨(cN : H) * y * (cN : H)⁻¹, hcyP, ?_⟩
        rw [map_mul, map_mul, map_inv, hcgen_split, hy]
      let K : Subfield F := h826_scalarStabilizer W
      have hlambda_mem_K : (r : F) ^ 2 ∈ K := hlambda_mem_W
      have hK_le_W_card : Nat.card K ≤ Nat.card W := by
        let φ : K → W := fun a =>
          ⟨(a : F) * (x0 : F), a.property (x0 : F) x0.property⟩
        have hφinj : Function.Injective φ := by
          intro a b hab
          apply Subtype.ext
          have hval := congrArg Subtype.val hab
          exact mul_right_cancel₀ hx0_val_ne_zero hval
        exact Nat.card_le_card_of_injective φ hφinj
      have hK_le_q : Nat.card K ≤ p ^ m := by
        rw [← hWcard]
        exact hK_le_W_card
      have hcgen_order : orderOf cgen = Nat.card C :=
        orderOf_eq_card_of_forall_mem_zpowers hcgen
      have hsplit_order :
          orderOf (splitTorus r) = Nat.card (Z i0) := by
        calc
          orderOf (splitTorus r) = orderOf (conjH' (cN : H)) := by
            rw [hcgen_split]
          _ = orderOf (cN : H) :=
            orderOf_injective conjH' hconjH'_injective (cN : H)
          _ = orderOf cN := Subgroup.orderOf_coe cN
          _ = orderOf cgen := Subgroup.orderOf_coe cgen
          _ = Nat.card C := hcgen_order
          _ = Nat.card (Z i0) := hCcard
      let lambdaU : Fˣ := r ^ 2
      have hsplit_pow_fixed (j : ℕ) :
          (splitTorus r) ^ j * unipotent (x0 : F) *
              ((splitTorus r) ^ j)⁻¹ =
            unipotent ((lambdaU ^ j : Fˣ) * (x0 : F)) := by
        calc
          (splitTorus r) ^ j * unipotent (x0 : F) *
                ((splitTorus r) ^ j)⁻¹ =
              splitTorus (r ^ j) * unipotent (x0 : F) *
                (splitTorus (r ^ j))⁻¹ := by rw [map_pow]
          _ = unipotent (((r ^ j : Fˣ) : F) ^ 2 * (x0 : F)) :=
            hsplit_conj (r ^ j) (x0 : F)
          _ = unipotent ((lambdaU ^ j : Fˣ) * (x0 : F)) := by
            congr 2
            simp only [lambdaU, Units.val_pow_eq_pow_val]
            ring
      have hlambda_pow_of_split_pow {j : ℕ}
          (hj : (splitTorus r) ^ j = 1) :
          lambdaU ^ j = 1 := by
        have hfix := hsplit_pow_fixed j
        rw [hj] at hfix
        simp only [one_mul, mul_one, inv_one] at hfix
        have hcoord :
            (x0 : F) = (lambdaU ^ j : Fˣ) * (x0 : F) :=
          h_unipotent_injective hfix
        apply Units.ext
        apply mul_right_cancel₀ hx0_val_ne_zero
        simpa using hcoord.symm
      have hsplit_pow_of_lambda_pow {j : ℕ}
          (hj : lambdaU ^ j = 1) :
          (splitTorus r) ^ j = 1 := by
        have hfix := hsplit_pow_fixed j
        rw [hj] at hfix
        simp only [Units.val_one, one_mul] at hfix
        have hsplit_mem : splitTorus r ∈ T := by
          rw [hT_range]
          exact ⟨r, rfl⟩
        rcases hT_fixedPointFree
            ((splitTorus r) ^ j) (T.pow_mem hsplit_mem j)
            (unipotent (x0 : F))
            (hP_map_conjH'_le_U x0.property) hfix with ht | hx
        · exact ht
        · exact (hx0_unipotent_ne_one hx).elim
      have hlambda_order :
          orderOf lambdaU = Nat.card (Z i0) := by
        apply Nat.dvd_antisymm
        · apply orderOf_dvd_of_pow_eq_one
          apply hlambda_pow_of_split_pow
          rw [← hsplit_order]
          exact pow_orderOf_eq_one (splitTorus r)
        · rw [← hsplit_order]
          apply orderOf_dvd_of_pow_eq_one
          apply hsplit_pow_of_lambda_pow
          exact pow_orderOf_eq_one lambdaU
      let lambdaK0 : K := ⟨(lambdaU : F), hlambda_mem_K⟩
      have hlambdaK0_ne_zero : lambdaK0 ≠ 0 := by
        intro hzero
        have hval := congrArg Subtype.val hzero
        exact Units.ne_zero lambdaU hval
      let lambdaK : Kˣ := Units.mk0 lambdaK0 hlambdaK0_ne_zero
      let inclUnits : Kˣ →* Fˣ :=
        Units.map (K.subtype : K →+* F)
      have hinclUnits_injective : Function.Injective inclUnits :=
        Units.map_injective K.subtype_injective
      have hlambda_map :
          inclUnits lambdaK = lambdaU := by
        apply Units.ext
        rfl
      have hlambdaK_order :
          orderOf lambdaK = Nat.card (Z i0) := by
        calc
          orderOf lambdaK = orderOf (inclUnits lambdaK) :=
            (orderOf_injective inclUnits hinclUnits_injective lambdaK).symm
          _ = orderOf lambdaU := congrArg orderOf hlambda_map
          _ = Nat.card (Z i0) := hlambda_order
      have hKunits_card : Nat.card Kˣ = Nat.card K - 1 := by
        let : Fintype K := Fintype.ofFinite K
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
      have hCcard_dvd_K_sub_one : Nat.card (Z i0) ∣ Nat.card K - 1 := by
        rw [← hKunits_card, ← hlambdaK_order]
        exact orderOf_dvd_natCard lambdaK
      have hK_lower : Nat.card (Z i0) + 1 ≤ Nat.card K := by
        have hKcard_gt : 1 < Nat.card K := Finite.one_lt_card
        have hle := Nat.le_of_dvd (by omega) hCcard_dvd_K_sub_one
        calc
          Nat.card (Z i0) + 1 ≤ (Nat.card K - 1) + 1 :=
            Nat.add_le_add_right hle 1
          _ = Nat.card K := Nat.sub_add_cancel hKcard_gt.le
      let Point := ℙ F (Fin 2 → F)
      let inf : Point :=
        Projectivization.mk F ![(1 : F), 0] (by simp)
      let zero : Point :=
        Projectivization.mk F ![(0 : F), 1] (by simp)
      let affine (x : F) : Point :=
        Projectivization.mk F ![x, 1] (by simp)
      obtain ⟨rho, hrho, hrho_apply, _hrho_two_transitive⟩ :=
        huppert_II_6_11_projective_action (K := F) 2 (by omega)
      let : MulAction (PSL2MatrixGroup F) Point :=
        MulAction.compHom Point rho
      have hunipotent_fixes_inf (x : F) :
          unipotent x • inf = inf := by
        rw [hunipotent_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) inf = inf
        rw [hrho_apply]
        dsimp only [inf]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨1, ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct]
      have hsplit_fixes_inf (a : Fˣ) :
          splitTorus a • inf = inf := by
        rw [hsplitTorus_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) inf = inf
        rw [hrho_apply]
        dsimp only [inf]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨(a : F), ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct]
      have hsplit_fixes_zero (a : Fˣ) :
          splitTorus a • zero = zero := by
        rw [hsplitTorus_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) zero = zero
        rw [hrho_apply]
        dsimp only [zero]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨(a⁻¹ : F), ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct]
      have hunipotent_affine (w x : F) :
          unipotent w • affine x = affine (x + w) := by
        rw [hunipotent_matrix]
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)) (affine x) =
          affine (x + w)
        rw [hrho_apply]
        dsimp only [affine]
        rw [Projectivization.smul_mk]
        apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
        refine ⟨1, ?_⟩
        ext i
        fin_cases i <;>
          simp [Matrix.mulVec, dotProduct, add_comm]
      have hunipotent_fixed_eq_inf
          (w : F) (hw : w ≠ 0) (z : Point)
          (hfix : unipotent w • z = z) :
          z = inf := by
        rw [← Projectivization.mk_rep z] at hfix
        rw [hunipotent_matrix] at hfix
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F))
              (Projectivization.mk F z.rep z.rep_nonzero) =
            Projectivization.mk F z.rep z.rep_nonzero at hfix
        rw [hrho_apply, Projectivization.smul_mk] at hfix
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
          ⟨a, ha⟩
        have h0 := congrFun ha (0 : Fin 2)
        have h1 := congrFun ha (1 : Fin 2)
        simp [Matrix.mulVec, dotProduct] at h0 h1
        by_cases hz1 : z.rep 1 = 0
        · rw [← Projectivization.mk_rep z]
          dsimp only [inf]
          apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
          refine ⟨z.rep 0, ?_⟩
          ext i
          fin_cases i
          · simp
          · simp [hz1]
        · have ha_one : a = 1 := by
            apply mul_right_cancel₀ hz1
            simpa using h1
          rw [ha_one, one_mul] at h0
          have hprod : w * z.rep 1 = 0 := by
            linear_combination -h0
          exact (mul_ne_zero hw hz1 hprod).elim
      have hB_fixes_inf :
          U ⊔ T ≤ MulAction.stabilizer (PSL2MatrixGroup F) inf := by
        apply sup_le
        · intro g hg
          rw [MulAction.mem_stabilizer_iff]
          rw [hU_range] at hg
          rcases hg with ⟨x, rfl⟩
          exact hunipotent_fixes_inf x
        · intro g hg
          rw [MulAction.mem_stabilizer_iff]
          rw [hT_range] at hg
          rcases hg with ⟨a, rfl⟩
          exact hsplit_fixes_inf a
      have hfix_inf_mem_B
          (g : PSL2MatrixGroup F) (hfix : g • inf = inf) :
          g ∈ U ⊔ T := by
        refine QuotientGroup.induction_on g ?_ hfix
        intro A hAfix
        have hA10 :
            (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
          change rho
              (QuotientGroup.mk'
                (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F)) A) inf = inf at hAfix
          rw [hrho_apply] at hAfix
          dsimp only [inf] at hAfix
          rw [Projectivization.smul_mk] at hAfix
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hAfix with
            ⟨a, ha⟩
          have h1 := congrFun ha (1 : Fin 2)
          simpa [Matrix.GeneralLinearGroup.toLin_apply,
            Matrix.mulVec, dotProduct] using h1.symm
        have hdet :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 *
                (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
          have h := A.property
          rw [Matrix.det_fin_two, hA10, mul_zero, sub_zero] at h
          exact h
        have ha_zero :
            (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
          left_ne_zero_of_mul_eq_one hdet
        let aU : Fˣ :=
          Units.mk0 ((A : Matrix (Fin 2) (Fin 2) F) 0 0) ha_zero
        have hd_inv :
            (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (aU⁻¹ : F) := by
          simpa [aU] using eq_inv_of_mul_eq_one_right hdet
        let Bsl : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![1,
              (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                (A : Matrix (Fin 2) (Fin 2) F) 0 0;
              0, 1], by simp [Matrix.det_fin_two]⟩
        let Dsl : Matrix.SpecialLinearGroup (Fin 2) F :=
          ⟨!![(aU : F), 0; 0, (aU⁻¹ : F)],
            by simp [Matrix.det_fin_two]⟩
        have hfactor : A = Bsl * Dsl := by
          apply Subtype.ext
          ext i j
          fin_cases i <;> fin_cases j
          · simp [Bsl, Dsl, Matrix.mul_apply, aU]
          · simp [Bsl, Dsl, Matrix.mul_apply, aU, ha_zero]
          · simpa [Bsl, Dsl, Matrix.mul_apply, aU] using hA10
          · simpa [Bsl, Dsl, Matrix.mul_apply, aU] using hd_inv
        have hBsl :
            QuotientGroup.mk'
                (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F)) Bsl =
              unipotent
                ((A : Matrix (Fin 2) (Fin 2) F) 0 1 *
                  (A : Matrix (Fin 2) (Fin 2) F) 0 0) := by
          rw [hunipotent_matrix]
        have hDsl :
            QuotientGroup.mk'
                (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F)) Dsl =
              splitTorus aU := by
          rw [hsplitTorus_matrix]
        change QuotientGroup.mk'
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) F)) A ∈ U ⊔ T
        rw [hfactor, map_mul, hBsl, hDsl]
        exact (U ⊔ T).mul_mem
          ((show U ≤ U ⊔ T from le_sup_left)
            (by rw [hU_range]; exact ⟨_, rfl⟩))
          ((show T ≤ U ⊔ T from le_sup_right)
            (by rw [hT_range]; exact ⟨_, rfl⟩))
      have hmem_NP_of_image_mem_B
          (g : H) (hgB : conjH' g ∈ U ⊔ T) :
          g ∈ NP := by
        let Qg : Subgroup H :=
          (P : Subgroup H).map (MulAut.conj g).toMonoidHom
        have hg_normalizes_U :
            conjH' g ∈ Subgroup.normalizer (U : Set (PSL2MatrixGroup F)) :=
          hB_le_normalizer hgB
        have hQg_map_le_U : Qg.map conjH' ≤ U := by
          rintro y ⟨z, ⟨x, hxP, rfl⟩, rfl⟩
          change conjH' (g * x * g⁻¹) ∈ U
          rw [map_mul, map_mul, map_inv]
          exact
            (Subgroup.mem_normalizer_iff.mp hg_normalizes_U
              (conjH' x)).mp
              (hP_map_conjH'_le_U
                (Subgroup.mem_map_of_mem conjH' hxP))
        have hP_normalizes_Qg :
            (P : Subgroup H) ≤ Subgroup.normalizer (Qg : Set H) := by
          intro x hxP
          rw [Subgroup.mem_normalizer_iff]
          intro y
          have hxU : conjH' x ∈ U :=
            hP_map_conjH'_le_U (Subgroup.mem_map_of_mem conjH' hxP)
          have hzU (z : H) (hz : z ∈ Qg) : conjH' z ∈ U :=
            hQg_map_le_U (Subgroup.mem_map_of_mem conjH' hz)
          have hcomm (z : H) (hz : z ∈ Qg) : Commute x z := by
            let : IsMulCommutative U := hU_commutative
            apply hconjH'_injective
            simpa only [map_mul] using setLike_mul_comm hxU (hzU z hz)
          constructor
          · intro hy
            have hxy : x * y * x⁻¹ = y := by
              calc
                x * y * x⁻¹ = y * x * x⁻¹ := by
                  rw [(hcomm y hy).eq]
                _ = y := by simp
            rwa [hxy]
          · intro hy
            have hzcomm : Commute x (x * y * x⁻¹) :=
              hcomm (x * y * x⁻¹) hy
            have hy_eq : y = x * y * x⁻¹ := by
              calc
                y = x⁻¹ * (x * y * x⁻¹) * x := by group
                _ = x⁻¹ * (x * (x * y * x⁻¹)) := by
                  rw [mul_assoc, hzcomm.eq.symm]
                _ = x * y * x⁻¹ := by simp
            rw [hy_eq]
            exact hy
        have hQg_isPGroup : IsPGroup p Qg :=
          P.isPGroup'.map (MulAut.conj g).toMonoidHom
        have hsup_isPGroup :
            IsPGroup p ((P : Subgroup H) ⊔ Qg : Subgroup H) :=
          P.isPGroup'.to_sup_of_normal_right' hQg_isPGroup hP_normalizes_Qg
        have hsup_eq_P :
            (P : Subgroup H) ⊔ Qg = (P : Subgroup H) :=
          P.is_maximal' hsup_isPGroup le_sup_left
        have hQg_le_P : Qg ≤ (P : Subgroup H) := by
          calc
            Qg ≤ (P : Subgroup H) ⊔ Qg := le_sup_right
            _ = (P : Subgroup H) := hsup_eq_P
        have hQg_card : Nat.card Qg = Nat.card P :=
          Subgroup.card_map_of_injective (MulAut.conj g).injective
        have hQg_eq_P : Qg = (P : Subgroup H) :=
          Subgroup.eq_of_le_of_card_ge hQg_le_P (by rw [hQg_card])
        apply (Subgroup.conjAct_pointwise_smul_iff
          (H := (P : Subgroup H)) (g := g)).mp
        change Qg = (P : Subgroup H)
        exact hQg_eq_P
      let rhoH : H →* Equiv.Perm Point := rho.comp conjH'
      let : MulAction H Point := MulAction.compHom Point rhoH
      have hstabilizer_inf :
          MulAction.stabilizer H inf = NP := by
        ext g
        rw [MulAction.mem_stabilizer_iff]
        constructor
        · intro hfix
          apply hmem_NP_of_image_mem_B g
          apply hfix_inf_mem_B (conjH' g)
          exact hfix
        · intro hgNP
          have hgB0 : conjH (g : H) ∈ U ⊔ T :=
            hNP_maps_B ⟨g, hgNP⟩
          have hgB : conjH' g ∈ U ⊔ T := by
            change u⁻¹ * conjH g * (u⁻¹)⁻¹ ∈ U ⊔ T
            exact (U ⊔ T).mul_mem
              ((U ⊔ T).mul_mem
                ((show U ≤ U ⊔ T from le_sup_left) (U.inv_mem huU)) hgB0)
              ((show U ≤ U ⊔ T from le_sup_left) (by simpa using huU))
          apply hB_fixes_inf
          exact hgB
      let S := MulAction.orbit H inf
      let baseS : S := ⟨inf, MulAction.mem_orbit_self inf⟩
      have hstabilizer_base :
          MulAction.stabilizer H baseS = NP := by
        ext g
        rw [MulAction.mem_stabilizer_iff]
        constructor
        · intro hfix
          have hfix_val := congrArg Subtype.val hfix
          have : g • inf = inf := by
            rw [MulAction.orbit.coe_smul] at hfix_val
            exact hfix_val
          rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf] at this
          exact this
        · intro hg
          apply Subtype.ext
          change g • inf = inf
          rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
          exact hg
      have hsplit_fixed_eq_inf_or_zero
          (a : Fˣ) (ha : splitTorus a ≠ 1) (z : Point)
          (hfix : splitTorus a • z = z) :
          z = inf ∨ z = zero := by
        rw [← Projectivization.mk_rep z] at hfix
        rw [hsplitTorus_matrix] at hfix
        change rho
            (QuotientGroup.mk'
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F))
              (Projectivization.mk F z.rep z.rep_nonzero) =
            Projectivization.mk F z.rep z.rep_nonzero at hfix
        rw [hrho_apply, Projectivization.smul_mk] at hfix
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
          ⟨c0, hc0⟩
        have h0 := congrFun hc0 (0 : Fin 2)
        have h1 := congrFun hc0 (1 : Fin 2)
        simp [Matrix.mulVec, dotProduct] at h0 h1
        by_cases hz0 : z.rep 0 = 0
        · right
          rw [← Projectivization.mk_rep z]
          dsimp only [zero]
          apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
          refine ⟨z.rep 1, ?_⟩
          ext i
          fin_cases i
          · simp [hz0]
          · simp
        · by_cases hz1 : z.rep 1 = 0
          · left
            rw [← Projectivization.mk_rep z]
            dsimp only [inf]
            apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).2
            refine ⟨z.rep 0, ?_⟩
            ext i
            fin_cases i
            · simp
            · simp [hz1]
          · exfalso
            have hc_eq_a : c0 = (a : F) := by
              apply mul_right_cancel₀ hz0
              simpa using h0
            have hc_eq_ainv : c0 = (a⁻¹ : F) := by
              apply mul_right_cancel₀ hz1
              simpa using h1
            have ha_sq : (a : F) ^ 2 = 1 := by
              have hai : (a : F) = (a⁻¹ : F) :=
                hc_eq_a.symm.trans hc_eq_ainv
              calc
                (a : F) ^ 2 = (a : F) * (a : F) := pow_two _
                _ = (a : F) * (a⁻¹ : F) :=
                  congrArg (fun z : F => (a : F) * z) hai
                _ = 1 := mul_inv_cancel₀ (Units.ne_zero a)
            have hfix_x0 :
                splitTorus a * unipotent (x0 : F) *
                    (splitTorus a)⁻¹ =
                  unipotent (x0 : F) := by
              rw [hsplit_conj, ha_sq, one_mul]
            have haT : splitTorus a ∈ T := by
              rw [hT_range]
              exact ⟨a, rfl⟩
            rcases hT_fixedPointFree
                (splitTorus a) haT (unipotent (x0 : F))
                (hP_map_conjH'_le_U x0.property) hfix_x0 with ha1 | hx1
            · exact ha ha1
            · exact hx0_unipotent_ne_one hx1
      have hzero_mem_S
          (hS_card : Nat.card S = p ^ m + 1) :
          zero ∈ S := by
        by_contra hzero_not
        let cToH : C →* H := NP.subtype.comp C.subtype
        let : MulAction C S := MulAction.compHom S cToH
        have hbase_fixed (d : C) : d • baseS = baseS := by
          apply Subtype.ext
          change (cToH d) • inf = inf
          apply MulAction.mem_stabilizer_iff.mp
          rw [hstabilizer_inf]
          exact (d : NP).property
        let S0 : SubMulAction C S :=
          { carrier := {y | y ≠ baseS}
            smul_mem' := by
              intro d y hy hdy
              apply hy
              calc
                y = d⁻¹ • (d • y) := (inv_smul_smul d y).symm
                _ = d⁻¹ • baseS := congrArg (fun z : S => d⁻¹ • z) hdy
                _ = baseS := hbase_fixed d⁻¹ }
        have hstab (y : S0) :
            MulAction.stabilizer C y = ⊥ := by
          rw [eq_bot_iff]
          intro d hd
          by_contra hd_ne_one
          have hdy : d • (y : S) = (y : S) := by
            have hdy0 : d • y = y :=
              MulAction.mem_stabilizer_iff.mp hd
            simpa only [SubMulAction.val_smul] using
              congrArg Subtype.val hdy0
          have hpoint_fixed :
              conjH' (cToH d) • ((y : S) : Point) = ((y : S) : Point) := by
            have hval := congrArg Subtype.val hdy
            exact hval
          rcases hcgen d with ⟨j, hj⟩
          have himage :
              conjH' (cToH d) = splitTorus (r ^ j) := by
            calc
              conjH' (cToH d) = conjH' (cToH (cgen ^ j)) := by rw [← hj]
              _ = (conjH' (cToH cgen)) ^ j := map_zpow conjH' _ _
              _ = (splitTorus r) ^ j := by
                have hcToH : cToH cgen = (cN : H) := rfl
                rw [hcToH, hcgen_split]
              _ = splitTorus (r ^ j) := (map_zpow splitTorus r j).symm
          have himage_ne : splitTorus (r ^ j) ≠ 1 := by
            intro himage_one
            apply hd_ne_one
            apply Subtype.ext
            apply Subtype.ext
            apply hconjH'_injective
            change conjH' (cToH d) = conjH' (cToH 1)
            rw [himage, himage_one]
            exact (map_one conjH').symm
          have hfixed_cases :=
            hsplit_fixed_eq_inf_or_zero (r ^ j) himage_ne
              ((y : S) : Point) (by rwa [← himage])
          rcases hfixed_cases with hyinf | hyzero
          · apply y.property
            apply Subtype.ext
            exact hyinf
          · apply hzero_not
            rw [← hyzero]
            exact (y : S).property
        have hC_dvd_S0 : Nat.card C ∣ Nat.card S0 := by
          have hcard :=
            Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
          rw [Nat.card_prod] at hcard
          exact ⟨Nat.card (Quotient (MulAction.orbitRel C S0)), by
            rw [mul_comm]
            exact hcard⟩
        have hS0card : Nat.card S0 = p ^ m := by
          have hsub : Nat.card S0 = Nat.card S - 1 := by
            change Nat.card {y : S // y ≠ baseS} = Nat.card S - 1
            let : Fintype S := Fintype.ofFinite S
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            simp
          rw [hsub, hS_card]
          omega
        have hzi0_dvd_q : Nat.card (Z i0) ∣ p ^ m := by
          rw [← hCcard, ← hS0card]
          exact hC_dvd_S0
        have hzi0_dvd_one : Nat.card (Z i0) ∣ 1 := by
          have hsub := Nat.dvd_sub hzi0_dvd_q hi0_dvd_sub_one
          have hdiff : p ^ m - (p ^ m - 1) = 1 := by omega
          rwa [hdiff] at hsub
        have hzi0_one := Nat.eq_one_of_dvd_one hzi0_dvd_one
        exact (hnontrivial i0).ne hzi0_one.symm
      have haffine_injective : Function.Injective affine := by
        intro x y hxy
        dsimp only [affine] at hxy
        rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hxy with
          ⟨a, ha⟩
        have h0 := congrFun ha (0 : Fin 2)
        have h1 := congrFun ha (1 : Fin 2)
        simp at h1
        simpa [h1] using h0.symm
      have hsubline_swap
          (hS_card : Nat.card S = p ^ m + 1) :
          ∃ h : H,
            h • inf = zero ∧ h • zero = inf ∧
            (∀ z : S, (z : Point) ≠ inf →
              ∃ w : W, (z : Point) = affine (w : F)) ∧
            NP ⊔ Subgroup.zpowers h = ⊤ := by
        have hzeroS : zero ∈ S := hzero_mem_S hS_card
        have hzero_ne_inf : zero ≠ inf := by
          intro hzero_inf
          dsimp only [zero, inf] at hzero_inf
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp
              hzero_inf with ⟨a, ha⟩
          have h0 := congrFun ha (0 : Fin 2)
          have h1 := congrFun ha (1 : Fin 2)
          simp at h1
        let zeroS : S := ⟨zero, hzeroS⟩
        let S0 := {z : S // z ≠ baseS}
        have hS0card : Nat.card S0 = p ^ m := by
          have hsub : Nat.card S0 = Nat.card S - 1 := by
            change Nat.card {z : S // z ≠ baseS} = Nat.card S - 1
            let : Fintype S := Fintype.ofFinite S
            rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            simp
          rw [hsub, hS_card]
          omega
        have haffine_mem_S (w : W) : affine (w : F) ∈ S := by
          rcases w.property with ⟨g, hgP, hg⟩
          rcases hzeroS with ⟨h0, hh0⟩
          change h0 • inf = zero at hh0
          refine ⟨g * h0, ?_⟩
          change (g * h0) • inf = affine (w : F)
          rw [mul_smul, hh0]
          change rho (conjH' g) zero = affine (w : F)
          rw [hg]
          change unipotent (w : F) • affine 0 = affine (w : F)
          simpa using hunipotent_affine (w : F) 0
        have haffine_ne_inf (w : W) : affine (w : F) ≠ inf := by
          intro hwi
          dsimp only [affine, inf] at hwi
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hwi with
            ⟨a, ha⟩
          have h1 := congrFun ha (1 : Fin 2)
          simp at h1
        let affineW : W → S0 := fun w =>
          ⟨⟨affine (w : F), haffine_mem_S w⟩, by
            intro heq
            apply haffine_ne_inf w
            exact congrArg Subtype.val heq⟩
        have haffineW_inj : Function.Injective affineW := by
          intro x y hxy
          apply Subtype.ext
          apply haffine_injective
          exact congrArg (fun z : S0 => ((z : S) : Point)) hxy
        have haffineW_card : Nat.card W = Nat.card S0 := by
          rw [hWcard, hS0card]
        have haffineW_surj : Function.Surjective affineW :=
          (Nat.bijective_iff_injective_and_card affineW).mpr
            ⟨haffineW_inj, haffineW_card⟩ |>.2
        have hcover :
            ∀ z : S, (z : Point) ≠ inf →
              ∃ w : W, (z : Point) = affine (w : F) := by
          intro z hz
          have hzbase : z ≠ baseS := by
            intro heq
            exact hz (congrArg Subtype.val heq)
          obtain ⟨w, hw⟩ := haffineW_surj ⟨z, hzbase⟩
          refine ⟨w, ?_⟩
          exact congrArg (fun y : S0 => ((y : S) : Point)) hw.symm
        have hP_trans :
            ∀ y z : S0, ∃ g : P, (g : H) • (y : S) = (z : S) := by
          intro y z
          obtain ⟨wy, hwy⟩ := hcover (y : S) (by
            intro hy
            exact y.property (Subtype.ext hy))
          obtain ⟨wz, hwz⟩ := hcover (z : S) (by
            intro hz
            exact z.property (Subtype.ext hz))
          have hdiff_mem : unipotent ((wz : F) - (wy : F)) ∈ P0 := by
            change (wz : F) - (wy : F) ∈ W
            exact W.sub_mem wz.property wy.property
          rcases hdiff_mem with ⟨g, hgP, hg⟩
          refine ⟨⟨g, hgP⟩, ?_⟩
          apply Subtype.ext
          change rho (conjH' g) ((y : S) : Point) = ((z : S) : Point)
          rw [hwy, hwz, hg]
          change unipotent ((wz : F) - (wy : F)) • affine (wy : F) =
            affine (wz : F)
          rw [hunipotent_affine]
          congr 2
          ring
        have htwo :
            MulAction.IsMultiplyPretransitive H S 2 := by
          rw [MulAction.is_two_pretransitive_iff]
          intro a b c d hab hcd
          let : MulAction.IsPretransitive H S := inferInstance
          obtain ⟨g, hg⟩ :=
            (inferInstance : MulAction.IsPretransitive H S).exists_smul_eq
              a baseS
          obtain ⟨k, hk⟩ :=
            (inferInstance : MulAction.IsPretransitive H S).exists_smul_eq
              baseS c
          have hgb : g • b ≠ baseS := by
            intro hgb
            exact hab (smul_left_cancel g (hg.trans hgb.symm))
          have hkd : k⁻¹ • d ≠ baseS := by
            intro hkd
            apply hcd
            calc
              c = k • baseS := hk.symm
              _ = k • (k⁻¹ • d) := by rw [hkd]
              _ = d := smul_inv_smul k d
          obtain ⟨p0, hp0⟩ :=
            hP_trans ⟨g • b, hgb⟩ ⟨k⁻¹ • d, hkd⟩
          refine ⟨k * (p0 : H) * g, ?_, ?_⟩
          · simp only [mul_smul]
            have hpbase : (p0 : H) • baseS = baseS := by
              apply Subtype.ext
              change (p0 : H) • inf = inf
              rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
              exact Subgroup.le_normalizer p0.property
            rw [hg, hpbase, hk]
          · simp only [mul_smul]
            rw [hp0, smul_inv_smul]
        have hzeroS_ne_base : zeroS ≠ baseS := by
          intro heq
          exact hzero_ne_inf (congrArg Subtype.val heq)
        let : Nontrivial S :=
          ⟨⟨zeroS, baseS, hzeroS_ne_base⟩⟩
        have htwo' := (MulAction.is_two_pretransitive_iff.mp htwo)
          hzeroS_ne_base.symm hzeroS_ne_base
        rcases htwo' with ⟨h, hinf, hzero⟩
        have : MulAction.IsPreprimitive H S :=
          MulAction.isPreprimitive_of_is_two_pretransitive htwo
        have hcoatom :
            IsCoatom (MulAction.stabilizer H baseS) :=
          MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive H baseS
        rw [hstabilizer_base] at hcoatom
        have hgen : NP ⊔ Subgroup.zpowers h = ⊤ := by
          rcases hcoatom.le_iff.mp le_sup_left with htop | heq
          · exact htop
          · exfalso
            have hhNP : h ∈ NP := by
              rw [← heq]
              exact (show Subgroup.zpowers h ≤ NP ⊔ Subgroup.zpowers h from
                le_sup_right) (Subgroup.mem_zpowers h)
            have hhfix : h • inf = inf := by
              rw [← MulAction.mem_stabilizer_iff, hstabilizer_inf]
              exact hhNP
            exact hzero_ne_inf ((congrArg Subtype.val hinf).symm.trans hhfix)
        refine ⟨h, congrArg Subtype.val hinf,
          congrArg Subtype.val hzero, hcover, hgen⟩
      have hPGL_embedding
          (hKcard : Nat.card K = p ^ m)
          (hswap : H) (hswap_inf : hswap • inf = zero)
          (hswap_zero : hswap • zero = inf)
          (hcover : ∀ z : S, (z : Point) ≠ inf →
            ∃ w : W, (z : Point) = affine (w : F))
          (hgen : NP ⊔ Subgroup.zpowers hswap = ⊤) :
          ∃ phi : H →* Matrix.ProjGenLinGroup (Fin 2) K,
            Function.Injective phi ∧
              ∃ c : Matrix.ProjGenLinGroup (Fin 2) F, ∀ h : H,
                h826_pglMap K.subtype (phi h) =
                  c * h826_pslToPGL (h : PSL2MatrixGroup F) * c⁻¹ := by
        let scalarMap : K → W := fun a =>
          ⟨(a : F) * (x0 : F), a.property (x0 : F) x0.property⟩
        have hscalarMap_inj : Function.Injective scalarMap := by
          intro a b hab
          apply Subtype.ext
          have hval := congrArg Subtype.val hab
          exact mul_right_cancel₀ hx0_val_ne_zero hval
        have hscalarMap_card : Nat.card K = Nat.card W := by
          rw [hKcard, hWcard]
        have hscalarMap_surj : Function.Surjective scalarMap :=
          (Nat.bijective_iff_injective_and_card scalarMap).mpr
            ⟨hscalarMap_inj, hscalarMap_card⟩ |>.2
        have hW_span (w : W) :
            ∃ k : K, (w : F) = (k : F) * (x0 : F) := by
          obtain ⟨k, hk⟩ := hscalarMap_surj w
          exact ⟨k, congrArg Subtype.val hk.symm⟩
        have haffine_ne_inf (w : W) : affine (w : F) ≠ inf := by
          intro hwi
          dsimp only [affine, inf] at hwi
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hwi with
            ⟨a, ha⟩
          have h1 := congrFun ha (1 : Fin 2)
          simp at h1
        let D : GL (Fin 2) F :=
          Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(x0 : F), 0; 0, 1]
            (by simp [Matrix.det_fin_two, hx0_val_ne_zero])
        let Di : GL (Fin 2) F :=
          Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(x0 : F)⁻¹, 0; 0, 1]
            (by simp [Matrix.det_fin_two, hx0_val_ne_zero])
        have hDi : Di = D⁻¹ := by
          apply eq_inv_of_mul_eq_one_right
          apply Matrix.GeneralLinearGroup.ext
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [D, Di, Matrix.mul_apply, hx0_ne_zero]
        let iotaF : PSL2MatrixGroup F →*
            Matrix.ProjGenLinGroup (Fin 2) F :=
          h826_pslToPGL
        let dPGL : Matrix.ProjGenLinGroup (Fin 2) F :=
          Matrix.ProjGenLinGroup.mk D
        let toF : H →* Matrix.ProjGenLinGroup (Fin 2) F :=
          (MulAut.conj dPGL⁻¹).toMonoidHom.comp
            (iotaF.comp conjH')
        let j : Matrix.ProjGenLinGroup (Fin 2) K →*
            Matrix.ProjGenLinGroup (Fin 2) F :=
          h826_pglMap K.subtype
        have hj_injective : Function.Injective j :=
          h826_pglMap_injective K.subtype K.subtype_injective
        let L : Subgroup H := j.range.comap toF
        have hP_le_L : (P : Subgroup H) ≤ L := by
          intro x hxP
          have hxU : conjH' x ∈ U :=
            hP_map_conjH'_le_U
              (Subgroup.mem_map_of_mem conjH' hxP)
          rw [hU_range] at hxU
          rcases hxU with ⟨w, hw⟩
          have hwW : w ∈ W := by
            change unipotent.toMonoidHom w ∈ P0
            rw [hw]
            exact Subgroup.mem_map_of_mem conjH' hxP
          obtain ⟨k, hk⟩ := hW_span ⟨w, hwW⟩
          let Usl : Matrix.SpecialLinearGroup (Fin 2) F :=
            ⟨!![1, w; 0, 1], by simp [Matrix.det_fin_two]⟩
          let Ak : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![1, k; 0, 1] (by simp [Matrix.det_fin_two])
          have hmat :
              Di * Matrix.SpecialLinearGroup.toGL Usl * D =
                Matrix.GeneralLinearGroup.map K.subtype Ak := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i
            all_goals fin_cases j0
            all_goals simp [D, Di, Usl, Ak, Matrix.mul_apply,
              hx0_ne_zero, mul_comm]
            all_goals field_simp
            simpa [mul_comm] using hk
          change toF x ∈ j.range
          refine ⟨Matrix.ProjGenLinGroup.mk Ak, ?_⟩
          rw [h826_pglMap_mk]
          have hiota :
              iotaF (conjH' x) =
                Matrix.ProjGenLinGroup.mk
                  (Matrix.SpecialLinearGroup.toGL Usl) := by
            rw [← hw]
            change iotaF (unipotent (w : F)) =
              Matrix.ProjGenLinGroup.mk
                (Matrix.SpecialLinearGroup.toGL Usl)
            rw [hunipotent_matrix]
            exact h826_pslToPGL_mk Usl
          change
            Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.map K.subtype Ak) =
              dPGL⁻¹ * iotaF (conjH' x) * (dPGL⁻¹)⁻¹
          rw [hiota]
          have hd_inv :
              dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
            dsimp only [dPGL]
            rw [← map_inv, ← hDi]
          have hd_inv_inv :
              (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
                Matrix.ProjGenLinGroup.mk D := by
            rw [← map_inv, hDi, inv_inv]
          rw [hd_inv, hd_inv_inv]
          change
            Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.map K.subtype Ak) =
              Matrix.ProjGenLinGroup.mk Di *
                Matrix.ProjGenLinGroup.mk
                  (Matrix.SpecialLinearGroup.toGL Usl) *
                Matrix.ProjGenLinGroup.mk D
          rw [← map_mul, ← map_mul, hmat]
        have hcgen_mem_L : (cN : H) ∈ L := by
          let Bk : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![lambdaK0, 0; 0, 1]
              (by simp [Matrix.det_fin_two, hlambdaK0_ne_zero])
          let BF : GL (Fin 2) F :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![(lambdaU : F), 0; 0, 1]
              (by simp [Matrix.det_fin_two])
          let Rgl : GL (Fin 2) F :=
            Matrix.SpecialLinearGroup.toGL
              (⟨!![(r : F), 0; 0, (r⁻¹ : F)],
                  by simp [Matrix.det_fin_two]⟩ :
                Matrix.SpecialLinearGroup (Fin 2) F)
          have hmap_Bk :
              Matrix.GeneralLinearGroup.map K.subtype Bk = BF := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i <;> fin_cases j0 <;>
              simp [Bk, BF, lambdaK0, lambdaU]
          have hBF_scalar :
              BF =
                Matrix.GeneralLinearGroup.scalar (Fin 2) r * Rgl := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i <;> fin_cases j0 <;>
              simp [BF, Rgl, lambdaU,
                Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, pow_two]
          have hBF_comm_D : Di * BF * D = BF := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i
            all_goals fin_cases j0
            all_goals simp [D, Di, BF, Matrix.mul_apply]
            all_goals field_simp
          change toF (cN : H) ∈ j.range
          refine ⟨Matrix.ProjGenLinGroup.mk Bk, ?_⟩
          rw [h826_pglMap_mk, hmap_Bk]
          have hiota :
              iotaF (conjH' (cN : H)) =
                Matrix.ProjGenLinGroup.mk BF := by
            rw [hcgen_split, hsplitTorus_matrix,
              h826_pslToPGL_mk]
            rw [hBF_scalar, map_mul,
              Matrix.ProjGenLinGroup.mk_scalar, one_mul]
          change
            Matrix.ProjGenLinGroup.mk BF =
              dPGL⁻¹ * iotaF (conjH' (cN : H)) * (dPGL⁻¹)⁻¹
          rw [hiota]
          have hd_inv :
              dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
            dsimp only [dPGL]
            rw [← map_inv, ← hDi]
          have hd_inv_inv :
              (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
                Matrix.ProjGenLinGroup.mk D := by
            rw [← map_inv, hDi, inv_inv]
          rw [hd_inv, hd_inv_inv]
          change Matrix.ProjGenLinGroup.mk BF =
            Matrix.ProjGenLinGroup.mk Di *
              Matrix.ProjGenLinGroup.mk BF *
                Matrix.ProjGenLinGroup.mk D
          rw [← map_mul, ← map_mul, hBF_comm_D]
        have hswap_mem_L : hswap ∈ L := by
          rcases QuotientGroup.mk'_surjective
              (Subgroup.center
                (Matrix.SpecialLinearGroup (Fin 2) F))
              (conjH' hswap) with ⟨A, hA⟩
          have hA00 :
              (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
            have hfix := hswap_inf
            change rho (conjH' hswap) inf = zero at hfix
            rw [← hA, hrho_apply] at hfix
            dsimp only [inf, zero] at hfix
            rw [Projectivization.smul_mk] at hfix
            rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
              ⟨a, ha⟩
            have h0 := congrFun ha (0 : Fin 2)
            simpa [Matrix.GeneralLinearGroup.toLin_apply,
              Matrix.mulVec, dotProduct] using h0.symm
          have hA11 :
              (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
            have hfix := hswap_zero
            change rho (conjH' hswap) zero = inf at hfix
            rw [← hA, hrho_apply] at hfix
            dsimp only [inf, zero] at hfix
            rw [Projectivization.smul_mk] at hfix
            rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hfix with
              ⟨a, ha⟩
            have h1 := congrFun ha (1 : Fin 2)
            simpa [Matrix.GeneralLinearGroup.toLin_apply,
              Matrix.mulVec, dotProduct] using h1.symm
          have hA10_ne :
              (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
            intro hc
            have hdet := A.property
            rw [Matrix.det_fin_two, hA00, hA11, hc] at hdet
            norm_num at hdet
          have haffine_x0_mem : affine (x0 : F) ∈ S := by
            rcases x0.property with ⟨g, hgP, hg⟩
            refine ⟨g * hswap, ?_⟩
            change (g * hswap) • inf = affine (x0 : F)
            rw [mul_smul, hswap_inf]
            change rho (conjH' g) zero = affine (x0 : F)
            rw [hg]
            change unipotent (x0 : F) • affine 0 = affine (x0 : F)
            simpa using hunipotent_affine (x0 : F) 0
          let zswap : S :=
            ⟨hswap • affine (x0 : F), by
              rcases haffine_x0_mem with ⟨g, hg⟩
              change g • inf = affine (x0 : F) at hg
              refine ⟨hswap * g, ?_⟩
              change (hswap * g) • inf = hswap • affine (x0 : F)
              rw [mul_smul, hg]⟩
          have hzswap_ne_inf : (zswap : Point) ≠ inf := by
            intro hz
            have hzero_eq :
                hswap • zero = hswap • affine (x0 : F) := by
              change hswap • zero = (zswap : Point)
              rw [hswap_zero, hz]
            have hzero_affine : zero = affine (x0 : F) :=
              smul_left_cancel hswap hzero_eq
            have hxzero : (0 : F) = (x0 : F) := by
              apply haffine_injective
              simpa [affine, zero] using hzero_affine
            exact hx0_ne_zero (Subtype.ext hxzero.symm)
          obtain ⟨w, hw⟩ := hcover zswap hzswap_ne_inf
          obtain ⟨k, hk⟩ := hW_span w
          have hk_ne_zero : k ≠ 0 := by
            intro hk0
            have hwzero : (w : F) = 0 := by simp [hk, hk0]
            have hz_zero : (zswap : Point) = zero := by
              rw [hw, hwzero]
            have hinf_affine :
                hswap • inf = hswap • affine (x0 : F) := by
              rw [hswap_inf, ← hz_zero]
            have hia : inf = affine (x0 : F) :=
              smul_left_cancel hswap hinf_affine
            exact (haffine_ne_inf x0) hia.symm
          have hact :
              rho (QuotientGroup.mk'
                (Subgroup.center
                  (Matrix.SpecialLinearGroup (Fin 2) F)) A)
                  (affine (x0 : F)) =
                affine (w : F) := by
            rw [hA]
            exact hw
          dsimp only [affine] at hact
          rw [hrho_apply, Projectivization.smul_mk] at hact
          rcases (Projectivization.mk_eq_mk_iff' F _ _ _ _).mp hact with
            ⟨a0, ha0⟩
          have ha0_0 := congrFun ha0 (0 : Fin 2)
          have ha0_1 := congrFun ha0 (1 : Fin 2)
          simp [Matrix.mulVec, dotProduct, hA00, hA11] at ha0_0 ha0_1
          let Ak : GL (Fin 2) K :=
            Matrix.GeneralLinearGroup.mkOfDetNeZero
              !![0, k; 1, 0]
              (by simp [Matrix.det_fin_two, hk_ne_zero])
          let scale : Fˣ := Units.mk0
            ((A : Matrix (Fin 2) (Fin 2) F) 1 0 * (x0 : F))
            (mul_ne_zero hA10_ne hx0_val_ne_zero)
          have hmat :
              Di * Matrix.SpecialLinearGroup.toGL A * D =
                Matrix.GeneralLinearGroup.scalar (Fin 2) scale *
                  Matrix.GeneralLinearGroup.map K.subtype Ak := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j0
            fin_cases i <;> fin_cases j0
            · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
                dotProduct, hA00]
            · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
                dotProduct, hA00]
              rw [← ha0_0, ha0_1, hk]
              field_simp
            · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
                dotProduct, hA11]
            · simp [D, Di, Ak, scale, Matrix.mul_apply, Matrix.vecMul,
                dotProduct, hA11]
          change toF hswap ∈ j.range
          refine ⟨Matrix.ProjGenLinGroup.mk Ak, ?_⟩
          rw [h826_pglMap_mk]
          have hiota :
              iotaF (conjH' hswap) =
                Matrix.ProjGenLinGroup.mk
                  (Matrix.SpecialLinearGroup.toGL A) := by
            rw [← hA]
            exact h826_pslToPGL_mk A
          change
            Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.map K.subtype Ak) =
              dPGL⁻¹ * iotaF (conjH' hswap) * (dPGL⁻¹)⁻¹
          rw [hiota]
          have hd_inv :
              dPGL⁻¹ = Matrix.ProjGenLinGroup.mk Di := by
            dsimp only [dPGL]
            rw [← map_inv, ← hDi]
          have hd_inv_inv :
              (Matrix.ProjGenLinGroup.mk Di)⁻¹ =
                Matrix.ProjGenLinGroup.mk D := by
            rw [← map_inv, hDi, inv_inv]
          rw [hd_inv, hd_inv_inv]
          change
            Matrix.ProjGenLinGroup.mk
                (Matrix.GeneralLinearGroup.map K.subtype Ak) =
              Matrix.ProjGenLinGroup.mk Di *
                Matrix.ProjGenLinGroup.mk
                  (Matrix.SpecialLinearGroup.toGL A) *
                Matrix.ProjGenLinGroup.mk D
          rw [← map_mul, ← map_mul, hmat, map_mul,
            Matrix.ProjGenLinGroup.mk_scalar, one_mul]
        have hNP_le_L : NP ≤ L := by
          have hPN_le : PN ≤ L.comap NP.subtype := by
            intro n hn
            apply hP_le_L
            exact hn
          have hC_le : C ≤ L.comap NP.subtype := by
            intro d hd
            let dc : C := ⟨d, hd⟩
            rcases hcgen dc with ⟨z, hz⟩
            have hzNP : (cgen : NP) ^ z = d :=
              congrArg Subtype.val hz
            have hzH : ((cgen : NP) : H) ^ z = (d : H) :=
              congrArg Subtype.val hzNP
            change ((d : NP) : H) ∈ L
            rw [← hzH]
            simpa only [cN] using L.zpow_mem hcgen_mem_L z
          have htop_le : (⊤ : Subgroup NP) ≤ L.comap NP.subtype := by
            rw [← hcomp.sup_eq_top]
            exact sup_le hPN_le hC_le
          intro n hn
          change (⟨n, hn⟩ : NP) ∈ L.comap NP.subtype
          exact htop_le (Subgroup.mem_top (⟨n, hn⟩ : NP))
        have hLtop : L = ⊤ := by
          apply top_unique
          rw [← hgen]
          exact sup_le hNP_le_L
            (Subgroup.zpowers_le.mpr hswap_mem_L)
        have htoF_range : ∀ x : H, toF x ∈ j.range := by
          intro x
          change x ∈ L
          rw [hLtop]
          trivial
        let toRange : H →* j.range :=
          toF.codRestrict j.range htoF_range
        let eJ : Matrix.ProjGenLinGroup (Fin 2) K ≃* j.range :=
          MulEquiv.ofBijective j.rangeRestrict
            ⟨fun a b hab => hj_injective (congrArg Subtype.val hab),
              MonoidHom.rangeRestrict_surjective j⟩
        let phi : H →* Matrix.ProjGenLinGroup (Fin 2) K :=
          eJ.symm.toMonoidHom.comp toRange
        have hphi_injective : Function.Injective phi := by
          intro x y hxy
          apply hconjH'_injective
          apply h826_pslToPGL_injective
          apply (MulAut.conj dPGL⁻¹).injective
          change toF x = toF y
          have hrange : toRange x = toRange y := by
            apply eJ.symm.injective
            exact hxy
          exact congrArg Subtype.val hrange
        obtain ⟨gH, hgH⟩ := hconjH_conj
        let c : Matrix.ProjGenLinGroup (Fin 2) F :=
          dPGL⁻¹ * iotaF (u⁻¹ * gH)
        refine ⟨phi, hphi_injective, c, ?_⟩
        intro h
        have hphi_eq : j (phi h) = toF h := by
          have he := eJ.apply_symm_apply (toRange h)
          have he' : eJ (phi h) = toRange h := by
            simp [phi]
          exact congrArg Subtype.val he'
        change j (phi h) = c * iotaF (h : PSL2MatrixGroup F) * c⁻¹
        rw [hphi_eq]
        change
          dPGL⁻¹ * iotaF (u⁻¹ * conjH h * (u⁻¹)⁻¹) * (dPGL⁻¹)⁻¹ =
            (dPGL⁻¹ * iotaF (u⁻¹ * gH)) *
              iotaF (h : PSL2MatrixGroup F) *
                (dPGL⁻¹ * iotaF (u⁻¹ * gH))⁻¹
        rw [hgH]
        simp only [map_mul, map_inv]
        group
      have htwo_torus_core :
          (p ^ m = 3 ∧ Nat.card H = 60 ∧
            (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
            Nat.card (Sylow 5 H) = 6 ∧
            Function.Injective (MulAction.toPermHom H (Sylow 5 H))) ∨
          (2 * m ∣ f ∧ Nonempty
            (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) ∧
            Nonempty (SubfieldConjugacyWitness p m H)) ∨
          (m ∣ f ∧ Nonempty
            (H ≃* PSL2MatrixGroup (GaloisField p m)) ∧
            Nonempty (SubfieldConjugacyWitness p m H)) := by
        have horder_cases :=
          h826_group_order_cases
            (p ^ m) (Nat.card (Z i0)) (Nat.card (Z i1))
            (Nat.card H) NP.index (NZ i0).index (NZ i1).index
            hpm_gt (hnontrivial i0) (hnontrivial i1)
            ((hcoprime i0).pow_left m) ((hcoprime i1).pow_left m)
            hi0_dvd_sub_one htorus_gcd
            (by simpa only [c] using hH_eq_c)
            hNP_index_factor hi0_factor hi1_factor hcount_pair
        rcases horder_cases with hsmall | hfull | hhalf
        · left
          rcases hsmall with ⟨hpm3, hi0card, hi1card, hcard60⟩
          have hrestriction : p = 5 ∨ 5 ∣ p ^ (2 * f) - 1 := by
            by_cases hp5 : p = 5
            · exact Or.inl hp5
            · right
              have hfive_torus :
                  5 ∣ (Nat.card F - 1) /
                      Nat.gcd (Nat.card F - 1) 2 ∨
                    5 ∣ (Nat.card F + 1) /
                      Nat.gcd (Nat.card F - 1) 2 := by
                have h := hdivides i1
                rw [hi1card] at h
                exact h
              have hgcd_dvd_add :
                  Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
                have hadd := Nat.dvd_add
                  (Nat.gcd_dvd_left (Nat.card F - 1) 2)
                  (Nat.gcd_dvd_right (Nat.card F - 1) 2)
                have hFpos : 0 < Nat.card F := Nat.card_pos
                convert hadd using 1
                all_goals omega
              have hfive_factor :
                  5 ∣ Nat.card F - 1 ∨ 5 ∣ Nat.card F + 1 := by
                rcases hfive_torus with hminus | hplus
                · exact Or.inl (dvd_trans hminus
                    (Nat.div_dvd_of_dvd
                      (Nat.gcd_dvd_left (Nat.card F - 1) 2)))
                · exact Or.inr (dvd_trans hplus
                    (Nat.div_dvd_of_dvd hgcd_dvd_add))
              have hfive_sq : 5 ∣ Nat.card F ^ 2 - 1 := by
                have hfactor :
                    Nat.card F ^ 2 - 1 =
                      (Nat.card F - 1) * (Nat.card F + 1) := by
                  simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
                rw [hfactor]
                rcases hfive_factor with hminus | hplus
                · exact dvd_mul_of_dvd_left hminus _
                · exact dvd_mul_of_dvd_right hplus _
              rw [hFcard, ← pow_mul] at hfive_sq
              simpa [mul_comm] using hfive_sq
          have hi1index : (Z i1).index = 12 := by
            have hmul := (Z i1).card_mul_index
            rw [hi1card, hcard60] at hmul
            apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5)
            simpa using hmul
          have hNZi1index : (NZ i1).index = 6 := by
            have hfactor := hi1_factor
            rw [hi1card, hcard60] at hfactor
            apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 10)
            norm_num at hfactor ⊢
            exact hfactor
          let : Fact (Nat.Prime 5) := ⟨by decide⟩
          let hZi1P : IsPGroup 5 (Z i1) :=
            IsPGroup.of_card (n := 1) (by simpa using hi1card)
          let Q : Sylow 5 H := hZi1P.toSylow (by
            rw [hi1index]
            norm_num)
          have hSylow5 : Nat.card (Sylow 5 H) = 6 := by
            calc
              Nat.card (Sylow 5 H) =
                  (Subgroup.normalizer (Q : Set H)).index :=
                Q.card_eq_index_normalizer
              _ = (NZ i1).index := by rfl
              _ = 6 := hNZi1index
          let act := MulAction.toPermHom H (Sylow 5 H)
          have hker_le_normalizer (R : Sylow 5 H) :
              act.ker ≤ Subgroup.normalizer (R : Set H) := by
            intro x hx
            have hxperm : act x = 1 := hx
            have hxfix : x • R = R := by
              have h := DFunLike.congr_fun hxperm R
              simpa [act] using h
            exact Sylow.smul_eq_iff_mem_normalizer.mp hxfix
          have hnormalizer_card_ten :
              Nat.card (Subgroup.normalizer (Q : Set H)) = 10 := by
            have hQindex :
                (Subgroup.normalizer (Q : Set H)).index = 6 := by
              calc
                (Subgroup.normalizer (Q : Set H)).index =
                    Nat.card (Sylow 5 H) :=
                  Q.card_eq_index_normalizer.symm
                _ = 6 := hSylow5
            have hmul :=
              (Subgroup.normalizer (Q : Set H)).card_mul_index
            rw [hQindex, hcard60] at hmul
            apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 6)
            simpa using hmul
          have hker_card_dvd_ten : Nat.card act.ker ∣ 10 := by
            have hdvd : Nat.card act.ker ∣
                Nat.card (Subgroup.normalizer (Q : Set H)) :=
              Subgroup.card_dvd_of_le (hker_le_normalizer Q)
            rw [hnormalizer_card_ten] at hdvd
            exact hdvd
          have hno_sylow_le_ker (R : Sylow 5 H) :
              ¬ (R : Subgroup H) ≤ act.ker := by
            intro hRker
            let : Fintype (Sylow 5 H) := Fintype.ofFinite _
            obtain ⟨S, hSR⟩ :=
              Fintype.exists_ne_of_one_lt_card
                (by simpa [Nat.card_eq_fintype_card] using
                  (show 1 < Nat.card (Sylow 5 H) by
                    rw [hSylow5]
                    norm_num)) R
            have hRnormalizesS :
                (R : Subgroup H) ≤ Subgroup.normalizer (S : Set H) := by
              intro x hx
              exact hker_le_normalizer S (hRker hx)
            have hsupP :
                IsPGroup 5
                  ((R : Subgroup H) ⊔ (S : Subgroup H) : Subgroup H) :=
              R.isPGroup'.to_sup_of_normal_right' S.isPGroup' hRnormalizesS
            have hsup_eq :
                (R : Subgroup H) ⊔ (S : Subgroup H) = S :=
              S.is_maximal' hsupP le_sup_right
            have hRleS : (R : Subgroup H) ≤ S := by
              calc
                (R : Subgroup H) ≤ (R : Subgroup H) ⊔ (S : Subgroup H) :=
                  le_sup_left
                _ = S := hsup_eq
            exact hSR (Sylow.ext (R.is_maximal' S.isPGroup' hRleS))
          have hfive_not_dvd_ker : ¬ 5 ∣ Nat.card act.ker := by
            intro hfive
            obtain ⟨x, hxorder⟩ :=
              exists_prime_orderOf_dvd_card' 5 hfive
            have hxHorder : orderOf (x : H) = 5 :=
              (Subgroup.orderOf_coe x).trans hxorder
            have hXisP : IsPGroup 5 (Subgroup.zpowers (x : H)) :=
              IsPGroup.of_card
                (((Nat.card_zpowers (x : H)).trans hxHorder).trans
                  (pow_one 5).symm)
            obtain ⟨R, hXR⟩ := hXisP.exists_le_sylow
            have hXcard : Nat.card (Subgroup.zpowers (x : H)) = 5 :=
              (Nat.card_zpowers (x : H)).trans hxHorder
            have hRcard : Nat.card R = 5 := by
              calc
                Nat.card R = Nat.card Q :=
                  Nat.card_congr (Sylow.equiv R Q).toEquiv
                _ = 5 := by
                  change Nat.card (Z i1) = 5
                  exact hi1card
            have hXR_eq :
                Subgroup.zpowers (x : H) = (R : Subgroup H) :=
              Subgroup.eq_of_le_of_card_ge hXR (by rw [hXcard, hRcard])
            apply hno_sylow_le_ker R
            rw [← hXR_eq]
            intro y hy
            rcases hy with ⟨j, rfl⟩
            exact act.ker.zpow_mem x.2 j
          have hker_card_cases :
              Nat.card act.ker = 1 ∨ Nat.card act.ker = 2 := by
            have hpos : 0 < Nat.card act.ker := Nat.card_pos
            have hle : Nat.card act.ker ≤ 10 :=
              Nat.le_of_dvd (by norm_num) hker_card_dvd_ten
            interval_cases h : Nat.card act.ker <;> norm_num [h] at *
          have hker_bot : act.ker = ⊥ := by
            rcases hker_card_cases with hker_one | hker_two
            · exact Subgroup.card_eq_one.mp hker_one
            · exfalso
              obtain ⟨y, hyorder⟩ :=
                exists_prime_orderOf_dvd_card' 5 (by
                  rw [hcard60]
                  norm_num)
              obtain ⟨c0, hc0order⟩ :=
                exists_prime_orderOf_dvd_card' 2 (by rw [hker_two])
              have hc0ne : c0 ≠ 1 := by
                intro hc
                rw [hc, orderOf_one] at hc0order
                norm_num at hc0order
              obtain ⟨c1, hc1ne, hc1unique⟩ :=
                (Nat.card_eq_two_iff' (1 : act.ker)).mp hker_two
              have hc0eq : c0 = c1 := hc1unique c0 hc0ne
              have hc0central : (c0 : H) ∈ Subgroup.center H := by
                rw [Subgroup.mem_center_iff]
                intro g
                let d : act.ker :=
                  ⟨g * (c0 : H) * g⁻¹,
                    (inferInstance : act.ker.Normal).conj_mem
                      (c0 : H) c0.2 g⟩
                have hdne : d ≠ 1 := by
                  intro hd
                  have hdval := congrArg Subtype.val hd
                  change g * (c0 : H) * g⁻¹ = 1 at hdval
                  apply hc0ne
                  apply Subtype.ext
                  calc
                    (c0 : H) = g⁻¹ * (g * (c0 : H) * g⁻¹) * g := by group
                    _ = 1 := by rw [hdval]; simp
                have hdeq : d = c0 := by
                  rw [hc0eq]
                  exact hc1unique d hdne
                have hdval := congrArg Subtype.val hdeq
                change g * (c0 : H) * g⁻¹ = (c0 : H) at hdval
                calc
                  g * (c0 : H) = (g * (c0 : H) * g⁻¹) * g := by group
                  _ = (c0 : H) * g := by rw [hdval]
              have hc0Horder : orderOf (c0 : H) = 2 :=
                (Subgroup.orderOf_coe c0).trans hc0order
              have hyHorder : orderOf (y : H) = 5 :=
                hyorder
              have hcomm : Commute (c0 : H) (y : H) :=
                (Subgroup.mem_center_iff.mp hc0central (y : H)).symm
              have hcop :
                  Nat.Coprime (orderOf (c0 : H)) (orderOf (y : H)) := by
                rw [hc0Horder, hyHorder]
                norm_num
              let x : H := (c0 : H) * (y : H)
              have hxorder : orderOf x = 10 := by
                dsimp only [x]
                rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop,
                  hc0Horder, hyHorder]
              have hxne : x ≠ 1 := by
                intro hx
                rw [hx, orderOf_one] at hxorder
                norm_num at hxorder
              obtain ⟨A, hxA, _⟩ :=
                huppert_II_8_22_unique_family hFcard H Z
                  hcyclic hnontrivial hcoprime hmaximal
                  hrepresentative hdistinct x hxne
              rcases A with Qp | z
              · have hxdvd : orderOf x ∣ Nat.card Qp :=
                  (Qp : Subgroup H).orderOf_dvd_natCard hxA
                have hQpcard : Nat.card Qp = 3 := by
                  calc
                    Nat.card Qp = Nat.card P :=
                      Nat.card_congr (Sylow.equiv Qp P).toEquiv
                    _ = 3 := hPm.trans hpm3
                rw [hxorder, hQpcard] at hxdvd
                norm_num at hxdvd
              · have hxdvd : orderOf x ∣ Nat.card z.2.1 :=
                  z.2.1.orderOf_dvd_natCard hxA
                obtain ⟨g, hg⟩ := z.2.2
                have hzcard : Nat.card z.2.1 = Nat.card (Z z.1) := by
                  rw [hg, Subgroup.card_map_of_injective
                    (MulAut.conj g).injective]
                have hz_cases : z.1 = i0 ∨ z.1 = i1 := by
                  have hzmem : z.1 ∈ ({i0, i1} : Finset (Fin 2)) := by
                    rw [huniv_pair]
                    simp
                  simpa using hzmem
                rw [hxorder, hzcard] at hxdvd
                rcases hz_cases with hzi0 | hzi1
                · rw [hzi0, hi0card] at hxdvd
                  norm_num at hxdvd
                · rw [hzi1, hi1card] at hxdvd
                  norm_num at hxdvd
          have hfaithful : Function.Injective act := by
            rw [← MonoidHom.ker_eq_bot_iff]
            exact hker_bot
          exact ⟨hpm3, hcard60, hrestriction, hSylow5, hfaithful⟩
        · have hKcard : Nat.card K = p ^ m := by
            apply Nat.le_antisymm hK_le_q
            calc
              p ^ m = (p ^ m - 1) + 1 :=
                (Nat.sub_add_cancel (Nat.zero_lt_of_lt hpm_gt)).symm
              _ = Nat.card (Z i0) + 1 := by rw [hfull.1]
              _ ≤ Nat.card K := hK_lower
          have hS_card : Nat.card S = p ^ m + 1 := by
            have hNPindex : NP.index = p ^ m + 1 := by
              have hqsubpos : 0 < p ^ m - 1 := by omega
              apply Nat.eq_of_mul_eq_mul_left
                (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
                  hqsubpos)
              calc
                (p ^ m * (p ^ m - 1)) * NP.index =
                    Nat.card NP * NP.index := by rw [hNPcard, hfull.1]
                _ = Nat.card H := NP.card_mul_index
                _ = (p ^ m + 1) * p ^ m * (p ^ m - 1) := hfull.2.2
                _ = (p ^ m * (p ^ m - 1)) * (p ^ m + 1) := by ring
            have hindex_card :=
              MulAction.index_stabilizer_of_transitive H baseS
            rw [hstabilizer_base, hNPindex] at hindex_card
            exact hindex_card.symm
          obtain ⟨hswap, hswap_inf, hswap_zero, hcover, hgen⟩ :=
            hsubline_swap hS_card
          have hmdiv : m ∣ f := by
            have hsplit_dvd :
                p ^ m - 1 ∣
                  (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
              rw [← hfull.1]
              exact hi0_dvd_ambient
            have hpowdiv : p ^ m - 1 ∣ p ^ f - 1 := by
              rw [← hFcard]
              exact dvd_trans hsplit_dvd
                (Nat.div_dvd_of_dvd
                  (Nat.gcd_dvd_left (Nat.card F - 1) 2))
            exact h826_exponent_dvd_of_pow_sub_one_dvd
              (Fact.out : p.Prime).two_le hpowdiv
          obtain ⟨phi, hphi, conjugator, hphi_conj⟩ :=
            hPGL_embedding hKcard hswap hswap_inf hswap_zero hcover hgen
          have hwitness : Nonempty (SubfieldConjugacyWitness p m H) :=
            ⟨{ K := K
               card_eq := hKcard
               phi := phi
               phi_injective := hphi
               conjugator := conjugator
               map_phi := hphi_conj }⟩
          have hPGLcard :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                p ^ m * ((p ^ m) ^ 2 - 1) := by
            rw [h826_card_pgl2, hKcard]
          have hfactor :
              (p ^ m) ^ 2 - 1 =
                (p ^ m - 1) * (p ^ m + 1) := by
            simpa [mul_comm] using Nat.sq_sub_sq (p ^ m) 1
          have hFullCardEq :
              Nat.card H =
                Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) := by
            rw [hfull.2.2, hPGLcard, hfactor]
            ring
          let : Fintype K := Fintype.ofFinite K
          let : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
            Finite.of_surjective Matrix.ProjGenLinGroup.mk
              Matrix.ProjGenLinGroup.mk_surjective
          let eHPGL :
              H ≃* Matrix.ProjGenLinGroup (Fin 2) K :=
            MulEquiv.ofBijective phi
              ((Nat.bijective_iff_injective_and_card phi).2
                ⟨hphi, hFullCardEq⟩)
          by_cases hp_two : p = 2
          · subst p
            let : CharP K 2 :=
              charP_of_card_eq_prime_pow (by simpa using hKcard)
            let : Algebra (ZMod 2) K := ZMod.algebra K 2
            have htwozero : (2 : K) = 0 :=
              CharP.cast_eq_zero K 2
            have hneg_one : (-1 : K) = 1 := by
              apply (neg_eq_iff_add_eq_zero).2
              rw [show (1 : K) + 1 = 2 by norm_num, htwozero]
            have hcenter :
                Nat.card
                    (Subgroup.center
                      (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 :=
              huppert614_card_center_of_neg_one_eq_one hneg_one
            have hPSLcard := huppert614_card_psl_mul_center (K := K)
            rw [hcenter, mul_one] at hPSLcard
            have hPSLPGLcard :
                Nat.card (PSL2MatrixGroup K) =
                  Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) :=
              hPSLcard.trans (h826_card_pgl2 (K := K)).symm
            let ePSLPGL :
                PSL2MatrixGroup K ≃*
                  Matrix.ProjGenLinGroup (Fin 2) K :=
              MulEquiv.ofBijective h826_pslToPGL
                ((Nat.bijective_iff_injective_and_card
                    (h826_pslToPGL (K := K))).2
                  ⟨h826_pslToPGL_injective, hPSLPGLcard⟩)
            let eK :=
              GaloisField.algEquivGaloisField 2 m hKcard
            let eHPSL : H ≃* PSL2MatrixGroup K :=
              eHPGL.trans ePSLPGL.symm
            exact Or.inr (Or.inr
              ⟨hmdiv, ⟨eHPSL.trans (h826_pslEquiv eK.toRingEquiv)⟩,
                hwitness⟩)
          · have hp_odd : Odd p :=
              (Fact.out : p.Prime).odd_of_ne_two hp_two
            have hFodd : Odd (Nat.card F) := by
              rw [hFcard]
              exact hp_odd.pow
            have hF_two_dvd : 2 ∣ Nat.card F - 1 :=
              even_iff_two_dvd.mp (Nat.Odd.sub_odd hFodd odd_one)
            have hFgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hF_two_dvd (dvd_refl 2))
            have hsplit_dvd :
                p ^ m - 1 ∣ (p ^ f - 1) / 2 := by
              rw [← hFcard, ← hFgcd, ← hfull.1]
              exact hi0_dvd_ambient
            have hpow_two_dvd : 2 ∣ p ^ f - 1 := by
              rwa [← hFcard]
            have htwo_split_dvd :
                2 * (p ^ m - 1) ∣ p ^ f - 1 :=
              Nat.mul_dvd_of_dvd_div hpow_two_dvd hsplit_dvd
            have hqminus_dvd : p ^ m - 1 ∣ p ^ f - 1 :=
              dvd_trans hsplit_dvd
                (Nat.div_dvd_of_dvd hpow_two_dvd)
            have htwo_dvd_quot :
                2 ∣ (p ^ f - 1) / (p ^ m - 1) :=
              (Nat.dvd_div_iff_mul_dvd hqminus_dvd).2
                (by simpa [mul_comm] using htwo_split_dvd)
            obtain ⟨k, hfk⟩ := hmdiv
            have hquotEven :
                Even (((p ^ m) ^ k - 1) / (p ^ m - 1)) := by
              rw [hfk, pow_mul] at htwo_dvd_quot
              exact even_iff_two_dvd.mpr htwo_dvd_quot
            have hsumEven :
                Even (∑ i ∈ Finset.range k, (p ^ m) ^ i) := by
              rw [Nat.geomSum_eq (by omega)]
              exact hquotEven
            have hkEven : Even k := by
              rw [Finset.even_sum_iff_even_card_odd] at hsumEven
              simpa [(hp_odd.pow : Odd (p ^ m)).pow] using hsumEven
            have htwo_m_div : 2 * m ∣ f := by
              rcases hkEven with ⟨r0, hr0⟩
              refine ⟨r0, ?_⟩
              rw [hfk, hr0]
              ring
            let : Algebra (ZMod p) K := ZMod.algebra K p
            let eK :=
              GaloisField.algEquivGaloisField p m hKcard
            let pglHom :
                Matrix.ProjGenLinGroup (Fin 2) K →*
                  Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m) :=
              h826_pglMap eK.toRingEquiv.toRingHom
            let : Finite
                (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) :=
              Finite.of_surjective Matrix.ProjGenLinGroup.mk
                Matrix.ProjGenLinGroup.mk_surjective
            have hPGLFieldCard :
                Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                  Nat.card
                    (Matrix.ProjGenLinGroup (Fin 2)
                      (GaloisField p m)) := by
              rw [h826_card_pgl2, h826_card_pgl2,
                Nat.card_congr eK.toEquiv]
            let ePGL :
                Matrix.ProjGenLinGroup (Fin 2) K ≃*
                  Matrix.ProjGenLinGroup (Fin 2)
                    (GaloisField p m) :=
              MulEquiv.ofBijective pglHom
                ((Nat.bijective_iff_injective_and_card pglHom).2
                  ⟨h826_pglMap_injective _
                    eK.injective, hPGLFieldCard⟩)
            exact Or.inr (Or.inl
              ⟨htwo_m_div, ⟨eHPGL.trans ePGL⟩, hwitness⟩)
        · have hqodd : Odd (p ^ m) := hhalf.1.odd_of_right
          have hp_ne_two : p ≠ 2 := by
            intro hp
            subst p
            have hnot : ¬ 2 ∣ 2 ^ m :=
              Nat.prime_two.coprime_iff_not_dvd.mp hhalf.1.symm
            exact hnot (dvd_pow_self 2 hm_ne_zero)
          have hp_three : 3 ≤ p := by
            have hpgt := (Fact.out : p.Prime).one_lt
            omega
          have hq_two_dvd : 2 ∣ p ^ m - 1 :=
            even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one)
          have hzi0_twice :
              2 * Nat.card (Z i0) = p ^ m - 1 := by
              rw [hhalf.2.1, mul_comm]
              exact Nat.div_mul_cancel hq_two_dvd
          let : Algebra (ZMod p) K := ZMod.algebra K p
          have hKcard : Nat.card K = p ^ m := by
            let e := Module.finrank (ZMod p) K
            have hKpow : p ^ e = Nat.card K :=
              FiniteField.pow_finrank_eq_natCard p K
            have he_le_m : e ≤ m := by
              rw [← Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt,
                hKpow]
              exact hK_le_q
            obtain ⟨m0, hm0⟩ :=
              Nat.exists_eq_succ_of_ne_zero hm_ne_zero
            have hqeq : p ^ m = p ^ m0 * p := by
              rw [hm0, pow_succ]
            have hprev_lt_K : p ^ m0 < Nat.card K := by
              have hp_bound :
                  3 * p ^ m0 ≤ p ^ m := by
                rw [hqeq]
                simpa [mul_comm] using
                  Nat.mul_le_mul_left (p ^ m0) hp_three
              omega
            have heq : e = m := by
              by_contra hne
              have he_lt : e < m := lt_of_le_of_ne he_le_m hne
              have he_le_m0 : e ≤ m0 := by omega
              have hpow_le : p ^ e ≤ p ^ m0 :=
                Nat.pow_le_pow_right (Fact.out : p.Prime).pos he_le_m0
              rw [hKpow] at hpow_le
              omega
            rw [← hKpow, heq]
          have hS_card : Nat.card S = p ^ m + 1 := by
            have hcard_rewrite :
                Nat.card H =
                  (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) := by
              rw [hhalf.2.2.2, show Nat.gcd (p ^ m - 1) 2 = 2 from
                Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                  (Nat.dvd_gcd hq_two_dvd (dvd_refl 2))]
              exact Nat.mul_div_assoc ((p ^ m + 1) * p ^ m)
                hq_two_dvd
            have hNPindex : NP.index = p ^ m + 1 := by
              have hhalfpos : 0 < (p ^ m - 1) / 2 :=
                Nat.div_pos (by omega) (by norm_num)
              apply Nat.eq_of_mul_eq_mul_left
                (Nat.mul_pos (Nat.zero_lt_of_lt hpm_gt)
                  hhalfpos)
              calc
                (p ^ m * ((p ^ m - 1) / 2)) * NP.index =
                    Nat.card NP * NP.index := by
                      rw [hNPcard, hhalf.2.1]
                _ = Nat.card H := NP.card_mul_index
                _ = (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) :=
                  hcard_rewrite
                _ = (p ^ m * ((p ^ m - 1) / 2)) * (p ^ m + 1) := by ring
            have hindex_card :=
              MulAction.index_stabilizer_of_transitive H baseS
            rw [hstabilizer_base, hNPindex] at hindex_card
            exact hindex_card.symm
          obtain ⟨hswap, hswap_inf, hswap_zero, hcover, hgen⟩ :=
            hsubline_swap hS_card
          have hmdiv : m ∣ f := by
            have hf_ne_zero :=
              huppert_II_8_27_field_exponent_ne_zero hFcard
            have hFodd : Odd (Nat.card F) := by
              rw [hFcard]
              exact ((Fact.out : p.Prime).odd_of_ne_two hp_ne_two).pow
            have hF_two_dvd : 2 ∣ Nat.card F - 1 :=
              even_iff_two_dvd.mp (Nat.Odd.sub_odd hFodd odd_one)
            have hFgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hF_two_dvd (dvd_refl 2))
            have hhalf_dvd :
                (p ^ m - 1) / 2 ∣ (Nat.card F - 1) / 2 := by
              calc
                (p ^ m - 1) / 2 = Nat.card (Z i0) := hhalf.2.1.symm
                _ ∣ (Nat.card F - 1) /
                    Nat.gcd (Nat.card F - 1) 2 := hi0_dvd_ambient
                _ = (Nat.card F - 1) / 2 := by rw [hFgcd]
            obtain ⟨k, hk⟩ := hhalf_dvd
            have hpowdiv_card : p ^ m - 1 ∣ Nat.card F - 1 := by
              refine ⟨k, ?_⟩
              calc
                Nat.card F - 1 =
                    ((Nat.card F - 1) / 2) * 2 :=
                  (Nat.div_mul_cancel hF_two_dvd).symm
                _ = (((p ^ m - 1) / 2) * k) * 2 := by rw [hk]
                _ = (p ^ m - 1) * k := by
                  rw [mul_assoc, mul_comm k 2, ← mul_assoc,
                    Nat.div_mul_cancel hq_two_dvd]
            have hpowdiv : p ^ m - 1 ∣ p ^ f - 1 := by
              rwa [hFcard] at hpowdiv_card
            exact h826_exponent_dvd_of_pow_sub_one_dvd
              (Fact.out : p.Prime).two_le hpowdiv
          obtain ⟨phi, hphi, conjugator, hphi_conj⟩ :=
            hPGL_embedding hKcard hswap hswap_inf hswap_zero hcover hgen
          have hwitness : Nonempty (SubfieldConjugacyWitness p m H) :=
            ⟨{ K := K
               card_eq := hKcard
               phi := phi
               phi_injective := hphi
               conjugator := conjugator
               map_phi := hphi_conj }⟩
          have hcharF_ne_two : ringChar F ≠ 2 := by
            rw [ringChar.eq F p]
            exact hp_ne_two
          have hnegF : (-1 : F) ≠ 1 :=
            Ring.neg_one_ne_one_of_char_ne_two hcharF_ne_two
          have hnegK : (-1 : K) ≠ 1 := by
            intro hneg
            apply hnegF
            simpa using congrArg Subtype.val hneg
          have htwoK : (2 : K) ≠ 0 := by
            intro htwo
            apply hnegK
            apply (neg_eq_iff_add_eq_zero).2
            simpa [show (1 : K) + 1 = 2 by norm_num] using htwo
          have hcardH :
              Nat.card H =
                (p ^ m + 1) * p ^ m * ((p ^ m - 1) / 2) := by
            rw [hhalf.2.2.2, show Nat.gcd (p ^ m - 1) 2 = 2 from
              Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
                (Nat.dvd_gcd hq_two_dvd (dvd_refl 2))]
            exact Nat.mul_div_assoc ((p ^ m + 1) * p ^ m)
              hq_two_dvd
          have hPGLcard :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                p ^ m * ((p ^ m) ^ 2 - 1) := by
            rw [h826_card_pgl2, hKcard]
          have hfactor :
              (p ^ m) ^ 2 - 1 = (p ^ m - 1) * (p ^ m + 1) := by
            simpa [mul_comm] using Nat.sq_sub_sq (p ^ m) 1
          have hPGLtwice :
              Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
                Nat.card H * 2 := by
            rw [hPGLcard, hfactor, hcardH]
            obtain ⟨r0, hr0⟩ := hq_two_dvd
            rw [hr0]
            simp
            ring
          have hRangeCard :
              Nat.card H = Nat.card phi.range :=
            Nat.card_congr (MonoidHom.ofInjective hphi).toEquiv
          let : Fintype K := Fintype.ofFinite K
          let : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
            Finite.of_surjective Matrix.ProjGenLinGroup.mk
              Matrix.ProjGenLinGroup.mk_surjective
          let : Finite phi.range :=
            Finite.of_injective phi.range.subtype
              phi.range.subtype_injective
          have hphiIndex : phi.range.index = 2 := by
            have hindex := phi.range.index_mul_card
            rw [← hRangeCard, hPGLtwice] at hindex
            apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
            calc
              phi.range.index * Nat.card H = Nat.card H * 2 := hindex
              _ = 2 * Nat.card H := by ring
          have hPSLindex :=
            h826_pslToPGL_range_index_eq_two hnegK
          have hRangeEq :=
            h826_index_two_subgroup_eq_pslRange
              htwoK phi.range hphiIndex hPSLindex
          let eHRange : H ≃* phi.range :=
            MonoidHom.ofInjective hphi
          let ePSLRange :
              PSL2MatrixGroup K ≃*
                (h826_pslToPGL (K := K)).range :=
            MonoidHom.ofInjective h826_pslToPGL_injective
          let eHK : H ≃* PSL2MatrixGroup K :=
            eHRange.trans
              ((MulEquiv.subgroupCongr hRangeEq).trans ePSLRange.symm)
          let eK :=
            GaloisField.algEquivGaloisField p m hKcard
          exact Or.inr (Or.inr
            ⟨hmdiv, ⟨eHK.trans (h826_pslEquiv eK.toRingEquiv)⟩,
              hwitness⟩)
      exact Or.inr htwo_torus_core
  have h826_semidirect_structure
      (hcard : Nat.card H =
        Nat.card (Subgroup.normalizer (P : Set H))) :
      ∃ t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤ := by
    have hPnormal : (P : Subgroup H).Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      exact Subgroup.eq_top_of_card_eq
        (H := Subgroup.normalizer (P : Set H)) hcard.symm
    have hPelementary : IsElementaryAbelian p P :=
      h826_sylow_elementary hFcard H P
    have h826_cyclic_complement :
        ∃ C : Subgroup H,
          IsCyclic C ∧ Disjoint (P : Subgroup H) C ∧
            (P : Subgroup H) ⊔ C = ⊤ ∧
            Nat.card C ∣
              (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
            (∀ c : C, c ≠ 1 →
              ∀ x : (P : Subgroup H), x ≠ 1 →
              (c : H) * (x : H) * (c : H)⁻¹ ≠ (x : H)) := by
      classical
      let N : Subgroup H := Subgroup.normalizer (P : Set H)
      have hN : N = Subgroup.normalizer (P : Set H) := rfl
      have hNtop : N = ⊤ := by
        exact Subgroup.eq_top_of_card_eq (H := N) hcard.symm
      have hP_le_N : (P : Subgroup H) ≤ N := Subgroup.le_normalizer
      let PN : Subgroup N := (P : Subgroup H).subgroupOf N
      let : PN.Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (by
          simp [N])
      obtain ⟨hquotient_cyclic, hquotient_card_dvd,
          hNormalizer_fixedPointFree, _⟩ :=
        h821_borel_quotient_data hFcard H P
          (by rw [← Subgroup.one_lt_card_iff_ne_bot, hPm]
              exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
                ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero,
                  fun h => hP_nontrivial (hPm.trans h)⟩)
          N hN PN rfl
      have hquotient_card_dvd_sub_one :
          Nat.card (N ⧸ PN) ∣ Nat.card F - 1 :=
        dvd_trans hquotient_card_dvd
          (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card F - 1) 2))
      have hf_ne_zero : f ≠ 0 :=
        huppert_II_8_27_field_exponent_ne_zero hFcard
      have hp_dvd_cardF : p ∣ Nat.card F := by
        rw [hFcard]
        exact dvd_pow_self p hf_ne_zero
      have hp_not_dvd_cardF_sub_one : ¬ p ∣ Nat.card F - 1 := by
        intro hp_sub
        have hp_one : p ∣ 1 := by
          have hd := Nat.dvd_sub hp_dvd_cardF hp_sub
          have hcard_pos : 0 < Nat.card F := Nat.card_pos
          have hsub : Nat.card F - (Nat.card F - 1) = 1 := by
            omega
          rwa [hsub] at hd
        exact (Fact.out : p.Prime).not_dvd_one hp_one
      have hcop_p_quotient :
          Nat.Coprime p (Nat.card (N ⧸ PN)) :=
        Nat.Coprime.of_dvd_right hquotient_card_dvd_sub_one
          ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
            hp_not_dvd_cardF_sub_one)
      have hPNcard : Nat.card PN = p ^ m := by
        calc
          Nat.card PN = Nat.card P :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe hP_le_N).toEquiv
          _ = p ^ m := hPm
      have hPNindex : PN.index = Nat.card (N ⧸ PN) := rfl
      have hPN_coprime_index : Nat.Coprime (Nat.card PN) PN.index := by
        rw [hPNcard, hPNindex]
        exact hcop_p_quotient.pow_left m
      obtain ⟨CN, hcomp⟩ :=
        Subgroup.exists_right_complement'_of_coprime hPN_coprime_index
      have hCNcyclic : IsCyclic CN := by
        let eC : N ⧸ PN ≃* CN := hcomp.symm.QuotientMulEquiv
        let : IsCyclic (N ⧸ PN) := hquotient_cyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      let C : Subgroup H := CN.map N.subtype
      have hCcyclic : IsCyclic C := by
        let eC : CN ≃* C :=
          Subgroup.equivMapOfInjective CN N.subtype N.subtype_injective
        let : IsCyclic CN := hCNcyclic
        exact isCyclic_of_surjective eC.toMonoidHom eC.surjective
      have hPNmap : PN.map N.subtype = (P : Subgroup H) := by
        exact Subgroup.map_subgroupOf_eq_of_le hP_le_N
      have hdisjoint : Disjoint (P : Subgroup H) C := by
        rw [← hPNmap]
        exact Subgroup.disjoint_map N.subtype_injective hcomp.disjoint
      have hsup : (P : Subgroup H) ⊔ C = ⊤ := by
        rw [← hPNmap, ← Subgroup.map_sup, hcomp.sup_eq_top]
        rw [← MonoidHom.range_eq_map, N.range_subtype, hNtop]
      have hCNcard : Nat.card CN = Nat.card (N ⧸ PN) := by
        calc
          Nat.card CN = PN.index := hcomp.symm.index_eq_card.symm
          _ = Nat.card (N ⧸ PN) := hPNindex
      have hCcard : Nat.card C = Nat.card (N ⧸ PN) := by
        calc
          Nat.card C = Nat.card CN :=
            Subgroup.card_map_of_injective N.subtype_injective
          _ = Nat.card (N ⧸ PN) := hCNcard
      have hCdiv : Nat.card C ∣
          (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 := by
        rw [hCcard]
        exact hquotient_card_dvd
      have hCfixedPointFree :
          ∀ c : C, c ≠ 1 →
            ∀ x : (P : Subgroup H), x ≠ 1 →
            (c : H) * (x : H) * (c : H)⁻¹ ≠ (x : H) := by
        intro c hc x hx
        rcases c.property with ⟨n, hnCN, hn⟩
        have hnPN : n ∉ PN := by
          intro hnmem
          have hn_one : n = 1 :=
            Subgroup.disjoint_def.mp hcomp.disjoint hnmem hnCN
          apply hc
          apply Subtype.ext
          change (c : H) = 1
          rw [← hn, hn_one]
          rfl
        have hnfree := hNormalizer_fixedPointFree n hnPN x hx
        intro hfix
        apply hnfree
        have hn' : (n : H) = (c : H) := hn
        rw [hn']
        exact hfix
      exact ⟨C, hCcyclic, hdisjoint, hsup, hCdiv,
        hCfixedPointFree⟩
    obtain ⟨C, hCcyclic, hPCdisjoint, hPCsup, hCdiv,
        hCfixedPointFree⟩ :=
      h826_cyclic_complement
    have h826_complement_order_divides_sylow :
        Nat.card C ∣ p ^ m - 1 := by
      let : (P : Subgroup H).Normal := hPnormal
      let : MulDistribMulAction C P :=
        MulDistribMulAction.compHom P
          ((MulAut.conjNormal (H := (P : Subgroup H))).comp C.subtype)
      have hfree :
          ∀ c : C, c ≠ 1 →
            ∀ x : (P : Subgroup H), c • x = x → x = 1 := by
        intro c hc x hfix
        by_contra hx
        have hconj :
            (c : H) * (x : H) * (c : H)⁻¹ = (x : H) := by
          have hconj' := congrArg Subtype.val hfix
          change (c : H) * (x : H) * (c : H)⁻¹ = (x : H) at hconj'
          exact hconj'
        exact hCfixedPointFree c hc x hx hconj
      have hdiv := h826_card_actor_dvd_group_card_sub_one hfree
      rwa [hPm] at hdiv
    have h826_complement_order_divides_ambient :
        Nat.card C ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 := by
      rw [← hFcard]
      exact hCdiv
    exact ⟨Nat.card C, h826_complement_order_divides_sylow,
      h826_complement_order_divides_ambient, P, C, hPnormal,
      hPelementary, hPm, hCcyclic, rfl, hPCdisjoint, hPCsup⟩
  have h826_A5_order_sixty
      (hcard60 : Nat.card H = 60)
      (hSylow5 : Nat.card (Sylow 5 H) = 6)
      (hfaithful : Function.Injective
        (MulAction.toPermHom H (Sylow 5 H))) :
      Nonempty (H ≃* alternatingGroup (Fin 5)) := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : FaithfulSMul H (Sylow 5 H) := by
      rw [faithfulSMul_iff]
      intro g hg
      apply hfaithful
      apply DFunLike.ext _ _
      intro Q
      simpa using hg Q
    exact huppert_II_8_25_transitive_degree_six_order_sixty
      (Sylow.isPretransitive_of_finite (p := 5) (G := H)) hSylow5 hcard60
  rcases h826_counting_shapes with hsemidirect | hA5 | hPGL | hPSL
  · obtain ⟨t, ht_subfield, ht_ambient, N, C, hNnormal, hNelem,
      hNcard, hCcyclic, hCcard, hdisjoint, hsup⟩ :=
      h826_semidirect_structure hsemidirect
    exact Or.inl ⟨m, t, ht_subfield, ht_ambient, N, C, hNnormal,
      hNelem, hNcard, hCcyclic, hCcard, hdisjoint, hsup⟩
  · rcases hA5 with
      ⟨hpm3, hcard60, hrestriction, hSylow5, hfaithful⟩
    have hHA5 := h826_A5_order_sixty hcard60 hSylow5 hfaithful
    exact Or.inr (Or.inl ⟨m, hpm3, hrestriction, hHA5⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨m, hm_ne_zero, hPGL.1, hPGL.2⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨m, hm_ne_zero, hPSL.1, hPSL.2⟩))

/-- Backward-compatible projection of the concrete II.8.26 endpoint. -/
public theorem huppert_II_8_26_dickson_case_p_part_normalizer_large
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (P : Sylow p H) (hP_nontrivial : Nat.card P ≠ 1)
    (hnormalizer : Subgroup.normalizer (P : Set H) ≠ (P : Subgroup H)) :
    (∃ m t : ℕ,
      t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
      ∃ N C : Subgroup H,
        N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
        IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
    (∃ m : ℕ, p ^ m = 3 ∧
      (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
      Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) := by
  rcases
      huppert_II_8_26_dickson_case_p_part_normalizer_large_with_subfield
        hFcard H P hP_nontrivial hnormalizer with
    hsemidirect | hA5 | hPGL | hPSL
  · exact Or.inl hsemidirect
  · exact Or.inr (Or.inl hA5)
  · rcases hPGL with ⟨m, hm, hmdiv, hiso, _hw⟩
    exact Or.inr (Or.inr (Or.inl ⟨m, hm, hmdiv, hiso⟩))
  · rcases hPSL with ⟨m, hm, hmdiv, hiso, _hw⟩
    exact Or.inr (Or.inr (Or.inr ⟨m, hm, hmdiv, hiso⟩))
/--
Huppert II, Main Theorem 8.27 (Dickson), stated as the direct subgroup
classification for `PSL(2,p^f)`.  The eight alternatives are written in the
statement itself rather than hidden behind a local classification-data type.
-/
public theorem huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F)) :
    IsElementaryAbelian p H ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
      ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
      (∃ m t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
        Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m)) ∧
        Nonempty (SubfieldConjugacyWitness p m H)) ∨
      (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) ∧
        Nonempty (SubfieldConjugacyWitness p m H)) := by
  let P : Sylow p H := default
  obtain ⟨m, hPm⟩ := P.isPGroup'.exists_card_eq
  by_cases hP_trivial : p ^ m = 1
  · have hp_not_dvd_card_H : ¬ p ∣ Nat.card H := by
      intro hpdiv
      have hpdvdP : p ∣ Nat.card P := P.dvd_card_of_dvd_card hpdiv
      rw [hPm, hP_trivial] at hpdvdP
      exact (Fact.out : p.Prime).not_dvd_one hpdvdP
    rcases huppert_II_8_24_dickson_case_no_p_part hFcard H hp_not_dvd_card_H with
      h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · have hP_nontrivial : Nat.card P ≠ 1 := by
      intro hPone
      apply hP_trivial
      rw [← hPm, hPone]
    by_cases hnormalizer :
        Subgroup.normalizer (P : Set H) = (P : Subgroup H)
    · have hpm : 1 < p ^ m := by
        exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
          ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero, hP_trivial⟩
      rcases huppert_II_8_23_dickson_case_p_part_normalizer_self
          hFcard H P hPm hpm hnormalizer with h | h | h
      · exact Or.inl h.2
      · rcases h with ⟨hpm2, z, hzodd, hzdiv, hHcard, hHdihedral⟩
        exact Or.inr (Or.inr (Or.inl ⟨z, hzdiv, hHcard, hHdihedral⟩))
      · rcases h with ⟨hpm3, hHA4⟩
        have hp_ne_two : p ≠ 2 := by
          intro hp
          subst p
          cases m with
          | zero => norm_num at hpm3
          | succ m =>
              rw [pow_succ] at hpm3
              omega
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hp_ne_two, hHA4⟩)))
    · rcases huppert_II_8_26_dickson_case_p_part_normalizer_large_with_subfield
          hFcard H P hP_nontrivial hnormalizer with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · rcases h with ⟨m, _hpm3, hrestriction, hA5⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl ⟨hrestriction, hA5⟩)))))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
      · exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

/-- Backward-compatible projection of Dickson's subgroup classification. -/
public theorem huppert_II_8_27_dickson_psl2_subgroup_classification
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (PSL2MatrixGroup F)) :
    IsElementaryAbelian p H ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
      ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
      (∃ m t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
        Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
      (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  rcases
      huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield
        hFcard H with
    hElementary | hCyclic | hDihedral | hA4 | hS4 | hA5 |
      hSemidirect | hPSL | hPGL
  · exact Or.inl hElementary
  · exact Or.inr (Or.inl hCyclic)
  · exact Or.inr (Or.inr (Or.inl hDihedral))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hA4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hS4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA5)))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSemidirect))))))
  · rcases hPSL with ⟨m, hm, hmdiv, hiso, _hw⟩
    exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨m, hm, hmdiv, hiso⟩)))))))
  · rcases hPGL with ⟨m, hm, hmdiv, hiso, _hw⟩
    exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨m, hm, hmdiv, hiso⟩)))))))
end Dickson
end CFSG.Glauberman
