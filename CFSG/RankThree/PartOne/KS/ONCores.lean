module

public import CFSG.RankThree.PartOne.KS.OuterGeneral
public import CFSG.RankThree.Native.ONSevenCentralizers

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.RankThree.Native
open CFSG.ONSchreier (Pv)
open scoped Pointwise

theorem onSeven_record_core_bot (r : Fin 5) :
    inSubgroup (aschbacherSolvableCore 7)
      (Pv ⊓ centralizer ({onSevenLine (onSevenRep r)} :
        Set (Equiv.Perm (Fin CFSG.ONSchreier.N)))) = ⊥ := by
  obtain ⟨-, -, hC, hlow, hhigh, -, -⟩ := R3E_ON_full_seven_centralizer_structures
  have hCr := hC r
  by_cases hr : r.val < 3
  · obtain ⟨r', rfl⟩ : ∃ r' : Fin 3, r = Fin.castLE (by norm_num) r' :=
      ⟨⟨r.val, hr⟩, Fin.ext rfl⟩
    obtain ⟨-, hFC, hFnorm, hFcard, hcent, -⟩ := hlow r'
    have hFp : IsPGroup 7 (onSevenF r') :=
      IsPGroup.of_card (n := 3) (by rw [hFcard]; norm_num)
    refine line_core_bot_of_normal_pgroup (by norm_num) (P := Pv) (R := Pv) (B := Pv)
      (Z := onSevenF r') le_rfl le_rfl (onSeven_mem_P.2.2.2.1 r') hFp
      (hFC.trans (hCr.le.trans inf_le_left)) ?_ ?_
    · rw [inf_comm, ← hCr]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hFC).1 hFnorm
    · rw [inf_comm Pv, ← hCr, inf_comm]
      exact hFp.to_le hcent
  · have hCp : IsPGroup 7 (onSevenC r) :=
      IsPGroup.of_card (n := 2) (by rw [hhigh r (by omega)]; norm_num)
    refine line_core_bot_of_normal_pgroup (by norm_num) (P := Pv) (R := Pv) (B := Pv)
      (Z := onSevenC r) le_rfl le_rfl (onSeven_mem_P.2.2.1 r) hCp
      (hCr.le.trans inf_le_left) ?_ ?_
    · rw [inf_comm, ← hCr]
      exact Subgroup.le_normalizer
    · rw [inf_comm Pv, ← hCr]
      exact hCp.to_le inf_le_left

theorem onSeven_line_core_bot (j : Fin 57) :
    inSubgroup (aschbacherSolvableCore 7)
      (Pv ⊓ centralizer ({onSevenLine j} : Set (Equiv.Perm (Fin CFSG.ONSchreier.N)))) = ⊥ := by
  obtain ⟨-, -, -, -, -, htrans, hcov⟩ := R3E_ON_full_seven_centralizer_structures
  obtain ⟨r, t, ht, htj⟩ := hcov j
  obtain ⟨hhP, he1, he6, hjlt, hconj⟩ := htrans r t ht
  have hjj : (⟨t.line, hjlt⟩ : Fin 57) = j := Fin.ext htj
  rw [hjj] at hconj
  set h := onSevenTransporterPerm t with hh
  set y := h * onSevenLine (onSevenRep r) * h⁻¹ with hy
  have hord : orderOf y = 7 := by
    have : y = MulAut.conj h (onSevenLine (onSevenRep r)) := rfl
    rw [this, MulEquiv.orderOf_eq, orderOf_onSevenLine]
  have hcop : Nat.Coprime t.power (orderOf y) := by
    rw [hord]
    exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).2 fun hd =>
      absurd (Nat.le_of_dvd (by omega) hd) (by omega)).symm
  have hcent : centralizer ({onSevenLine j} : Set (Equiv.Perm (Fin CFSG.ONSchreier.N))) =
      centralizer ({y} : Set (Equiv.Perm (Fin CFSG.ONSchreier.N))) := by
    rw [← hconj]
    exact centralizer_singleton_pow_eq hcop
  have h1 := card_core_conj (p := 7) (by norm_num) Pv hhP (onSevenLine (onSevenRep r))
  rw [← hy, onSeven_record_core_bot r, Subgroup.card_bot, ← hcent] at h1
  exact Subgroup.card_eq_one.mp h1

theorem onSeven_core_bot (y : Equiv.Perm (Fin CFSG.ONSchreier.N)) (hy : y ∈ Pv)
    (hord : orderOf y = 7) :
    inSubgroup (aschbacherSolvableCore 7)
      (Pv ⊓ centralizer ({y} : Set (Equiv.Perm (Fin CFSG.ONSchreier.N)))) = ⊥ := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, -⟩ := R3E_ON_full_seven_centralizer_structures
  exact core_bot_of_lines (P := Pv) (R := Pv) (by norm_num) hQsyl hlines
    (fun j B hPB hBR => by rw [le_antisymm hBR hPB]; exact onSeven_line_core_bot j)
    Pv le_rfl le_rfl y hy hord

theorem onSeven_core_bot_of_equiv {X : Type*} [Group X] [Finite X] (φ : X ≃* Pv) {x : X}
    (hx : orderOf x = 7) :
    inSubgroup (aschbacherSolvableCore 7) (centralizer ({x} : Set X)) = ⊥ := by
  have h1 := card_aschbacherCore_centralizer_mulEquiv (p := 7) (by norm_num) φ x
  have h2 := card_aschbacherCore_subgroup_centralizer (p := 7) (by norm_num) Pv (φ x)
  have h3 : orderOf (((φ x : Pv)) : Equiv.Perm (Fin CFSG.ONSchreier.N)) = 7 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
  rw [onSeven_core_bot _ (φ x).2 h3, Subgroup.card_bot] at h2
  rw [h2] at h1
  exact Subgroup.card_eq_one.mp h1

end CFSG.RankThree.PartOne
