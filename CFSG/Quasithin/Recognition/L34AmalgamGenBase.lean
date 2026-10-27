
module

public import CFSG.Quasithin.Recognition.L34AmalgamDataBase
public meta import CFSG.Quasithin.Recognition.L34AmalgamDataBase
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import CFSG.Quasithin.Recognition.L34AmalgamGenInputs
public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs
public import CFSG.Quasithin.Recognition.M22WittData
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Quasithin.Recognition.M22UniqueDataInputs
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Quasithin.Recognition.M22UniqueSystem
public import Certificates.Data.CFSGNative.Mathieu.M22

@[expose] public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem not_of_count_eq_zero (Q : (Fin 22 → Fin 22) → Prop)
    [DecidablePred Q]
    (h : m22Count Q = 0) (g : M22) : ¬ Q ⇑(g : Equiv.Perm (Fin 22)) := by
  intro hg
  have : 0 < Nat.card {x : M22 // Q ⇑(x : Equiv.Perm (Fin 22))} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨g, hg⟩⟩, inferInstance⟩
  rw [card_m22_subtype, h] at this
  exact absurd this (lt_irrefl 0)

theorem tab_getD (g : M22) (x : Fin 22) : (tab g).getD x.val 0 = (g : Equiv.Perm (Fin 22)) x := by
  simp [tab]

theorem evalW_mem_closure {X : Type*} [Group X] (f : Fin 5 → X) (S : Set (Fin 5))
    (w : List (Fin 5 × Bool)) (hw : ∀ x ∈ w, x.1 ∈ S) :
    evalW f w ∈ Subgroup.closure (f '' S) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons x w ih =>
    have hx : f x.1 ∈ Subgroup.closure (f '' S) :=
      Subgroup.subset_closure ⟨x.1, hw x (List.mem_cons_self), rfl⟩
    have hrest := ih fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have e : evalW f (x :: w) = cond x.2 (f x.1) (f x.1)⁻¹ * evalW f w := by
      simp [evalW]
    rw [e]
    refine Subgroup.mul_mem _ ?_ hrest
    rcases x with ⟨i, b⟩
    cases b
    · exact Subgroup.inv_mem _ hx
    · exact hx

theorem mem_m22TwoStab_iff {g : M22} : g ∈ m22TwoStab ↔
    (g : Equiv.Perm (Fin 22)) 0 = 0 ∧ (g : Equiv.Perm (Fin 22)) 1 = 1 := by
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, smul_m22_def,
    smul_m22_def]

theorem card_B :
    Nat.card ↥(m22TwoStab ⊓ m22PtHexStab) = 192 := by
  rw [← count_two_point_hexad, ← card_m22_subtype]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [Subgroup.mem_inf, mem_m22TwoStab_iff, M22Witt.mem_m22PtHexStab_iff]
  constructor
  · rintro ⟨⟨h0, h1⟩, -, hh⟩
    exact ⟨h0, h1, hh⟩
  · rintro ⟨h0, h1, hh⟩
    exact ⟨⟨h0, h1⟩, h0, hh⟩

theorem eq_of_card_eq_five_mul {X : Type*} [Group X] [Finite X] {A S T : Subgroup X}
    (hAS : A ≤ S) (hST : S ≤ T) (hcard : Nat.card T = 5 * Nat.card A) {x : X} (hxS : x ∈ S)
    (hxA : x ∉ A) : S = T := by
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hAS
  obtain ⟨e, he⟩ := Subgroup.card_dvd_of_le hST
  have hA : 0 < Nat.card A := Nat.card_pos
  have hde : d * e = 5 := by
    rw [he, hd, mul_assoc] at hcard
    exact Nat.eq_of_mul_eq_mul_left hA (hcard.trans (mul_comm _ _))
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [mul_one] at hd
    exact hxA ((Subgroup.eq_of_le_of_card_ge hAS hd.le) ▸ hxS)
  have he1 : e = 1 := by
    have h5 : d ∣ 5 := ⟨e, hde.symm⟩
    rcases (Nat.dvd_prime (by norm_num)).mp h5 with h | h
    · exact absurd h hd1
    · rw [h] at hde; omega
  exact Subgroup.eq_of_le_of_card_ge hST (by rw [he, he1, mul_one])

theorem sup_P1_P2 :
    m22TwoStab ⊔ m22PtHexStab = stabilizer M22 (0 : Fin 22) := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun k hk => ?_
  have hk0 : k • (0 : Fin 22) = 0 := MulAction.mem_stabilizer_iff.mp hk
  by_cases hk1 : k • (1 : Fin 22) = 1
  · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hk, MulAction.mem_stabilizer_iff.mpr hk1⟩)
  have hx0 : k • (1 : Fin 22) ≠ 0 := by
    intro h
    rw [← hk0] at h
    exact absurd (smul_left_cancel _ h) (by decide)
  obtain ⟨i, hi, hi1⟩ := exists_fix_zero (w := 2) (by decide) (by decide)
  have hiP : i ∈ m22PtHexStab := by rw [m22PtHexStab, inf_comm]; exact hi
  obtain ⟨p, hp0, hp1, hp2⟩ := exists_smul_eq_triple (a := (0 : Fin 22)) (b := 1) (c := 2)
    (a' := 0) (b' := 1) (c' := k • (1 : Fin 22)) (by decide) (by decide) (by decide)
    (by decide) (Ne.symm hx0) (Ne.symm hk1)
  have hpP : p ∈ m22TwoStab := Subgroup.mem_inf.mpr
    ⟨MulAction.mem_stabilizer_iff.mpr hp0, MulAction.mem_stabilizer_iff.mpr hp1⟩
  set j := p * i with hj
  have hjS : j ∈ m22TwoStab ⊔ m22PtHexStab :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hpP) (Subgroup.mem_sup_right hiP)
  have hj1 : j • (1 : Fin 22) = k • 1 := by rw [hj, mul_smul, hi1, hp2]
  have hjk : j⁻¹ * k ∈ m22TwoStab := by
    refine Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr ?_,
      MulAction.mem_stabilizer_iff.mpr ?_⟩
    · have hj0 : j • (0 : Fin 22) = 0 := by
        rw [hj, mul_smul, MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hiP).1, hp0]
      rw [mul_smul, hk0, inv_smul_eq_iff, hj0]
    · rw [mul_smul, ← hj1, inv_smul_smul]
  have := Subgroup.mul_mem _ hjS (Subgroup.mem_sup_left hjk)
  rwa [mul_inv_cancel_left] at this

end CFSG.Quasithin.L34Amalgam
