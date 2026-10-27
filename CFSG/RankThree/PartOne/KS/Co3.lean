module

public import CFSG.RankThree.PartOne.KS.AllInner
public import CFSG.RankThree.PartOne.KS.Combine
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.RankThree.PartOne.KS.Lines
public import CFSG.RankThree.Native.Co3FiveCentralizers
public import CFSG.Sporadic.Co3

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Co3 CFSG.RankThree.Native
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

@[expose] def Co3AllInner : Prop := ∀ α : MulAut co3P, ∃ g : co3P, α = MulAut.conj g

theorem co3P_isSimpleGroup : IsSimpleGroup co3P := by
  have h : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Co3 :=
    CFSG.Sporadic.Co3.fam_co3_simplicity.2.2
  exact @MulEquiv.isSimpleGroup _ _ _ _ h co3PermEquiv.symm

theorem co3P_nonabelian : ∃ a b : co3P, a * b ≠ b * a := by
  obtain ⟨-, -, -, -, -, hC0, -, -, ⟨g, hg, h, hh, hne⟩, -⟩ :=
    R3E_Co3_full_five_centralizer_structures
  have hD : co3FiveD ≤ co3P := (commutator_self_le co3FiveC0).trans (hC0.le.trans inf_le_right)
  exact ⟨⟨g, hD hg⟩, ⟨h, hD hh⟩, fun e => hne (congrArg Subtype.val e)⟩

theorem co3P_center : center co3P = ⊥ :=
  have := co3P_isSimpleGroup
  center_eq_bot_of_simple co3P_nonabelian

theorem co3_autModel (hAut : Co3AllInner) : AutModel co3P co3P where
  le := le_rfl
  conj_mem := fun x hx _ hp => co3P.mul_mem (co3P.mul_mem hx hp) (co3P.inv_mem hx)
  surj := fun α => by
    obtain ⟨g, hg⟩ := hAut α
    exact ⟨g, g.2, fun p => by rw [hg]; simp [MulAut.conj_apply]⟩
  inj := fun x hx hc => by
    have hmem : (⟨x, hx⟩ : co3P) ∈ center co3P := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [co3P_center, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem

theorem card_mulAut_co3P (hAut : Co3AllInner) : Nat.card (MulAut co3P) = 495766656000 := by
  rw [card_mulAut_eq_card_of_allInner co3P_center hAut, card_co3P]

theorem co3_core_bot_zero :
    inSubgroup (aschbacherSolvableCore 5)
      (co3P ⊓ centralizer ({co3FiveLine 0} : Set (Equiv.Perm (Fin 276)))) = ⊥ := by
  obtain ⟨-, -, -, -, -, hC0, -, hDs, hDnab, -, -, hDcard, -⟩ :=
    R3E_Co3_full_five_centralizer_structures
  have hC0P : co3FiveC0 ≤ co3P := hC0.le.trans inf_le_right
  have hDle : co3FiveD ≤ co3FiveC0 := commutator_self_le co3FiveC0
  have hDq : IsQuasisimple co3FiveD := by
    have := hDs
    obtain ⟨g, hg, h, hh, hne⟩ := hDnab
    exact isQuasisimple_of_isSimpleGroup ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hne (congrArg Subtype.val e)⟩
  refine line_core_bot_of_normal_component Nat.prime_five (P := co3P) (R := co3P) le_rfl le_rfl
    (hDle.trans hC0P) hDq (hDle.trans (hC0.le.trans inf_le_left)) ?_ ?_
  · rw [inf_comm, ← hC0]
    exact le_normalizer_commutator_self _
  · rw [inf_comm co3P, ← hC0, inf_comm]
    exact IsPGroup.of_card (n := 1) (by rw [hDcard, pow_one])

theorem co3_core_bot_25 :
    inSubgroup (aschbacherSolvableCore 5)
      (co3P ⊓ centralizer ({co3FiveLine 25} : Set (Equiv.Perm (Fin 276)))) = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hC25, -, hAC, hAnorm, -, hAexp, -, hAcent⟩ :=
    R3E_Co3_full_five_centralizer_structures
  have hAp : IsPGroup 5 co3FiveA := fun g => ⟨1, by
    rw [pow_one, ← hAexp]
    exact Monoid.pow_exponent_eq_one g⟩
  refine line_core_bot_of_normal_pgroup Nat.prime_five (P := co3P) (R := co3P) le_rfl le_rfl
    (hAC.trans (hC25.le.trans inf_le_right)) hAp (hAC.trans (hC25.le.trans inf_le_left)) ?_ ?_
  · rw [inf_comm, ← hC25]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).1 hAnorm
  · rw [inf_comm co3P, ← hC25, inf_comm]
    exact hAp.to_le hAcent

theorem co3_core_bot_line (j : Fin 31) :
    inSubgroup (aschbacherSolvableCore 5)
      (co3P ⊓ centralizer ({co3FiveLine j} : Set (Equiv.Perm (Fin 276)))) = ⊥ := by
  by_cases hj : (j : ℕ) = 25
  · have : j = 25 := Fin.ext hj
    rw [this]
    exact co3_core_bot_25
  · obtain ⟨-, -, htrans, hrec0, -⟩ := R3E_Co3_full_five_centralizer_structures
    obtain ⟨hjP, hjconj⟩ := htrans j
    rw [(hrec0 j).2 hj] at hjconj
    have h1 := card_core_conj Nat.prime_five co3P hjP (co3FiveLine 0)
    rw [hjconj, co3_core_bot_zero, Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.mp h1

theorem almostSimpleLocalCoresTrivial_five_Co3 (hAut : Co3AllInner) :
    AlmostSimpleLocalCoresTrivial 5 (Carrier .Co3) := by
  intro H _ _ K _ hK hC x hx
  obtain ⟨e⟩ := hK
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, -⟩ := R3E_Co3_full_five_centralizer_structures
  have hline := core_bot_of_lines (P := co3P) (R := co3P) Nat.prime_five hQsyl hlines
    (fun j B hPB hBR => by rw [le_antisymm hBR hPB]; exact co3_core_bot_line j)
  exact aschbacherCore_centralizer_eq_bot_of_model (co3_autModel hAut) (by omega) Nat.prime_five
    (by norm_num) hline K (e.trans co3PermEquiv) hC x hx

theorem sporadicPlaneOdd_Co3 (hAut : Co3AllInner) : SporadicPlaneOdd (Carrier .Co3) := by
  refine sporadicPlaneOdd_of_almostSimple {5} (fun q hq _ => ?_) ?_
  · rw [Finset.mem_singleton.mp hq]
    exact almostSimplePlaneOdd_of_localCoresTrivial Nat.prime_five
      (almostSimpleLocalCoresTrivial_five_Co3 hAut)
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp5 : p ≠ 5 := fun h => hpS (by simp [h])
    have hcard : Nat.card (MulAut T) = 2 ^ 10 * 3 ^ 7 * 5 ^ 3 * 1771 := by
      rw [Nat.card_congr (MulAut.congr (e.trans co3PermEquiv)).toEquiv, card_mulAut_co3P hAut]
      norm_num
    rw [hcard]
    exact not_sq_dvd_mul_of_coprime (B := 42) hp (coprime_two_three_five_pow hp hp3 hp5 10 7 3)
      (by norm_num) (by decide) (by norm_num)

end CFSG.RankThree.PartOne
