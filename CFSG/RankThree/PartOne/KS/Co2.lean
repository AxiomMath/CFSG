module

public import CFSG.RankThree.PartOne.KS.AllInner
public import CFSG.RankThree.PartOne.KS.Combine
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.RankThree.Native.Co2FiveCentralizers
public import CFSG.Sporadic.Co2
public import CFSG.RankThree.PartOne.KS.ModelR

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Co2Cert CFSG.RankThree.Native
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

@[expose] def Co2AllInner : Prop := ∀ α : MulAut co2P, ∃ g : co2P, α = MulAut.conj g

theorem co2P_isSimpleGroup : IsSimpleGroup co2P := by
  have h : IsSimpleGroup CFSG.Blueprint.NativeSporadic.Co2 :=
    CFSG.Sporadic.Co2.fam_co2_simplicity.2.2
  exact @MulEquiv.isSimpleGroup _ _ _ _ h co2PermEquiv.symm

theorem co2P_nonabelian : ∃ a b : co2P, a * b ≠ b * a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hC1, -, -, ⟨g, hg, h, hh, hne⟩, -⟩ :=
    R3E_Co2_full_five_centralizer_structures
  have hD : co2FiveD ≤ co2P := (commutator_self_le co2FiveC1).trans (hC1.le.trans inf_le_right)
  exact ⟨⟨g, hD hg⟩, ⟨h, hD hh⟩, fun e => hne (congrArg Subtype.val e)⟩

theorem co2P_center : center co2P = ⊥ :=
  have := co2P_isSimpleGroup
  center_eq_bot_of_simple co2P_nonabelian

theorem co2_autModel (hAut : Co2AllInner) : AutModel co2P co2P :=
  autModel_self_of_allInner co2P_center hAut

theorem card_mulAut_co2P (hAut : Co2AllInner) : Nat.card (MulAut co2P) = 42305421312000 := by
  rw [card_mulAut_eq_card_of_allInner co2P_center hAut, card_co2P]

theorem co2_core_bot_rep (i : Fin 2) (B : Subgroup (Equiv.Perm (Fin 2300))) (hPB : co2P ≤ B)
    (hBR : B ≤ co2P) :
    inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({co2FiveLine (co2FiveRepLine i)} : Set (Equiv.Perm (Fin 2300)))) = ⊥ := by
  obtain ⟨-, -, -, -, hC0, -, hAC, hAn, -, hAexp, -, hAcent, hC1, -, hDs, hDnab, -, -, hDcard⟩ :=
    R3E_Co2_full_five_centralizer_structures
  fin_cases i
  · exact core_bot_of_record_five hC0 hAC hAn (hAC.trans (hC0.le.trans inf_le_right)) hAexp
      hAcent hPB hBR
  · exact core_bot_of_record_derived hC1 hDs hDnab
      ((commutator_self_le co2FiveC1).trans (hC1.le.trans inf_le_right)) hDcard hPB hBR

theorem co2_core_bot (hAut : Co2AllInner) (B : Subgroup (Equiv.Perm (Fin 2300)))
    (hPB : co2P ≤ B) (hBR : B ≤ co2P) (y : Equiv.Perm (Fin 2300)) (hy : y ∈ co2P)
    (hord : orderOf y = 5) :
    inSubgroup (aschbacherSolvableCore 5) (B ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 2300)))) =
      ⊥ := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, -⟩ := R3E_Co2_full_five_centralizer_structures
  refine core_bot_of_lines_R Nat.prime_five (co2_autModel hAut) (by omega) hQsyl hlines
    (fun j => ?_) B hPB hBR y hy hord
  obtain ⟨hjP, hjconj⟩ := htrans j
  exact ⟨co2FiveRepLine (co2FiveRecordOf j), ⟨co2FiveTransporter j, hjP, hjconj⟩,
    fun B' hPB' hBR' => co2_core_bot_rep _ B' hPB' hBR'⟩

theorem almostSimpleLocalCoresTrivial_five_Co2 (hAut : Co2AllInner) :
    AlmostSimpleLocalCoresTrivial 5 (Carrier .Co2) := by
  intro H _ _ K _ hK hC x hx
  obtain ⟨e⟩ := hK
  exact aschbacherCore_centralizer_eq_bot_of_model (co2_autModel hAut) (by omega) Nat.prime_five
    (by norm_num) (fun B hPB hBR y hyP hy => co2_core_bot hAut B hPB hBR y hyP hy) K
    (e.trans co2PermEquiv) hC x hx

theorem sporadicPlaneOdd_Co2 (hAut : Co2AllInner) : SporadicPlaneOdd (Carrier .Co2) := by
  refine sporadicPlaneOdd_of_almostSimple {5} (fun q hq _ => ?_) ?_
  · rw [Finset.mem_singleton.mp hq]
    exact almostSimplePlaneOdd_of_localCoresTrivial Nat.prime_five
      (almostSimpleLocalCoresTrivial_five_Co2 hAut)
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp5 : p ≠ 5 := fun h => hpS (by simp [h])
    have hcard : Nat.card (MulAut T) = 2 ^ 18 * 3 ^ 6 * 5 ^ 3 * 1771 := by
      rw [Nat.card_congr (MulAut.congr (e.trans co2PermEquiv)).toEquiv, card_mulAut_co2P hAut]
      norm_num
    rw [hcard]
    exact not_sq_dvd_mul_of_coprime (B := 42) hp (coprime_two_three_five_pow hp hp3 hp5 18 6 3)
      (by norm_num) (by decide) (by norm_num)

end CFSG.RankThree.PartOne
