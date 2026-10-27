module

public import CFSG.RankThree.PartOne.KS.ModelR
public import CFSG.RankThree.PartOne.KS.Combine
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.RankThree.PartOne.KS.RuFiveCentralizers
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.RuSchreier
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

theorem ru_autModel : AutModel ruP ruP := by
  obtain ⟨hcenter, hconj, -, -⟩ := CTUC_Ru_full_inner_automorphisms_and_second_centralizer
  exact
  { le := le_rfl
    conj_mem := fun x hx _ hp => ruP.mul_mem (ruP.mul_mem hx hp) (ruP.inv_mem hx)
    surj := fun α => by
      obtain ⟨g, hg⟩ := hconj.2 α
      exact ⟨g, g.2, fun p => by rw [← hg]; simp [MulAut.conj_apply]⟩
    inj := fun x hx hc => by
      have hmem : (⟨x, hx⟩ : ruP) ∈ center ruP := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hc g g.2).symm
      rw [hcenter, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem }

theorem ru_core_bot_record (i : Fin 31) (hi : i = 0 ∨ i = 1)
    (B : Subgroup (Equiv.Perm (Fin 4060))) (hPB : ruP ≤ B) (hBR : B ≤ ruP) :
    inSubgroup (aschbacherSolvableCore 5)
      (B ⊓ centralizer ({ruFiveLine i} : Set (Equiv.Perm (Fin 4060)))) = ⊥ := by
  obtain ⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC1, -⟩, ⟨hA0C, hA0n, hA0P, -, hA0e, -, hA0c⟩,
    ⟨hDs, hDnab, -, hDP, -, hDcard⟩⟩ := R3E_Ru_full_five_centralizer_structures
  rcases hi with rfl | rfl
  · exact core_bot_of_record_five hC0 hA0C hA0n hA0P hA0e hA0c hPB hBR
  · exact core_bot_of_record_derived hC1 hDs hDnab hDP hDcard hPB hBR

theorem ru_core_bot (B : Subgroup (Equiv.Perm (Fin 4060))) (hPB : ruP ≤ B) (hBR : B ≤ ruP)
    (y : Equiv.Perm (Fin 4060)) (hy : y ∈ ruP) (hord : orderOf y = 5) :
    inSubgroup (aschbacherSolvableCore 5) (B ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 4060)))) =
      ⊥ := by
  obtain ⟨⟨-, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -⟩ :=
    R3E_Ru_full_five_centralizer_structures
  refine core_bot_of_lines_R Nat.prime_five ru_autModel (by omega) hQsyl hlines (fun j => ?_) B
    hPB hBR y hy hord
  obtain ⟨hjR, hjconj⟩ := htrans j
  have hmem : (ruFiveRecordOf j : ℕ) = 0 ∨ (ruFiveRecordOf j : ℕ) = 1 := by
    have := hrecmem j
    simpa using this
  refine ⟨ruFiveRecordOf j, ⟨ruFiveTransporter j, hjR, hjconj⟩, fun B' hPB' hBR' => ?_⟩
  refine ru_core_bot_record _ ?_ B' hPB' hBR'
  rcases hmem with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem almostSimpleLocalCoresTrivial_five_Ru : AlmostSimpleLocalCoresTrivial 5 (Carrier .Ru) := by
  intro H _ _ K _ hK hC x hx
  obtain ⟨e⟩ := hK
  exact aschbacherCore_centralizer_eq_bot_of_model ru_autModel (by omega) Nat.prime_five
    (by norm_num) (fun B hPB hBR y hyP hy => ru_core_bot B hPB hBR y hyP hy) K
    (e.trans ruEquivP) hC x hx

theorem sporadicPlaneOdd_Ru : SporadicPlaneOdd (Carrier .Ru) := by
  refine sporadicPlaneOdd_of_almostSimple {5} (fun q hq _ => ?_) ?_
  · rw [Finset.mem_singleton.mp hq]
    exact almostSimplePlaneOdd_of_localCoresTrivial Nat.prime_five
      almostSimpleLocalCoresTrivial_five_Ru
  · intro T _ _ _ hnab hTA p hp hp3 hpS
    obtain ⟨e⟩ := hTA
    have hp5 : p ≠ 5 := fun h => hpS (by simp [h])
    have hcard : Nat.card (MulAut T) = 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 2639 := by
      obtain ⟨-, hconj, -, -⟩ := CTUC_Ru_full_inner_automorphisms_and_second_centralizer
      rw [Nat.card_congr (MulAut.congr (e.trans ruEquivP)).toEquiv,
        ← Nat.card_congr (Equiv.ofBijective (MulAut.conj : ruP →* MulAut ruP) hconj),
        card_ruP_five]
      norm_num
    rw [hcard]
    exact not_sq_dvd_mul_of_coprime (B := 51) hp (coprime_two_three_five_pow hp hp3 hp5 14 3 3)
      (by norm_num) (by decide) (by norm_num)

end CFSG.RankThree.PartOne
