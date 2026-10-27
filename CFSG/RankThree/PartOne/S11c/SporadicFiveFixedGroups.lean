module

public import CFSG.RankThree.PartOne.S11c.SporadicFiveFixed
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneTh
public import CFSG.RankThree.PartOne.KS.Suz
public import CFSG.Sporadic.Schreier.J4SOuter

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.SmallOddCore
  CFSG.RankThree.Native CFSG.Sporadic.SuzOddCore
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Sporadic.ThSchreier (ctuc_Th_full_automorphism_group)
open CFSG.Sporadic.J4Schreier (R3E_J4_outer_automorphism_group_no_large_primes)

theorem noFiveFixedPSU3_Th :
    NoFiveFixedPSU3 (Carrier .Th) := by
  have hinv : ThPlane.InvCentConj ThPlane.thData.M := ThPlane.invCentConj_J
  have hfix5 : ∀ v, ThPlane.thData.act ThPlane.w5 v = v → v = 0 := fun v hv =>
    ThPlane.fix5 v (by rw [← ThPlane.act_w5]; exact hv)
  refine noFiveFixedPSU3_of_data (P := (⊤ : Subgroup J)) (R := (⊤ : Subgroup J)) le_rfl
    (thEquivJ.trans Subgroup.topEquiv.symm) (k := 8) (by norm_num) ?_ ?_
  · intro T _ _ eT α _
    let e0 : T ≃* CFSG.Blueprint.NativeSporadic.Th := eT
    obtain ⟨hinn, -⟩ := ctuc_Th_full_automorphism_group.2 T ⟨e0⟩
    have hmem : α ∈ inner T := hinn ▸ Subgroup.mem_top α
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, hb⟩
  · exact fun y _ hord R2 h2 hle =>
      ThPlane.card_le_eight_five_gen ThPlane.thData hinv ThPlane.w5_mem
        ThPlane.orderOf_π_w5 hfix5 y hord R2 h2 (hle.trans inf_le_right)

theorem not_sq_dvd_card_mulAut_J4_five
    {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    (e : T ≃* CFSG.Blueprint.NativeSporadic.J4) : ¬ 5 ^ 2 ∣ Nat.card (MulAut T) := by
  have hc : center T = ⊥ := center_eq_bot_of_simple hnab
  rw [card_mulAut_eq_mul_card_outer hc]
  have hout : ¬ 5 ∣ Nat.card (Outer T) := fun hd => by
    rcases (R3E_J4_outer_automorphism_group_no_large_primes ⟨e⟩).1 5 Nat.prime_five hd with h | h
      <;> omega
  have hcop : Nat.Coprime (5 ^ 2) (Nat.card (Outer T)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hout)
  intro hdvd
  have hT : Nat.card T = 86775571046077562880 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4
  rw [hT] at hdvd
  have := hcop.dvd_of_dvd_mul_right hdvd
  norm_num at this

theorem noFiveFixedPSU3_J4 :
    NoFiveFixedPSU3 (Carrier .J4) :=
  noFiveFixedPSU3_of_not_sq_dvd fun _ _ _ _ hnab eT => not_sq_dvd_card_mulAut_J4_five hnab eT

theorem noFiveFixedPSU3_Suz :
    NoFiveFixedPSU3 (Carrier .Suz) := by
  obtain ⟨⟨-, -, -, -, hQsyl⟩, ⟨hlines, -⟩, hCD, hgood, hbad⟩ :=
    R3E_Suz_full_five_centralizer_structures
  refine noFiveFixedPSU3_of_model_card suz_autModel suz_card_le suzEquivM ?_
  refine card_ne_of_lines_cent Nat.prime_five suzM_le_suzT hQsyl hlines (fun j => ?_)
  refine ⟨j, ⟨1, suzT.one_mem, by simp⟩, fun R2 hle => ?_⟩
  have hC : suzFiveC j = centralizer ({suzFiveLine j} : Set (Equiv.Perm (Fin 1782))) ⊓ suzT :=
    (hCD j).1
  have hle' : R2 ≤ suzFiveC j := by
    rw [hC, inf_comm]
    exact hle
  have hdvd := Subgroup.card_dvd_of_le hle'
  have hbound : Nat.card (suzFiveC j) ≤ 3600 := by
    by_cases hg : j.val = 0 ∨ j.val = 3 ∨ j.val = 4
    · exact (hgood j hg).1.le
    · have : j.val = 1 ∨ j.val = 2 ∨ j.val = 5 := by
        have := j.2
        omega
      exact ((hbad j this).1).le.trans (by norm_num)
  have hpos : 0 < Nat.card (suzFiveC j) := Nat.card_pos
  have := Nat.le_of_dvd hpos hdvd
  omega

end CFSG.RankThree.PartOne.HNRed
