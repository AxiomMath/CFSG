
module

public import CFSG.RankThree.PartOne.S11c.HNSevenFixBase

public import CFSG.RankThree.PartOne.S11c.HNCoverAbstract
public import CFSG.RankThree.PartOne.S11c.HNSevenInputs
public import CFSG.Sporadic.HNOddCore.InvRow2
public import CFSG.Sporadic.HNSchreier.Order
public import Certificates.Certificate14980
public import Mathlib.GroupTheory.Perm.Centralizer

public noncomputable section

namespace CFSG.RankThree.PartOne.HNRed

open Equiv Subgroup
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.He.Native
open CFSG.RankThree.PartOne.HNRed.Native

theorem seven_parts :
    plettersOK 17 sevenWord = true ∧
    fixedSet hnsData.n #[pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) sevenWord] = [0] ∧
    natOK natStrongArr (pinvs 12 natStrongArr) sevenWord (natArr cyc7) = true := by
  obtain ⟨h1, h2⟩ := Certificates.certificate14980
  refine ⟨?_, ?_, ?_⟩
  · unfold sevenChecksO sevenChecksR at h1
    rw [← hRegs_eq, ← hStrongArr_eq] at h1
    unfold sevenChecksH at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.1
  · unfold sevenChecksO sevenChecksR at h1
    rw [← hRegs_eq, ← hStrongArr_eq] at h1
    unfold sevenChecksH at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact h1.2
  · unfold sevenNatCheck at h2
    rw [← natStrongArr_eq] at h2
    exact h2

theorem natWord_seven :
    natWord sevenWord = sigma7 :=
  natWord_of_natOK prep_sigma7 (seven_parts).2.2

theorem thetaJ_sevenH :
    (thetaJ (hWordH sevenWord) : Perm (Fin 12)) = sigma7 := by
  rw [thetaJ_hWordH, natWord_seven]

theorem orderOf_sevenJ :
    orderOf sevenJ = 7 :=
  orderOf_coe_of_equiv thetaJ (hWordH sevenWord) (by
    rw [← Subgroup.orderOf_coe, thetaJ_sevenH, orderOf_sigma7])

theorem fix_seven
    {x : X} (h : sevenJ • x = x) : x = x0 := by
  have hmem : x.val ∈ fixedSet hnsData.n
      #[pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) sevenWord] := by
    apply mem_fixedSet_of x.isLt
    intro g hg
    rw [Array.mem_singleton] at hg
    rw [hg, prep_hWord (seven_parts).1 x]
    exact congrArg Fin.val h
  rw [(seven_parts).2.1] at hmem
  exact Fin.ext (List.mem_singleton.1 hmem)

theorem centralizer_sevenJ_le_HJ :
    centralizer ({sevenJ} : Set JH) ≤ HJ := fun c hc =>
  (mem_HJ_iff_fix c).2 (smul_eq_of_mem_centralizer
    ((mem_HJ_iff_fix _).1 (hWordJ_mem sevenWord)) (fun _ h => fix_seven h) hc)

theorem card_centralizer_sevenJ_dvd :
    Nat.card (centralizer ({sevenJ} : Set JH)) ∣ 840 := by
  have hu : sevenJ ∈ HJ := hWordJ_mem sevenWord
  have h := card_centralizer_dvd_of_embedding thetaHom thetaHom_injective hu
    centralizer_sevenJ_le_HJ
  have e : thetaHom (⟨sevenJ, hu⟩ : HJ) = sigma7 := thetaJ_sevenH
  rwa [e, card_centralizer_sigma7] at h

theorem not_25_dvd_card_centralizer_sevenJ :
    ¬ 5 ^ 2 ∣ Nat.card (centralizer ({sevenJ} : Set JH)) := fun h => by
  have := h.trans card_centralizer_sevenJ_dvd
  norm_num at this

theorem exists_conj_pow_of_commute_seven_JH
    {f w : JH}
    (hf : orderOf f = 5) (hw : orderOf w = 5)
    (hfu : ∃ u : JH, orderOf u = 7 ∧ f * u = u * f)
    (hwu : ∃ u : JH, orderOf u = 7 ∧ w * u = u * w) :
    ∃ (g : JH) (a : ℕ), w = g * f ^ a * g⁻¹ :=
  exists_conj_pow_of_commute_seven orderOf_sevenJ (by rw [card_JH]; norm_num)
    not_25_dvd_card_centralizer_sevenJ hf hw hfu hwu

end CFSG.RankThree.PartOne.HNRed
