module

public import CFSG.RankThree.PartTwo.Sec15.KL3Sub3ProofAct
public import CFSG.RankThree.PartTwo.Sec15.KL3Sub3ProofArith
public import CFSG.RankThree.PartTwo.Sec15.KL3Sub3ProofSL
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.RankThree.PartTwo.Sec15.KL3Sub2ProofL325

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub3Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem false_of_alternating_seven {T : Type} [Group T] (e : T ≃* alternatingGroup (Fin 7))
    (hAut : 6720 ∣ Nat.card (MulAut T)) : False := by
  have h1 : Nat.card (MulAut T) = Nat.card (MulAut (alternatingGroup (Fin 7))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have h2 : Nat.card (MulAut (alternatingGroup (Fin 7))) = Nat.card (Equiv.Perm (Fin 7)) :=
    (Nat.card_congr (Equiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
        (by norm_num)))).symm
  rw [h1, h2, Nat.card_perm, Nat.card_fin] at hAut
  norm_num [Nat.factorial] at hAut

theorem false_of_m11 {T : Type} [Group T]
    (e : T ≃* CFSG.Assembly.LowTwoRank.StatedM11) (hT : Nat.card T ∣ 152334000000) : False := by
  rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.GL2Recognition.card_lowTwoRankStatedM11]
    at hT
  norm_num at hT

theorem kl325Quasi :
    KL325Quasi := by
  intro G H hHG hnorm hq _ hscal hHdet hZ hGdet hcard g hg
  have hodd : Odd (Nat.card (GaloisField 5 2)) := by
    rw [card_galois]
    exact ⟨12, rfl⟩
  have hAut : 6720 ∣ Nat.card (MulAut (H ⧸ Subgroup.center H)) :=
    dvd_card_mulAut G H hnorm hq.1 hscal hGdet hcard
  have hO : 6720 ∣ Nat.card (H ⧸ Subgroup.center H) *
      Nat.card (Outer (H ⧸ Subgroup.center H)) :=
    hAut.trans (card_mulAut_dvd _)
  have hT : Nat.card (H ⧸ Subgroup.center H) ∣ 152334000000 :=
    card_SL_galois ▸ card_quotient_center_dvd hHdet
  rcases CFSG.RankThree.SubgroupLists.quotient_center_rank_two_cases hodd hq hHdet hZ with
    ⟨r, f, hr, hr2, hf, h⟩ | ⟨r, f, hr, hr2, hf, h⟩ | ⟨r, f, hr, hr2, hf, h⟩ | h | he | he
  · obtain ⟨hs, -, -, ho, -⟩ := linear_model_outer_two_part_bound _ 2 r f h
    exact (false_of_psl2 hr hr2 hf hs hT (ho rfl) hO).elim
  · obtain ⟨hs, -, -, -, ho⟩ := linear_model_outer_two_part_bound _ 3 r f h
    have h3 := eq_of_psl3 hr hr2 hf hs hT (ho le_rfl) hO
    apply hHG
    refine (forall_mem_iff_det_of_card hHdet hZ ?_ g).mpr hg
    rw [card_galois, card_SL_galois, show Nat.gcd (25 - 1) 3 = 3 by norm_num]
    exact h3
  · obtain ⟨hs, -, ho, -, -⟩ := unitary_model_outer_two_part_bound _ 3 r f h
    exact (false_of_psu3 hr hr2 hf hs hT ho hO).elim
  · obtain ⟨hs, -, ho, -, -⟩ := unitary_model_outer_two_part_bound _ 3 2 2 h
    exact (false_of_psu34 hs ho hO).elim
  · obtain ⟨e⟩ := he
    exact (false_of_alternating_seven e hAut).elim
  · obtain ⟨e⟩ := he
    exact (false_of_m11 e hT).elim

theorem kl325SubgroupOrder :
    KL325SubgroupOrder :=
  KL3Sub2Proof.kl325SubgroupOrder_of_quasi kl325Quasi

end KL3Sub3Proof

end CFSG.RankThree.PartTwo.Sec15
