module

public import CFSG.LocalAnalysis.SteinbergCCHSPresentation

public section

namespace CFSG.LocalAnalysis.HigmanSimsCover

open Subgroup CFSG.CosetTable CFSG.LieType.Multipliers CFSG.RankThree.PerfectCover

abbrev wFree : Fin 3 → FreeGroup (Fin 3) := fun i => FreeGroup.mk (commWords (pairs i))

theorem wFree_mem (i : Fin 3) : wFree i ∈ commutator (FreeGroup (Fin 3)) :=
  mk_commWords_mem_commutator _

abbrev Cover : Type := PresentedCover (wordSet rels) wFree

noncomputable abbrev coverπ
    : Cover →* CFSG.Blueprint.NativeSporadic.HS :=
  coverMap isPresentation_HS pairs_eval_HS

theorem coverRelators_eq : coverRelators (wordSet rels) wFree = wordSet coverWs :=
  coverRelators_wordSet rels fun i => commWords (pairs i)

theorem card_coverWs_le
    : Finite (PG 3 coverWs) ∧ Nat.card (PG 3 coverWs) ≤ 2 * 44352000 :=
  cover_bound

theorem two_dvd_orderOf_coverWs :
    2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ coverWs.map FreeGroup.mk}
      (FreeGroup.mk kerWord)) :=
  kerWord_order

theorem card_cover_le
    : Finite Cover ∧ Nat.card Cover ≤ 2 * 44352000 := by
  have key : ∀ S : Set (FreeGroup (Fin 3)), wordSet coverWs = S →
      Finite (PresentedGroup S) ∧ Nat.card (PresentedGroup S) ≤ 2 * 44352000 := by
    rintro S rfl
    exact card_coverWs_le
  exact key _ coverRelators_eq.symm

noncomputable abbrev kerElt : Cover := PresentedGroup.mk _ (FreeGroup.mk kerWord)

theorem two_dvd_orderOf_kerElt : 2 ∣ orderOf kerElt := by
  have key : ∀ S : Set (FreeGroup (Fin 3)), wordSet coverWs = S →
      2 ∣ orderOf (PresentedGroup.mk S (FreeGroup.mk kerWord)) := by
    rintro S rfl
    exact two_dvd_orderOf_coverWs
  exact key _ coverRelators_eq.symm

theorem kerElt_mem : kerElt ∈ coverπ.ker := by
  rw [MonoidHom.mem_ker, coverMap_mk]
  exact isPresentation_HS.lift_eq_one (List.mem_map_of_mem kerWord_mem)

instance : Finite Cover := card_cover_le.1

theorem card_ker_coverπ
    : Nat.card coverπ.ker = 2 := by
  have hX : Nat.card CFSG.Blueprint.NativeSporadic.HS = 44352000 := CFSG.Sporadic.HS.card_HS
  have h := coverπ.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (coverMap_surjective isPresentation_HS pairs_eval_HS)).toEquiv, hX] at h
  have hle : Nat.card coverπ.ker ≤ 2 := by
    have := card_cover_le.2
    omega
  have hdvd : 2 ∣ Nat.card coverπ.ker := by
    refine two_dvd_orderOf_kerElt.trans ?_
    rw [← Subgroup.orderOf_mk kerElt kerElt_mem]
    exact orderOf_dvd_natCard _
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)

theorem card_hopfMultiplier
    : Nat.card (hopfMultiplier CFSG.Blueprint.NativeSporadic.HS) = 2 := by
  rw [Nat.card_congr (hopfMultiplierEquivKer isPresentation_HS wFree_mem pairs_eval_HS).toEquiv]
  exact card_ker_coverπ

end CFSG.LocalAnalysis.HigmanSimsCover
