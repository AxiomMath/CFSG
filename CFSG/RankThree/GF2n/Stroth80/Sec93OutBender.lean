module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.CGT.Timmesfeld75.ListWCL2
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_le_two_of_isElemAbelian_of_cyclic_sylow {Y : Type} [Group Y] [Finite Y]
    (hY : ∀ P : Sylow 2 Y, IsCyclic P) (A : Subgroup Y) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 := by
  obtain ⟨P, hAP⟩ := (IsElemAbelian.isPGroup hA).exists_le_sylow
  haveI : IsCyclic P := hY P
  haveI : IsCyclic A :=
    isCyclic_of_injective (Subgroup.inclusion hAP) (Subgroup.inclusion_injective hAP)
  haveI : Fintype A := Fintype.ofFinite A
  classical
  have h := IsCyclic.card_pow_eq_one_le (α := A) (n := 2) (by norm_num)
  have hall : (Finset.univ.filter fun a : A => a ^ 2 = 1) = Finset.univ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Subtype.ext (hA.2 a a.2)
  rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card] at h
  exact h


theorem benderType_of_psl2 {G : Type} [Group G] {f : ℕ}
    (hG : StatedClassicalModel G .PSL 2 2 f) : BenderType G f 1 1 := by
  obtain ⟨hf, ⟨e⟩⟩ := exists_psl2_galois_of_statedClassicalModel hG
  exact BenderType.linear f hf e

theorem exists_benderType_of_sz {G : Type} [Group G] {s : ℕ}
    (hG : CFSG.Blueprint.LieModel G .twistedB2 0 2 s) : ∃ n i e, BenderType G n i e := by
  obtain ⟨a, ha, -, ⟨e⟩⟩ := exists_sz_of_lieModel hG
  exact isBenderGroup_iff_exists_benderType.mp (isBenderGroup_of_mulEquiv_sz ha e)

theorem exists_benderType_of_psu3 {G : Type} [Group G] {s : ℕ} (hs : 2 ≤ s)
    (hG : StatedClassicalModel G .PSU 3 2 s) : ∃ n i e, BenderType G n i e := by
  obtain ⟨e⟩ := exists_psu3_of_statedClassicalModel hs hG
  exact isBenderGroup_iff_exists_benderType.mp (.isPSU3 s hs (e.trans (MulEquiv.subgroupCongr
    (show CFSG.Open.PSU3 2 s = CFSG.Theory.Comparator.PSU3Model s from rfl))))

theorem outer_elemAbelian_card_le_two_of_benderType
    {K : Type} [Group K] [Finite K] {n i e : ℕ} (h : BenderType K n i e)
    (A : Subgroup (Outer K)) (hA : IsElemAbelian 2 A) : Nat.card A ≤ 2 := by
  haveI : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    DFunLike.coe_injective
  haveI : Finite (Outer K) := inferInstance
  exact card_le_two_of_isElemAbelian_of_cyclic_sylow (fun P => h.isCyclic_sylow_outer P) A hA

theorem listOutBound_psl2 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : StatedClassicalModel S .PSL 2 2 f) (A : Subgroup (Outer S)) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 4 :=
  (outer_elemAbelian_card_le_two_of_benderType (benderType_of_psl2 hS) A hA).trans (by norm_num)

theorem listOutBound_sz {S : Type} [Group S] [Finite S] {s : ℕ}
    (hS : CFSG.Blueprint.LieModel S .twistedB2 0 2 s) (A : Subgroup (Outer S))
    (hA : IsElemAbelian 2 A) : Nat.card A ≤ 4 := by
  obtain ⟨n, i, e, h⟩ := exists_benderType_of_sz hS
  exact (outer_elemAbelian_card_le_two_of_benderType h A hA).trans (by norm_num)

theorem listOutBound_psu3 {S : Type} [Group S] [Finite S] {s : ℕ}
    (hs : 2 ≤ s) (hS : StatedClassicalModel S .PSU 3 2 s) (A : Subgroup (Outer S))
    (hA : IsElemAbelian 2 A) : Nat.card A ≤ 4 := by
  obtain ⟨n, i, e, h⟩ := exists_benderType_of_psu3 hs hS
  exact (outer_elemAbelian_card_le_two_of_benderType h A hA).trans (by norm_num)

end CFSG.RankThree.GF2n.Stroth80
