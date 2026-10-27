module

public import CFSG.RankThree.PartTwo.Sec14.Item1446
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sub147

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem commutator_le_of_le_pPrimeCoreOf (hA : IsE27 A) (h444 : Item1444 A LB)
    {Y N W : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G))
    (hIN : delta A LB (pPrimeCoreOf 3 Y) ≤ N) (hWK : W ≤ pPrimeCoreOf 3 Y)
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hWN : W ≤ Subgroup.normalizer (N : Set G))
    {B Q : Subgroup G} (hB : IsHyperplane A B) (hQ : Q ∈ scriptQZero A LB)
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) :
    ⁅Q, W⁆ ≤ N := by
  have hB9 : 3 ^ 2 ≤ Nat.card B := by
    have h := hB.2
    rw [hA.2] at h
    have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [h9]
    omega
  have hW3 : Nat.Coprime 3 (Nat.card W) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hWK) (coprime_card_pPrimeCoreOf 3 Y)
  have hWT : W ≤ commutatorInSubgroup Q N := by
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three
      (Sec5.isElemAbelian_of_le hA.1 hB.1) hB9 (hB.1.trans hAW) hW3 fun v hv hv1 k hk => ?_
    refine mem_commutatorInSubgroup.mpr ⟨hWN (Subgroup.mem_inf.mp hk).1, fun q hq => ?_⟩
    have hQv : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {v}) :=
      ⟨hQ, hQY.trans (inf_le_right.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)))⟩
    have hk' : k ∈ pPrimeCoreOf 3 Y ⊓ Subgroup.centralizer {v} :=
      Subgroup.mem_inf.mpr ⟨hWK (Subgroup.mem_inf.mp hk).1, (Subgroup.mem_inf.mp hk).2⟩
    exact hIN (commutator_inf_centralizer_le_delta h444 hA.1.1 hY (hB.1 hv) hv1 hQv
      (hQY.trans inf_le_left) (Subgroup.commutator_mem_commutator hq hk'))
  rw [Subgroup.commutator_le]
  intro q hq k hk
  exact (mem_commutatorInSubgroup.mp (hWT hk)).2 q hq

theorem commutator_deltaZero_le_of_le_pPrimeCoreOf (hA : IsE27 A) (h444 : Item1444 A LB)
    {Y N W : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G))
    (hIN : delta A LB (pPrimeCoreOf 3 Y) ≤ N) (hWK : W ≤ pPrimeCoreOf 3 Y)
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hWN : W ≤ Subgroup.normalizer (N : Set G))
    (hXN : deltaZero A LB Y ≤ Subgroup.normalizer (N : Set G)) :
    ⁅deltaZero A LB Y, W⁆ ≤ N := by
  have hXT : deltaZero A LB Y ≤ commutatorInSubgroup W N := by
    rw [deltaZero_eq_iSup hA Y]
    refine iSup₂_le fun B hB => sSup_le fun Q hQ x hx => ?_
    have hxX : x ∈ deltaZero A LB Y := deltaZero_mono inf_le_left (le_deltaZero hQ.1 hQ.2 hx)
    refine mem_commutatorInSubgroup.mpr ⟨hXN hxX, fun k hk => ?_⟩
    have h := Subgroup.commutator_le.mp
      (commutator_le_of_le_pPrimeCoreOf hA h444 hY hIN hWK hAW hWN hB hQ.1 hQ.2) x hx k hk
    rw [← commutatorElement_inv]
    exact inv_mem h
  rw [Subgroup.commutator_le]
  intro x hx k hk
  rw [← commutatorElement_inv]
  exact inv_mem ((mem_commutatorInSubgroup.mp (hXT hx)).2 k hk)

theorem le_delta_pPrimeCoreOf_of_isPerfect (hA : IsE27 A) (h444 : Item1444 A LB)
    (h146 : Item146 A LB) {Y W : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hWperf : Group.IsPerfect W)
    (hWX : W ≤ deltaZero A LB Y) (hWK : W ≤ pPrimeCoreOf 3 Y) :
    W ≤ delta A LB (pPrimeCoreOf 3 Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : pPrimeCoreOf 3 Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)),
      hY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)⟩
  have hXN : deltaZero A LB Y ≤
      Subgroup.normalizer (delta A LB (pPrimeCoreOf 3 Y) : Set G) :=
    (deltaZero_le_delta Y).trans (delta_le_normalizer_delta
      (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hK (le_normalizer_pPrimeCoreOf 3 Y))
  calc W = ⁅W, W⁆ := (Subgroup.isPerfect_iff.mp hWperf).symm
    _ ≤ ⁅deltaZero A LB Y, W⁆ := Subgroup.commutator_mono hWX le_rfl
    _ ≤ delta A LB (pPrimeCoreOf 3 Y) :=
      commutator_deltaZero_le_of_le_pPrimeCoreOf hA h444 hY le_rfl hWK hAW (hWX.trans hXN) hXN

theorem mem_scriptQ_of_isPerfect (hA : IsE27 A) (h444 : Item1444 A LB) (h146 : Item146 A LB)
    {Y W : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G))
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hWperf : Group.IsPerfect W)
    (hWX : W ≤ deltaZero A LB Y) (hWK : W ≤ pPrimeCoreOf 3 Y) : W ∈ scriptQ A LB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : pPrimeCoreOf 3 Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)),
      hY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)⟩
  exact mem_scriptQ_of_le (delta_mem_scriptQ hA h146 hK)
    (le_delta_pPrimeCoreOf_of_isPerfect hA h444 h146 hY hAW hWperf hWX hWK) hAW

end CFSG.RankThree.PartTwo.Sec15.Sub147
