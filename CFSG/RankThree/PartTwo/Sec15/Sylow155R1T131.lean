module

import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Item1446

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Late

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_deltaZero_le_delta_of_le_normalizer {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hA : IsE27 A) (h444 : Item1444 A LB) (h146 : Item146 A LB)
    {K V : Subgroup G} (hKΔ : K ≤ delta A LB K) (hV : V ∈ invariantPiSubgroups ⊤ A (piCompl 3))
    (hVK : V ≤ K) (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    ⁅deltaZero A LB K, V⁆ ≤ delta A LB V := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := delta A LB V with hD
  have hKD : K ≤ Subgroup.normalizer (D : Set G) :=
    hKΔ.trans (delta_le_normalizer_delta (fun Z hZ => delta_mem_scriptQ hA h146 hZ) hV hKV)
  have hV3 : Nat.Coprime 3 (Nat.card V) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three V).mp hV.2.1)
  have hQV : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q : Subgroup G,
      Q ∈ collectionIn (scriptQZero A LB) (K ⊓ Subgroup.centralizer (B : Set G)) →
      V ≤ commutatorInSubgroup Q D := by
    intro B hB Q hQ
    have hB9 : 3 ^ 2 ≤ Nat.card B := by
      have h := hB.2
      rw [hA.2] at h
      have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
      rw [h9]
      omega
    have hQK : Q ≤ K := hQ.2.trans inf_le_left
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three
      (Sec5.isElemAbelian_of_le hA.1 hB.1) hB9 (hB.1.trans hV.2.2) hV3 fun v hv hv1 k hk => ?_
    refine mem_commutatorInSubgroup.mpr ⟨hKD (hVK (Subgroup.mem_inf.mp hk).1), fun q hq => ?_⟩
    have hvA : v ∈ A := hB.1 hv
    have hQv : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {v}) :=
      ⟨hQ.1, hQ.2.trans (inf_le_right.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv)))⟩
    have hAv : A ≤ Subgroup.normalizer
        ((Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) :=
      le_trans (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨v, hvA⟩))) Subgroup.le_normalizer
    have hS : V ⊓ Subgroup.centralizer {v} ∈
        invariantPiSubgroups (Subgroup.centralizer {v}) (A ⊔ Q) (piCompl 3) :=
      ⟨inf_le_right, isPiSubgroup_piCompl_of_le hV.2.1 inf_le_left,
        sup_le (le_normalizer_inf hV.2.2 hAv)
          (le_normalizer_inf (hQK.trans hKV) (hQv.2.trans Subgroup.le_normalizer))⟩
    have hmem := h444 v hvA hv1 Q hQv _ hS
    have hle : ⁅Q, V ⊓ Subgroup.centralizer {v}⁆ ≤ V := by
      refine (Subgroup.commutator_mono le_rfl inf_le_left).trans ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQK.trans hKV)
    exact le_delta hmem.1 hle (Subgroup.commutator_mem_commutator hq hk)
  have hXT : deltaZero A LB K ≤ commutatorInSubgroup V D := by
    rw [deltaZero_eq_iSup hA K]
    refine iSup₂_le fun B hB => sSup_le fun Q hQ x hx => ?_
    refine mem_commutatorInSubgroup.mpr ⟨hKD (hQ.2.trans inf_le_left hx), fun k hk => ?_⟩
    have h := (mem_commutatorInSubgroup.mp (hQV B hB Q hQ hk)).2 x hx
    rw [← commutatorElement_inv]
    exact inv_mem h
  rw [Subgroup.commutator_le]
  intro x hx k hk
  rw [← commutatorElement_inv]
  exact inv_mem ((mem_commutatorInSubgroup.mp (hXT hx)).2 k hk)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
