module

public import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1423

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec6 CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_index_two {N K : Subgroup G} (hidx : (N.subgroupOf K).index = 2) :
    ⁅K, K⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  set S := N.subgroupOf K with hS
  set a : K := ⟨x, hx⟩
  set b : K := ⟨y, hy⟩
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ S ↔ (a * b * a⁻¹ ∈ S ↔ b⁻¹ ∈ S) :=
    Subgroup.mul_mem_iff_of_index_two hidx
  have h2 : a * b * a⁻¹ ∈ S ↔ (a * b ∈ S ↔ a⁻¹ ∈ S) := Subgroup.mul_mem_iff_of_index_two hidx
  have h3 : a * b ∈ S ↔ (a ∈ S ↔ b ∈ S) := Subgroup.mul_mem_iff_of_index_two hidx
  have hi1 : a⁻¹ ∈ S ↔ a ∈ S := inv_mem_iff
  have hi2 : b⁻¹ ∈ S ↔ b ∈ S := inv_mem_iff
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ S := by
    rw [h1, h2, h3, hi1, hi2]
    by_cases hp : a ∈ S <;> by_cases hq : b ∈ S <;>
      simp only [hp, hq, iff_self, iff_true, iff_false, not_true_eq_false]
  rw [commutatorElement_def]
  exact Subgroup.mem_subgroupOf.mp hmem

omit [Finite G] in
theorem commutator_sup_zpowers_le {N : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (N : Set G)) :
    ⁅N ⊔ Subgroup.zpowers c, N ⊔ Subgroup.zpowers c⁆ ≤ N := by
  have hZ : Subgroup.zpowers c ≤ Subgroup.normalizer (N : Set G) := Subgroup.zpowers_le.mpr hc
  have hZN : Subgroup.zpowers c ⊔ N ≤ Subgroup.normalizer (N : Set G) :=
    sup_le hZ Subgroup.le_normalizer
  have hcomm : ⁅Subgroup.zpowers c, Subgroup.zpowers c⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  rw [sup_comm]
  calc ⁅Subgroup.zpowers c ⊔ N, Subgroup.zpowers c ⊔ N⁆
      ≤ ⁅Subgroup.zpowers c, Subgroup.zpowers c ⊔ N⁆ ⊔ N :=
        commutator_sup_le_of_le_normalizer hZ hZN
    _ ≤ N := by
        refine sup_le ?_ le_rfl
        rw [Subgroup.commutator_comm]
        refine (commutator_sup_le_of_le_normalizer hZ hZ).trans ?_
        rw [hcomm, bot_sup_eq]

omit [Finite G] in
theorem eq_bot_of_isPerfect_of_le {P S : Subgroup G} (hP : Group.IsPerfect P) (hPS : P ≤ S)
    (hS : Group.IsSolvable S) : P = ⊥ := by
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPS)
      (Subgroup.inclusion_injective hPS)
  exact Group.IsPerfect.not_isSolvable P inferInstance

theorem three_dvd_card_of_sec14Std {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) :
    3 ∣ Nat.card L :=
  three_dvd_card_of_types148
    (h.chosen136.2 c h.toSec13Data.zpowers_mem_omegaA L h.toSec13Data.mem_lA).1

theorem commutator_le_theta_of_item142 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {hAab : IsMulCommutative A} {hcA : c ∈ A} (h142 : Item142 A (lB A) c L hAab hcA)
    {D : Subgroup G} (hDp : Group.IsPerfect D) (hDc : D ≤ Subgroup.centralizer ({c} : Set G))
    (hD3 : ¬ 3 ∣ Nat.card D) (hAD : A ≤ Subgroup.normalizer (D : Set G)) :
    ⁅D, L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  let _ := ker142_normal (LB := lB A) hAab hcA
  have hD := h.toSec13Data
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ H := by
    rw [← centralizer_zpowers148]
    exact Subgroup.centralizer_le_normalizer _
  have hDH : D ∈ invariantPiSubgroups H A (piCompl 3) :=
    ⟨hDc.trans hCH, (isPiSubgroup_piCompl_iff Nat.prime_three D).mpr hD3, hAD⟩
  obtain ⟨Q, hQ, hDQ⟩ := exists_le_mem_maxInvariantPiSubgroups hDH
  obtain ⟨hQmem, halt⟩ := h142 Q hQ
  have hLmem : L ∈ thetaComponentsIn (Subgroup.centralizer ({c} : Set G)) :=
    hD.mem_thetaComponentsAt
  have hLq := isQuasisimple_of_mem_thetaComponentsIn1423 hLmem
  have hLp := isPerfect_of_mem_thetaComponentsIn hLmem
  have hL3 := three_dvd_card_of_sec14Std h
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h hL3
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := hD.le_centralizer
  have hLC : L ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    hLc.trans Subgroup.le_normalizer
  have finish : ∀ M : Subgroup G, D ≤ M → ¬ 3 ∣ Nat.card M →
      M ≤ Subgroup.centralizer ({c} : Set G) → L ≤ Subgroup.normalizer (M : Set G) →
      ⁅D, L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    intro M hDM hM3 hMc hLM
    exact (Subgroup.commutator_mono hDM le_rfl).trans
      (commutator_le_theta_of_normalizes hLq hLp hL3 hM3 (hMc.trans hCL) hLM)
  have hinf3 : ∀ N : Subgroup G, Nat.Coprime 3 (Nat.card N) →
      ¬ 3 ∣ Nat.card (N ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
    intro N hN h3
    have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN
    exact this (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  rcases halt with ⟨-, hQK, hOK, hcard⟩ | ⟨hK, hsub⟩
  ·
    rw [← hHdef] at hOK hcard
    set K := k142 A (lB A) c with hKdef
    have hidx : ((pPrimeCoreOf 3 H).subgroupOf K).index = 2 := by
      have h1 := Subgroup.card_mul_index ((pPrimeCoreOf 3 H).subgroupOf K)
      have h2 : Nat.card ↥((pPrimeCoreOf 3 H).subgroupOf K) = Nat.card (pPrimeCoreOf 3 H) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
      rw [h2, hcard] at h1
      have hpos : 0 < Nat.card (pPrimeCoreOf 3 H) := Nat.card_pos
      have h3 : Nat.card (pPrimeCoreOf 3 H) * ((pPrimeCoreOf 3 H).subgroupOf K).index =
          Nat.card (pPrimeCoreOf 3 H) * 2 := by rw [h1, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hpos h3
    have hDO : D ≤ pPrimeCoreOf 3 H :=
      le_of_isPerfect_of_commutator_le hDp (hDQ.trans hQK.le) (commutator_le_of_index_two hidx)
    refine finish _ (le_inf hDO hDc) (hinf3 _ (coprime_card_pPrimeCoreOf 3 H)) inf_le_right ?_
    refine (le_inf ?_ hLC).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (hLc.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
  ·
    set K := k142 A (lB A) c with hKdef
    set P := pPrimeCoreOf 3 K with hPdef
    have hQK : Q ≤ K := le_delta hQmem.1 (hQmem.2.trans hCH)
    have hDKA : D ≤ kA142 A (lB A) c := (hDQ.trans hQK).trans le_sup_left
    have hsol : Group.IsSolvable (img142 A (lB A) c Q) := by
      rcases hsub with ⟨-, a, ha, -, heq⟩ | ⟨-, ⟨hab, -⟩, -⟩ | ⟨-, ⟨T, ⟨e⟩⟩, -⟩
      · rw [heq]
        have hamem : alpha142 A (lB A) c a ha ∈ img142 A (lB A) c A :=
          ⟨⟨a, Subgroup.mem_sup_right ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
        refine CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer ?_
          (theta_solvable_and_not_dvd _).1 (theta_solvable_and_not_dvd _).1
        refine (theta_le _).trans ((inf_le_inf_left _ ?_).trans (le_normalizer_theta _))
        exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hamem)
      · exact Group.isSolvable_of_comm fun x y => hab.1.is_comm.comm x y
      · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have : Finite ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) :=
          Finite.of_equiv _ e.toEquiv
        have : Group.IsNilpotent
            ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) :=
          T.isPGroup'.isNilpotent
        exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hDimg : img142 A (lB A) c D = ⊥ := by
      have hDp' : Group.IsPerfect (D.subgroupOf (kA142 A (lB A) c)) := by
        have := hDp
        exact Group.IsPerfect.ofSurjective
          (f := (Subgroup.subgroupOfEquivOfLe hDKA).symm.toMonoidHom) (MulEquiv.surjective _)
      have hperf : Group.IsPerfect (img142 A (lB A) c D) := Group.IsPerfect.map _
      exact eq_bot_of_isPerfect_of_le hperf
        (Subgroup.map_mono (Subgroup.subgroupOf_mono _ (hDQ.trans le_rfl))) hsol
    have hDker : D ≤ P ⊔ Subgroup.zpowers c := by
      have h1 : D.subgroupOf (kA142 A (lB A) c) ≤ ker142 A (lB A) c := by
        have := (Subgroup.map_eq_bot_iff _).mp hDimg
        rwa [QuotientGroup.ker_mk'] at this
      exact LocalCores.le_of_subgroupOf_le hDKA h1
    have hcP : c ∈ Subgroup.normalizer (P : Set G) :=
      normalizer_le_normalizer_pPrimeCoreOf 3 K
        ((le_normalizer_sSup fun Q' hQ' => hQ'.1.1.2.2 : A ≤ Subgroup.normalizer (K : Set G)) hcA)
    have hDP : D ≤ P := le_of_isPerfect_of_commutator_le hDp hDker (commutator_sup_zpowers_le hcP)
    refine finish _ (le_inf hDP hDc) (hinf3 _ (coprime_card_pPrimeCoreOf 3 K)) inf_le_right ?_
    have hLK : L ≤ K := by
      rw [hK]
      exact le_sup_left.trans le_sup_left
    exact (le_inf (hLK.trans (le_normalizer_pPrimeCoreOf 3 K)) hLC).trans
      Subgroup.inf_normalizer_le_normalizer_inf

end CFSG.RankThree.PartTwo.Sec15.Proof1423
