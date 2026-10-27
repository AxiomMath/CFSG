module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import Certificates.Certificate17260
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Data

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.J2Cover


@[expose] noncomputable def permY0 : Equiv.Perm (Fin 315) := perm y0Arr

@[expose] noncomputable def P3j : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 p3Tbls

theorem rep_permY0 (h : isInvA 315 y0Arr (invCand 315 y0Arr) = true) :
    CFSG.Monster.B.Co2.Rep 315 y0Arr permY0 :=
  (rep_permOfArr h).1

theorem exists_conj_orderOf_four :
    ∀ r ∈ [permA, permTwoA, permU], ∃ y ∈ P, orderOf (r * (y⁻¹ * r * y)) = 4 := by
  have hc : kf2Check = true := Certificates.certificate17260.1
  have key : ∀ i < 3, ∀ r, CFSG.Monster.B.Co2.Rep 315 invReps[i]! r →
      ∃ y ∈ P, orderOf (r * (y⁻¹ * r * y)) = 4 := by
    intro i hi r hr
    have h := List.all_eq_true.1 hc i (List.mem_range.2 hi)
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hinv, hP⟩, hord⟩ := h
    obtain ⟨hy, hyinv⟩ := rep_permOfArr hinv
    refine ⟨permOfArr 315 kf2Arrs[i]!, (mem_P_iff hy).1 hP, ?_⟩
    have hrep := rep_compA hr (rep_compA (rep_compA hyinv hr) hy)
    exact (ordTest_iff_perm (rep_arrTable (by norm_num) hrep) (by norm_num)).1 hord
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact key 0 (by norm_num) _ rep_permA
  · exact key 1 (by norm_num) _ rep_permTwoA
  · exact key 2 (by norm_num) _ rep_permU

theorem permY0_facts :
    permY0 ∈ P ∧ permY0 * permTwoA = permTwoA * permY0 ∧ orderOf permY0 = 3 := by
  have h : y0Check = true := Certificates.certificate17260.2.1
  simp only [y0Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hinv, hP⟩, hcomm⟩, hord⟩ := h
  have hy := rep_permY0 hinv
  refine ⟨(mem_P_iff hy).1 hP, ?_, ?_⟩
  · exact eq_of_eqA (rep_compA hy rep_permTwoA) (rep_compA rep_permTwoA hy) hcomm
  · exact (ordTest_iff_perm (rep_arrTable (by norm_num) hy) (by norm_num)).1 hord

theorem tp_arrTable_eq {g : Array ℕ} (hg : isInvA 315 g (invCand 315 g) = true)
    (hp : permOK 315 (arrTable 315 g) = true) : tp 315 (arrTable 315 g) = permOfArr 315 g :=
  CFSG.Sporadic.Schreier.rep_unique (rep_tp hp) (rep_arrTable (by norm_num) (rep_permOfArr hg).1)

theorem P3j_facts :
    P3j ≤ P ∧ Nat.card P3j = 27 ∧ CFSG.Quasithin.centerOf P3j = Subgroup.zpowers permY0 := by
  classical
  have h : p3Check = true := Certificates.certificate17260.2.2
  simp only [p3Check, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hgens, hperm⟩, henum⟩, hnc⟩ := h
  have hgens' := List.all_eq_true.1 hgens
  have hperm' := List.all_eq_true.1 hperm
  have hfact : ∀ g ∈ p3List, isInvA 315 g (invCand 315 g) = true ∧ inP g = true ∧
      commA g y0Arr = true ∧ permOfArr 315 g ∈ P3j := by
    intro g hg
    have h1 := hgens' g hg
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨hi, hp⟩, hc⟩ := h1
    have hmem : arrTable 315 g ∈ p3Tbls := List.mem_map_of_mem hg
    refine ⟨hi, hp, hc, ?_⟩
    rw [P3j, genOf, ← tp_arrTable_eq hi (hperm' _ hmem)]
    exact Subgroup.subset_closure ⟨_, by simpa using hmem, rfl⟩
  have hgen : ∀ x ∈ {x | x ∈ p3Tbls.toArray}, ∃ g ∈ p3List, tp 315 x = permOfArr 315 g := by
    intro x hx
    have hx' : x ∈ p3Tbls := by simpa using hx
    have hpx := hperm' x hx'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx'
    exact ⟨g, hg, tp_arrTable_eq (hfact g hg).1 hpx⟩
  have hy0mem : y0Arr ∈ p3List := List.mem_cons_self
  have ha : p3a ∈ p3List := List.mem_cons_of_mem _ List.mem_cons_self
  have hc : p3c ∈ p3List :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hle : P3j ≤ P := by
    rw [P3j, genOf, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, he⟩ := hgen x hx
    rw [he]
    exact (mem_P_iff (rep_permOfArr (hfact g hg).1).1).1 (hfact g hg).2.1
  have hcard : Nat.card P3j = 27 := (enumOK_spec (by norm_num) hperm' henum).1
  have hinv0 := (hfact _ hy0mem).1
  have hy0cent : permY0 ∈ Subgroup.centralizer (P3j : Set (Equiv.Perm (Fin 315))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, P3j, genOf] at hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨T, hT, rfl⟩ := hx
      obtain ⟨g, hg, he⟩ := hgen T hT
      rw [he]
      exact eq_of_eqA (rep_compA (rep_permOfArr (hfact g hg).1).1 (rep_permY0 hinv0))
        (rep_compA (rep_permY0 hinv0) (rep_permOfArr (hfact g hg).1).1) (hfact g hg).2.2.1
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx => rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_inv_cancel_right]
  have hy0 : y0Check = true := Certificates.certificate17260.2.1
  simp only [y0Check, Bool.and_eq_true] at hy0
  have hordY : orderOf permY0 = 3 :=
    (ordTest_iff_perm (rep_arrTable (by norm_num) (rep_permY0 hinv0)) (by norm_num)).1 hy0.2
  have hnab : ∃ a ∈ P3j, ∃ b ∈ P3j, a * b ≠ b * a := by
    refine ⟨_, (hfact _ ha).2.2.2, _, (hfact _ hc).2.2.2, fun he => ?_⟩
    have := (eqA_iff (rep_compA (rep_permOfArr (hfact _ ha).1).1 (rep_permOfArr (hfact _ hc).1).1)
      (rep_compA (rep_permOfArr (hfact _ hc).1).1 (rep_permOfArr (hfact _ ha).1).1)).2 he
    rw [show commA p3a p3c = eqA 315 (compA 315 p3a p3c) (compA 315 p3c p3a) from rfl,
      this] at hnc
    exact Bool.noConfusion hnc
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hZ : Nat.card (CFSG.Quasithin.centerOf P3j) = 3 :=
    CFSG.AGLEmbedding.card_centerOf_of_nonabelian (by rw [hcard]; norm_num) hnab
  refine ⟨hle, hcard, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    exact ⟨(hfact _ hy0mem).2.2.2, hy0cent⟩
  · rw [hZ, Nat.card_zpowers, hordY]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

end
