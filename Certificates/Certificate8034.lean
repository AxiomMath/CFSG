module

public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMaxInputs
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K8034
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.RankThree.PartTwo.KFacts.L34Max
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.L34MaxT
  CFSG.Certificates.Kernel.PkEnum CFSG.Certificates CFSG.Sporadic.Schreier

namespace Certificates

private theorem testBit_orL (l : List Nat) (j : Nat) : (orL l).testBit j = decide (j ∈ l) := by
  induction l with
  | nil => simp [orL]
  | cons k l ih =>
    have h : orL (k :: l) = orL l ||| (1 <<< k) := rfl
    rw [h, Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases hj : j = k
    · subst hj
      simp
    · have hk : k ≠ j := fun e => hj e.symm
      simp [List.mem_cons, hj, hk]

private theorem mem_u0L (a : Fin 21) : (a : Nat) ∈ u0L ↔ a ∈ U0 := by
  revert a
  decide

private theorem keyN_bit (y : CV 21) (j : Nat) :
    (keyN y).testBit j = decide (∃ h : j < 21, (⟨j, h⟩ : Fin 21) ∈ keyF (ev y)) := by
  rw [keyN, testBit_orL]
  apply decide_eq_decide.2
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hu : ∀ i ∈ u0L, i < 21 := by decide
    have hi21 : i < 21 := hu i hi
    refine ⟨y.2.2.1 i hi21, ?_⟩
    rw [keyF, Finset.mem_image]
    exact ⟨⟨i, hi21⟩, (mem_u0L ⟨i, hi21⟩).1 hi, Fin.ext rfl⟩
  · rintro ⟨hj, hm⟩
    rw [keyF, Finset.mem_image] at hm
    obtain ⟨a, ha, he⟩ := hm
    exact ⟨a, (mem_u0L a).2 ha, congrArg Fin.val he⟩

private theorem keyN_eq_iff (y y' : CV 21) : keyN y = keyN y' ↔ keyF (ev y) = keyF (ev y') := by
  constructor
  · intro h
    ext j
    have h1 := congrArg (fun m => m.testBit j) h
    simp only [keyN_bit] at h1
    simpa [j.2] using h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [keyN_bit, keyN_bit, h]

private theorem keyF_one : keyF (ev (1 : CV 21)) = U0 := by
  rw [ev_one, keyF]
  exact Finset.image_id

private theorem targets_bit (y : CV 21) :
    targets.contains (keyF (ev y)) = targetBits.testBit (keyN y) := by
  rw [targetBits, testBit_orL, Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff,
    targets, elemsT_eq_elemsC, List.flatMap_map, List.mem_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨n, hn, hm⟩
    obtain ⟨g, hg, he⟩ := List.mem_map.1 hm
    refine ⟨n, hn, List.mem_map.2 ⟨cOf g, List.mem_map.2 ⟨g, hg, rfl⟩, ?_⟩⟩
    rw [keyN_eq_iff, ev_mul, ev_cOf]
    exact he
  · rintro ⟨n, hn, hm⟩
    obtain ⟨c, hc, he⟩ := List.mem_map.1 hm
    obtain ⟨g, hg, hgc⟩ := List.mem_map.1 hc
    refine ⟨n, hn, List.mem_map.2 ⟨g, hg, ?_⟩⟩
    have h2 := (keyN_eq_iff _ _).1 he
    rw [← hgc, ev_mul, ev_cOf] at h2
    exact h2

private theorem stab_eq : stabCheck = stabC := by
  rw [stabCheck.eq_1, stabC.eq_1, elemsT_eq_elemsC, List.all_map]
  refine congrArg (List.all (elemsC QP21)) (funext fun y => ?_)
  simp only [Function.comp_apply]
  have h1 : (keyF (ev y) = U0) ↔ (keyN y = orL u0L) := by
    rw [← kKey1, keyN_eq_iff, keyF_one]
  by_cases hc : keyF (ev y) = U0
  · rw [if_pos hc, if_pos (h1.1 hc), sift_ev]
  · rw [if_neg hc, if_neg (mt h1.2 hc), targets_bit]

open CFSG.Certificates CFSG.RankThree.PartTwo.KFacts.L34Max in
theorem certificate8034 : (QN0.check = true ∧ QN0.orderCertificate = 72)
    ∧ (QE0.check = true ∧ QE0.orderCertificate = 9)
    ∧ CFSG.RankThree.PartTwo.KFacts.L34Max.normCheck = true
    ∧ outCheck = true
    ∧ genCheck = true
    ∧ stabCheck = true := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, kGen, ?_⟩
  · exact check_certificate_of _ _ _ _ _ kQN0.1
  · rw [orderCertificate_eq_orderV]
    exact kQN0.2
  · exact check_certificate_of _ _ _ _ _ kQE0.1
  · rw [orderCertificate_eq_orderV]
    exact kQE0.2
  · unfold CFSG.RankThree.PartTwo.KFacts.L34Max.normCheck
    simp only [sift_eq_siftP]
    exact kNorm
  · unfold CFSG.RankThree.PartTwo.KFacts.L34Max.outCheck
    rw [sift_eq_siftP]
    exact kOut
  · rw [stab_eq]
    exact kStab

end Certificates
