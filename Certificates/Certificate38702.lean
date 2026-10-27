module

public import Certificates.Data.Kernel.SmithD6.WtCheck
public import CFSG.GF2Type.SmithTypeE.DMod.CliffordTv
public import CFSG.GF2Type.SmithTypeE.DMod.Planes
import Certificates.Kernel.SmithD6Wt.TreeMath
import Certificates.Kernel.SmithD6Adj.Glue
import CFSG.Certificates.Kernel.SmithD6KcSound

namespace Certificates

open CertificateChecks

open CFSG.SmithD6 CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod CertificateChecks.SmithD6Pinned

theorem wt_getD38702 {i : ℕ} (hi : i < 75735) : wt i = J.wtC.flatten.getD i 0 := by
  have hl : i < J.wtC.flatten.length := by rw [SmithD6Wt.wtC_flatten_length]; exact hi
  rw [pinnedModel.wt_get i hl, List.getD_eq_getElem _ _ hl]

theorem zip_getD38702 {α β : Type} {a : List α} {b : List β} (h : a.length = b.length) (da : α)
    (db : β) {i : ℕ} (hi : i < a.length) : (a.zip b).getD i (da, db) = (a.getD i da, b.getD i db) := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zip, ← h, min_self]; exact hi), List.getElem_zip,
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (h ▸ hi)]

theorem planes38702 : ∀ i < 75735, planeL (exC (J.wtC.flatten.getD i 0))
    (J.pbC.flatten.getD i #[]).toList (J.ppC.flatten.getD i #[]).toList = true := by
  obtain ⟨hpb, hpp⟩ := SmithD6Wt.pbC_ppC_length
  have h64 := SmithD6Wt.wt64C_length
  have hZc : ∀ c < 37, (List.zipWith List.zip J.pbC J.ppC).getD c [] =
      (J.pbC.getD c []).zip (J.ppC.getD c []) := fun c hc => by
    rw [List.getD_eq_getElem _ _ (by simp [hpb, hpp]; omega), List.getElem_zipWith,
      List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  have hZl : (List.zipWith List.zip J.pbC J.ppC).length = 37 := by simp [hpb, hpp]
  obtain ⟨-, h1⟩ := SmithD6Wt.forall_flatten
    (fun s (bp : Array ℕ × Array ℕ) => planeL s bp.1.toList bp.2.toList = true) 0 (#[], #[])
    J.wt64C (List.zipWith List.zip J.pbC J.ppC) (by rw [h64, hZl]) fun c hc => by
      rw [h64] at hc
      obtain ⟨e1, e2, h3⟩ := SmithD6Wt.planes c hc
      rw [hZc c hc]
      refine ⟨by rw [List.length_zip, e1, e2, min_self], fun i hi => ?_⟩
      rw [zip_getD38702 (e1.trans e2.symm) _ _ (by rw [e1]; exact hi)]
      exact h3 i hi
  obtain ⟨hl2, h2⟩ := SmithD6Wt.forall_flatten (fun (bp : Array ℕ × Array ℕ) b => bp.1 = b)
    (#[], #[]) #[] (List.zipWith List.zip J.pbC J.ppC) J.pbC (by rw [hZl, hpb]) fun c hc => by
      rw [hZl] at hc
      obtain ⟨e1, e2, -⟩ := SmithD6Wt.planes c (by omega)
      rw [hZc c hc]
      refine ⟨by rw [List.length_zip, e1, e2, min_self], fun i hi => ?_⟩
      rw [List.length_zip, e1, e2, min_self] at hi
      rw [zip_getD38702 (e1.trans e2.symm) _ _ (by rw [e1]; exact hi)]
  obtain ⟨-, h3⟩ := SmithD6Wt.forall_flatten (fun (bp : Array ℕ × Array ℕ) b => bp.2 = b)
    (#[], #[]) #[] (List.zipWith List.zip J.pbC J.ppC) J.ppC (by rw [hZl, hpp]) fun c hc => by
      rw [hZl] at hc
      obtain ⟨e1, e2, -⟩ := SmithD6Wt.planes c (by omega)
      rw [hZc c hc]
      refine ⟨by rw [List.length_zip, e1, e2, min_self], fun i hi => ?_⟩
      rw [List.length_zip, e1, e2, min_self] at hi
      rw [zip_getD38702 (e1.trans e2.symm) _ _ (by rw [e1]; exact hi)]
  intro i hi
  have hlen : J.wt64C.flatten.length = 75735 := SmithD6Wt.wt64_facts.2.1
  have hZ : i < (List.zipWith List.zip J.pbC J.ppC).flatten.length := by
    rw [hl2, SmithD6Wt.planes_flat.1]; exact hi
  have := h1 i (by omega)
  rw [SmithD6Wt.wt64_getD, h2 i hZ, h3 i hZ] at this
  exact this

theorem planeFacts38702 {s : ℕ} {B P : Array ℕ} (h : planeL s B.toList P.toList = true) :
    B.size = 6 ∧ P.size = 6 ∧ (∀ m < 6, B[m]! < 4096) ∧ (∀ d < 64, d = 0 ∨ xorComb B d ≠ 0) ∧
      ∀ d < 64, memR B P (xorComb B d) = true := by
  obtain ⟨-, hlB, hlP, hann, hpiv⟩ := planeL_sound h
  have hB : ∀ m < 6, B[m]! < 4096 := fun m hm => by
    refine (hann _ ?_).1
    rw [getElem!_eq_getD_toList, List.getD_eq_getElem _ _ (by rw [hlB]; exact hm)]
    exact List.getElem_mem _
  rcases P with ⟨ps⟩
  have hp : ∀ j < 6, ∀ k < 6, B[k]!.testBit (ps.getD j 0) = (k == j) := fun j hj k hk => by
    rw [getElem!_eq_getD_toList]
    exact hpiv j hj k hk
  have hc : ∀ d < 64, coefOf ⟨ps⟩ (xorComb B d) = d := fun d hd => by
    apply Nat.eq_of_testBit_eq
    intro m
    by_cases hm : m < 6
    · rw [testBit_coefOf _ hm]
      exact testBit_xorComb_piv (p := fun j => ps.getD j 0) hp d hm
    · have h64 : (64 : ℕ) ≤ 2 ^ m := by
        have := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega : 6 ≤ m)
        simpa using this
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (coefOf_lt _ _) h64),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hd h64)]
  refine ⟨by rw [← Array.length_toList]; exact hlB, by rw [← Array.length_toList]; exact hlP, hB,
    fun d hd => ?_, fun d hd => ?_⟩
  · by_cases h0 : xorComb B d = 0
    · left
      have e := hc d hd
      rw [h0, ← xorComb_zero B, hc 0 (by norm_num)] at e
      exact e.symm
    · exact Or.inr h0
  · unfold memR
    rw [hc d hd]
    exact beq_self_eq_true _

public section

open CFSG.SmithD6 CFSG.KD.SmithD6 CFSG.GF2Type.SmithTypeE.DMod in
theorem certificate38702 : (wtArr.size = 75735 ∧ wtArr[0]! = 1 ∧ (∀ i < 75735, wt i < 4294967296) ∧
      (∀ i < 75734, wt i < wt (i + 1)) ∧ ∀ i < 75735, wtIdx (wt i) = i) ∧
    (∀ i < 75735, (pbArr[i]!).size = 6 ∧ (ppArr[i]!).size = 6 ∧ (∀ m < 6, (pbArr[i]!)[m]! < 4096) ∧
      (∀ d < 64, d = 0 ∨ xorComb pbArr[i]! d ≠ 0) ∧
      ∀ d < 64, memR pbArr[i]! ppArr[i]! (xorComb pbArr[i]! d) = true) ∧
    pbArr[0]! = fBasis ∧
    (∀ i < 75735, planeSpan pbArr[i]! = annSub (exL (decode32 (wt i)))) ∧
    (∀ i < 75735, ∀ g < 13, ∃ j < 75735,
      tlift (dec12 (gensV.getD g (0, 0)).1) (dec12 (gensV.getD g (0, 0)).2)
        (exL (decode32 (wt i))) = exL (decode32 (wt j))) ∧
    (∀ j < 75735, fModel (decode32 (wt 0)) (decode32 (wt j)) = 1 ↔
      Disjoint (planeSpan pbArr[0]!) (planeSpan pbArr[j]!)) ∧
    ∀ Q : ℕ → Prop, Q 0 → (∀ g < 13, ∀ p < 75735, ∀ i < 75735,
      tlift (dec12 (gensV.getD g (0, 0)).1) (dec12 (gensV.getD g (0, 0)).2)
        (exL (decode32 (wt p))) = exL (decode32 (wt i)) → Q p → Q i) → ∀ i < 75735, Q i := by
  have hl := SmithD6Wt.wtC_flatten_length
  have hw : ∀ i < 75735, wt i = J.wtC.flatten.getD i 0 := fun i hi => wt_getD38702 hi
  have hpb := pinnedModel.pbArr_get
  refine ⟨⟨?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, fun i hi => ?_, ?_,
    fun i hi => ?_, fun i hi g hg => ?_, fun j hj => ?_, fun Q h0 hstep => ?_⟩
  · rw [← Array.length_toList, pinnedModel.wtArr_toList, hl]
  · change wt 0 = 1
    rw [hw 0 (by norm_num), SmithD6Wt.first.1]
  · have hi' : i < J.wtC.flatten.length := by rw [hl]; exact hi
    rw [pinnedModel.wt_get i hi']
    exact lt_of_lt_of_eq (SmithD6Adj.lt_of_mem (List.getElem_mem hi')) (by norm_num)
  · have hi' : i < J.wtC.flatten.length := by rw [hl]; omega
    have hi1 : i + 1 < J.wtC.flatten.length := by rw [hl]; omega
    rw [pinnedModel.wt_get i hi', pinnedModel.wt_get (i + 1) hi1]
    exact List.pairwise_iff_getElem.1 SmithD6Trees.wt_facts.1 _ _ hi' hi1 (Nat.lt_succ_self i)
  · have hi' : i < J.wtC.flatten.length := by rw [hl]; exact hi
    rw [pinnedModel.wt_get i hi']
    exact SmithD6Uw.wtIdx_get pinnedModel.wtArr_toList hi'
  · rw [hpb i hi, pinnedModel.ppArr_get i hi]
    exact planeFacts38702 (planes38702 i hi)
  · rw [hpb 0 (by norm_num)]
    exact SmithD6Wt.first.2
  · rw [hpb i hi, hw i hi]
    exact SmithD6Wt.ann i hi
  · have hi' : i < J.wtC.flatten.length := by rw [hl]; exact hi
    obtain ⟨t, ht, he⟩ := SmithD6Wt.closure32 _ (List.getElem_mem hi') g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    refine ⟨j, by rw [hl] at hj; exact hj, ?_⟩
    rw [pinnedModel.wt_get i hi', pinnedModel.wt_get j hj]
    exact he
  · rw [hpb 0 (by norm_num), hpb j hj, hw 0 (by norm_num), hw j hj]
    exact SmithD6Wt.gram j hj
  · refine SmithD6Wt.tree32 Q h0 fun g hg p hp i hi he hQ => hstep g hg p hp i hi ?_ hQ
    rw [hw p hp, hw i hi]
    exact he

end

end Certificates
