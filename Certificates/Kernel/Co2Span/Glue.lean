module

public import CFSG.GF2Type.Widths1112.Co2Module.EnumInputs
import Certificates.Kernel.Co2Span.Checks
import CFSG.Certificates.Kernel.Co2Span.Peel
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CertificateChecks.KernelCo2Span

open CFSG.KC.Co2Span CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.GF2W1112
  CFSG.GF2Type.Widths1112.Co2Module CFSG.Sporadic.SmallF2 Matrix

private theorem nat_of_beq {a b : Nat} (h : (a == b) = true) : a = b := beq_iff_eq.1 h

private theorem hYZ (k : Fin 3) : uXOf 1 (iY k) = MatP 22 (D.YP.getD k.val 0) ∧
    uXOf 1 (iZ k) = MatP 22 (D.ZP.getD k.val 0) := by
  have h := allN_iff.1 ch38960yz k.val k.isLt
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [xPackS, strictN_eq', strictN_eq'] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [uXOf_one_eq, ← nat_of_beq h1]
    rfl
  · rw [uXOf_one_eq, ← nat_of_beq h2]
    rfl

private theorem hB (i : Nat) (hi : i < 11) :
    rowsMatrix 22 (w12UBRows[i]!) = MatP 22 (D.BP.getD i 0) := by
  have h := ch38960rows
  simp only [Bool.and_eq_true] at h
  exact rowsAgree_sound (allN_iff.1 h.1 i hi)

private theorem hM0 : rowsMatrix 22 w12UM0Rows = MatP 22 D.M0P := by
  have h := ch38960rows
  simp only [Bool.and_eq_true] at h
  exact rowsAgree_sound h.2

theorem span38960 : ∀ M : Matrix (Fin 22) (Fin 22) (ZMod 2),
    (∀ k : Fin 3, M * uXOf 1 (iY k) = uXOf 1 (iZ k) * M) →
      ∃ c : Fin 11 → ZMod 2, M = ∑ i : Fin 11, c i • rowsMatrix 22 (w12UBRows[i.val]!) := by
  intro M hM
  have hsol : ∀ i < 11, ∀ k < 3, MatP 22 (D.BP.getD i 0) * MatP 22 (D.YP.getD k 0) =
      MatP 22 (D.ZP.getD k 0) * MatP 22 (D.BP.getD i 0) := by
    intro i hi k hk
    have h := allN_iff.1 (allN_iff.1 ch38960sol i hi) k hk
    rw [eqK_iff, MatP_mulV, MatP_mulV] at h
    exact h
  have hfree : ∀ i < 11, ∀ j < 11, (D.BP.getD i 0).testBit (w12UFree.getD j 0) = (i == j) :=
    fun i hi j hj => beq_iff_eq.1 (allN_iff.1 (allN_iff.1 ch38960free i hi) j hj)
  obtain ⟨c, hc⟩ := span_of_peel (Ys := D.YP) (Zs := D.ZP) (Bs := D.BP) (L := D.STEPS)
    (free := w12UFree) rfl (by decide) ch38960peel hsol hfree M (fun k hk => by
      have h := hM ⟨k, hk⟩
      rw [(hYZ ⟨k, hk⟩).1, (hYZ ⟨k, hk⟩).2] at h
      exact h)
  refine ⟨c, ?_⟩
  rw [hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hB i.val i.isLt]

private theorem exists_code :
    ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), ∃ c : Fin 16, A = thetaCode c.val := by
  decide

private theorem isUnit_code : ∀ c ∈ w12USCodes, IsUnit (thetaCode c) := by
  intro c hc
  rw [Matrix.isUnit_iff_isUnit_det]
  simp only [w12USCodes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [thetaCode, Matrix.det_fin_two] <;> decide

private theorem hX (c : Nat) (hc : c < 16) :
    uXOf (thetaCode c) (iN 0) = MatP 22 (D.XC0.getD c 0) ∧
      uXOf (thetaCode c) (iN 1) = MatP 22 (D.XC1.getD c 0) := by
  have h := allN_iff.1 ch38961x c hc
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [xPackS, strictN_eq', strictN_eq'] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [uXOf_eq, ← nat_of_beq h1]
    rfl
  · rw [uXOf_eq, ← nat_of_beq h2]
    rfl

private theorem tw_getD : ∀ j : Fin 8, w12UTauWords.toList.getD j.val [] =
    w12UTauWords.getD j.val [] := by
  decide

private theorem kk_getD : ∀ j : Fin 8, w12UTauOrd.toList.getD j.val 0 = uKk j := by
  decide

theorem enum38961 : ∀ (c : Fin 11 → ZMod 2) (θ : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 2)),
    (∑ i : Fin 11, c i • rowsMatrix 22 (w12UBRows[i.val]!)) ^ 3 = 1 →
    (∀ j, (wordProd (fun s => uXOf (θ s) (iN s)) (uTw j) *
      ∑ i : Fin 11, c i • rowsMatrix 22 (w12UBRows[i.val]!)) ^ uKk j = 1) →
    ∃ S : Matrix (Fin 2) (Fin 2) (ZMod 2), IsUnit S ∧
      (∀ s, Qfin S * uXOf (θ s) (iN s) = uX0 s * Qfin S) ∧
      Qfin S * (∑ i : Fin 11, c i • rowsMatrix 22 (w12UBRows[i.val]!)) =
        rowsMatrix 22 w12UM0Rows * Qfin S := by
  intro c θ h3 hrel
  set cc := CFSG.Sporadic.SmallF2.Native.ofBits 11
    (fun i => if h : i < 11 then decide (c ⟨i, h⟩ = 1) else false) with hcc
  have hccl : cc < 2048 := ofBits_lt 11 _
  have hM : MatP 22 (comboP D.BP cc) = ∑ i : Fin 11, c i • rowsMatrix 22 (w12UBRows[i.val]!) := by
    rw [MatP_comboP]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB i.val i.isLt, hcc, ofBits_testBit]
    simp only [i.isLt, decide_true, Bool.true_and, ↓reduceDIte]
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (c i) with h | h <;> simp [h]
  obtain ⟨c₀, hc₀⟩ := exists_code (θ 0)
  obtain ⟨c₁, hc₁⟩ := exists_code (θ 1)
  have hθ0 : uXOf (θ 0) (iN 0) = MatP 22 (D.XC0.getD c₀.val 0) := by
    rw [hc₀]
    exact (hX c₀.val c₀.isLt).1
  have hθ1 : uXOf (θ 1) (iN 1) = MatP 22 (D.XC1.getD c₁.val 0) := by
    rw [hc₁]
    exact (hX c₁.val c₁.isLt).2
  have hG : ∀ q : Nat × Nat, (fun s => uXOf (θ s) (iN s)) ⟨q.1 % 2, Nat.mod_lt _ (by norm_num)⟩ =
      if q.1 % 2 == 0 then MatP 22 (D.XC0.getD c₀.val 0) else MatP 22 (D.XC1.getD c₁.val 0) := by
    intro q
    rcases Nat.mod_two_eq_zero_or_one q.1 with e | e
    · have : (⟨q.1 % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 0 := Fin.ext e
      simp only [this, e, beq_self_eq_true, ↓reduceIte]
      exact hθ0
    · have : (⟨q.1 % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 1 := Fin.ext e
      simp only [this, e]
      exact hθ1
  have hlen : w12UTauWords.toList.length = 8 := rfl
  have hrel' : ∀ j < w12UTauWords.toList.length,
      (MatP 22 (CFSG.KC.Co2Span.wordP (D.XC0.getD c₀.val 0) (D.XC1.getD c₁.val 0)
        (w12UTauWords.toList.getD j [])) * MatP 22 (comboP D.BP cc)) ^
          w12UTauOrd.toList.getD j 0 = 1 := by
    intro j hj
    have hj8 : j < 8 := hlen ▸ hj
    have h := hrel ⟨j, hj8⟩
    rw [← hM] at h
    rw [tw_getD ⟨j, hj8⟩, kk_getD ⟨j, hj8⟩, CFSG.KC.Co2Span.MatP_wordP]
    convert h using 3
    unfold wordProd uTw
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp only [Function.comp_apply]
    rw [← hG q]
  obtain ⟨Q, hQ, hQ1, hQ2, hQ3⟩ := enum_sound ch38961enum (by decide) (by decide) hccl c₀.isLt
    c₁.isLt (by rw [hM]; exact h3) hrel'
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hQ
  have hlq : D.QP.length = 6 := by decide
  have hn6 : n < 6 := hlq ▸ hn
  have hq := allN_iff.1 ch38961q n hn6
  rw [xPackS, strictN_eq', strictN_eq'] at hq
  have hQS : MatP 22 (D.QP[n]) = Qfin (thetaCode (w12USCodes.getD n 0)) := by
    rw [Qfin_eq, nat_of_beq hq, List.getD_eq_getElem _ 0 hn]
    rfl
  have hX01 : MatP 22 (D.XC0.getD 9 0) = uX0 0 := by
    rw [← (hX 9 (by norm_num)).1]
    rfl
  have hX02 : MatP 22 (D.XC1.getD 11 0) = uX0 1 := by
    rw [← (hX 11 (by norm_num)).2]
    rfl
  refine ⟨thetaCode (w12USCodes.getD n 0), isUnit_code _ ?_, ?_, ?_⟩
  · have hs : w12USCodes.length = 6 := rfl
    rw [List.getD_eq_getElem _ _ (hs ▸ hn6)]
    exact List.getElem_mem _
  · intro s
    rw [← hQS]
    fin_cases s
    · change MatP 22 D.QP[n] * uXOf (θ 0) (iN 0) = uX0 0 * MatP 22 D.QP[n]
      rw [hθ0, ← hX01]
      exact hQ1
    · change MatP 22 D.QP[n] * uXOf (θ 1) (iN 1) = uX0 1 * MatP 22 D.QP[n]
      rw [hθ1, ← hX02]
      exact hQ2
  · rw [← hQS, ← hM, hM0]
    exact hQ3

end CertificateChecks.KernelCo2Span
