module

public import CFSG.RankThree.PartOne.K133Spor.HSPairInputs

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

theorem rep_powA5 {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    Rep n (powA5 n t) (g ^ 5) := by
  have := rep_compA h (rep_compA h (rep_compA h (rep_compA h h)))
  have e : g ^ 5 = g * (g * (g * (g * g))) := by simp [pow_succ, mul_assoc]
  rw [e]
  exact this

theorem memLineA_spec {n : ℕ} {xa fa : Array ℕ} {X f : Equiv.Perm (Fin n)} (hX : Rep n xa X)
    (hf : Rep n fa f) (h : memLineA n xa fa = true) : f ∈ Subgroup.zpowers X := by
  have hX2 := rep_compA hX hX
  have hX3 := rep_compA hX hX2
  have hX4 := rep_compA hX hX3
  unfold memLineA at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · rw [eqA_iff hf rep_idA] at h
    rw [h]; exact Subgroup.one_mem _
  · rw [eqA_iff hf hX] at h
    rw [h]; exact Subgroup.mem_zpowers _
  · rw [eqA_iff hf hX2] at h
    rw [h]; exact mul_mem (Subgroup.mem_zpowers X) (Subgroup.mem_zpowers X)
  · rw [eqA_iff hf hX3] at h
    rw [h]
    exact mul_mem (Subgroup.mem_zpowers X)
      (mul_mem (Subgroup.mem_zpowers X) (Subgroup.mem_zpowers X))
  · rw [eqA_iff hf hX4] at h
    rw [h]
    exact mul_mem (Subgroup.mem_zpowers X) (mul_mem (Subgroup.mem_zpowers X)
      (mul_mem (Subgroup.mem_zpowers X) (Subgroup.mem_zpowers X)))

theorem pairFree_of_check {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (henum : enumOK n gs ps c = true) {xa : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hX : Rep n xa X) (hcheck : pairFreeCheck n c.pts xa = true)
    {u f : Equiv.Perm (Fin n)} (hu : u ∈ Subgroup.closure (permsA n gs))
    (hf : f ∈ Subgroup.closure (permsA n gs)) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hf5 : f ^ 5 = 1)
    (hf1 : f ≠ 1) (hfX : f ∉ Subgroup.zpowers X) (hcomm : u * f = f * u) : False := by
  obtain ⟨i, hi, hRu⟩ := enumOK_exists_rep hps henum hu
  obtain ⟨j, hj, hRf⟩ := enumOK_exists_rep hps henum hf
  unfold pairFreeCheck at hcheck
  rw [Array.all_eq_true] at hcheck
  have h1 := hcheck i hi
  have hA : (eqA n (compA n c.pts[i]! c.pts[i]!) (idA n) && !eqA n c.pts[i]! (idA n)) = true := by
    rw [Bool.and_eq_true, eqA_iff (rep_compA hRu hRu) rep_idA, Bool.not_eq_true',
      Bool.eq_false_iff, ne_eq, eqA_iff hRu rep_idA]
    exact ⟨hu2, hu1⟩
  rw [← getElem!_pos c.pts i hi] at h1
  simp only [hA, Bool.not_true, Bool.false_or] at h1
  rw [Array.all_eq_true] at h1
  have h2 := h1 j hj
  have hB : (eqA n (powA5 n c.pts[j]!) (idA n) && !eqA n c.pts[j]! (idA n)) = true := by
    rw [Bool.and_eq_true, eqA_iff (rep_powA5 hRf) rep_idA, Bool.not_eq_true',
      Bool.eq_false_iff, ne_eq, eqA_iff hRf rep_idA]
    exact ⟨hf5, hf1⟩
  have hM : memLineA n xa c.pts[j]! = false := by
    by_contra hne
    exact hfX (memLineA_spec hX hRf (by simpa using hne))
  have hC : eqA n (compA n c.pts[i]! c.pts[j]!) (compA n c.pts[j]! c.pts[i]!) = true := by
    rw [eqA_iff (rep_compA hRu hRf) (rep_compA hRf hRu)]
    exact hcomm
  rw [← getElem!_pos c.pts j hj] at h2
  simp [hB, hM, hC] at h2

end CFSG.RankThree.PartOne.K133Spor
