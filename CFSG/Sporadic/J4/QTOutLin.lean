module

public import CFSG.Sporadic.J4.QTOutLinGen
public import CFSG.Sporadic.J4.QTOutMatNative
public import CFSG.Sporadic.J4.F2Spec

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native Matrix

theorem triOK_spec {vs : Array V2} {ps : Array ℕ} (h : triOK vs ps = true) :
    vs.size = ps.size ∧ ∀ k < vs.size, (vs[k]!).wf = true ∧ ps[k]! < 112 ∧
      (vs[k]!).testBit ps[k]! = true ∧ ∀ j < k, (vs[k]!).testBit ps[j]! = false := by
  unfold triOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.not_eq_true'] at h
  refine ⟨h.1, fun k hk => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h.2 k hk
  exact ⟨h1, h2, h3, h4⟩

theorem tri_indep {vs : Array V2} {ps : Array ℕ} (h : triOK vs ps = true) :
    IndepF (fun k : Fin vs.size => (vs[k.val]!).toVec) := by
  obtain ⟨hsz, hk⟩ := triOK_spec h
  unfold IndepF
  intro g hg
  have key : ∀ n : ℕ, ∀ k : Fin vs.size, k.val < n → g k = 0 := by
    intro n
    induction n with
    | zero => intro k hk'; omega
    | succ n ih =>
      intro k hk'
      by_cases hlt : k.val < n
      · exact ih k hlt
      · have hkn : k.val = n := by omega
        obtain ⟨_, hp, hbit, hjk⟩ := hk k.val k.isLt
        have h1 := congrFun hg ⟨ps[k.val]!, hp⟩
        rw [Finset.sum_apply] at h1
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
        rw [Finset.sum_eq_single k] at h1
        · rw [V2.toVec_apply] at h1
          simp only [hbit, ite_true, mul_one] at h1
          exact h1
        · intro j _ hjk'
          rcases lt_or_gt_of_ne (fun h => hjk' (Fin.ext h)) with hjlt | hjgt
          · rw [ih j (by omega), zero_mul]
          · obtain ⟨_, _, _, hjj⟩ := hk j.val j.isLt
            have h5 := hjj k.val hjgt
            have h6 : (vs[j.val]!).toVec ⟨ps[k.val]!, hp⟩ = 0 := by
              rw [V2.toVec_apply]
              simp only [h5, Bool.false_eq_true, ite_false]
            rw [h6, mul_zero]
        · intro hk0; exact absurd (Finset.mem_univ k) hk0
  intro k
  exact key (k.val + 1) k (by omega)

end CFSG.Sporadic.J4.QT
