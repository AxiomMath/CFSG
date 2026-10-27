module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G2YSound

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

theorem w183finSp44G2Y_exists_of_zip_all_mem {α β : Type} (f : α × β → Bool) :
    ∀ (L : List α) (R : List β), L.length = R.length → (L.zip R).all f = true →
      ∀ a ∈ L, ∃ b ∈ R, f (a, b) = true
  | [], _, _, _, a, ha => by simp at ha
  | _ :: _, [], h, _, _, _ => by simp at h
  | x :: L, y :: R, h, hall, a, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hall.1⟩
    · obtain ⟨b, hb, hfb⟩ :=
        w183finSp44G2Y_exists_of_zip_all_mem f L R (by simpa using h) hall.2 a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hfb⟩

theorem w183finSp44G2Y_g2Rows_length : g2Rows.length = 8 := by decide +kernel

theorem w183finSp44G2Y_corData_length : corData.length = 8 := by decide +kernel

theorem w183finSp44G2Y_g2_complete_bounded : ∀ p ∈ pairsL,
    (∃ e, 0 < e ∧ (e - 1) / 3 < g2Pool.length ∧
      checkTIfail invsA[p.1]! invsA[p.2]! e = true) ∨
    ∃ c, checkCor invsA[p.1]! invsA[p.2]! c = true ∧ w183finSp44G2Y_corRowValid c = true := by
  refine forall_pairsL fun k hk p hp => ?_
  have h := g2_blocks k hk
  simp only [g2BlockOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨e, i⟩, hmem, hei⟩ :=
    w183finSp44G2Y_exists_of_zip_all_mem _ _ _ (by simpa using h.1) h.2 p hp
  by_cases he : e = 0
  · subst he
    rw [if_pos rfl] at hei
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hei
    obtain ⟨c, hc_mem, -, hc_check⟩ := hei
    refine Or.inr ⟨c, hc_check, ?_⟩
    have hk8c : k < corData.length := by rw [w183finSp44G2Y_corData_length]; exact hk
    have hc_mem' : c ∈ corData[k] := by
      rwa [List.getD_eq_getElem _ _ hk8c] at hc_mem
    have hrow : corData[k].all w183finSp44G2Y_corRowValid = true :=
      (List.all_eq_true.mp w183finSp44G2Y_corData_valid) _ (List.getElem_mem hk8c)
    exact (List.all_eq_true.mp hrow) c hc_mem'
  · rw [if_neg he] at hei
    refine Or.inl ⟨e, Nat.pos_of_ne_zero he, ?_, hei⟩
    have hk8r : k < g2Rows.length := by rw [w183finSp44G2Y_g2Rows_length]; exact hk
    have heR : e ∈ g2Rows[k] := by
      have hmem' : e ∈ g2Rows.getD k [] := (List.of_mem_zip hmem).1
      rwa [List.getD_eq_getElem _ _ hk8r] at hmem'
    have hrow : g2Rows[k].all (fun e => e ≤ 606) = true :=
      (List.all_eq_true.mp w183finSp44G2Y_rows_bound) _ (List.getElem_mem hk8r)
    have he606 : e ≤ 606 := of_decide_eq_true ((List.all_eq_true.mp hrow) e heR)
    rw [w183finSp44G2Y_g2Pool_length, Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)]
    omega

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
