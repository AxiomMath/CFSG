module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Fix
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Gc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Max
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Prod

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem routeB_core (F : FanTree Γ G) (h40 : Fan40 F) (h54 : Fan54 F) (T : Track Γ G)
    (h47 : ∀ a b c : ℤ, IsTArc T a b → (c = a ∨ c = b) → valence Γ (T.line.vert c) = 3)
    (h48len : ∀ a b : ℤ, IsTArc T a b → b - a ≤ 8) {z : G} {a : ℤ}
    (hzC : T.line.IsCoreCFix z a (a + 2) (a - 3) (a + 2 + 3)) (hzc : z ∈ T.line.Zc)
    (hZT : ∀ v ∈ T.fixer, (∀ k ∈ nbrStab Γ G (T.line.vert (a + 2)), k * v = v * k) → v = 1)
    (C : LblCtx Γ z (T.line.vert (a + 1)) (T.line.vert (a + 2))) : False := by
  classical
  have hcz : z ∈ Cinv G (T.line.vert (a + 1)) := C.cinv
  have hne : T.line.vert (a + 1) ≠ T.line.vert (a + 2 + 1) := by
    have := T.line.vert_pred_ne_succ (a + 2)
    rwa [show a + 2 - 1 = a + 1 by ring] at this
  have hK : ∀ u, Γ.Adj (T.line.vert (a + 2)) u →
      Lb z (T.line.vert (a + 1)) u ∈ nbrStab Γ G (T.line.vert (a + 2)) := fun u hu =>
    Lb_mem_nbrStab F hcz C.ball C.adj hu
  have hcomK : ∀ u, Γ.Adj (T.line.vert (a + 2)) u → ∀ k ∈ nbrStab Γ G (T.line.vert (a + 2)),
      k * Lb z (T.line.vert (a + 1)) u = Lb z (T.line.vert (a + 1)) u * k := fun u hu k hk =>
    comm_nbrStab_Lb F hcz C.adj hu hk
  have hnT : ∀ u, Γ.Adj (T.line.vert (a + 2)) u → Lb z (T.line.vert (a + 1)) u ∉ T.fixer :=
    fun u hu h => C.ne_one F hu (hZT _ h (hcomK u hu))
  have hfix : ∀ u, Γ.Adj (T.line.vert (a + 2)) u → ∀ i, a - 1 ≤ i → i ≤ a + 5 →
      Lb z (T.line.vert (a + 1)) u • T.line.vert i = T.line.vert i := by
    intro u hu
    have := fix_off F h40 h54 T hzc hzC.core (r := 3) ⟨1, by norm_num⟩ (hnT u hu)
      (MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ (hK u hu))) fun j hj1 hj2 => by
      have hKj : lab T z j ∈ nbrStab Γ G (T.line.vert (a + 2)) :=
        T.line.mem_nbrStab_of_fix F (u := a + 2)
          ((mem_fixIdx_lab T z j (a + 2 - 1)).2 ((hzC.fix _).2 ⟨by omega, by omega⟩))
          ((mem_fixIdx_lab T z j (a + 2)).2 ((hzC.fix _).2 ⟨by omega, by omega⟩))
          ((mem_fixIdx_lab T z j (a + 2 + 1)).2 ((hzC.fix _).2 ⟨by omega, by omega⟩))
      exact (comm_nbrStab_Lb F hcz C.adj hu hKj).symm
    exact fun i h1 h2 => this i (by omega) (by omega)
  obtain ⟨c₁, hc₁, hnc₁⟩ := exists_nbr_not_mem C.v5
    {T.line.vert (a + 1), T.line.vert (a + 2 + 1)} (Finset.card_le_two.trans (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnc₁
  obtain ⟨c₂, c₃, hc₂, hc₃, hnd⟩ := exists_five_nbrs C.v5 (a₁ := T.line.vert (a + 1))
    (a₂ := T.line.vert (a + 2 + 1)) (a₃ := c₁) hne (fun h => hnc₁.1 h.symm)
    (fun h => hnc₁.2 h.symm)
  have hadj : ∀ u ∈ [T.line.vert (a + 1), T.line.vert (a + 2 + 1), c₁, c₂, c₃],
      Γ.Adj (T.line.vert (a + 2)) u := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with hu | hu | hu | hu | hu <;> rw [hu]
    · exact C.adj.symm
    · exact T.line.adj (a + 2)
    · exact hc₁
    · exact hc₂
    · exact hc₃
  have hcard : (Finset.univ : Finset (Bool × Bool)).card <
      ([T.line.vert (a + 1), T.line.vert (a + 2 + 1), c₁, c₂, c₃].toFinset).card := by
    rw [List.toFinset_card_of_nodup hnd]
    simp
  obtain ⟨p, hp, q, hq, hpq, hty⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
    (f := fun u => (decide (Lb z (T.line.vert (a + 1)) u • T.line.vert (a + 6) =
      T.line.vert (a + 6)), decide (Lb z (T.line.vert (a + 1)) u • T.line.vert (a - 2) =
      T.line.vert (a - 2)))) (fun u _ => Finset.mem_univ _)
  have hp' := hadj p (List.mem_toFinset.1 hp)
  have hq' := hadj q (List.mem_toFinset.1 hq)
  simp only [Prod.mk.injEq, decide_eq_decide] at hty
  have hv2 : (Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q) *
      (Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q) = 1 := by
    have hc := C.commute F hp' hq'
    calc _ = Lb z (T.line.vert (a + 1)) p * (Lb z (T.line.vert (a + 1)) q *
          Lb z (T.line.vert (a + 1)) p) * Lb z (T.line.vert (a + 1)) q := by simp only [mul_assoc]
      _ = Lb z (T.line.vert (a + 1)) p * (Lb z (T.line.vert (a + 1)) p *
          Lb z (T.line.vert (a + 1)) q) * Lb z (T.line.vert (a + 1)) q := by rw [← hc]
      _ = (Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) p) *
          (Lb z (T.line.vert (a + 1)) q * Lb z (T.line.vert (a + 1)) q) := by
        simp only [mul_assoc]
      _ = 1 := by rw [C.sq F hp', C.sq F hq', one_mul]
  have hv1 : Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q ≠ 1 := by
    intro h
    have := eq_inv_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right (C.sq F hp')] at this
    exact C.ne p q hp' hq' hpq this.symm
  have hvfix : ∀ i, a - 2 ≤ i → i ≤ a + 6 →
      (Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q) • T.line.vert i =
        T.line.vert i := by
    intro i h1 h2
    by_cases hi : a - 1 ≤ i ∧ i ≤ a + 5
    · rw [mul_smul, hfix q hq' i hi.1 hi.2, hfix p hp' i hi.1 hi.2]
    · have hcase : i = a - 2 ∨ i = a + 6 := by omega
      rcases hcase with rfl | rfl
      · by_cases hpf : Lb z (T.line.vert (a + 1)) p • T.line.vert (a - 2) = T.line.vert (a - 2)
        · rw [mul_smul, hty.2.1 hpf, hpf]
        · have hqf : ¬ Lb z (T.line.vert (a + 1)) q • T.line.vert (a - 2) =
              T.line.vert (a - 2) := fun h => hpf (hty.2.2 h)
          have e : a - 1 - 1 = a - 2 := by ring
          have := mul_fix_left F T.line (p := a - 1) (C.sq F hp') (C.sq F hq')
            (hfix p hp' (a - 1 + 1) (by omega) (by omega))
            (hfix p hp' (a - 1) (by omega) (by omega)) (by rw [e]; exact hpf)
            (hfix q hq' (a - 1 + 1) (by omega) (by omega))
            (hfix q hq' (a - 1) (by omega) (by omega)) (by rw [e]; exact hqf)
          rwa [e] at this
      · by_cases hpf : Lb z (T.line.vert (a + 1)) p • T.line.vert (a + 6) = T.line.vert (a + 6)
        · rw [mul_smul, hty.1.1 hpf, hpf]
        · have hqf : ¬ Lb z (T.line.vert (a + 1)) q • T.line.vert (a + 6) =
              T.line.vert (a + 6) := fun h => hpf (hty.1.2 h)
          have e : a + 5 + 1 = a + 6 := by ring
          have := mul_fix_right F T.line (q := a + 5) (C.sq F hp') (C.sq F hq')
            (hfix p hp' (a + 5 - 1) (by omega) (by omega))
            (hfix p hp' (a + 5) (by omega) (by omega)) (by rw [e]; exact hpf)
            (hfix q hq' (a + 5 - 1) (by omega) (by omega))
            (hfix q hq' (a + 5) (by omega) (by omega)) (by rw [e]; exact hqf)
          rwa [e] at this
  have hvnot : Lb z (T.line.vert (a + 1)) p * Lb z (T.line.vert (a + 1)) q ∉ T.fixer :=
    fun hmem => hv1 (hZT _ hmem fun k hk =>
      Commute.mul_right (hcomK p hp' k hk) (hcomK q hq' k hk))
  have hps : PSeg T (a - 2) (a + 6) := ⟨by omega, fun hle =>
    hvnot (hle (Subgroup.subset_closure ⟨(T.mem_subFixer).2 hvfix, hv2⟩))⟩
  obtain ⟨a', b', ha', hb', hpsg, hmax⟩ := T.exists_pseg_max F hps
  have hθ := ((fan42_2b T F h40 a' b').2 ⟨hpsg, hmax⟩).1
  have hlen := h48len a' b' hθ
  have hval3 := h47 a' b' a' hθ (Or.inl rfl)
  have ha'eq : a' = a - 2 := by omega
  have hv5 : valence Γ (T.line.vert a') = 5 := by
    rw [ha'eq]
    have := valence_vert_add_two_mul F T.line (a + 2) (-2)
    rw [show a + 2 + 2 * (-2) = a - 2 by ring] at this
    rw [this]
    exact C.v5
  omega

end P514

end CFSG.Quasithin.Fan86
