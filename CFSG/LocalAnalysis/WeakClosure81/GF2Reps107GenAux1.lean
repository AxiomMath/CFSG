module

public import CFSG.Quasithin.Background.Asc81cPfBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

open CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

theorem w107_cardFactors_le_of_dvd {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) : Ω a ≤ Ω b := by
  rw [ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_apply]
  exact (Nat.primeFactorsList_sublist_of_dvd h hb).length_le

omit [Finite W] in
private theorem w107_commSub_top_sup_le (X Y : Subgroup (MulAut W)) :
    commSub (⊤ : Subgroup W) (X ⊔ Y) ≤
      commSub (⊤ : Subgroup W) X ⊔ commSub (⊤ : Subgroup W) Y := by
  have h := CFSG.Quasithin.Asc81c.Pf.commSub_iSup (fun b : Bool => cond b X Y)
  rw [iSup_bool_eq, iSup_bool_eq] at h
  exact h.le

theorem w107_rk_commSub_closure_le (c : ℕ) (S : Set (MulAut W))
    (hS : ∀ s ∈ S, rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers s)) ≤ c) :
    ∀ T : Finset (MulAut W), (↑T : Set (MulAut W)) ⊆ S →
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.closure (↑T : Set (MulAut W)))) ≤
        c * Ω (Nat.card ↥(Subgroup.closure (↑T : Set (MulAut W)))) := by
  classical
  intro T
  refine Finset.induction (motive := fun T => (↑T : Set (MulAut W)) ⊆ S →
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.closure (↑T : Set (MulAut W)))) ≤
        c * Ω (Nat.card ↥(Subgroup.closure (↑T : Set (MulAut W))))) ?base ?step T
  · intro _
    have hbot : commSub (⊤ : Subgroup W) (Subgroup.closure (↑(∅ : Finset (MulAut W)) :
        Set (MulAut W))) = ⊥ := by
      rw [Finset.coe_empty, Subgroup.closure_empty, commSub_eq_bot_iff]
      intro w _ x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx, MulAut.one_apply]
    rw [hbot, rk_bot]
    simp
  · intro s T' hs ih hTS
    have hT'S : (↑T' : Set (MulAut W)) ⊆ S := fun x hx => hTS (by
      rw [Finset.coe_insert]
      exact Set.mem_insert_of_mem s hx)
    have hsS : s ∈ S := hTS (by rw [Finset.coe_insert]; exact Set.mem_insert s _)
    have hB : Subgroup.closure (↑(insert s T') : Set (MulAut W)) =
        Subgroup.closure (↑T' : Set (MulAut W)) ⊔ Subgroup.zpowers s := by
      rw [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
      exact sup_comm ..
    rcases em (s ∈ Subgroup.closure (↑T' : Set (MulAut W))) with hsA | hsA
    · rw [hB, sup_eq_left.mpr (Subgroup.zpowers_le.mpr hsA)]
      exact ih hT'S
    · have hle : Subgroup.closure (↑T' : Set (MulAut W)) ≤
          Subgroup.closure (↑(insert s T') : Set (MulAut W)) := by rw [hB]; exact le_sup_left
      have hlt : Subgroup.closure (↑T' : Set (MulAut W)) <
          Subgroup.closure (↑(insert s T') : Set (MulAut W)) := by
        refine lt_of_le_of_ne hle ?_
        intro heq
        have hsB : s ∈ Subgroup.closure (↑(insert s T') : Set (MulAut W)) :=
          Subgroup.subset_closure (Finset.mem_insert_self s T')
        exact hsA (heq.symm ▸ hsB)
      have hdvd : Nat.card ↥(Subgroup.closure (↑T' : Set (MulAut W))) ∣
          Nat.card ↥(Subgroup.closure (↑(insert s T') : Set (MulAut W))) :=
        Subgroup.card_dvd_of_le hle
      have hltcard : Nat.card ↥(Subgroup.closure (↑T' : Set (MulAut W))) <
          Nat.card ↥(Subgroup.closure (↑(insert s T') : Set (MulAut W))) :=
        Subgroup.card_lt_of_lt hlt
      obtain ⟨k, hk⟩ := hdvd
      have hApos : 0 < Nat.card ↥(Subgroup.closure (↑T' : Set (MulAut W))) := Nat.card_pos
      have hk2 : 2 ≤ k := by
        have h1 : 1 < k := by nlinarith [hk, hltcard, hApos]
        omega
      have hk0 : k ≠ 0 := by omega
      have hA0 : Nat.card ↥(Subgroup.closure (↑T' : Set (MulAut W))) ≠ 0 := hApos.ne'
      have hcomm : commSub (⊤ : Subgroup W)
            (Subgroup.closure (↑(insert s T') : Set (MulAut W))) ≤
          commSub (⊤ : Subgroup W) (Subgroup.closure (↑T' : Set (MulAut W))) ⊔
            commSub (⊤ : Subgroup W) (Subgroup.zpowers s) := by
        rw [hB]
        exact w107_commSub_top_sup_le _ _
      have hrk1 : rk ↥(commSub (⊤ : Subgroup W)
            (Subgroup.closure (↑(insert s T') : Set (MulAut W)))) ≤
          rk ↥(commSub (⊤ : Subgroup W) (Subgroup.closure (↑T' : Set (MulAut W)))) +
            rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers s)) := by
        refine (rk_mono hcomm).trans ?_
        have h := rk_sup_add_rk_inf
          (commSub (⊤ : Subgroup W) (Subgroup.closure (↑T' : Set (MulAut W))))
          (commSub (⊤ : Subgroup W) (Subgroup.zpowers s))
        omega
      have hih := ih hT'S
      have hgens := hS s hsS
      have hOm : Ω (Nat.card ↥(Subgroup.closure (↑(insert s T') : Set (MulAut W)))) =
          Ω (Nat.card ↥(Subgroup.closure (↑T' : Set (MulAut W)))) + Ω k := by
        rw [hk, ArithmeticFunction.cardFactors_mul hA0 hk0]
      rw [hOm]
      calc rk ↥(commSub (⊤ : Subgroup W)
              (Subgroup.closure (↑(insert s T') : Set (MulAut W))))
          ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.closure (↑T' : Set (MulAut W)))) +
              rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers s)) := hrk1
        _ ≤ c * Ω (Nat.card ↥(Subgroup.closure (↑T' : Set (MulAut W)))) + c :=
              Nat.add_le_add hih hgens
        _ ≤ c * (Ω (Nat.card ↥(Subgroup.closure (↑T' : Set (MulAut W)))) + Ω k) := by
              have hk1 : 1 ≤ Ω k := by
                have : 0 < Ω k :=
                  ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
                omega
              nlinarith [Nat.mul_le_mul_left c hk1]

theorem w107_cardFactors_nineteen : Ω (3 * (2 ^ 10 * 3 ^ 6 * 5 * 7)) = 19 := by
  rw [ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_mul (by norm_num) (by norm_num),
    ArithmeticFunction.cardFactors_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.cardFactors_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.cardFactors_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.cardFactors_apply_prime_pow (by norm_num : Nat.Prime 2),
    ArithmeticFunction.cardFactors_apply_prime_pow (by norm_num : Nat.Prime 3)]

theorem w107_cardFactors_le_nineteen {a : ℕ} (h : a ∣ 3 * (2 ^ 10 * 3 ^ 6 * 5 * 7)) :
    Ω a ≤ 19 := by
  have hN : 3 * (2 ^ 10 * 3 ^ 6 * 5 * 7) ≠ 0 := by norm_num
  have ha : a ≠ 0 := by rintro rfl; exact hN (zero_dvd_iff.mp h)
  calc Ω a ≤ Ω (3 * (2 ^ 10 * 3 ^ 6 * 5 * 7)) := w107_cardFactors_le_of_dvd h hN
    _ = 19 := w107_cardFactors_nineteen

end CFSG.LocalAnalysis.WeakClosure81
