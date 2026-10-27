module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.WeakClosure81

lemma b5_FiveSevenAltSub_eq_one_of_dvd_eight_of_modeq_five {m : ℕ} (h : m ∣ 8)
    (hm : m % 5 = 1) : m = 1 := by
  have hle : m ≤ 8 := Nat.le_of_dvd (by norm_num) h
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at h
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  interval_cases m <;> simp_all

lemma b5_FiveSevenAltSub_eq_one_of_dvd_nine_of_modeq_five {m : ℕ} (h : m ∣ 9)
    (hm : m % 5 = 1) : m = 1 := by
  have hle : m ≤ 9 := Nat.le_of_dvd (by norm_num) h
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at h
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  interval_cases m <;> simp_all

lemma b5_FiveSevenAltSub_index_eq_three_or_nine {m : ℕ} (h : m ∣ 9) (h1 : m ≠ 1) :
    m = 3 ∨ m = 9 := by
  have hle : m ≤ 9 := Nat.le_of_dvd (by norm_num) h
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at h
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  interval_cases m <;> simp_all

theorem eq_top_of_dvd_card_of_mulEquiv_alternatingGroup_six {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 6)) {N : Subgroup X} (h8 : 8 ∣ Nat.card N)
    (h5 : 5 ∣ Nat.card N) : N = ⊤ := by
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup X := e.isSimpleGroup
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases hN : N = ⊤
  · exact hN
  · exfalso
    have hXcard : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hdvd : Nat.card ↥N ∣ 360 := by
      have h := Subgroup.card_subgroup_dvd_card N
      rwa [hXcard] at h
    have h40 : 40 ∣ Nat.card ↥N := by
      have hc : Nat.Coprime 8 5 := by decide
      have h := hc.mul_dvd_of_dvd_of_dvd h8 h5
      simpa using h
    have hidx_dvd9 : N.index ∣ 9 := by
      obtain ⟨c, hc⟩ := h40
      have hmul := Subgroup.card_mul_index N
      rw [hc, hXcard] at hmul
      have hmul' : 40 * (c * N.index) = 40 * 9 := by
        rw [show (40 : ℕ) * 9 = 360 by norm_num, ← hmul, mul_assoc]
      have hci : c * N.index = 9 := Nat.mul_left_cancel (by norm_num) hmul'
      exact ⟨c, by rw [← hci, mul_comm]⟩
    have hidx1 : N.index ≠ 1 := fun h => hN (Subgroup.index_eq_one.mp h)
    rcases b5_FiveSevenAltSub_index_eq_three_or_nine hidx_dvd9 hidx1 with hidx3 | hidx9
    ·
      haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite
      have hcore : N.normalCore.index ∣ 6 := by
        have h := Subgroup.index_normalCore_dvd_factorial_index N
        rw [hidx3] at h
        simpa [Nat.factorial] using h
      haveI : N.normalCore.Normal := Subgroup.normalCore_normal N
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N.normalCore with hbot | htop
      · rw [hbot, Subgroup.index_bot, hXcard] at hcore
        norm_num at hcore
      · have : (⊤ : Subgroup X) ≤ N := by
          rw [← htop]
          exact Subgroup.normalCore_le N
        exact hN (top_le_iff.mp this)
    ·
      have hNcard : Nat.card ↥N = 40 := by
        have h := Subgroup.card_mul_index N
        rw [hidx9, hXcard] at h
        omega
      let P : Sylow 5 ↥N := Classical.choice Sylow.nonempty
      have hP5 : Nat.card ↥(P : Subgroup ↥N) = 5 := by
        rw [Sylow.card_eq_multiplicity, hNcard]
        have hf : (40 : ℕ).factorization 5 = 1 := by
          rw [Nat.factorization_def _ Nat.prime_five]
          decide +kernel
        rw [hf, pow_one]
      have hPindex : (P : Subgroup ↥N).index = 8 := by
        have h := Subgroup.card_mul_index (P : Subgroup ↥N)
        rw [hP5, hNcard] at h
        omega
      have hnsyl : Nat.card (Sylow 5 ↥N) = 1 := by
        apply b5_FiveSevenAltSub_eq_one_of_dvd_eight_of_modeq_five
        · rw [← hPindex]
          exact Sylow.card_dvd_index P
        · have h := card_sylow_modEq_one 5 ↥N
          simpa [Nat.ModEq] using h
      haveI : Subsingleton (Sylow 5 ↥N) := (Nat.card_eq_one_iff_unique.mp hnsyl).1
      have hPnormal : (P : Subgroup ↥N).Normal := Sylow.normal_of_subsingleton P
      set Q : Subgroup X := (P : Subgroup ↥N).map N.subtype with hQdef
      have hQcard : Nat.card ↥Q = 5 := by
        rw [hQdef, Subgroup.card_map_of_injective N.subtype_injective]
        exact hP5
      have key : ∀ (m : X) (hm : m ∈ N) (x : X), x ∈ Q → m * x * m⁻¹ ∈ Q := by
        intro m hm x hx
        rw [hQdef] at hx ⊢
        rw [Subgroup.mem_map] at hx ⊢
        obtain ⟨p, hp, rfl⟩ := hx
        exact ⟨⟨m, hm⟩ * p * ⟨m, hm⟩⁻¹, hPnormal.conj_mem p hp ⟨m, hm⟩, rfl⟩
      have hNle : N ≤ Subgroup.normalizer Q := by
        intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · exact key m hm x
        · intro hx
          have h := key m⁻¹ (N.inv_mem hm) (m * x * m⁻¹) hx
          rwa [show m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x by group] at h
      have hQeq : Nat.card ↥Q = 5 ^ (Nat.card X).factorization 5 := by
        rw [hQcard, hXcard]
        have hf : (360 : ℕ).factorization 5 = 1 := by
          rw [Nat.factorization_def _ Nat.prime_five]
          decide +kernel
        rw [hf, pow_one]
      have hn'9 : Nat.card (Sylow 5 X) ∣ 9 := by
        rw [Sylow.card_eq_index_normalizer (Sylow.ofCard Q hQeq)]
        change (Subgroup.normalizer (Q : Set X)).index ∣ 9
        exact (Subgroup.index_dvd_of_le hNle).trans hidx_dvd9
      have hn'1 : Nat.card (Sylow 5 X) = 1 := by
        apply b5_FiveSevenAltSub_eq_one_of_dvd_nine_of_modeq_five hn'9
        have h := card_sylow_modEq_one 5 X
        simpa [Nat.ModEq] using h
      haveI : Subsingleton (Sylow 5 X) := (Nat.card_eq_one_iff_unique.mp hn'1).1
      have hQnormal : Q.Normal := by
        have h := Sylow.normal_of_subsingleton (Sylow.ofCard Q hQeq)
        rwa [Sylow.coe_ofCard Q hQeq] at h
      haveI : Q.Normal := hQnormal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with hQbot | hQtop
      · rw [hQbot, Subgroup.card_bot] at hQcard
        norm_num at hQcard
      · rw [hQtop, Subgroup.card_top, hXcard] at hQcard
        norm_num at hQcard

end CFSG.LocalAnalysis.WeakClosure81
