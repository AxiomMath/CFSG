module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaDiag1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaR1

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

theorem relIndex_Bh_P1h :
    Bh.relIndex P1h = 3 := by
  have h := Subgroup.relIndex_mul_card Bh P1h
  have h1 : Nat.card ↥(Bh ⊓ P1h) = 384 := by rw [inf_eq_left.2 Bh_le_P1h]; exact card_Bh
  rw [h1, card_P1h] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 384) (h.trans (by norm_num))

theorem relIndex_Bh_P2h :
    Bh.relIndex P2h = 5 := by
  have h := Subgroup.relIndex_mul_card Bh P2h
  have h1 : Nat.card ↥(Bh ⊓ P2h) = 384 := by rw [inf_eq_left.2 Bh_le_P2h]; exact card_Bh
  rw [h1, card_P2h] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 384) (h.trans (by norm_num))

@[expose] def UGood (s t u : Ah) : Prop :=
  u * u = 1 ∧ u ∈ Bh ∧ t * u * t ∈ Bh ∧ s * (t * u * t) * s ∈ Bh ∧
    t * (s * (t * u * t) * s) * t ∈ Bh ∧ s * u * s ∉ Bh

@[expose] def WGood (s t w : Ah) : Prop :=
  w * w = 1 ∧ w ∈ Bh ∧ s * w * s ∈ Bh ∧ t * (s * w * s) * t ∈ Bh ∧
    s * (t * (s * w * s) * t) * s ∈ Bh ∧ t * w * t ∉ Bh

theorem ahBN_of_good
    {s t u w₁ w₂ w₃ : Ah} (hs1 : s ∈ P1h) (hs2 : s * s = 1) (hs3 : s ∉ Bh) (ht1 : t ∈ P2h)
    (ht2 : t * t = 1) (ht3 : t ∉ Bh) (hst : (s * t) ^ 4 = 1) (hu : UGood s t u)
    (h1 : WGood s t w₁) (h2 : WGood s t w₂) (h3 : WGood s t w₃)
    (p12 : t * (w₁ * w₂) * t ∉ Bh) (p13 : t * (w₁ * w₃) * t ∉ Bh)
    (p23 : t * (w₂ * w₃) * t ∉ Bh) : AhBN s t [1, u] [1, w₁, w₂, w₃] := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu.1
  have hw1 : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right h1.1
  have hw2 : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right h2.1
  have hw3 : w₃⁻¹ = w₃ := inv_eq_of_mul_eq_one_right h3.1
  have hU : ∀ x ∈ [1, u], x ∈ Bh := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Bh.one_mem
    · exact hu.2.1
  have hW : ∀ x ∈ [1, w₁, w₂, w₃], x ∈ Bh := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Bh.one_mem
    · exact h1.2.1
    · exact h2.2.1
    · exact h3.2.1
  refine ⟨hs1, hs2, hs3, ht1, ht2, ht3, braid_of_pow_four hs2 ht2 hst, hU, hW, ?_, ?_, ?_, ?_,
    by simp, by simp⟩
  · refine exists_mem_cos Bh_le_P1h [1, u] s hs1 hU hs3 (by rw [relIndex_Bh_P1h]; rfl) ?_
    refine List.Pairwise.cons (fun a ha => ?_) (List.Pairwise.cons (fun a ha => ?_)
      List.Pairwise.nil)
    · obtain rfl : a = u := List.mem_singleton.1 ha
      rw [hsi, hui, one_mul]
      exact hu.2.2.2.2.2
    · exact absurd ha (List.not_mem_nil)
  · refine exists_mem_cos Bh_le_P2h [1, w₁, w₂, w₃] t ht1 hW ht3
      (by rw [relIndex_Bh_P2h]; rfl) ?_
    refine List.Pairwise.cons (fun a ha => ?_) (List.Pairwise.cons (fun a ha => ?_)
      (List.Pairwise.cons (fun a ha => ?_) (List.Pairwise.cons (fun a ha => ?_)
        List.Pairwise.nil)))
    · rcases List.mem_cons.1 ha with rfl | ha
      · rw [hti, hw1, one_mul]; exact h1.2.2.2.2.2
      · rcases List.mem_cons.1 ha with rfl | ha
        · rw [hti, hw2, one_mul]; exact h2.2.2.2.2.2
        · obtain rfl : a = w₃ := List.mem_singleton.1 ha
          rw [hti, hw3, one_mul]; exact h3.2.2.2.2.2
    · rcases List.mem_cons.1 ha with rfl | ha
      · rw [hti, hw2]; exact p12
      · obtain rfl : a = w₃ := List.mem_singleton.1 ha
        rw [hti, hw3]; exact p13
    · obtain rfl : a = w₃ := List.mem_singleton.1 ha
      rw [hti, hw3]; exact p23
    · exact absurd ha (List.not_mem_nil)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp [ht2, hs2, Bh.one_mem]
    · exact ⟨hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [ht2, hs2, Bh.one_mem]
    · exact ⟨h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1⟩
    · exact ⟨h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2.1⟩
    · exact ⟨h3.2.2.1, h3.2.2.2.1, h3.2.2.2.2.1⟩

end CFSG.Quasithin.H13.F431.U42Aut
