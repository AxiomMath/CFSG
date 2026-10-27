module

public import Certificates.Kernel.U33ExitTwo.Checks
public import CFSG.Certificates.Kernel.U33ExitTwoSound
public import CFSG.GH74.KGroups.U33

public section

namespace Certificates

open CFSG.KC.U33Exit CFSG.KD.U33Exit CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

open CFSG.GH74.KGroups.U33 CFSG.ClassicalInvolution.Q3.TA3.Check in
theorem certificate55113 : ∀ t ∈ QP.originalSubgroup, t * t = 1 → t ≠ 1 →
    (∀ a b a' b' : Equiv.Perm (Fin 28),
      (a ∈ QA.originalSubgroup ∧ b ∈ QA.originalSubgroup ∧ a * a = t ∧ b * b = t ∧
        b * a = t * a * b) →
      (a' ∈ QA.originalSubgroup ∧ b' ∈ QA.originalSubgroup ∧ a' * a' = t ∧ b' * b' = t ∧
        b' * a' = t * a' * b') →
      ((a ∈ QP.originalSubgroup ∧ b ∈ QP.originalSubgroup) ↔
        (a' ∈ QP.originalSubgroup ∧ b' ∈ QP.originalSubgroup)) →
      ∀ x ∈ q8B t a b, x ∈ q8B t a' b') ∧
    ∃ ao bo ai bi g : Equiv.Perm (Fin 28),
      (ao ∈ QA.originalSubgroup ∧ bo ∈ QA.originalSubgroup ∧ ao * ao = t ∧ bo * bo = t ∧
        bo * ao = t * ao * bo) ∧
      ¬(ao ∈ QP.originalSubgroup ∧ bo ∈ QP.originalSubgroup) ∧
      (ai ∈ QA.originalSubgroup ∧ bi ∈ QA.originalSubgroup ∧ ai * ai = t ∧ bi * bi = t ∧
        bi * ai = t * ai * bi) ∧
      ai ∈ QP.originalSubgroup ∧ bi ∈ QP.originalSubgroup ∧ g ∈ QA.originalSubgroup ∧
      (∃ c ∈ q8B t ao bo, c * c = t ∧ g * c * g⁻¹ * t = t * (g * c * g⁻¹)) ∧
      ∃ d ∈ q8B t ao bo, ∃ x ∈ q8B t ai bi, g * d * g⁻¹ * x * (g * d * g⁻¹)⁻¹ ∉ q8B t ai bi := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h192, -⟩ := Certificates.certificate5133
  have hPc : Nat.card QP.originalSubgroup = 6048 := by rw [card_group QP QP_ok, QP_valid.2]
  have hAc : Nat.card QA.originalSubgroup = 12096 := by rw [card_group QA QA_ok, QA_valid.2]
  have hpaP : pa ∈ QP.originalSubgroup := by
    rw [QP_closure]
    exact pa_mem
  have hpbP : pb ∈ QP.originalSubgroup := by
    rw [QP_closure]
    exact pb_mem
  have hSA : ∀ s ∈ [pa, pb, sg0], s ∈ QA.originalSubgroup := by
    intro s hs
    rw [QA_closure]
    apply Subgroup.subset_closure
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp
  have hP : ∀ l < 2, [pa, pb, sg0].getD l 1 ∈ QP.originalSubgroup := by
    intro l hl
    rcases l with _ | _ | l
    · exact hpaP
    · exact hpbP
    · omega
  have hout : ∀ x ∈ QP.originalSubgroup, x * [pa, pb, sg0].getD 2 1 ∉ QP.originalSubgroup := by
    intro x hx hxs
    change x * sg0 ∈ QP.originalSubgroup at hxs
    have hs : sg0 ∈ QP.originalSubgroup := by
      have h := QP.originalSubgroup.mul_mem (QP.originalSubgroup.inv_mem hx) hxs
      rwa [inv_mul_cancel_left] at h
    have hle : QA.originalSubgroup ≤ QP.originalSubgroup := by
      rw [QA_closure, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl)
      · exact hpaP
      · exact hpbP
      · exact hs
    have h := Subgroup.card_le_of_le hle
    rw [hAc, hPc] at h
    omega
  have hgen := gens_ok
  simp only [Bool.and_eq_true] at hgen
  obtain ⟨⟨⟨g0, g1⟩, g2⟩, gu⟩ := hgen
  have hgl : u33Gen = [u33Gen.getD 0 0, u33Gen.getD 1 0, u33Gen.getD 2 0] := rfl
  have hS : List.Forall₂ Rep u33Gen [pa, pb, sg0] := by
    rw [hgl]
    exact .cons (rep_of_repB g0) (.cons (rep_of_repB g1) (.cons (rep_of_repB g2) .nil))
  have hC : Nat.card {g // g ∈ QA.originalSubgroup ∧ g * pu = pu * g} = u33C.length := by
    rw [QA_closure, beq_iff.1 len_ok]
    exact h192
  have h0 : AtT QP.originalSubgroup QA.originalSubgroup pu :=
    atT_of_checks hS (rep_of_repB gu) hSA hP hout ent_ok inc_ok hC uniq_ok wit_ok
  have hnorm : ∀ s ∈ QA.originalSubgroup, ∀ x ∈ QP.originalSubgroup,
      s * x * s⁻¹ ∈ QP.originalSubgroup := by
    rw [QP_closure, QA_closure]
    exact conj_AP
  intro t ht ht2 ht1
  have ht' : t ∈ Subgroup.closure ({pa, pb} : Set (Equiv.Perm (Fin 28))) := by
    rw [← QP_closure]
    exact ht
  obtain ⟨σ, hσ, rfl⟩ := invol_P t ht' (orderOf_eq_prime (by rw [sq]; exact ht2) ht1)
  rw [← QA_closure] at hσ
  exact atT_conj hnorm h0 hσ

end Certificates
