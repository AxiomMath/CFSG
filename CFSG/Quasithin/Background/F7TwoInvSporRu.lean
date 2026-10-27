module

public import CFSG.Quasithin.Background.F7TwoInvSporModel
public import CFSG.Quasithin.Background.F7TwoInvL2Model
public import CFSG.Sporadic.Schreier.RuAutInner
public import Certificates.Certificate7418

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier
open CFSG.Blueprint

section Check


theorem ruInvChk_spec :
    (ruA0 * ruA1 * ruA0⁻¹ * ruA1⁻¹) ^ 7 = 1 ∧ ruA0 * ruA1 * ruA0⁻¹ * ruA1⁻¹ ≠ 1 ∧
    (ruA1 ^ 2 * ruA0 * (ruA1 ^ 2)⁻¹ * ruA0⁻¹) ^ 7 = 1 ∧
      ruA1 ^ 2 * ruA0 * (ruA1 ^ 2)⁻¹ * ruA0⁻¹ ≠ 1 := by
  have h := Certificates.certificate7418
  simp only [ruInvChk, ruSevenChk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have rA := rep_ruA0
  have rB := rep_ruA1
  have rAi := rep_ruInv rA ruBasic_check.1
  have rBi := rep_ruInv rB ruBasic_check.2.1
  have c1 : Rep 4060 (ruCommA ruA0A ruA1A (ruInv ruA0A) (ruInv ruA1A))
      (ruA0 * ruA1 * ruA0⁻¹ * ruA1⁻¹) := rep_compA (rep_compA (rep_compA rA rB) rAi) rBi
  have rB2 : Rep 4060 (compA 4060 ruA1A ruA1A) (ruA1 ^ 2) := by
    rw [pow_two]
    exact rep_compA rB rB
  have rB2i : Rep 4060 (compA 4060 (ruInv ruA1A) (ruInv ruA1A)) (ruA1 ^ 2)⁻¹ := by
    rw [pow_two, mul_inv_rev]
    exact rep_compA rBi rBi
  have c2 : Rep 4060 (ruCommA (compA 4060 ruA1A ruA1A) ruA0A
      (compA 4060 (ruInv ruA1A) (ruInv ruA1A)) (ruInv ruA0A))
      (ruA1 ^ 2 * ruA0 * (ruA1 ^ 2)⁻¹ * ruA0⁻¹) :=
    rep_compA (rep_compA (rep_compA rB2 rA) rB2i) rAi
  refine ⟨eq_of_eqA (rep_powA c1 7) rep_idA h1, fun e => ?_,
    eq_of_eqA (rep_powA c2 7) rep_idA h3, fun e => ?_⟩
  · rw [(eqA_iff c1 rep_idA).2 e] at h2
    exact absurd h2 (by decide)
  · rw [(eqA_iff c2 rep_idA).2 e] at h4
    exact absurd h4 (by decide)

end Check

section Classes


theorem invAutGen_ruP :
    ∀ φ : MulAut ruP, φ * φ = 1 → φ ≠ 1 → InvAutGen ruP φ := by
  obtain ⟨hcenter, hconj, -, -⟩ := CTUC_Ru_full_inner_automorphisms_and_second_centralizer
  obtain ⟨y1, y1n, y2, y2n⟩ := ruInvChk_spec
  have hsq := ruA1_sq_mem
  have hb : ∀ n : ℕ, (ruA0 * ruA1 * ruA0⁻¹ * ruA1⁻¹) ^ 2 ^ n ≠ 1 :=
    pow_two_pow_ne_one_of_pow (s := 0) (m := 7) (by decide) (by simpa using y1) (by simpa using y1n)
  have ha : ∀ n : ℕ, (ruA1 ^ 2 * ruA0 * (ruA1 ^ 2)⁻¹ * ruA0⁻¹) ^ 2 ^ n ≠ 1 :=
    pow_two_pow_ne_one_of_pow (s := 0) (m := 7) (by decide) (by simpa using y2) (by simpa using y2n)
  refine invAutGen_of_model (P := ruP) (R := ruP) le_rfl
    (fun x hx _ hp => ruP.mul_mem (ruP.mul_mem hx hp) (ruP.inv_mem hx))
    (fun α => by
      obtain ⟨g, hg⟩ := hconj.2 α
      exact ⟨g, g.2, fun p => by rw [← hg]; simp [MulAut.conj_apply]⟩)
    (fun x hx hc => by
      have hmem : (⟨x, hx⟩ : ruP) ∈ Subgroup.center ruP := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hc g g.2).symm
      rw [hcenter, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem)
    closure_ruA' [ruA1 ^ 2, ruA0] ?_ ?_
  · intro x hxR hx2 hx1
    have hord : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
    have hx : x ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨hxR, hord⟩
    rw [ruInvolutions_eq] at hx
    rcases hx with hz | haA
    · have e := CFSG.Sporadic.RuSchreier.conjSet_eq_of_mem hsq
      obtain ⟨g, hg, hgx⟩ : x ∈ CFSG.Sporadic.RuSchreier.conjSet ruP (ruA1 ^ 2) := by
        rw [e]
        exact hz
      exact ⟨ruA1 ^ 2, by simp, g, hg, hgx.symm⟩
    · obtain ⟨g, hg, hgx⟩ := haA
      exact ⟨ruA0, by simp, g, hg, hgx.symm⟩
  · intro ρ hρ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · refine ⟨ruP.pow_mem ruA1_mem 2, 1, one_mem _, ?_⟩
      simp only [one_mul, inv_one, mul_one]
      exact seedOK_pair (Or.inl ha) (Or.inr ((Commute.refl ruA1).pow_left 2).eq) (Or.inl ha)
    · refine ⟨ruA0_mem, 1, one_mem _, ?_⟩
      simp only [one_mul, inv_one, mul_one]
      exact seedOK_pair (Or.inr rfl) (Or.inl hb) (Or.inr hb)

theorem invAutGen_carrier_Ru :
    ∀ φ : MulAut (NativeSporadic.Carrier .Ru), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .Ru) φ :=
  invAutGen_of_mulEquiv_forall ruEquivP invAutGen_ruP

end Classes

end CFSG.Quasithin.F7Two
