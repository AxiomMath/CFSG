module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Second

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

section LinearAlgebra

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup E] [Module K E] [Finite E]

theorem involution_apply_eq_self_of_card_le {D : Submodule K E} (hD : Nat.card D ≤ Nat.card K)
    (L : E →ₗ[K] E) (hL : ∀ d ∈ D, L d ∈ D) (hL2 : ∀ e, L (L e) = e) {d : E} (hd : d ∈ D) :
    L d = d := by
  by_cases hd0 : d = 0
  · rw [hd0, map_zero]
  have hle : K ∙ d ≤ D := (Submodule.span_singleton_le_iff_mem d D).mpr hd
  have hcard : Nat.card D ≤ Nat.card (K ∙ d) := by
    rw [← Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton K E d hd0).toEquiv]
    exact hD
  have heq : K ∙ d = D := Submodule.toAddSubgroup_injective
    (AddSubgroup.eq_of_le_of_card_ge (H := (K ∙ d).toAddSubgroup) (K := D.toAddSubgroup) hle
      hcard)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (heq ▸ hL d hd : L d ∈ K ∙ d)
  have hcc : (c * c) • d = d := by
    rw [mul_smul, hc, ← map_smul, hc, hL2]
  have hc1 : c * c = 1 := by
    have h0 : (c * c - 1) • d = 0 := by rw [sub_smul, one_smul, hcc, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hd0)
  have hc2 : c = 1 := by
    rcases mul_self_eq_one_iff.mp hc1 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  rw [← hc, hc2, one_smul]

end LinearAlgebra

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem IsZConjugate.sq_mem_QB (H : StrothHyp M Q Z) {X : Subgroup G} (hX : IsZConjugate Z X)
    {a : G} (ha : a ∈ QB X) : a ^ 2 ∈ X := by
  obtain ⟨g, rfl⟩ := hX
  rw [QB_conj_eq H g] at ha
  exact sq_mem_Z (H.conj g) ha

private theorem mem_CQt_sup_of_forall (H : StrothHyp M Q Z) {P : Subgroup G} (hPM : P ≤ M)
    {u : G} (hu : u ∈ Q) (hP : ∀ l ∈ P, ⁅l, u⁆ ∈ Z) : u ∈ CQt Q Z (Q ⊔ P) := by
  refine ⟨hu, fun l hl => ?_⟩
  let S : Subgroup G :=
    { carrier := {s | s ∈ M ∧ ⁅s, u⁆ ∈ Z}
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨M.mul_mem haM hbM, ?_⟩
        have e : ⁅a * b, u⁆ = a * ⁅b, u⁆ * a⁻¹ * ⁅a, u⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        refine Z.mul_mem ?_ ha
        have := (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 haM) _).mp hb
        simpa using this
      one_mem' := ⟨M.one_mem, by simpa [commutatorElement_def] using Z.one_mem⟩
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨M.inv_mem haM, ?_⟩
        have e : ⁅a⁻¹, u⁆ = a⁻¹ * ⁅a, u⁆⁻¹ * a := by
          simp only [commutatorElement_def]; group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp (H.Z_normal.2 (M.inv_mem haM)) _).mp
          (Z.inv_mem ha)
        simpa using this }
  have hQS : Q ≤ S := fun q hq => ⟨H.Q_normal.1 hq, comm_mem_Z H hq hu⟩
  have hPS : P ≤ S := fun p hp => ⟨hPM hp, hP p hp⟩
  exact (sup_le hQS hPS hl).2

theorem Sec10Hyp.mem_sup_of_forall_comm_mem (h34 : Stroth34Statement) {hc : Ctx M Q Z B}
    {n : ℕ} (H : Sec10Hyp hc n) {μ : G} (hμ : μ ∈ M) {u : G} (hu : u ∈ Q)
    (hl : ∀ l ∈ QB (conjSubgroup μ B) ⊓ M, ⁅l, u⁆ ∈ Z) : u ∈ conjSubgroup μ B ⊔ Z := by
  have H' := H.conj_of_mem hμ
  have h35 := (stroth_3_5 h34 (hc.conj_of_mem hμ) H'.width H'.n_gt H'.noA2 H'.gen).2.1
  have h : u ∈ CQt Q Z (LB M Q (conjSubgroup μ B)) :=
    mem_CQt_sup_of_forall hc.hyp inf_le_right hu hl
  rw [h35] at h
  exact h

end CFSG.RankThree.GF2n.Stroth80
