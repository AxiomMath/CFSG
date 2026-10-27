module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomBasic

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem card_normalized_le [Finite F] (hσ : ∀ c, σ (σ c) = c) {U : Submodule F (Fin 6 → F)}
    (hU : NonDeg σ U) (h3 : finrank F U = 3) {S : Set (Fin 6 → F)} (hS : ClosedPts σ S)
    {z : Fin 6 → F} (hzU : z ∈ U) (hz0 : z ≠ 0) (hzi : herm σ z z = 0) (hzS : z ∉ S) :
    Nat.card {x : Fin 6 → F // x ∈ S ∧ x ∈ U ∧ herm σ z x = 1} ≤ Nat.card F := by
  have hzperp : z ∈ orth σ (Submodule.span F {z}) := by
    rw [mem_orth]
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [herm_smul_left, hzi, mul_zero]
  have hLz : Submodule.span F {z} ≤ U := (Submodule.span_singleton_le_iff_mem z U).mpr hzU
  have hzW : Submodule.span F {z} ≤ U ⊓ orth σ (Submodule.span F {z}) :=
    (Submodule.span_singleton_le_iff_mem z _).mpr (Submodule.mem_inf.mpr ⟨hzU, hzperp⟩)
  have hW2 : finrank F ↥(U ⊓ orth σ (Submodule.span F {z})) = 2 := by
    have h := finrank_inf_orth hσ hU hLz
    rw [finrank_span_singleton hz0, h3] at h
    omega
  obtain ⟨e, heW, heN⟩ : ∃ e ∈ U ⊓ orth σ (Submodule.span F {z}),
      e ∉ Submodule.span F {z} := by
    by_contra hcon
    push Not at hcon
    have heq : Submodule.span F {z} = U ⊓ orth σ (Submodule.span F {z}) :=
      le_antisymm hzW (fun e he => hcon e he)
    have h1 := hW2
    rw [← heq, finrank_span_singleton hz0] at h1
    omega
  have heU : e ∈ U := (Submodule.mem_inf.mp heW).1
  have hze : herm σ z e = 0 :=
    (mem_orth σ).mp (Submodule.mem_inf.mp heW).2 z (Submodule.mem_span_singleton_self z)
  have hez : herm σ e z = 0 := herm_eq_zero_comm σ hσ hze
  have hLe : Submodule.span F {z, e} ≤ U :=
    Submodule.span_le.mpr (Set.insert_subset_iff.mpr ⟨hzU, Set.singleton_subset_iff.mpr heU⟩)
  have hli : LinearIndependent F ![z, e] :=
    (LinearIndependent.pair_iff' hz0).mpr fun a ha =>
      heN (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)
  have hfinL : finrank F (Submodule.span F {z, e}) = 2 := by
    have h := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty z e ![], Fintype.card_fin] at h
    exact h
  have hdimU' : finrank F ↥(U ⊓ orth σ (Submodule.span F {z, e})) = 1 := by
    have h := finrank_inf_orth hσ hU hLe
    rw [hfinL, h3] at h
    omega
  have hzLe : Submodule.span F {z} ≤ U ⊓ orth σ (Submodule.span F {z, e}) := by
    refine (Submodule.span_singleton_le_iff_mem z _).mpr (Submodule.mem_inf.mpr ⟨hzU, ?_⟩)
    rw [mem_orth]
    intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    simp only [herm_add_left, herm_smul_left, hzi, hez, mul_zero, add_zero]
  have hUz : U ⊓ orth σ (Submodule.span F {z, e}) = Submodule.span F {z} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hzLe
    rw [finrank_span_singleton hz0, hdimU']
  refine Nat.card_le_card_of_injective (fun x => herm σ e x.1) ?_
  rintro ⟨x₁, hx₁S, hx₁U, hx₁z⟩ ⟨x₂, hx₂S, hx₂U, hx₂z⟩ hf
  dsimp only at hf
  have key : x₁ = x₂ := by
    by_contra hne
    have hd_U : x₁ - x₂ ∈ U := Submodule.sub_mem U hx₁U hx₂U
    have hz_d : herm σ z (x₁ - x₂) = 0 := by
      rw [herm_sub_right, hx₁z, hx₂z, sub_self]
    have he_d : herm σ e (x₁ - x₂) = 0 := by
      rw [herm_sub_right, hf, sub_self]
    have hd_orth : x₁ - x₂ ∈ orth σ (Submodule.span F {z, e}) := by
      rw [mem_orth]
      intro w hw
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
      simp only [herm_add_left, herm_smul_left, hz_d, he_d, mul_zero, add_zero]
    have hd_mem : x₁ - x₂ ∈ U ⊓ orth σ (Submodule.span F {z, e}) :=
      Submodule.mem_inf.mpr ⟨hd_U, hd_orth⟩
    rw [hUz] at hd_mem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd_mem
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hne (sub_eq_zero.mp hc.symm)
    have hz' : z = c⁻¹ • (x₁ - x₂) := by
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hzspan : z ∈ Submodule.span F {x₁, x₂} := by
      rw [Submodule.mem_span_pair]
      refine ⟨c⁻¹, -c⁻¹, ?_⟩
      rw [hz', smul_sub, neg_smul, sub_eq_add_neg]
    have hx₁i : herm σ x₁ x₁ = 0 := (hS.iso x₁ hx₁S).2
    have hx₂i : herm σ x₂ x₂ = 0 := (hS.iso x₂ hx₂S).2
    have hx₁0 : x₁ ≠ 0 := (hS.iso x₁ hx₁S).1
    have hx₂notin : x₂ ∉ Submodule.span F {x₁} := by
      intro hmem
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
      have hμz : herm σ z x₂ = μ := by
        rw [← hμ, herm_smul_right, hx₁z, mul_one]
      rw [hx₂z] at hμz
      apply hne
      rw [← hμ, ← hμz, one_smul]
    have hne_ip : herm σ x₁ x₂ ≠ 0 :=
      herm_ne_zero_of_noTI hσ (fun L hL h2 => noTI_of_nonDeg_three hσ hU h3 hL h2)
        hx₁U hx₂U hx₁0 hx₂notin hx₁i hx₂i
    exact hzS (hS.secant x₁ hx₁S x₂ hx₂S hne_ip z hz0 hzi hzspan)
  exact Subtype.ext key

end CFSG.RankThree.GF2n.Smith81.S81V
