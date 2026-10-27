module

public import CFSG.Monster.Existence.Census.ThreeCosets
public import CFSG.Monster.Existence.Census.CosetOneFusion
public import CFSG.Monster.Existence.InvolutionClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census Matrix
open CFSG.Monster.B.Short (tStar rStar isShortCoord_rStar)
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

@[expose] def ConjToQmat (x : SpaceB ≃ₗ[ℚ] SpaceB) : Prop :=
  ∃ c ∈ Gmat, ∃ r : Q, r ≠ 1 ∧ r * r = 1 ∧ c * x * c⁻¹ = rhoEquiv r

theorem ConjToQmat.conj {x g : SpaceB ≃ₗ[ℚ] SpaceB} (h : ConjToQmat x) (hg : g ∈ Gmat) :
    ConjToQmat (g * x * g⁻¹) := by
  obtain ⟨c, hc, r, hr1, hr2, hcx⟩ := h
  refine ⟨c * g⁻¹, mul_mem hc (inv_mem hg), r, hr1, hr2, ?_⟩
  rw [← hcx]
  group

theorem conjToQmat_rho (r : Q) (h1 : r ≠ 1) (h2 : r * r = 1) : ConjToQmat (rhoEquiv r) :=
  ⟨1, one_mem _, r, h1, h2, by group⟩

theorem conjToQmat_of_mem_rhoQ {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : f ∈ rhoQ) (hff : f * f = 1)
    (hf1 : f ≠ 1) : ConjToQmat f := by
  obtain ⟨r, rfl⟩ := mem_rhoQ.1 hf
  refine conjToQmat_rho r ?_ ?_
  · rintro rfl
    exact hf1 rhoEquiv_one'
  · apply rhoEquiv_injective
    rw [rhoEquiv_mul, hff, rhoEquiv_one']

theorem mem_Gmat_of_Gvis (f : Gvis) : (f : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat := Hmat_le_Gmat f.2

theorem conjToQmat_cosetElt_zero :
    ConjToQmat ((cosetElt 1 0 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [cosetElt_zero]
  have ht := trialityTargets_involutions (qP 0 3 60) (by simp)
  exact ⟨tauB ^ 2, pow_mem tauB_mem_Gmat 2, qP 0 3 60, ht.1, ht.2, trialityWitness_one⟩

theorem conjToQmat_cosetElt_sixtythree :
    ConjToQmat ((cosetElt 1 63 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [cosetElt_sixtythree]
  have ht := trialityTargets_involutions (qP 1 60 60) (by simp)
  exact ⟨tauB ^ 2, pow_mem tauB_mem_Gmat 2, qP 1 60 60, ht.1, ht.2, trialityWitness_two⟩

theorem conjToQmat_cosetElt_196668 :
    ConjToQmat ((cosetElt 1 196668 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [cosetElt_196668]
  have ht := trialityTargets_involutions (qP 1 3 48) (by simp)
  exact ⟨tauB, tauB_mem_Gmat, qP 1 3 48, ht.1, ht.2, trialityWitness_three⟩

theorem conjToQmat_of_mem_cosetInv_one
    {f : Gvis} (hf : f ∈ cosetInv 1) :
    ConjToQmat (f : SpaceB ≃ₗ[ℚ] SpaceB) := by
  obtain ⟨g, n, hn, hgf⟩ := exists_conj_cosetElt_of_mem_cosetInv_one hf
  have h : ConjToQmat ((cosetElt 1 n : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact conjToQmat_cosetElt_zero
    · exact conjToQmat_cosetElt_sixtythree
    · exact conjToQmat_cosetElt_196668
  have h' := h.conj (mem_Gmat_of_Gvis g⁻¹)
  rw [← hgf] at h'
  have e : ((g⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) *
      ((g * f * g⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) * ((g⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ =
        (f : SpaceB ≃ₗ[ℚ] SpaceB) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e] at h'
  exact h'

theorem conjToQmat_of_mem_cosetInv_two
    {f : Gvis} (hf : f ∈ cosetInv 2) :
    ConjToQmat (f : SpaceB ≃ₗ[ℚ] SpaceB) := by
  obtain ⟨E, hE⟩ : ∃ E : Gvis, E = rhoGvis (qP 0 734 0) * cosetRep 2 := ⟨_, rfl⟩
  have hEc : (E : SpaceB ≃ₗ[ℚ] SpaceB) =
      rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB) := by rw [hE]; rfl
  have hW := trialityWitness_four
  have ht := trialityTargets_involutions (qP 1 734 0) (by simp)
  have hconj : ConjToQmat (E : SpaceB ≃ₗ[ℚ] SpaceB) :=
    ⟨tauB, tauB_mem_Gmat, qP 1 734 0, ht.1, ht.2, by rw [hEc]; exact hW⟩
  have hEE : E * E = 1 := by
    apply Subtype.ext
    have h1 : (tauB * (E : SpaceB ≃ₗ[ℚ] SpaceB) * tauB⁻¹) = rhoEquiv (qP 1 734 0) := by
      rw [hEc]; exact hW
    have h2 : rhoEquiv (qP 1 734 0) * rhoEquiv (qP 1 734 0) = 1 := by
      rw [← rhoEquiv_mul, ht.2, rhoEquiv_one']
    have h3 : (E : SpaceB ≃ₗ[ℚ] SpaceB) = tauB⁻¹ * rhoEquiv (qP 1 734 0) * tauB := by
      rw [← h1]; group
    show (E : SpaceB ≃ₗ[ℚ] SpaceB) * (E : SpaceB ≃ₗ[ℚ] SpaceB) = 1
    calc (E : SpaceB ≃ₗ[ℚ] SpaceB) * (E : SpaceB ≃ₗ[ℚ] SpaceB) =
        (tauB⁻¹ * rhoEquiv (qP 1 734 0) * tauB) * (tauB⁻¹ * rhoEquiv (qP 1 734 0) * tauB) := by
          rw [← h3]
      _ = tauB⁻¹ * (rhoEquiv (qP 1 734 0) * rhoEquiv (qP 1 734 0)) * tauB := by group
      _ = 1 := by rw [h2]; group
  have hER : E ∈ cosetR 2 := by
    rw [mem_cosetR_iff, hE, map_mul]
    have : piVis (rhoGvis (qP 0 734 0)) = 1 := by
      rw [← MonoidHom.mem_ker, ker_piVis]
      exact rhoGvis_mem _
    rw [this, one_mul]
  have hEinv : E ∈ cosetInv 2 := ⟨hER, hEE⟩
  have hcls : cosetInv 2 = qmatClass E := by
    have h1 : E ∈ qmatClass (cosetElt 2 734) := by rw [← cosetInv_two_eq]; exact hEinv
    rw [cosetInv_two_eq, qmatClass_eq_of_mem h1]
  rw [hcls] at hf
  obtain ⟨u, hu, hux⟩ := exists_conj_of_mem_qmatClass hf
  have h' := hconj.conj (mem_Gmat_of_Gvis u⁻¹)
  have e : ((u⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) * (E : SpaceB ≃ₗ[ℚ] SpaceB) *
      ((u⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = (f : SpaceB ≃ₗ[ℚ] SpaceB) := by
    have : f = u⁻¹ * E * u := by rw [← hux]; group
    rw [this]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e] at h'
  exact h'

theorem not_mem_cosetInv_six
    (f : Gvis) : f ∉ cosetInv 6 := by
  intro hf
  have h0 : (cosetInv 6).ncard = 0 := ncard_cosetInv_six
  have := (Set.ncard_eq_zero (cosetInv_finite (Or.inr (Or.inr rfl)))).1 h0
  rw [this] at hf
  exact hf

theorem generated_involutions_conj_Qmat
    (t : Gmat) (ht : orderOf t = 2) :
    ∃ c : Gmat, ∃ r : Q, r ≠ 1 ∧ r * r = 1 ∧
      ((c * t * c⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv r := by
  obtain ⟨c, f, hfc, hff, hf1, hcases⟩ := generated_involutions_three_visible_cosets t ht
  have hf : ConjToQmat (f : SpaceB ≃ₗ[ℚ] SpaceB) := by
    have hff' : (f : SpaceB ≃ₗ[ℚ] SpaceB) * (f : SpaceB ≃ₗ[ℚ] SpaceB) = 1 := by
      have := congrArg Subtype.val hff
      simpa using this
    have hf1' : (f : SpaceB ≃ₗ[ℚ] SpaceB) ≠ 1 := fun h => hf1 (Subtype.ext (by simpa using h))
    rcases hcases with h | h | h | h
    · exact conjToQmat_of_mem_rhoQ h hff' hf1'
    · exact conjToQmat_of_mem_cosetInv_one ⟨h, hff⟩
    · exact conjToQmat_of_mem_cosetInv_two ⟨h, hff⟩
    · exact absurd ⟨h, hff⟩ (not_mem_cosetInv_six f)
  rw [hfc] at hf
  obtain ⟨c', hc', r, hr1, hr2, hcr⟩ := hf
  refine ⟨⟨c' * (c : SpaceB ≃ₗ[ℚ] SpaceB), mul_mem hc' c.2⟩, r, hr1, hr2, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcr ⊢
  rw [← hcr]
  group

theorem isConj_of_conj {a g : Gmat} {c : SpaceB ≃ₗ[ℚ] SpaceB} (hc : c ∈ Gmat)
    (h : c * (g : SpaceB ≃ₗ[ℚ] SpaceB) * c⁻¹ = (a : SpaceB ≃ₗ[ℚ] SpaceB)) : IsConj a g := by
  refine isConj_iff.2 ⟨⟨c⁻¹, inv_mem hc⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  rw [← h]
  group

theorem tStar_mem_shortInv : tStar ∈ shortInv := ⟨rStar, isShortCoord_rStar, rfl⟩

theorem generated_group_two_involution_classes :
    ∀ g : Gmat, orderOf g = 2 → IsConj xGmat g ∨ IsConj tGmat g := by
  intro g hg
  obtain ⟨c, r, hr1, hr2, hcr⟩ := generated_involutions_conj_Qmat g hg
  have hmem : rhoEquiv r ∈ involQmat :=
    ⟨rhoEquiv_mem_rhoQ r, fun h => hr1 (rhoEquiv_injective (h.trans rhoEquiv_one'.symm)),
      by rw [← rhoEquiv_mul, hr2, rhoEquiv_one']⟩
  rw [involQmat_eq] at hmem
  have hc : (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gmat := c.2
  have hcr' : (c : SpaceB ≃ₗ[ℚ] SpaceB) * (g : SpaceB ≃ₗ[ℚ] SpaceB) *
      (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = rhoEquiv r := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcr
  rcases hmem with (h | h) | h
  · left
    exact isConj_of_conj hc (hcr'.trans (Set.mem_singleton_iff.1 h))
  · right
    obtain ⟨d, hd, hdt⟩ := shortInv_transitive tStar_mem_shortInv h
    refine isConj_of_conj (c := d⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB))
      (mul_mem (inv_mem (Hmat_le_Gmat hd)) hc) ?_
    show _ = tStar
    calc d⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB) * (g : SpaceB ≃ₗ[ℚ] SpaceB) *
          (d⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB))⁻¹ =
        d⁻¹ * ((c : SpaceB ≃ₗ[ℚ] SpaceB) * (g : SpaceB ≃ₗ[ℚ] SpaceB) *
          (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹) * d := by group
      _ = tStar := by rw [hcr', ← hdt]; group
  · left
    obtain ⟨d, hd, hdx⟩ := exists_Gmat_conj_xmat h
    refine isConj_of_conj (c := d⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB)) (mul_mem (inv_mem hd) hc) ?_
    show _ = xmat
    calc d⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB) * (g : SpaceB ≃ₗ[ℚ] SpaceB) *
          (d⁻¹ * (c : SpaceB ≃ₗ[ℚ] SpaceB))⁻¹ =
        d⁻¹ * ((c : SpaceB ≃ₗ[ℚ] SpaceB) * (g : SpaceB ≃ₗ[ℚ] SpaceB) *
          (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹) * d := by group
      _ = xmat := by rw [hcr', ← hdx]; group

theorem generated_group_two_involution_classes_distinct :
    orderOf xGmat = 2 ∧ ¬ IsConj xGmat tGmat ∧
      LinearMap.trace ℚ SpaceB (xmat : SpaceB →ₗ[ℚ] SpaceB) = 276 ∧
      LinearMap.trace ℚ SpaceB (tStar : SpaceB →ₗ[ℚ] SpaceB) = 4372 :=
  ⟨orderOf_xGmat, not_isConj_xGmat_tGmat, trace_xmat', trace_tStar⟩

end CFSG.Monster.Existence.Census
