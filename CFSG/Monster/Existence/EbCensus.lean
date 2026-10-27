module

public import CFSG.Monster.Existence.EbFrame
public import CFSG.Monster.Existence.EbCase2
public import Certificates.Certificate16019

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

theorem exists_Gmat_conj_of_conj {f f' t : SpaceB ≃ₗ[ℚ] SpaceB} (ht : t ∈ Gmat)
    (h : t * f * t⁻¹ = f') (hf' : ∃ g ∈ Gmat, g * xmat * g⁻¹ = f') :
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = f := by
  obtain ⟨g, hg, hgf⟩ := hf'
  refine ⟨t⁻¹ * g, Gmat.mul_mem (Gmat.inv_mem ht) hg, ?_⟩
  calc t⁻¹ * g * xmat * (t⁻¹ * g)⁻¹ = t⁻¹ * (g * xmat * g⁻¹) * t := by group
    _ = t⁻¹ * f' * t := by rw [hgf]
    _ = f := by rw [← h]; group

theorem exists_Gmat_conj_of_mem_qmatClass {f f' : Gvis} (hf : f ∈ qmatClass f')
    (h' : ∃ g ∈ Gmat, g * xmat * g⁻¹ = (f' : SpaceB ≃ₗ[ℚ] SpaceB)) :
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = (f : SpaceB ≃ₗ[ℚ] SpaceB) := by
  obtain ⟨u, hu, rfl⟩ := hf
  refine exists_Gmat_conj_of_conj (t := (u : SpaceB ≃ₗ[ℚ] SpaceB)) (Hmat_le_Gmat u.2) ?_ h'
  change (u : SpaceB ≃ₗ[ℚ] SpaceB) * ((u : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * (f' : SpaceB ≃ₗ[ℚ] SpaceB) *
    (u : SpaceB ≃ₗ[ℚ] SpaceB)) * (u : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ = (f' : SpaceB ≃ₗ[ℚ] SpaceB)
  group

theorem conjQ_cosetPair_fix
    {i : ℕ} {y : Model.Pauli} (h : alphaN i y = y) :
    conjQ (cosetPair i) (pauliQ y) = pauliQ y := by
  rw [conjQ_cosetPair, h]

theorem rhoEquiv_mul_cosetRep_comm
    {i : ℕ} {q : Q} (h : conjQ (cosetPair i) q = q) :
    rhoEquiv q * (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) =
      (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv q := by
  have h1 := Visible.thetaEquiv_conj_rhoEquiv (cosetPair i) q
  rw [h] at h1
  rw [coe_cosetRep]
  exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem alphaN_one_63 :
    alphaN 1 (false, 63, 0) = (false, 63, 0) :=
  Certificates.certificate16019.1

theorem alphaN_one_60_48 :
    alphaN 1 (false, 60, 48) = (false, 60, 48) :=
  Certificates.certificate16019.2

theorem eb_classRep_four :
    classRep 4 = cosetRep 1 * rhoGvis (qP 0 63 0) := by
  rw [classRep, cosetElt, classEnc_four, qOfEnc_eq_qP (s := 0) (A := 63) (D := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [pauliEnc])]

theorem cosetElt_one_196668 :
    cosetElt 1 196668 = cosetRep 1 * rhoGvis (qP 0 60 48) := by
  rw [cosetElt, qOfEnc_eq_qP (s := 0) (A := 60) (D := 48) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [pauliEnc])]

theorem exists_Gmat_conj_classRep_four
    (w2 : tauB ^ 2 * (rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) *
      (tauB ^ 2)⁻¹ = rhoEquiv (qP 1 60 60)) :
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = (classRep 4 : SpaceB ≃ₗ[ℚ] SpaceB) := by
  have hc : conjQ (cosetPair 1) (qP 0 63 0) = qP 0 63 0 :=
    conjQ_cosetPair_fix (y := (false, 63, 0)) alphaN_one_63
  have e : (classRep 4 : SpaceB ≃ₗ[ℚ] SpaceB) =
      rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) := by
    rw [eb_classRep_four, rhoEquiv_mul_cosetRep_comm hc]
    rfl
  rw [e]
  exact exists_Gmat_conj_of_conj (pow_mem tauB_mem_Gmat 2) w2
    exists_Gmat_conj_rhoEquiv_qP_one_sixty_sixty

theorem exists_Gmat_conj_cosetElt_one_196668
    (w3 : tauB * (rhoEquiv (qP 0 60 48) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) * tauB⁻¹ =
      rhoEquiv (qP 1 3 48)) :
    ∃ g ∈ Gmat, g * xmat * g⁻¹ = (cosetElt 1 196668 : SpaceB ≃ₗ[ℚ] SpaceB) := by
  have hc : conjQ (cosetPair 1) (qP 0 60 48) = qP 0 60 48 :=
    conjQ_cosetPair_fix (y := (false, 60, 48)) alphaN_one_60_48
  have e : (cosetElt 1 196668 : SpaceB ≃ₗ[ℚ] SpaceB) =
      rhoEquiv (qP 0 60 48) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) := by
    rw [cosetElt_one_196668, rhoEquiv_mul_cosetRep_comm hc]
    rfl
  rw [e]
  exact exists_Gmat_conj_of_conj tauB_mem_Gmat w3 exists_Gmat_conj_rhoEquiv_qP_one_three_fortyeight

theorem rhoEquiv_mul_cosetRep_mem_cosetR
    {i : ℕ} (q : Q) :
    rhoGvis q * cosetRep i ∈ cosetR i := by
  rw [mem_cosetR_iff, map_mul, (piVis_eq_one_iff _).2 ⟨q, rfl⟩, one_mul]

theorem exists_Gmat_conj_cosetInv_two
    (w4 : tauB * (rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB)) * tauB⁻¹ =
      rhoEquiv (qP 1 734 0)) :
    ∃ g₂ ∈ cosetInv 2, ∃ g ∈ Gmat, g * xmat * g⁻¹ = (g₂ : SpaceB ≃ₗ[ℚ] SpaceB) := by
  have hx := exists_Gmat_conj_rhoEquiv_qP_one_734_zero
  have hinv : rhoEquiv (qP 1 734 0) * rhoEquiv (qP 1 734 0) = 1 :=
    (frameInv_subset rhoEquiv_qP_one_734_zero_mem_frameInv).2.2
  refine ⟨rhoGvis (qP 0 734 0) * cosetRep 2, ⟨rhoEquiv_mul_cosetRep_mem_cosetR _, ?_⟩, ?_⟩
  · apply Subtype.ext
    change (rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB)) *
      (rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB)) = 1
    set a := rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB) with ha
    have h1 : a = tauB⁻¹ * rhoEquiv (qP 1 734 0) * tauB := by rw [← w4]; group
    calc a * a = tauB⁻¹ * (rhoEquiv (qP 1 734 0) * rhoEquiv (qP 1 734 0)) * tauB := by
          rw [h1]; group
      _ = 1 := by rw [hinv]; group
  · exact exists_Gmat_conj_of_conj tauB_mem_Gmat w4 hx

theorem CosetTwoBCensus.of_witnesses
    (w2 : tauB ^ 2 * (rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) *
      (tauB ^ 2)⁻¹ = rhoEquiv (qP 1 60 60))
    (w3 : tauB * (rhoEquiv (qP 0 60 48) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) * tauB⁻¹ =
      rhoEquiv (qP 1 3 48))
    (w4 : tauB * (rhoEquiv (qP 0 734 0) * (cosetRep 2 : SpaceB ≃ₗ[ℚ] SpaceB)) * tauB⁻¹ =
      rhoEquiv (qP 1 734 0))
    (fus : ∀ k < 137, k ≠ 0 → k ≠ 4 →
      ∃ g : Gvis, g * classRep k * g⁻¹ ∈ qmatClass (classRep 17)) :
    CosetTwoBCensus where
  one f hf hf0 := by
    obtain ⟨k, hk, hfk⟩ := mem_qmatClass_of_mem_cosetInv_one hf
    have hk0 : k ≠ 0 := fun h => hf0 (h ▸ hfk)
    have hkx : ∃ g ∈ Gmat, g * xmat * g⁻¹ = (classRep k : SpaceB ≃ₗ[ℚ] SpaceB) := by
      by_cases h4 : k = 4
      · subst h4
        exact exists_Gmat_conj_classRep_four w2
      · obtain ⟨g, hg⟩ := fus k hk hk0 h4
        have e17 : qmatClass (classRep 17) = qmatClass (cosetElt 1 196668) :=
          (qmatClass_eq_of_mem mem_qmatClass_seventeen).symm
        rw [e17] at hg
        exact exists_Gmat_conj_of_conj (t := (g : SpaceB ≃ₗ[ℚ] SpaceB)) (Hmat_le_Gmat g.2) rfl
          (exists_Gmat_conj_of_mem_qmatClass hg (exists_Gmat_conj_cosetElt_one_196668 w3))
    exact exists_Gmat_conj_of_mem_qmatClass hfk hkx
  two f hf := by
    obtain ⟨g₂, hg₂, hx₂⟩ := exists_Gmat_conj_cosetInv_two w4
    rw [cosetInv_two_eq] at hf hg₂
    have e : qmatClass g₂ = qmatClass (cosetElt 2 734) := qmatClass_eq_of_mem hg₂
    rw [← e] at hf
    exact exists_Gmat_conj_of_mem_qmatClass hf hx₂

end CFSG.Monster.Existence
