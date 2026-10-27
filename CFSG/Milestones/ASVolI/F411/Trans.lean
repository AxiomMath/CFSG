module

public import CFSG.Milestones.ASVolI.F45.Six

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF CFSG.Quasithin.F7

section Trans

variable {A : Type} [Group A] {p : ℕ}

theorem burnsideF411_oPPrime_mono_aux (p : ℕ) {P Q : Subgroup A} (h : P ≤ Q) :
    oPPrime p P ≤ oPPrime p Q :=
  Subgroup.closure_mono fun x hx => ⟨h hx.1, hx.2⟩

theorem burnsideF411_trans_of_c6_xv (hp : p.Prime) {P₁ P₂ : Subgroup A} (hgen : P₁ ⊔ P₂ = ⊤)
    (hc : ∀ w₁ ∈ CosetGeom.nbrs (incl P₁ P₂).xv \ {(incl P₁ P₂).lv},
      ∀ w₂ ∈ CosetGeom.nbrs (incl P₁ P₂).xv \ {(incl P₁ P₂).lv},
      ∃ g ∈ oPPrime p (stv (incl P₁ P₂) (incl P₁ P₂).xv ⊓ stv (incl P₁ P₂) (incl P₁ P₂).lv),
        g • w₁ = w₂) :
    ∀ a₁ ∈ P₁, ∀ a₂ ∈ P₁, a₁ ∉ P₂ → a₂ ∉ P₂ → ∃ s ∈ oPPrime p (P₁ ⊓ P₂), a₂⁻¹ * s * a₁ ∈ P₂ := by
  intro a₁ ha₁ a₂ ha₂ hn₁ hn₂
  let e : (incl P₁ P₂).G0 ≃* A :=
    MulEquiv.ofBijective (toE (incl P₁ P₂)) (burnsideF45_toE_bijective hgen)
  have he : ∀ g, toE (incl P₁ P₂) g = e g := fun _ => rfl
  have hnbr : ∀ a ∈ P₁, a ∉ P₂ →
      e.symm a • (incl P₁ P₂).lv ∈ CosetGeom.nbrs (incl P₁ P₂).xv \ {(incl P₁ P₂).lv} := by
    intro a ha hna
    have hx : e.symm a ∈ stv (incl P₁ P₂) (incl P₁ P₂).xv := by
      rw [burnsideF45_mem_stv_xv_iff, he, MulEquiv.apply_symm_apply]
      exact ha
    have hl : e.symm a ∉ stv (incl P₁ P₂) (incl P₁ P₂).lv := by
      rw [burnsideF45_mem_stv_lv_iff', he, MulEquiv.apply_symm_apply]
      exact hna
    refine ⟨?_, fun h => hl (MulAction.mem_stabilizer_iff.mpr h)⟩
    have hx' : e.symm a • (incl P₁ P₂).xv = (incl P₁ P₂).xv := MulAction.mem_stabilizer_iff.mp hx
    have h1 : (incl P₁ P₂).graph.Adj (e.symm a • (incl P₁ P₂).xv) (e.symm a • (incl P₁ P₂).lv) :=
      (CosetGeom.smul_adj (G₁ := (incl P₁ P₂).φ1.range) (G₂ := (incl P₁ P₂).φ2.range)
        (e.symm a)).mpr CosetGeom.adj_γ₀_γ₁
    rw [hx'] at h1
    exact h1
  obtain ⟨g, hg, hgw⟩ := hc _ (hnbr a₁ ha₁ hn₁) _ (hnbr a₂ ha₂ hn₂)
  have hst : (e.symm a₂)⁻¹ * g * e.symm a₁ ∈ stv (incl P₁ P₂) (incl P₁ P₂).lv := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hgw, inv_smul_smul]
  refine ⟨e g, ?_, ?_⟩
  · have h1 := burnsideF45_oPPrime_map_le hp e.toMonoidHom _ ⟨g, hg, rfl⟩
    refine burnsideF411_oPPrime_mono_aux p ?_ h1
    rintro _ ⟨y, ⟨hyx, hyl⟩, rfl⟩
    exact ⟨(burnsideF45_mem_stv_xv_iff y).mp hyx, (burnsideF45_mem_stv_lv_iff' y).mp hyl⟩
  · have := (burnsideF45_mem_stv_lv_iff' _).mp hst
    rw [he, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact this

theorem burnsideF411_trans_of_c6_lv (hp : p.Prime) {P₁ P₂ : Subgroup A} (hgen : P₁ ⊔ P₂ = ⊤)
    (hc : ∀ w₁ ∈ CosetGeom.nbrs (incl P₁ P₂).lv \ {(incl P₁ P₂).xv},
      ∀ w₂ ∈ CosetGeom.nbrs (incl P₁ P₂).lv \ {(incl P₁ P₂).xv},
      ∃ g ∈ oPPrime p (stv (incl P₁ P₂) (incl P₁ P₂).lv ⊓ stv (incl P₁ P₂) (incl P₁ P₂).xv),
        g • w₁ = w₂) :
    ∀ a₁ ∈ P₂, ∀ a₂ ∈ P₂, a₁ ∉ P₁ → a₂ ∉ P₁ → ∃ s ∈ oPPrime p (P₁ ⊓ P₂), a₂⁻¹ * s * a₁ ∈ P₁ := by
  intro a₁ ha₁ a₂ ha₂ hn₁ hn₂
  let e : (incl P₁ P₂).G0 ≃* A :=
    MulEquiv.ofBijective (toE (incl P₁ P₂)) (burnsideF45_toE_bijective hgen)
  have he : ∀ g, toE (incl P₁ P₂) g = e g := fun _ => rfl
  have hnbr : ∀ a ∈ P₂, a ∉ P₁ →
      e.symm a • (incl P₁ P₂).xv ∈ CosetGeom.nbrs (incl P₁ P₂).lv \ {(incl P₁ P₂).xv} := by
    intro a ha hna
    have hl : e.symm a ∈ stv (incl P₁ P₂) (incl P₁ P₂).lv := by
      rw [burnsideF45_mem_stv_lv_iff', he, MulEquiv.apply_symm_apply]
      exact ha
    have hx : e.symm a ∉ stv (incl P₁ P₂) (incl P₁ P₂).xv := by
      rw [burnsideF45_mem_stv_xv_iff, he, MulEquiv.apply_symm_apply]
      exact hna
    refine ⟨?_, fun h => hx (MulAction.mem_stabilizer_iff.mpr h)⟩
    have hl' : e.symm a • (incl P₁ P₂).lv = (incl P₁ P₂).lv := MulAction.mem_stabilizer_iff.mp hl
    have h1 : (incl P₁ P₂).graph.Adj (e.symm a • (incl P₁ P₂).lv) (e.symm a • (incl P₁ P₂).xv) :=
      (CosetGeom.smul_adj (G₁ := (incl P₁ P₂).φ1.range) (G₂ := (incl P₁ P₂).φ2.range)
        (e.symm a)).mpr CosetGeom.adj_γ₀_γ₁.symm
    rw [hl'] at h1
    exact h1
  obtain ⟨g, hg, hgw⟩ := hc _ (hnbr a₁ ha₁ hn₁) _ (hnbr a₂ ha₂ hn₂)
  have hst : (e.symm a₂)⁻¹ * g * e.symm a₁ ∈ stv (incl P₁ P₂) (incl P₁ P₂).xv := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hgw, inv_smul_smul]
  refine ⟨e g, ?_, ?_⟩
  · have h1 := burnsideF45_oPPrime_map_le hp e.toMonoidHom _ ⟨g, hg, rfl⟩
    refine burnsideF411_oPPrime_mono_aux p ?_ h1
    rintro _ ⟨y, ⟨hyl, hyx⟩, rfl⟩
    exact ⟨(burnsideF45_mem_stv_xv_iff y).mp hyx, (burnsideF45_mem_stv_lv_iff' y).mp hyl⟩
  · have := (burnsideF45_mem_stv_xv_iff _).mp hst
    rw [he, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact this

end Trans

end CFSG.ASVolI
