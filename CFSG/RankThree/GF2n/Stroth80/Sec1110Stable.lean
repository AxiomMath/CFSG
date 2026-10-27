module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110DualAct

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
variable {n : ℕ} {X₁ X₂ X₃ X₄ : Subgroup G}

theorem piImageStable_of_naturalRep (hn : 3 ≤ n)
    (hX₁ : X₁ = Z) (hX₂ : X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆)
    (hX₃ : X₃ = X₂) (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆)
    (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (h₄Q : X₄ ≤ Q)
    (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁ (Q))
    (nat4 : NaturalDualRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₄ X₃ (Q)) :
    PiImageStable M₀ X₂ := by
  classical
  have hZ₁ : Z ≤ X₁ := hX₁ ▸ le_rfl
  have hX₂Q : X₂ ≤ Q := fun x hx => h₄Q (h₃₄ (h₂₃ hx))
  have hX₂X₄ : X₂ ≤ X₄ := h₂₃.trans h₃₄
  have hZ₄ : Z ≤ X₄ := by
    rw [← hX₁]
    exact h₁₂.trans hX₂X₄
  let S : AddSubgroup M₀.E := M₀.img X₂
  let W : Submodule K M₀.E := Submodule.span K (S : Set M₀.E)
  let T : Submodule K M₀.E := M₀.B.orthogonal W
  have hBvan : ∀ e ∈ S, ∀ f ∈ S, M₀.B e f = 0 := by
    intro e he f hf
    obtain ⟨x, hxX₂, -, rfl⟩ := M₀.mem_img.mp he
    obtain ⟨y, hyX₂, -, rfl⟩ := M₀.mem_img.mp hf
    exact B_vanishes_on_X₂_of_naturalRep (M₀ := M₀) hn hX₁ hX₂Q nat2 hc hD x hxX₂ y hyX₂
  have hS_T : S ≤ T.toAddSubgroup := by
    intro e he
    change e ∈ M₀.B.orthogonal W
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    have hzero : ∀ v ∈ W, M₀.B v e = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact hBvan x hx e he
      | zero => simp
      | add x y _ _ ihx ihy => simp [map_add, ihx, ihy]
      | smul a x _ ih => simp [map_smul, ih]
    exact hzero v hv
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 (M₀ := M₀) hc.hyp hD
  have hspanX₄ : Submodule.span K (M₀.π '' (X₄ : Set G)) = cmComm M Q Z B K γ M₀ φ :=
    span_pi_X₄_eq_cmComm hc hD φ hφπ hX₄
  have hfin : Module.finrank K (cmComm M Q Z B K γ M₀ φ) = 2 * n :=
    finrank_cmComm_of_dualRep hc hD φ hφπ hX₁ hZ₁ h₁₂ h₂₃ h₃₄ h₄Q hX₃ hX₄ nat2 nat4
  have hcardcm : Nat.card ↥(cmComm M Q Z B K γ M₀ φ) = Nat.card K ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := cmComm M Q Z B K γ M₀ φ), hfin]
  have hcardX₄ : Nat.card ↥X₄ = Nat.card Z * Nat.card K ^ (2 * n) :=
    card_X₄_of_dualRep (m := n) hX₁ hZ₁ h₁₂ h₂₃ h₃₄ hX₃ nat2 nat4
  have hcard₄ := M₀.card_eq (S := X₄) h₄Q hZ₄
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hcardimg₄ : Nat.card ↥(M₀.img X₄) = Nat.card K ^ (2 * n) := by
    refine Nat.eq_of_mul_eq_mul_left hZpos ?_
    rw [← hcard₄, hcardX₄]
  have himg_le_cm : M₀.img X₄ ≤ (cmComm M Q Z B K γ M₀ φ).toAddSubgroup := by
    intro e he
    rw [← hspanX₄]
    obtain ⟨y, hyX₄, -, hye⟩ := M₀.mem_img.mp he
    exact hye ▸ Submodule.subset_span (Set.mem_image_of_mem M₀.π hyX₄)
  haveI hEfin : Finite M₀.E := Module.finite_of_finite K
  haveI : Finite ↥(cmComm M Q Z B K γ M₀ φ) := Subtype.finite
  have hcardcmAdd : Nat.card ↥(cmComm M Q Z B K γ M₀ φ).toAddSubgroup =
      Nat.card K ^ (2 * n) := by
    rw [show Nat.card ↥(cmComm M Q Z B K γ M₀ φ).toAddSubgroup =
      Nat.card ↥(cmComm M Q Z B K γ M₀ φ) from rfl, hcardcm]
  have himg_eq : M₀.img X₄ = (cmComm M Q Z B K γ M₀ φ).toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge himg_le_cm (by rw [hcardcmAdd, hcardimg₄])
  have hS_cm : S ≤ (cmComm M Q Z B K γ M₀ φ).toAddSubgroup := by
    have h := M₀.img_mono hX₂X₄
    rwa [himg_eq] at h
  have hS_le : S ≤ T.toAddSubgroup ⊓ (cmComm M Q Z B K γ M₀ φ).toAddSubgroup :=
    le_inf hS_T hS_cm
  have hle_S : T.toAddSubgroup ⊓ (cmComm M Q Z B K γ M₀ φ).toAddSubgroup ≤ S := by
    intro e he
    obtain ⟨heT, heC⟩ := AddSubgroup.mem_inf.mp he
    have heimg : e ∈ M₀.img X₄ := by rwa [himg_eq]
    obtain ⟨y, hyX₄, hyQ, hye⟩ := M₀.mem_img.mp heimg
    have hpair : ∀ x ∈ X₂, M₀.B (M₀.π x) (M₀.π y) = 0 := by
      intro x hxX₂
      have hπxW : M₀.π x ∈ W :=
        Submodule.subset_span (M₀.pi_mem_img hxX₂ (hX₂Q hxX₂))
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp heT) (M₀.π x) hπxW
      rwa [← hye] at h
    have hyX₃ : y ∈ X₃ :=
      B_pairing_kernel (M₀ := M₀) hn hX₁ hX₂ hX₃ hX₄ h₁₂ h₂₃ h₃₄ h₄Q hc hD nat2 nat4
        hyX₄ hpair
    have hyX₂ : y ∈ X₂ := by rwa [← hX₃]
    exact ⟨y, hyX₂, hyQ, hye⟩
  have hSeq : S = T.toAddSubgroup ⊓ (cmComm M Q Z B K γ M₀ φ).toAddSubgroup :=
    le_antisymm hS_le hle_S
  intro c e he
  have he' : e ∈ T.toAddSubgroup ⊓ (cmComm M Q Z B K γ M₀ φ).toAddSubgroup := hSeq ▸ he
  obtain ⟨heT, heC⟩ := AddSubgroup.mem_inf.mp he'
  show c • e ∈ S
  rw [hSeq]
  exact AddSubgroup.mem_inf.mpr
    ⟨T.smul_mem c heT, (cmComm M Q Z B K γ M₀ φ).smul_mem c heC⟩

end CFSG.RankThree.GF2n.Stroth80
