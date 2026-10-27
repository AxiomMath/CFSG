module

public import CFSG.Quasithin.Vol2.Ch1Sec3L42L5Fix
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.Quasithin.L139L42

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L (stabilizer_entries
  mem_stabilizer_flagSpace_of_entries eq_zero_or_eq_one_of_card_two)

variable {F : Type*} [Field F] [Finite F]

theorem ringEquiv_apply_of_card_two (hF : Nat.card F = 2) (σ : F ≃+* F) (c : F) : σ c = c := by
  rcases eq_zero_or_eq_one_of_card_two hF c with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

theorem det_eq_one_of_card_two (hF : Nat.card F = 2) (A : GL (Fin 5) F) :
    (A : Matrix (Fin 5) (Fin 5) F).det = 1 := by
  have hne : (A : Matrix (Fin 5) (Fin 5) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A : Matrix (Fin 5) (Fin 5) F)).mp A.isUnit).ne_zero
  exact (eq_zero_or_eq_one_of_card_two hF _).resolve_left hne

@[expose] noncomputable def toSL (hF : Nat.card F = 2) (A : GL (Fin 5) F) :
    SpecialLinearGroup (Fin 5) F :=
  ⟨A, det_eq_one_of_card_two hF A⟩

theorem coe_toSL (hF : Nat.card F = 2) (A : GL (Fin 5) F) :
    ((toSL hF A : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = A := rfl

theorem coe_toSL_inv (hF : Nat.card F = 2) (A : GL (Fin 5) F) :
    (((toSL hF A)⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
  have h1 : (((toSL hF A)⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
      (A : Matrix (Fin 5) (Fin 5) F) = 1 :=
    congrArg Subtype.val (inv_mul_cancel (toSL hF A))
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv h1]

omit [Finite F] in
theorem fix_of_conj_fix {A : GL (Fin 5) F} {M : Matrix (Fin 5) (Fin 5) F} {v : Fin 5 → F}
    (h : ((A : Matrix (Fin 5) (Fin 5) F) * M * ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
      *ᵥ v = v) :
    M *ᵥ (((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *ᵥ v) =
      ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *ᵥ v := by
  have h1 := congrArg (fun u => ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *ᵥ u) h
  simp only [Matrix.mulVec_mulVec] at h1 ⊢
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h1

omit [Finite F] in
theorem fixT_of_conj_fixT {A : GL (Fin 5) F} {M : Matrix (Fin 5) (Fin 5) F} {v : Fin 5 → F}
    (h : ((A : Matrix (Fin 5) (Fin 5) F) * M *
      ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))ᵀ *ᵥ v = v) :
    Mᵀ *ᵥ ((A : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ v) = (A : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ v := by
  have h1 := congrArg (fun u => (A : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ u) h
  simp only [Matrix.mulVec_mulVec, Matrix.transpose_mul] at h1 ⊢
  have e : (A : Matrix (Fin 5) (Fin 5) F)ᵀ *
      ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul] at h1

omit [Finite F] in
theorem eq_zero_of_mulVecT_eq_zero (A : GL (Fin 5) F) {v : Fin 5 → F}
    (h : (A : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ v = 0) : v = 0 := by
  have h1 := congrArg (fun u => ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ u) h
  have e : ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ *
      (A : Matrix (Fin 5) (Fin 5) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
  rwa [e, Matrix.one_mulVec] at h1

theorem exists_conj_of_preserves (hF : Nat.card F = 2) {i : ℕ} (hi : i = 1 ∨ i = 4)
    (β : MulAut (SpecialLinearGroup (Fin 5) F))
    (hβ : ∀ g ∈ stabilizer (flagSpace 5 F i), β g ∈ stabilizer (flagSpace 5 F i)) :
    ∃ A ∈ stabilizer (flagSpace 5 F i), β = MulAut.conj A := by
  obtain ⟨A, σ, hform | hform⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (n := 5) (K := F) (by norm_num) β
  ·
    have hσ : ∀ g : SpecialLinearGroup (Fin 5) F,
        (β g : Matrix (Fin 5) (Fin 5) F) = (A : Matrix (Fin 5) (Fin 5) F) *
          (g : Matrix (Fin 5) (Fin 5) F) * ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
      intro g
      rw [hform g]
      congr 2
      ext a b
      simp [ringEquiv_apply_of_card_two hF]
    have hβA : β = MulAut.conj (toSL hF A) := by
      ext g : 1
      apply Subtype.ext
      rw [hσ g, MulAut.conj_apply]
      change _ = (A : Matrix (Fin 5) (Fin 5) F) * (g : Matrix (Fin 5) (Fin 5) F) *
        (((toSL hF A)⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
      rw [coe_toSL_inv]
    refine ⟨toSL hF A, ?_, hβA⟩
    rcases hi with rfl | rfl
    ·
      set w : Fin 5 → F := ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *ᵥ Pi.single 0 1
        with hw
      have hfix : ∀ g ∈ stabilizer (flagSpace 5 F 1),
          (g : Matrix (Fin 5) (Fin 5) F) *ᵥ w = w := fun g hg => by
        have h1 := mulVec_e0_of_mem hF (hβ g hg)
        rw [hσ g] at h1
        exact fix_of_conj_fix h1
      have hw0 : ∀ k : Fin 5, k ≠ 0 → w k = 0 := fun k hk => apply_eq_zero_of_fix_one hfix hk
      have hwne : w ≠ 0 := by
        intro h0
        have h1 : (A : Matrix (Fin 5) (Fin 5) F) *ᵥ w = Pi.single 0 1 := by
          rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        rw [h0, Matrix.mulVec_zero] at h1
        have := congrFun h1 0
        simp at this
      have hw00 : w 0 = 1 := by
        rcases eq_zero_or_eq_one_of_card_two hF (w 0) with h | h
        · exact absurd (funext fun k => by
            by_cases hk : k = 0
            · rw [hk, h]; rfl
            · exact hw0 k hk) hwne
        · exact h
      have hwe : w = Pi.single 0 1 := funext fun k => by
        by_cases hk : k = 0
        · subst hk; simp [hw00]
        · rw [hw0 k hk, Pi.single_eq_of_ne hk]
      have hAe : (A : Matrix (Fin 5) (Fin 5) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
        calc (A : Matrix (Fin 5) (Fin 5) F) *ᵥ Pi.single 0 1
            = (A : Matrix (Fin 5) (Fin 5) F) *ᵥ w := by rw [hwe]
          _ = Pi.single 0 1 := by
            rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      refine mem_stabilizer_flagSpace_of_entries fun k l hl hk => ?_
      have hl0 : l = 0 := Fin.ext (by omega)
      have hk0 : k ≠ 0 := fun h => by subst h; simp at hk
      subst hl0
      have := congrFun hAe k
      rw [Matrix.mulVec_single_one] at this
      change (A : Matrix (Fin 5) (Fin 5) F) k 0 = _ at this
      rw [coe_toSL, this, Pi.single_eq_of_ne hk0]
    ·
      set u : Fin 5 → F := (A : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ Pi.single 4 1 with hu
      have hfix : ∀ g ∈ stabilizer (flagSpace 5 F 4),
          (g : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ u = u := fun g hg => by
        have h1 := mulVecT_e4_of_mem hF (hβ g hg)
        rw [hσ g] at h1
        exact fixT_of_conj_fixT h1
      have hu4 : ∀ k : Fin 5, k ≠ 4 → u k = 0 := fun k hk => apply_eq_zero_of_fixT_four hfix hk
      have hune : u ≠ 0 := by
        intro h0
        have := eq_zero_of_mulVecT_eq_zero A (hu ▸ h0)
        have := congrFun this 4
        simp at this
      have hu44 : u 4 = 1 := by
        rcases eq_zero_or_eq_one_of_card_two hF (u 4) with h | h
        · exact absurd (funext fun k => by
            by_cases hk : k = 4
            · rw [hk, h]; rfl
            · exact hu4 k hk) hune
        · exact h
      have hue : u = Pi.single 4 1 := funext fun k => by
        by_cases hk : k = 4
        · subst hk; simp [hu44]
        · rw [hu4 k hk, Pi.single_eq_of_ne hk]
      refine mem_stabilizer_flagSpace_of_entries fun k l hl hk => ?_
      have hk4 : k = 4 := Fin.ext (by have := k.isLt; omega)
      have hl4 : l ≠ 4 := fun h => by subst h; simp at hl
      subst hk4
      have := congrFun hue l
      rw [hu, Matrix.mulVec_single_one] at this
      change (A : Matrix (Fin 5) (Fin 5) F) 4 l = _ at this
      rw [coe_toSL, this, Pi.single_eq_of_ne hl4]
  ·
    exfalso
    have hσ : ∀ g : SpecialLinearGroup (Fin 5) F,
        (β g : Matrix (Fin 5) (Fin 5) F) = (A : Matrix (Fin 5) (Fin 5) F) *
          ((g⁻¹ : SpecialLinearGroup (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ *
            ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
      intro g
      rw [hform g]
      congr 2
      ext a b
      simp [ringEquiv_apply_of_card_two hF]
    rcases hi with rfl | rfl
    · set w : Fin 5 → F := ((A⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *ᵥ Pi.single 0 1
        with hw
      have hfix : ∀ h ∈ stabilizer (flagSpace 5 F 1),
          (h : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ w = w := fun h hh => by
        have h1 := mulVec_e0_of_mem hF (hβ h⁻¹ (inv_mem hh))
        rw [hσ h⁻¹, inv_inv] at h1
        exact fix_of_conj_fix h1
      have h0 := eq_zero_of_fixT_one hfix
      have h1 : (A : Matrix (Fin 5) (Fin 5) F) *ᵥ w = Pi.single 0 1 := by
        rw [hw, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at h1
      have := congrFun h1 0
      simp at this
    · set u : Fin 5 → F := (A : Matrix (Fin 5) (Fin 5) F)ᵀ *ᵥ Pi.single 4 1 with hu
      have hfix : ∀ h ∈ stabilizer (flagSpace 5 F 4),
          (h : Matrix (Fin 5) (Fin 5) F) *ᵥ u = u := fun h hh => by
        have h1 := mulVecT_e4_of_mem hF (hβ h⁻¹ (inv_mem hh))
        rw [hσ h⁻¹, inv_inv] at h1
        have h2 := fixT_of_conj_fixT h1
        rwa [Matrix.transpose_transpose] at h2
      have h0 := eq_zero_of_fix_four hfix
      have := eq_zero_of_mulVecT_eq_zero A (hu ▸ h0)
      have := congrFun this 4
      simp at this

end CFSG.Quasithin.L139L42
