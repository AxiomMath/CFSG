module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.Quasithin.Background.G2SL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Vol2.Ch6SL2Fix

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

theorem isSimpleGroup_sl2_of_charTwo {E : Type} [Field E] [Finite E] [CharP E 2]
    (h4 : 4 ≤ Nat.card E) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) E) := by
  classical
  have hs := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := E) 2 le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    have hr1 : r = 1 := by
      have : (r - 1) * (r - 1) = 0 := by
        linear_combination hr - r * h2 + h2
      exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) E ≃* Matrix.SpecialLinearGroup (Fin 2) E :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

section Basis

variable {F : Type} [Field F]

@[expose] def basisMat (u₁ u₂ : Fin 2 → F) : Matrix (Fin 2) (Fin 2) F :=
  !![u₁ 0, u₂ 0; u₁ 1, u₂ 1]

theorem basisMat_mulVec (u₁ u₂ x : Fin 2 → F) :
    (basisMat u₁ u₂).mulVec x = x 0 • u₁ + x 1 • u₂ := by
  funext i
  fin_cases i <;> simp [basisMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem det_basisMat (u₁ u₂ : Fin 2 → F) : (basisMat u₁ u₂).det = det2 u₁ u₂ := by
  rw [basisMat, Matrix.det_fin_two_of, det2]
  ring

@[expose] noncomputable def slConj (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun B := ⟨P * (B : Matrix (Fin 2) (Fin 2) F) * P⁻¹, by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_inv_cancel₀ hP]⟩
  map_one' := by
    apply Subtype.ext
    change P * 1 * P⁻¹ = 1
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP)]
  map_mul' B B' := by
    apply Subtype.ext
    change P * ((B : Matrix (Fin 2) (Fin 2) F) * B') * P⁻¹ =
      (P * (B : Matrix (Fin 2) (Fin 2) F) * P⁻¹) * (P * (B' : Matrix (Fin 2) (Fin 2) F) * P⁻¹)
    have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]

theorem slConj_coe (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0)
    (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((slConj P hP B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      P * (B : Matrix (Fin 2) (Fin 2) F) * P⁻¹ := rfl

theorem slConj_injective (P : Matrix (Fin 2) (Fin 2) F) (hP : P.det ≠ 0) :
    Function.Injective (slConj P hP) := by
  intro B B' hBB'
  have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
    P⁻¹ * (X : Matrix (Fin 2) (Fin 2) F) * P) hBB'
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP)
  have key : ∀ X : Matrix (Fin 2) (Fin 2) F, P⁻¹ * (P * X * P⁻¹) * P = X := fun X =>
    calc P⁻¹ * (P * X * P⁻¹) * P = (P⁻¹ * P) * X * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
  simp only [slConj_coe] at h1
  rw [key, key] at h1
  exact Subtype.ext h1

end Basis

section Stab

variable {F : Type} [Field F]

abbrev stabFixField (σ : F ≃+* F) : Subfield F := (σ : F →+* F).eqLocusField (RingHom.id F)

theorem mem_stabFixField {σ : F ≃+* F} {x : F} : x ∈ stabFixField σ ↔ σ x = x := Iff.rfl

@[expose] def stabSub (g : (Fin 2 → F) ≃+ (Fin 2 → F)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {B | ∀ w, (B : Matrix (Fin 2) (Fin 2) F).mulVec (g w) =
    g ((B : Matrix (Fin 2) (Fin 2) F).mulVec w)}
  one_mem' := by
    intro w
    simp
  mul_mem' := by
    intro B B' hB hB' w
    simp only [Set.mem_ofPred_eq] at hB hB' ⊢
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB', hB, Matrix.mulVec_mulVec]
  inv_mem' := by
    intro B hB w
    simp only [Set.mem_ofPred_eq] at hB ⊢
    have hinj : Function.Injective (B : Matrix (Fin 2) (Fin 2) F).mulVec := fun x y hxy => by
      rw [← inv_mulVec_mulVec B x, hxy, inv_mulVec_mulVec]
    apply hinj
    rw [mulVec_inv_mulVec, hB, mulVec_inv_mulVec]

theorem mem_stabSub {g : (Fin 2 → F) ≃+ (Fin 2 → F)} {B : Matrix.SpecialLinearGroup (Fin 2) F} :
    B ∈ stabSub g ↔ ∀ w, (B : Matrix (Fin 2) (Fin 2) F).mulVec (g w) =
      g ((B : Matrix (Fin 2) (Fin 2) F).mulVec w) := Iff.rfl

variable {g : (Fin 2 → F) ≃+ (Fin 2 → F)} {σ : F ≃+* F} {u₁ u₂ : Fin 2 → F}

theorem semilinear_basis (hσ : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w)
    (hu₁ : g u₁ = u₁) (hu₂ : g u₂ = u₂) (a b : F) :
    g (a • u₁ + b • u₂) = σ a • u₁ + σ b • u₂ := by
  rw [map_add, hσ, hσ, hu₁, hu₂]

theorem semilinear_basisMat (hσ : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w)
    (hu₁ : g u₁ = u₁) (hu₂ : g u₂ = u₂) (x : Fin 2 → F) :
    g ((basisMat u₁ u₂).mulVec x) = (basisMat u₁ u₂).mulVec (fun i => σ (x i)) := by
  rw [basisMat_mulVec, basisMat_mulVec, semilinear_basis hσ hu₁ hu₂]

theorem mem_stabSub_of_basis (hσ : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w)
    (hu₁ : g u₁ = u₁) (hu₂ : g u₂ = u₂) (hdet : det2 u₁ u₂ ≠ 0)
    {B : Matrix.SpecialLinearGroup (Fin 2) F}
    (h1 : g ((B : Matrix (Fin 2) (Fin 2) F).mulVec u₁) = (B : Matrix (Fin 2) (Fin 2) F).mulVec u₁)
    (h2 : g ((B : Matrix (Fin 2) (Fin 2) F).mulVec u₂) = (B : Matrix (Fin 2) (Fin 2) F).mulVec u₂) :
    B ∈ stabSub g := by
  intro w
  rw [eq_add_of_det2_ne_zero hdet w, semilinear_basis hσ hu₁ hu₂]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [map_add, hσ, hσ, h1, h2]

theorem eq_one_of_basis (hdet : det2 u₁ u₂ ≠ 0) {B : Matrix.SpecialLinearGroup (Fin 2) F}
    (h1 : (B : Matrix (Fin 2) (Fin 2) F).mulVec u₁ = u₁)
    (h2 : (B : Matrix (Fin 2) (Fin 2) F).mulVec u₂ = u₂) : B = 1 := by
  apply Subtype.ext
  apply matrix_eq_of_mulVec_eq
  intro w
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, eq_add_of_det2_ne_zero hdet w]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [h1, h2]

@[expose] noncomputable def slFormHom (σ : F ≃+* F) (u₁ u₂ : Fin 2 → F) (hdet : det2 u₁ u₂ ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) (stabFixField σ) →* Matrix.SpecialLinearGroup (Fin 2) F :=
  (slConj (basisMat u₁ u₂) (by rw [det_basisMat]; exact hdet)).comp
    (Matrix.SpecialLinearGroup.map (stabFixField σ).subtype)

theorem slFormHom_injective (hdet : det2 u₁ u₂ ≠ 0) :
    Function.Injective (slFormHom σ u₁ u₂ hdet) := by
  have hP : (basisMat u₁ u₂).det ≠ 0 := by rw [det_basisMat]; exact hdet
  show Function.Injective ((slConj (basisMat u₁ u₂) hP).comp
    (Matrix.SpecialLinearGroup.map (stabFixField σ).subtype))
  refine (slConj_injective _ hP).comp ?_
  intro M M' hMM'
  apply Subtype.ext
  ext i j
  have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F =>
    (X : Matrix (Fin 2) (Fin 2) F) i j) hMM'
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact this

theorem slFormHom_mulVec (hdet : det2 u₁ u₂ ≠ 0)
    (M : Matrix.SpecialLinearGroup (Fin 2) (stabFixField σ)) (x : Fin 2 → F) :
    ((slFormHom σ u₁ u₂ hdet M : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec ((basisMat u₁ u₂).mulVec x) =
      (basisMat u₁ u₂).mulVec (((M : Matrix (Fin 2) (Fin 2) (stabFixField σ)).map
        (stabFixField σ).subtype).mulVec x) := by
  have hP : (basisMat u₁ u₂).det ≠ 0 := by rw [det_basisMat]; exact hdet
  have hPP : (basisMat u₁ u₂)⁻¹ * basisMat u₁ u₂ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP)
  change ((basisMat u₁ u₂) * ((M : Matrix (Fin 2) (Fin 2) (stabFixField σ)).map
    (stabFixField σ).subtype) * (basisMat u₁ u₂)⁻¹).mulVec ((basisMat u₁ u₂).mulVec x) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPP, Matrix.mul_one,
    ← Matrix.mulVec_mulVec]

theorem range_slFormHom (hσ : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w)
    (hu₁ : g u₁ = u₁) (hu₂ : g u₂ = u₂) (hdet : det2 u₁ u₂ ≠ 0) :
    (slFormHom σ u₁ u₂ hdet).range = stabSub g := by
  classical
  set P := basisMat u₁ u₂ with hPdef
  have hP : P.det ≠ 0 := by rw [hPdef, det_basisMat]; exact hdet
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP)
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP)
  have hPx : ∀ w : Fin 2 → F, P.mulVec (P⁻¹.mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec]
  have hPinj : ∀ x y : Fin 2 → F, P.mulVec x = P.mulVec y → x = y := fun x y hxy => by
    have := congrArg (P⁻¹.mulVec) hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  apply le_antisymm
  ·
    rintro _ ⟨M, rfl⟩
    rw [mem_stabSub]
    intro w
    obtain ⟨x, rfl⟩ : ∃ x, P.mulVec x = w := ⟨P⁻¹.mulVec w, hPx w⟩
    rw [semilinear_basisMat hσ hu₁ hu₂, slFormHom_mulVec, slFormHom_mulVec,
      semilinear_basisMat hσ hu₁ hu₂]
    congr 1
    funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
      Subfield.coe_subtype, map_add, map_mul]
    rw [(mem_stabFixField.mp (M i 0).2), (mem_stabFixField.mp (M i 1).2)]
  ·
    intro B hB
    set N := P⁻¹ * (B : Matrix (Fin 2) (Fin 2) F) * P with hN
    have hfix : ∀ i j, σ (N i j) = N i j := by
      intro i j
      set y := N.mulVec (Pi.single j 1) with hy
      have hy' : P.mulVec y = (B : Matrix (Fin 2) (Fin 2) F).mulVec (P.mulVec (Pi.single j 1)) := by
        rw [hy, hN, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP',
          Matrix.one_mul, ← Matrix.mulVec_mulVec]
      have hgfix : g (P.mulVec (Pi.single j 1)) = P.mulVec (Pi.single j 1) := by
        rw [semilinear_basisMat hσ hu₁ hu₂]
        congr 1
        funext k
        simp only [Pi.single_apply]
        split_ifs <;> simp
      have h1 : g (P.mulVec y) = P.mulVec y := by
        rw [hy', ← (mem_stabSub.mp hB), hgfix]
      rw [semilinear_basisMat hσ hu₁ hu₂] at h1
      have h2 := congrFun (hPinj _ _ h1) i
      have hyij : y i = N i j := by
        rw [hy, Matrix.mulVec_single_one]
        rfl
      rw [← hyij]
      exact h2
    let N₀ : Matrix (Fin 2) (Fin 2) (stabFixField σ) := fun i j => ⟨N i j, hfix i j⟩
    have hN₀ : N₀.map (stabFixField σ).subtype = N := by
      ext i j
      rfl
    have hdetN : N.det = 1 := by
      rw [hN, Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
        Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_mul_cancel₀ hP]
    have hdetN₀ : N₀.det = 1 := by
      apply Subtype.ext
      have := RingHom.map_det (stabFixField σ).subtype N₀
      rw [RingHom.mapMatrix_apply, hN₀, hdetN] at this
      rw [Subfield.coe_one]
      exact this
    refine ⟨⟨N₀, hdetN₀⟩, Subtype.ext ?_⟩
    change P * N₀.map (stabFixField σ).subtype * P⁻¹ = (B : Matrix (Fin 2) (Fin 2) F)
    rw [hN₀, hN]
    simp only [Matrix.mul_assoc]
    rw [hPP', Matrix.mul_one, ← Matrix.mul_assoc, hPP', Matrix.one_mul]

@[expose] noncomputable def stabSubEquiv (hσ : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w)
    (hu₁ : g u₁ = u₁) (hu₂ : g u₂ = u₂) (hdet : det2 u₁ u₂ ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) (stabFixField σ) ≃* ↥(stabSub g) :=
  (MonoidHom.ofInjective (slFormHom_injective hdet)).trans
    (MulEquiv.subgroupCongr (range_slFormHom hσ hu₁ hu₂ hdet))

theorem isSimpleGroup_stabSub [CharP F 2] (hσ : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w)
    (hu₁ : g u₁ = u₁) (hu₂ : g u₂ = u₂) (hdet : det2 u₁ u₂ ≠ 0) [Finite F]
    (h4 : 4 ≤ Nat.card (stabFixField σ)) : IsSimpleGroup ↥(stabSub g) := by
  have := isSimpleGroup_sl2_of_charTwo (E := stabFixField σ) h4
  exact (stabSubEquiv hσ hu₁ hu₂ hdet).symm.isSimpleGroup

theorem exists_mem_stabSub_order_three [CharP F 2]
    (hσ : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w)
    (hu₁ : g u₁ = u₁) (hu₂ : g u₂ = u₂) (hdet : det2 u₁ u₂ ≠ 0) :
    ∃ B ∈ stabSub g, B ≠ 1 ∧ B ^ 3 = 1 := by
  refine ⟨slFormHom σ u₁ u₂ hdet (SL2Model.c3 (stabFixField σ)), ?_, ?_, ?_⟩
  · rw [← range_slFormHom hσ hu₁ hu₂ hdet]
    exact ⟨_, rfl⟩
  · intro h1
    apply SL2Model.c3_ne_one (F := stabFixField σ)
    apply slFormHom_injective hdet
    rw [h1, map_one]
  · rw [← map_pow, SL2Model.c3_pow_three, map_one]

theorem stabSub_le_oTwoUpper [CharP F 2] [Finite F]
    (hσ : ∀ (c : F) (w : Fin 2 → F), g (c • w) = σ c • g w)
    (hu₁ : g u₁ = u₁) (hu₂ : g u₂ = u₂) (hdet : det2 u₁ u₂ ≠ 0)
    (h4 : 4 ≤ Nat.card (stabFixField σ)) : stabSub g ≤ oTwoUpper (stabSub g) := by
  have hs := isSimpleGroup_stabSub hσ hu₁ hu₂ hdet h4
  obtain ⟨B, hB, hB1, hB3⟩ := exists_mem_stabSub_order_three hσ hu₁ hu₂ hdet
  have hnorm : ((oTwoUpper (stabSub g)).subgroupOf (stabSub g)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)]
    exact le_normalizer_oTwoUpper _
  rcases hs.eq_bot_or_eq_top_of_normal ((oTwoUpper (stabSub g)).subgroupOf (stabSub g)) with
    h0 | h0
  · exfalso
    have hBo : Odd (orderOf B) := by
      have h3 : orderOf B ∣ 3 := orderOf_dvd_of_pow_eq_one hB3
      exact Odd.of_dvd_nat (by decide) h3
    have hmem : (⟨B, hB⟩ : ↥(stabSub g)) ∈ (oTwoUpper (stabSub g)).subgroupOf (stabSub g) :=
      Subgroup.mem_subgroupOf.mpr (mem_oTwoUpper_of_odd hB hBo)
    rw [h0, Subgroup.mem_bot] at hmem
    exact hB1 (congrArg Subtype.val hmem)
  · intro x hx
    have : (⟨x, hx⟩ : ↥(stabSub g)) ∈ (oTwoUpper (stabSub g)).subgroupOf (stabSub g) := by
      rw [h0]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end Stab

end CFSG.Quasithin.H13
