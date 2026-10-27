module

public import CFSG.Quasithin.Background.FLc3Tr
public import CFSG.Quasithin.Background.FLc3Cnt
public import CFSG.Quasithin.Background.FLc2Fix
public import CFSG.Quasithin.Background.FLcAutMat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def actDl {n : ℕ} (g : SLt n) (x : Multiplicative (Vt n)) : Multiplicative (Vt n) :=
  Multiplicative.ofAdd ((mat g⁻¹)ᵀ *ᵥ Multiplicative.toAdd x)

theorem toAdd_actDl {n : ℕ} (g : SLt n) (x : Multiplicative (Vt n)) :
    Multiplicative.toAdd (actDl g x) = (mat g⁻¹)ᵀ *ᵥ Multiplicative.toAdd x := rfl

theorem actDl_hom {n : ℕ} (g : SLt n) (a b : Multiplicative (Vt n)) :
    actDl g (a * b) = actDl g a * actDl g b := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_actDl, toAdd_mul, Matrix.mulVec_add]

theorem actDl_one {n : ℕ} (a : Multiplicative (Vt n)) : actDl 1 a = a := by
  apply Multiplicative.toAdd.injective
  simp [toAdd_actDl]

theorem actDl_mul {n : ℕ} (g h : SLt n) (a : Multiplicative (Vt n)) :
    actDl (g * h) a = actDl g (actDl h a) := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_actDl, Matrix.mulVec_mulVec]
  congr 1
  rw [_root_.mul_inv_rev, mat_mul, Matrix.transpose_mul]

theorem vmodelDual {V : Type} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H}
    (h : (FFModel.dualNat (StatedSL n (ZMod 2))).RealizesVia H U Z π)
    (hZ : ∀ g ∈ H, ∀ z ∈ Z, g z = z) :
    Nonempty (VModel n (rhoOf π) U Z (Multiplicative (Vt n)) actDl) := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, -⟩ := vmodel_of_realizes (dualNatAct (StatedSL n (ZMod 2))) h
  let σ := specialLinearGroupEquivStatedSL n (ZMod 2)
  refine ⟨?_⟩
  refine
    { β := β
      surj := hβs
      inv := fun g u hu => hUinv _ u hu
      ker := fun u hu => (hβk u).1 hu
      equiv := fun g u hu => ?_
      Zfix := fun g z hz => hZ _ (rhoOf_mem π g) z hz
      act_hom := actDl_hom
      act_one := actDl_one
      act_mul := actDl_mul }
  have h1 := hβe (σ g) u hu
  refine h1.trans ?_
  apply Multiplicative.toAdd.injective
  show _ = (mat g⁻¹)ᵀ *ᵥ _
  simp only [dualNatAct, toAdd_ofAdd]
  have hinv : (((σ g)⁻¹ : ↥(StatedSL n (ZMod 2))) : GL (Fin n) (ZMod 2)) =
      (σ g⁻¹ : GL (Fin n) (ZMod 2)) := by rw [map_inv]
  rw [hinv, specialLinearGroupEquivStatedSL_coe]

theorem dual_fixed_iff_SL {n : ℕ} (g : SLt n) (w : Fin n → ZMod 2) :
    (mat g⁻¹)ᵀ *ᵥ w = w ↔ (mat g)ᵀ *ᵥ w = w := by
  constructor
  · intro h
    have h2 := congrArg ((mat g)ᵀ).mulVec h
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← mat_mul, inv_mul_cancel, mat_one,
      Matrix.transpose_one, Matrix.one_mulVec] at h2
    exact h2.symm
  · intro h
    have h2 := congrArg ((mat g⁻¹)ᵀ).mulVec h
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← mat_mul, mul_inv_cancel, mat_one,
      Matrix.transpose_one, Matrix.one_mulVec] at h2
    exact h2.symm

theorem card_fix_actM {n : ℕ} (A : Subgroup (SLt n)) :
    Nat.card {x : Multiplicative (Vt n) | ∀ g ∈ A, actM g x = x} =
      Nat.card {v : Vt n | ∀ y ∈ A, mat y *ᵥ v = v} := by
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun x => ?_)
  constructor
  · intro h y hy
    have := congrArg Multiplicative.toAdd (h y hy)
    rwa [toAdd_actM] at this
  · intro h y hy
    apply Multiplicative.toAdd.injective
    rw [toAdd_actM]
    exact h y hy

theorem card_fix_actDl {m : ℕ} (A : Subgroup (SLt (m + 2))) :
    Nat.card {x : Multiplicative (Vt (m + 2)) | ∀ g ∈ A, actDl g x = x} =
      Nat.card (FFC.fixDual (A.map (slEquivGLt (m + 2)).toMonoidHom)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun x => ?_)
  have e : ∀ y : SLt (m + 2), (((slEquivGLt (m + 2) y : GL (Fin (m + 2)) (ZMod 2)) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2))) = mat y := fun y => rfl
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    have := congrArg Multiplicative.toAdd (h y hy)
    rw [toAdd_actDl] at this
    show ((((slEquivGLt (m + 2) y : GL (Fin (m + 2)) (ZMod 2)) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)))ᵀ).mulVec (Multiplicative.toAdd x) = _
    rw [e]
    exact (dual_fixed_iff_SL y _).1 this
  · intro h y hy
    apply Multiplicative.toAdd.injective
    rw [toAdd_actDl]
    have h2 := h _ ⟨y, hy, rfl⟩
    have h3 : ((((slEquivGLt (m + 2) y : GL (Fin (m + 2)) (ZMod 2)) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)))ᵀ).mulVec (Multiplicative.toAdd x) =
        Multiplicative.toAdd x := h2
    rw [e] at h3
    exact (dual_fixed_iff_SL y _).2 h3

theorem card_fin_fun_two (d : ℕ) : Nat.card (Fin d → ZMod 2) = 2 ^ d := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

noncomputable def coordEquiv4 : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) ≃ (Fin 6 → ZMod 2) :=
  Multiplicative.toAdd.trans (Equiv.ofBijective _ (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)))

noncomputable def coordEquiv5 : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) ≃ (Fin 10 → ZMod 2) :=
  Multiplicative.toAdd.trans (Equiv.ofBijective _ (JonesParshall.wedgeCoord_bijective (K := ZMod 2)))

theorem card_X_ext4 : Nat.card (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) = 2 ^ 6 :=
  (Nat.card_congr coordEquiv4).trans (card_fin_fun_two 6)

theorem card_X_ext5 : Nat.card (Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2))) = 2 ^ 10 :=
  (Nat.card_congr coordEquiv5).trans (card_fin_fun_two 10)

theorem card_fix_actW4 (A : Subgroup (SLt 4)) :
    Nat.card {x : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) | ∀ g ∈ A, actW g x = x} =
      Nat.card {v : Fin 6 → ZMod 2 | ∀ y ∈ A, B5FinWedge.wedgeMat4 (mat y) *ᵥ v = v} := by
  refine Nat.card_congr (Equiv.subtypeEquiv coordEquiv4 fun x => ?_)
  have hc : ∀ g x, coordEquiv4 (actW g x) = B5FinWedge.wedgeMat4 (mat g) *ᵥ coordEquiv4 x :=
    fun g x => coord4_actW g x
  constructor
  · intro h y hy
    rw [← hc, h y hy]
  · intro h y hy
    apply coordEquiv4.injective
    rw [hc]
    exact h y hy

theorem card_fix_actW5 (A : Subgroup (SLt 5)) :
    Nat.card {x : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) | ∀ g ∈ A, actW g x = x} =
      Nat.card {v : Fin 10 → ZMod 2 | ∀ y ∈ A, JonesParshall.wedgeMat (mat y) *ᵥ v = v} := by
  refine Nat.card_congr (Equiv.subtypeEquiv coordEquiv5 fun x => ?_)
  have hc : ∀ g x, coordEquiv5 (actW g x) = JonesParshall.wedgeMat (mat g) *ᵥ coordEquiv5 x :=
    fun g x => coord5_actW g x
  constructor
  · intro h y hy
    rw [← hc, h y hy]
  · intro h y hy
    apply coordEquiv5.injective
    rw [hc]
    exact h y hy

theorem arith_one {a w c N v : ℕ} (hv : 0 < v) (h1 : N * c ≤ v * w) (h2 : a * w < N) :
    a * c < v := by
  have h3 : N * (a * c) < N * v := by
    calc N * (a * c) = a * (N * c) := by ring
      _ ≤ a * (v * w) := Nat.mul_le_mul_left a h1
      _ = v * (a * w) := by ring
      _ < v * N := Nat.mul_lt_mul_of_pos_left h2 hv
      _ = N * v := by ring
  exact Nat.lt_of_mul_lt_mul_left h3

theorem arith_two {a w₁ w₂ c N v : ℕ} (hv : 0 < v) (h1 : N * N * c ≤ v * (w₁ * w₂))
    (h2 : a * w₁ * w₂ < N * N) : a * c < v := by
  have h3 : (N * N) * (a * c) < (N * N) * v := by
    calc (N * N) * (a * c) = a * (N * N * c) := by ring
      _ ≤ a * (v * (w₁ * w₂)) := Nat.mul_le_mul_left a h1
      _ = v * (a * w₁ * w₂) := by ring
      _ < v * (N * N) := Nat.mul_lt_mul_of_pos_left h2 hv
      _ = (N * N) * v := by ring
  exact Nat.lt_of_mul_lt_mul_left h3

theorem arith_sq {a w c N v : ℕ} (ha : 2 ≤ a) (hw : 0 < w) (hv : 0 < v)
    (h1 : N * N * c ≤ v * (w * w)) (h2 : a * w ≤ N) : a * c < v := by
  have h3 : (a * w) * (a * w) ≤ N * N := Nat.mul_le_mul h2 h2
  have h4 : a * a * c * (w * w) ≤ v * (w * w) := by
    calc a * a * c * (w * w) = ((a * w) * (a * w)) * c := by ring
      _ ≤ (N * N) * c := Nat.mul_le_mul_right c h3
      _ ≤ v * (w * w) := h1
  have h5 : a * a * c ≤ v := Nat.le_of_mul_le_mul_right h4 (Nat.mul_pos hw hw)
  have h6 : 2 * (a * c) ≤ a * a * c := by nlinarith [Nat.zero_le (a * c)]
  omega

variable {V : Type} [CommGroup V] [Finite V]

theorem not_ff_nat2 {n : ℕ} (hn : 3 ≤ n) {ρ : SLt n →* MulAut V} (hρ : Function.Injective ρ)
    {I₀ I₁ : Subgroup V} (hdisj : I₀ ⊓ I₁ = ⊥)
    (D₀ : VModel n ρ I₀ ⊥ (Multiplicative (Vt n)) (fun g a => actM g a))
    (D₁ : VModel n ρ I₁ ⊥ (Multiplicative (Vt n)) (fun g a => actM g a))
    (A : Subgroup (SLt n)) (hU : A ≤ Ut n)
    (hR : ∀ y ∈ A, ∀ i j : Fin n, i < j → (∀ d ∈ ({1} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) →
      mat y i j = 0)
    (hA : A ≠ ⊥) :
    Nat.card (A.map ρ) * Nat.card (fixV (A.map ρ)) < Nat.card V := by
  have hT := card_fix_transfer₂ D₀ D₁ hdisj A
  have hL := card_mul_fixN_le (by omega : 1 ≤ n) A hU hR
  have hw : Nat.card {x : Multiplicative (Vt n) | ∀ g ∈ A, (fun (g : SLt n) (a : Multiplicative (Vt n)) =>
      actM g a) g x = x} = Nat.card {v : Vt n | ∀ y ∈ A, mat y *ᵥ v = v} := card_fix_actM A
  rw [hw, card_multiplicative_Vt] at hT
  have hcardA : Nat.card (A.map ρ) = Nat.card A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A ρ hρ).toEquiv.symm
  have h2 : 2 ≤ Nat.card A := by
    have := (Subgroup.one_lt_card_iff_ne_bot A).2 hA
    omega
  have hwpos : 0 < Nat.card {v : Vt n | ∀ y ∈ A, mat y *ᵥ v = v} :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, fun y _ => by simp⟩⟩, inferInstance⟩
  rw [hcardA]
  exact arith_sq h2 hwpos Nat.card_pos hT hL

theorem not_ff_ext4 {ρ : SLt 4 →* MulAut V} (hρ : Function.Injective ρ) {U' Z' : Subgroup V}
    (D : VModel 4 ρ U' Z' (Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) actW)
    (A : Subgroup (SLt 4)) (hU : A ≤ Ut 4)
    (hR : ∀ y ∈ A, ∀ i j : Fin 4, i < j → (∀ d ∈ ({2} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) →
      mat y i j = 0)
    (hA : A ≠ ⊥) :
    Nat.card (A.map ρ) * Nat.card (fixV (A.map ρ)) < Nat.card V := by
  have hT := card_fix_transfer D A
  have hL := card_mul_fixW4_lt A hU hR hA
  rw [card_X_ext4] at hT
  have hcardA : Nat.card (A.map ρ) = Nat.card A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A ρ hρ).toEquiv.symm
  rw [hcardA]
  rw [card_fix_actW4] at hT
  exact arith_one Nat.card_pos hT hL

theorem not_ff_ext5 {ρ : SLt 5 →* MulAut V} (hρ : Function.Injective ρ) {U' Z' : Subgroup V}
    (D : VModel 5 ρ U' Z' (Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2))) actW)
    (A : Subgroup (SLt 5)) (hU : A ≤ Ut 5)
    (hR : ∀ y ∈ A, ∀ i j : Fin 5, i < j → (∀ d ∈ ({2} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) →
      mat y i j = 0)
    (hA : A ≠ ⊥) :
    Nat.card (A.map ρ) * Nat.card (fixV (A.map ρ)) < Nat.card V := by
  have hT := card_fix_transfer D A
  have hL := card_mul_fixW5_lt A hU hR hA
  rw [card_X_ext5] at hT
  have hcardA : Nat.card (A.map ρ) = Nat.card A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A ρ hρ).toEquiv.symm
  rw [hcardA]
  rw [card_fix_actW5] at hT
  exact arith_one Nat.card_pos hT hL

theorem mem_Rgrp_of_entries {m : ℕ} (y : SLt (m + 2)) (hU : y ∈ Ut (m + 2))
    (hR : ∀ i j : Fin (m + 2), i < j → (∀ d ∈ ({1, m + 1} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) →
      mat y i j = 0) : slEquivGLt (m + 2) y ∈ FFC.Rgrp m := by
  have e : ((slEquivGLt (m + 2) y : GL (Fin (m + 2)) (ZMod 2)) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) (ZMod 2)) = mat y := rfl
  rw [FFC.mem_Rgrp, FFC.mem_Pgrp_iff, e]
  refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_⟩
  · by_cases hi : i = 0
    · subst hi
      simpa using hU.2 0
    · simpa [hi] using hU.1 i 0 (Fin.pos_iff_ne_zero.2 hi)
  · by_cases hj : j = Fin.last (m + 1)
    · subst hj
      simpa using hU.2 _
    · simpa [hj] using hU.1 _ j (lt_of_le_of_ne (Fin.le_last j) hj)
  · ext i j
    have hm : FFC.midBlock (slEquivGLt (m + 2) y) i j = mat y (FFC.midIdx i) (FFC.midIdx j) := rfl
    rw [hm]
    rcases lt_trichotomy i j with hij | hij | hij
    · have hlt : FFC.midIdx i < FFC.midIdx j := by
        simp only [FFC.midIdx, Fin.succ_lt_succ_iff, Fin.castSucc_lt_castSucc_iff]
        exact hij
      rw [hR _ _ hlt, Matrix.one_apply_ne hij.ne]
      intro d hd hid
      have hi1 : ((FFC.midIdx i : Fin (m + 2)) : ℕ) = (i : ℕ) + 1 := by simp [FFC.midIdx]
      have hj1 : ((FFC.midIdx j : Fin (m + 2)) : ℕ) = (j : ℕ) + 1 := by simp [FFC.midIdx]
      rcases hd with rfl | hd
      · omega
      · rw [Set.mem_singleton_iff] at hd
        subst hd
        rw [hj1]
        have := j.2
        omega
    · subst hij
      rw [Matrix.one_apply_eq]
      exact hU.2 _
    · have hlt : FFC.midIdx j < FFC.midIdx i := by
        simp only [FFC.midIdx, Fin.succ_lt_succ_iff, Fin.castSucc_lt_castSucc_iff]
        exact hij
      rw [Matrix.one_apply_ne hij.ne']
      exact hU.1 _ _ hlt

theorem not_ff_sum {m : ℕ} {ρ : SLt (m + 2) →* MulAut V} (hρ : Function.Injective ρ)
    {U₁ U₂ : Subgroup V} (hdisj : U₁ ⊓ U₂ = ⊥)
    (D₁ : VModel (m + 2) ρ U₁ ⊥ (Multiplicative (Vt (m + 2))) (fun g a => actM g a))
    (D₂ : VModel (m + 2) ρ U₂ ⊥ (Multiplicative (Vt (m + 2))) actDl)
    (A : Subgroup (SLt (m + 2))) (hU : A ≤ Ut (m + 2))
    (hR : ∀ y ∈ A, ∀ i j : Fin (m + 2), i < j →
      (∀ d ∈ ({1, m + 1} : Set ℕ), (i : ℕ) < d → (j : ℕ) < d) → mat y i j = 0)
    (hA : A ≠ ⊥) :
    Nat.card (A.map ρ) * Nat.card (fixV (A.map ρ)) < Nat.card V := by
  have hT := card_fix_transfer₂ D₁ D₂ hdisj A
  set A' : Subgroup (GL (Fin (m + 2)) (ZMod 2)) := A.map (slEquivGLt (m + 2)).toMonoidHom with hA'
  have hA'R : A' ≤ FFC.Rgrp m := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_Rgrp_of_entries y (hU hy) (hR y hy)
  have hcardA' : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A (slEquivGLt (m + 2)).toMonoidHom
      (slEquivGLt (m + 2)).injective).toEquiv.symm
  have hA'ne : A' ≠ ⊥ := by
    intro h
    apply hA
    rw [← Subgroup.card_eq_one, ← hcardA', h, Subgroup.card_bot]
  have hoff := FFC.model_offender hA'R hA'ne
  have hw1 : Nat.card {x : Multiplicative (Vt (m + 2)) | ∀ g ∈ A, (fun (g : SLt (m + 2))
      (a : Multiplicative (Vt (m + 2))) => actM g a) g x = x} = Nat.card (FFC.fixNat A') := by
    rw [show Nat.card {x : Multiplicative (Vt (m + 2)) | ∀ g ∈ A, (fun (g : SLt (m + 2))
      (a : Multiplicative (Vt (m + 2))) => actM g a) g x = x} =
        Nat.card {v : Vt (m + 2) | ∀ y ∈ A, mat y *ᵥ v = v} from card_fix_actM A]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun v => ?_)
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      exact h y hy
    · intro h y hy
      exact h _ ⟨y, hy, rfl⟩
  rw [hw1, card_fix_actDl A, card_multiplicative_Vt] at hT
  rw [hcardA'] at hoff
  have hcardA : Nat.card (A.map ρ) = Nat.card A :=
    Nat.card_congr (Subgroup.equivMapOfInjective A ρ hρ).toEquiv.symm
  rw [hcardA]
  exact arith_two Nat.card_pos hT hoff

end CFSG.Quasithin.FLc
