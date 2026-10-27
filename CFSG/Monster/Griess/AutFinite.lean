module

public import CFSG.Monster.Griess.ProductInvariance
public import CFSG.Monster.Griess.AxisSpectrum
public import CFSG.Monster.IsolatedAxesBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix Module

@[expose] def AutO : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) where
  carrier := {g | IsAlgAut g ∧ ∀ u v, bform (g u) (g v) = bform u v}
  mul_mem' {f g} hf hg := ⟨hf.1.mul hg.1, fun u v => by
    change bform (f (g u)) (f (g v)) = bform u v
    rw [hf.2, hg.2]⟩
  one_mem' := ⟨isAlgAut_one, fun _ _ => rfl⟩
  inv_mem' {f} hf := ⟨hf.1.inv, fun u v => by
    change bform (f.symm u) (f.symm v) = bform u v
    rw [← hf.2, f.apply_symm_apply, f.apply_symm_apply]⟩

theorem mem_AutO {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ AutO ↔ (∀ u v, g (gmul u v) = gmul (g u) (g v)) ∧ ∀ u v, bform (g u) (g v) = bform u v :=
  Iff.rfl

theorem tauB_mem_AutO : tauB ∈ AutO := ⟨isAlgAut_tauB, bform_tauB⟩

theorem bform_basisB_right (v : SpaceB) (k : BIdx) :
    bform v (basisB k) = basisB.repr v k * gramDiag k := by
  classical
  conv_lhs => rw [← basisB.sum_repr v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, bform_basisB,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem bform_self_eq_sum (v : SpaceB) :
    bform v v = ∑ k, gramDiag k * basisB.repr v k ^ 2 := by
  calc bform v v = bform v (∑ k, basisB.repr v k • basisB k) := by rw [basisB.sum_repr]
    _ = ∑ k, basisB.repr v k * bform v (basisB k) := by simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ k, gramDiag k * basisB.repr v k ^ 2 :=
        Finset.sum_congr rfl fun k _ => by rw [bform_basisB_right]; ring

theorem gramDiag_pos (k : BIdx) : 0 < gramDiag k := by
  rcases gramDiag_mem k with h | h <;> rw [h] <;> norm_num

abbrev ShortQ : Type := {r : Q // IsShortCoord (coordOf r)}

instance : Finite ShortQ := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [natCard_Q]; positivity)
  infer_instance

theorem ratVec_vPlus (i j : Fin 24) :
    ratVec (vPlus i j) = (4 : ℚ) • Pi.single i 1 + (4 : ℚ) • Pi.single j 1 := by
  funext k
  simp only [ratVec, vPlus, eℤ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> norm_num

theorem ratVec_vMinus (i j : Fin 24) :
    ratVec (vMinus i j) = (4 : ℚ) • Pi.single i 1 - (4 : ℚ) • Pi.single j 1 := by
  funext k
  simp only [ratVec, vMinus, eℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> norm_num

theorem vecMulVec_single_single (i j : Fin 24) :
    vecMulVec (Pi.single i (1 : ℚ)) (Pi.single j 1) = Matrix.single i j 1 := by
  ext k l
  simp only [vecMulVec_apply, Pi.single_apply, Matrix.single_apply]
  rcases eq_or_ne k i with rfl | hk
  · rcases eq_or_ne l j with rfl | hl
    · simp
    · simp [hl, Ne.symm hl]
  · simp [hk, Ne.symm hk]

theorem projMat_vPlus_sub_vMinus (i j : Fin 24) :
    projMat (vPlus i j) - projMat (vMinus i j) = Matrix.single i j 1 + Matrix.single j i 1 := by
  rw [projMat, projMat, ratVec_vPlus, ratVec_vMinus]
  simp only [add_vecMulVec, vecMulVec_add, sub_vecMulVec, vecMulVec_sub, smul_vecMulVec,
    vecMulVec_smul, vecMulVec_single_single]
  module

theorem projMat_vPlus_add_vMinus (i j : Fin 24) :
    projMat (vPlus i j) + projMat (vMinus i j) = Matrix.single i i 1 + Matrix.single j j 1 := by
  rw [projMat, projMat, ratVec_vPlus, ratVec_vMinus]
  simp only [add_vecMulVec, vecMulVec_add, sub_vecMulVec, vecMulVec_sub, smul_vecMulVec,
    vecMulVec_smul, vecMulVec_single_single]
  module

theorem isShortCoord_rMinus {i j : Fin 24} (hij : i < j) : IsShortCoord (coordOf (rMinus i j)) :=
  ⟨vMinus i j, vMinus_mem hij, (phi0_coordOf_rMinus hij).symm⟩

theorem isShortCoord_rPlus {i j : Fin 24} (hij : i < j) : IsShortCoord (coordOf (rPlus i j)) :=
  ⟨vPlus i j, vPlus_mem hij, (phi0_coordOf_rPlus hij).symm⟩

theorem coe_axisE_rMinus {i j : Fin 24} (hij : i < j) :
    (axisE (rMinus i j) : Matrix (Fin 24) (Fin 24) ℚ) = projMat (vMinus i j) :=
  axisE_eq_projMat (isShortCoord_rMinus hij) (vMinus_mem hij) (phi0_coordOf_rMinus hij).symm

theorem coe_axisE_rPlus {i j : Fin 24} (hij : i < j) :
    (axisE (rPlus i j) : Matrix (Fin 24) (Fin 24) ℚ) = projMat (vPlus i j) :=
  axisE_eq_projMat (isShortCoord_rPlus hij) (vPlus_mem hij) (phi0_coordOf_rPlus hij).symm

@[expose] noncomputable def axisSpan : Submodule ℚ SpaceB :=
  Submodule.span ℚ (⋃ r : ShortQ, MulAction.orbit AutO (axis r.1))

theorem axis_mem_axisSpan {r : Q} (hr : IsShortCoord (coordOf r)) : axis r ∈ axisSpan :=
  Submodule.subset_span (Set.mem_iUnion.2 ⟨⟨r, hr⟩, MulAction.mem_orbit_self _⟩)

theorem map_mem_axisSpan {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) {x : SpaceB}
    (hx : x ∈ axisSpan) : g x ∈ axisSpan := by
  refine Submodule.span_induction (p := fun x _ => g x ∈ axisSpan) ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨r, hy⟩ := Set.mem_iUnion.1 hy
    obtain ⟨h, rfl⟩ := hy
    refine Submodule.subset_span (Set.mem_iUnion.2 ⟨r, ⟨⟨g, hg⟩ * h, ?_⟩⟩)
    change (g * (h : SpaceB ≃ₗ[ℚ] SpaceB)) (axis r.1) = g ((h : SpaceB ≃ₗ[ℚ] SpaceB) (axis r.1))
    rfl
  · rw [map_zero]
    exact axisSpan.zero_mem
  · intro x y _ _ hx hy
    rw [map_add]
    exact axisSpan.add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact axisSpan.smul_mem c hx

theorem Xlift_mem_axisSpan {r : Q} (hr : IsShortCoord (coordOf r)) :
    ((0 : symMat), Xlift r, (0 : SpaceW)) ∈ axisSpan := by
  have e : (4 : ℚ)⁻¹ • (axis (zQ * r) - axis r) = ((0 : symMat), Xlift r, (0 : SpaceW)) := by
    rw [axis_zQ_mul hr, axis]
    module
  rw [← e]
  exact axisSpan.smul_mem _
    (axisSpan.sub_mem (axis_mem_axisSpan (isShortCoord_zQ_mul hr)) (axis_mem_axisSpan hr))

theorem axisE_mem_axisSpan {r : Q} (hr : IsShortCoord (coordOf r)) :
    (axisE r, (0 : SpaceX), (0 : SpaceW)) ∈ axisSpan := by
  have e : (4 : ℚ)⁻¹ • (axis r + axis (zQ * r)) = (axisE r, (0 : SpaceX), (0 : SpaceW)) := by
    rw [axis_zQ_mul hr, axis]
    module
  rw [← e]
  exact axisSpan.smul_mem _
    (axisSpan.add_mem (axis_mem_axisSpan hr) (axis_mem_axisSpan (isShortCoord_zQ_mul hr)))

theorem basisA_offDiag_mem_axisSpan {i j : Fin 24} (hij : i < j) :
    (basisA s(i, j), (0 : SpaceX), (0 : SpaceW)) ∈ axisSpan := by
  have e : basisA s(i, j) = axisE (rPlus i j) - axisE (rMinus i j) := by
    apply Subtype.ext
    rw [coe_basisA, ite_eq_right hij.ne, Submodule.coe_sub, coe_axisE_rPlus hij,
      coe_axisE_rMinus hij, projMat_vPlus_sub_vMinus]
  have e' : (basisA s(i, j), (0 : SpaceX), (0 : SpaceW)) =
      (axisE (rPlus i j), (0 : SpaceX), (0 : SpaceW)) -
        (axisE (rMinus i j), (0 : SpaceX), (0 : SpaceW)) := by
    rw [e, Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]
  rw [e']
  exact axisSpan.sub_mem (axisE_mem_axisSpan (isShortCoord_rPlus hij))
    (axisE_mem_axisSpan (isShortCoord_rMinus hij))

theorem exists_diagPair_mem_axisSpan {i j : Fin 24} (hij : i ≠ j) :
    ∃ A : symMat, (A, (0 : SpaceX), (0 : SpaceW)) ∈ axisSpan ∧
      (A : Matrix (Fin 24) (Fin 24) ℚ) = Matrix.single i i 1 + Matrix.single j j 1 := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨axisE (rPlus i j) + axisE (rMinus i j), ?_, ?_⟩
    · have e : (axisE (rPlus i j) + axisE (rMinus i j), (0 : SpaceX), (0 : SpaceW)) =
          (axisE (rPlus i j), (0 : SpaceX), (0 : SpaceW)) +
            (axisE (rMinus i j), (0 : SpaceX), (0 : SpaceW)) := by
        rw [Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]
      rw [e]
      exact axisSpan.add_mem (axisE_mem_axisSpan (isShortCoord_rPlus h))
        (axisE_mem_axisSpan (isShortCoord_rMinus h))
    · rw [Submodule.coe_add, coe_axisE_rPlus h, coe_axisE_rMinus h, projMat_vPlus_add_vMinus]
  · refine ⟨axisE (rPlus j i) + axisE (rMinus j i), ?_, ?_⟩
    · have e : (axisE (rPlus j i) + axisE (rMinus j i), (0 : SpaceX), (0 : SpaceW)) =
          (axisE (rPlus j i), (0 : SpaceX), (0 : SpaceW)) +
            (axisE (rMinus j i), (0 : SpaceX), (0 : SpaceW)) := by
        rw [Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]
      rw [e]
      exact axisSpan.add_mem (axisE_mem_axisSpan (isShortCoord_rPlus h))
        (axisE_mem_axisSpan (isShortCoord_rMinus h))
    · rw [Submodule.coe_add, coe_axisE_rPlus h, coe_axisE_rMinus h,
        projMat_vPlus_add_vMinus, add_comm]

theorem basisA_diag_mem_axisSpan (i : Fin 24) :
    (basisA s(i, i), (0 : SpaceX), (0 : SpaceW)) ∈ axisSpan := by
  have hne : i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by revert i; decide
  obtain ⟨A₁, h₁, e₁⟩ := exists_diagPair_mem_axisSpan hne.1
  obtain ⟨A₂, h₂, e₂⟩ := exists_diagPair_mem_axisSpan hne.2.1
  obtain ⟨A₃, h₃, e₃⟩ := exists_diagPair_mem_axisSpan hne.2.2
  have e : basisA s(i, i) = (2 : ℚ)⁻¹ • (A₁ + A₂ - A₃) := by
    apply Subtype.ext
    rw [coe_basisA, ite_eq_left rfl, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_add,
      e₁, e₂, e₃]
    module
  have e' : (basisA s(i, i), (0 : SpaceX), (0 : SpaceW)) =
      (2 : ℚ)⁻¹ • ((A₁, (0 : SpaceX), (0 : SpaceW)) + (A₂, (0 : SpaceX), (0 : SpaceW)) -
        (A₃, (0 : SpaceX), (0 : SpaceW))) := by
    rw [e, Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk_sub_mk, Prod.smul_mk,
      Prod.smul_mk, add_zero, add_zero, sub_zero, sub_zero, smul_zero, smul_zero]
  rw [e']
  exact axisSpan.smul_mem _ (axisSpan.sub_mem (axisSpan.add_mem h₁ h₂) h₃)

theorem basisA_mem_axisSpan (z : PairIdx) :
    (basisA z, (0 : SpaceX), (0 : SpaceW)) ∈ axisSpan := by
  induction z using Sym2.ind with
  | _ i j =>
    rcases lt_trichotomy i j with h | rfl | h
    · exact basisA_offDiag_mem_axisSpan h
    · exact basisA_diag_mem_axisSpan i
    · rw [Sym2.eq_swap]
      exact basisA_offDiag_mem_axisSpan h

theorem tbasis_odd_mem_axisSpan (c : C₀) (i : Fin 24) (k : Fin 3) :
    tbasis (.inr (.inr (.inl (c, i, k)))) ∈ axisSpan := by
  have h0 : tbasis (.inr (.inr (.inl (c, i, 0)))) ∈ axisSpan := by
    rw [tbasis_odd_zero]
    exact Xlift_mem_axisSpan (isShortCoord_labelElt (.inr (.inr (.inl (c, i)))))
  have h1 : tbasis (.inr (.inr (.inl (c, i, 1)))) ∈ axisSpan := by
    have := tauB_odd c i 0
    rw [show (0 : Fin 3) + 1 = 1 from rfl] at this
    rw [← this]
    exact map_mem_axisSpan tauB_mem_AutO h0
  have h2 : tbasis (.inr (.inr (.inl (c, i, 2)))) ∈ axisSpan := by
    have := tauB_odd c i 1
    rw [show (1 : Fin 3) + 1 = 2 from rfl] at this
    rw [← this]
    exact map_mem_axisSpan tauB_mem_AutO h1
  have hk : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hk k with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem tensor_mem_axisSpan (η : ZMod 2) (c : C₀) (i : Fin 24) :
    ((0 : symMat), (0 : SpaceX), tensor (Spin.E η c) (Pi.single i 1)) ∈ axisSpan := by
  have hη : ∀ η : ZMod 2, η = 0 ∨ η = 1 := by decide
  rcases hη η with rfl | rfl
  · have e : sgn (P ((c : C) : Fin 24 → ZMod 2)) • tbasis (.inr (.inr (.inl (c, i, 2)))) =
        ((0 : symMat), (0 : SpaceX), tensor (Spin.E 0 c) (Pi.single i 1)) := by
      rw [tbasis_odd_two, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero, smul_smul, sgn_sq,
        one_smul]
    rw [← e]
    exact axisSpan.smul_mem _ (tbasis_odd_mem_axisSpan c i 2)
  · have e : sgn (((c : C) : Fin 24 → ZMod 2) i) • tbasis (.inr (.inr (.inl (c, i, 1)))) =
        ((0 : symMat), (0 : SpaceX), tensor (Spin.E 1 c) (Pi.single i 1)) := by
      rw [tbasis_odd_one, Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero, smul_smul, sgn_sq,
        one_smul]
    rw [← e]
    exact axisSpan.smul_mem _ (tbasis_odd_mem_axisSpan c i 1)

theorem basisB_mem_axisSpan (k : BIdx) : basisB k ∈ axisSpan := by
  rcases k with z | c | ⟨⟨η, c⟩, i⟩
  · rw [basisB_inl]
    exact basisA_mem_axisSpan z
  · rw [basisB_inr_inl, ← Xlift_rep_eq c]
    exact Xlift_mem_axisSpan (isShortCoord_rep c)
  · rw [basisB_inr_inr]
    exact tensor_mem_axisSpan η c i

theorem axisSpan_eq_top : axisSpan = ⊤ :=
  eq_top_iff.2 (basisB.span_eq ▸ Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact basisB_mem_axisSpan k))

theorem finite_AutO_and_orbits :
    (∀ r : ShortQ, (MulAction.orbit AutO (axis r.1)).Finite) ∧ Finite AutO :=
  finite_of_isolated_axes_basis basisB gmul gmul_comm gramDiag gramDiag_pos AutO
    (fun _ hg => hg.1)
    (fun g hg v => by rw [← bform_self_eq_sum, ← bform_self_eq_sum, hg.2])
    (fun r : ShortQ => axis r.1) (fun _ => 16) (fun r => axis_mul_self r.2)
    (fun r => isUnit_two_axis_sub r.2) axisSpan_eq_top

instance : Finite AutO := finite_AutO_and_orbits.2

theorem rational_isometric_algebra_automorphisms_finite :
    (∀ g : SpaceB ≃ₗ[ℚ] SpaceB, g ∈ AutO ↔
      (∀ u v, g (gmul u v) = gmul (g u) (g v)) ∧ ∀ u v, bform (g u) (g v) = bform u v) ∧
    Finite AutO ∧ Finite ShortQ ∧
    (∀ r : ShortQ, (MulAction.orbit AutO (axis r.1)).Finite) ∧
    Submodule.span ℚ (⋃ r : ShortQ, MulAction.orbit AutO (axis r.1)) = ⊤ :=
  ⟨fun _ => mem_AutO, finite_AutO_and_orbits.2, inferInstance, finite_AutO_and_orbits.1,
    axisSpan_eq_top⟩

end CFSG.Monster.Griess
