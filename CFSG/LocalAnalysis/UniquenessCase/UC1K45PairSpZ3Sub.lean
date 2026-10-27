module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpOrd3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {B : LinearMap.BilinForm (ZMod 2) W} {a b : W ≃ₗ[ZMod 2] W}

@[expose] noncomputable def projP (hB : B.Nondegenerate) (ha : OrdThree B a) :
    W →ₗ[ZMod 2] W :=
  (commSp a).projection (B.orthogonal (commSp a)) (isCompl_commSp_orth hB ha)

theorem projP_mem (hB : B.Nondegenerate) (ha : OrdThree B a) (x : W) :
    projP hB ha x ∈ commSp a :=
  Submodule.projection_apply_mem _ x

theorem projP_of_mem (hB : B.Nondegenerate) (ha : OrdThree B a) {x : W} (hx : x ∈ commSp a) :
    projP hB ha x = x :=
  Submodule.projection_apply_of_mem_left _ hx

theorem projP_eq_zero_iff (hB : B.Nondegenerate) (ha : OrdThree B a) {x : W} :
    projP hB ha x = 0 ↔ x ∈ B.orthogonal (commSp a) :=
  Submodule.projection_apply_eq_zero_iff _

theorem sub_projP_mem (hB : B.Nondegenerate) (ha : OrdThree B a) (x : W) :
    x - projP hB ha x ∈ B.orthogonal (commSp a) :=
  Submodule.sub_projection_mem _ x

@[expose] def pairU (a b : W ≃ₗ[ZMod 2] W) : Submodule (ZMod 2) W := commSp a ⊔ commSp b

@[expose] def pairR (B : LinearMap.BilinForm (ZMod 2) W) (a b : W ≃ₗ[ZMod 2] W) :
    Submodule (ZMod 2) W :=
  pairU a b ⊓ B.orthogonal (commSp a)

theorem bilin_zero_on_plane (D : LinearMap.BilinForm (ZMod 2) W) {q₁ q₂ : W}
    (h11 : D q₁ q₁ = 0) (h12 : D q₁ q₂ = 0) (h21 : D q₂ q₁ = 0) (h22 : D q₂ q₂ = 0) {x y : W}
    (hx : x = 0 ∨ x = q₁ ∨ x = q₂ ∨ x = q₁ + q₂) (hy : y = 0 ∨ y = q₁ ∨ y = q₂ ∨ y = q₁ + q₂) :
    D x y = 0 := by
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp [map_add, h11, h12, h21, h22]

theorem projP_bil_eq (h : PairHyp B a b) (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥)
    {q q' : W} (hq : q ∈ commSp b) (hq' : q' ∈ commSp b) :
    B (projP h.nondeg h.ha q) (projP h.nondeg h.ha q') = B q q' := by
  set π := projP h.nondeg h.ha with hπ
  have hinj : ∀ x ∈ commSp b, π x = 0 → x = 0 := by
    intro x hx hx0
    have hmem : x ∈ commSp b ⊓ B.orthogonal (commSp a) :=
      Submodule.mem_inf.mpr ⟨hx, (projP_eq_zero_iff h.nondeg h.ha).mp hx0⟩
    rw [hQ0, Submodule.mem_bot] at hmem
    exact hmem
  have hne : commSp b ≠ ⊥ := by
    intro h0
    have := h.hb.rank
    rw [h0] at this
    simp at this
  obtain ⟨q₁, hq₁, hq₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hq₂ : b q₁ ∈ commSp b := apply_mem_commSp hq₁
  have hq₂0 : b q₁ ≠ 0 := apply_ne_zero hq₁0
  have hq₂1 : b q₁ ≠ q₁ := apply_ne_of_mem h.nondeg h.hb hq₁ hq₁0
  have hcases := commSp_cases h.nondeg h.hb hq₁ hq₁0
  have hq₃ : b (b q₁) = q₁ + b q₁ := apply_sq_of_mem h.hb hq₁
  have hπ1 : π q₁ ≠ 0 := fun h0 => hq₁0 (hinj _ hq₁ h0)
  have hπ2 : π (b q₁) ≠ 0 := fun h0 => hq₂0 (hinj _ hq₂ h0)
  have hπ12 : π q₁ ≠ π (b q₁) := by
    intro h0
    have : π (b q₁ - q₁) = 0 := by rw [map_sub, h0, sub_self]
    exact hq₂1 (sub_eq_zero.mp (hinj _ (sub_mem hq₂ hq₁) this))
  have hP1 : B (π q₁) (π (b q₁)) = 1 :=
    plane_pairing_one h.alt h.ha.rank (commSp_inf_orth h.nondeg h.ha) (projP_mem h.nondeg h.ha _)
      (projP_mem h.nondeg h.ha _) hπ1 hπ2 hπ12
  have hQ1 : B q₁ (b q₁) = 1 := bil_self_apply h.nondeg h.alt h.hb hq₁ hq₁0
  have hD : ∀ x y : W, (x = 0 ∨ x = q₁ ∨ x = b q₁ ∨ x = q₁ + b q₁) →
      (y = 0 ∨ y = q₁ ∨ y = b q₁ ∨ y = q₁ + b q₁) → ((B.compl₁₂ π π) - B) x y = 0 :=
    fun x y hx hy => bilin_zero_on_plane ((B.compl₁₂ π π) - B) (q₁ := q₁) (q₂ := b q₁)
      (by simp [h.alt.self_eq_zero]) (by simp [hP1, hQ1])
      (by simp [bil_comm_of_alt h.alt (π (b q₁)), bil_comm_of_alt h.alt (b q₁), hP1, hQ1])
      (by simp [h.alt.self_eq_zero]) hx hy
  have hx := hcases q hq
  have hy := hcases q' hq'
  rw [hq₃] at hx hy
  have := hD q q' hx hy
  simpa [sub_eq_zero] using this

theorem pairR_le_orth (h : PairHyp B a b) (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥) :
    pairR B a b ≤ B.orthogonal (commSp b) := by
  intro r hr
  obtain ⟨hrU, hrP⟩ := Submodule.mem_inf.mp hr
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hrU
  have h0 : projP h.nondeg h.ha (p + q) = 0 := (projP_eq_zero_iff h.nondeg h.ha).mpr hrP
  have hpq : p = projP h.nondeg h.ha q := by
    rw [map_add, projP_of_mem h.nondeg h.ha hp] at h0
    exact (eq_neg_of_add_eq_zero_left h0).trans (neg_eq_self' _)
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro q' hq'
  rw [bil_comm_of_alt h.alt]
  have h1 : B (projP h.nondeg h.ha q) q' = B (projP h.nondeg h.ha q) (projP h.nondeg h.ha q') := by
    have hperp : B (projP h.nondeg h.ha q) (q' - projP h.nondeg h.ha q') = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp (sub_projP_mem h.nondeg h.ha q')) _
        (projP_mem h.nondeg h.ha q)
    rw [map_sub, sub_eq_zero] at hperp
    exact hperp
  rw [map_add, LinearMap.add_apply, hpq, h1, projP_bil_eq h hQ0 hq hq', add_self_eq_zero']

@[expose] def zStab (B : LinearMap.BilinForm (ZMod 2) W) (a b : W ≃ₗ[ZMod 2] W) :
    Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {y | (∀ x, y x - x ∈ pairU a b) ∧ ∀ r ∈ pairR B a b, y r = r}
  mul_mem' := by
    rintro y y' ⟨hy1, hy2⟩ ⟨hy1', hy2'⟩
    refine ⟨fun x => ?_, fun r hr => ?_⟩
    · have e : (y * y') x - x = (y (y' x) - y' x) + (y' x - x) := by
        rw [LinearEquiv.mul_apply]; abel
      rw [e]
      exact add_mem (hy1 _) (hy1' x)
    · rw [LinearEquiv.mul_apply, hy2' r hr, hy2 r hr]
  one_mem' := by
    refine ⟨fun x => ?_, fun r _ => rfl⟩
    simp
  inv_mem' := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨fun x => ?_, fun r hr => ?_⟩
    · have e : y⁻¹ x - x = -(x - y⁻¹ x) := by abel
      have h1 : y (y⁻¹ x) - y⁻¹ x ∈ pairU a b := hy1 (y⁻¹ x)
      have h2 : y (y⁻¹ x) = x := by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
      rw [e]
      rw [h2] at h1
      exact neg_mem h1
    · have : y r = r := hy2 r hr
      calc y⁻¹ r = y⁻¹ (y r) := by rw [this]
        _ = r := by rw [← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]

theorem mem_zStab_iff {y : W ≃ₗ[ZMod 2] W} :
    y ∈ zStab B a b ↔ (∀ x, y x - x ∈ pairU a b) ∧ ∀ r ∈ pairR B a b, y r = r :=
  Iff.rfl

theorem a_mem_zStab (h : PairHyp B a b) : a ∈ zStab B a b := by
  refine ⟨fun x => ?_, fun r hr => ?_⟩
  · exact Submodule.mem_sup_left (sub_mem_commSp a x)
  · exact (fixed_iff_mem_orth h.nondeg h.ha.isom r).mpr (Submodule.mem_inf.mp hr).2

theorem b_mem_zStab (h : PairHyp B a b) (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥) :
    b ∈ zStab B a b := by
  refine ⟨fun x => ?_, fun r hr => ?_⟩
  · exact Submodule.mem_sup_right (sub_mem_commSp b x)
  · exact (fixed_iff_mem_orth h.nondeg h.hb.isom r).mpr (pairR_le_orth h hQ0 hr)

theorem closure_le_zStab (h : PairHyp B a b) (hQ0 : commSp b ⊓ B.orthogonal (commSp a) = ⊥) :
    Subgroup.closure ({a, b} : Set (W ≃ₗ[ZMod 2] W)) ≤ zStab B a b := by
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  · exact a_mem_zStab h
  · exact b_mem_zStab h hQ0

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
