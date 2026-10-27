module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionRich
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.StandardType

open CFSG.SeitzReduction.LinearPilot Matrix
open scoped commutatorElement

namespace LinSemisimple

variable {m : ℕ} {F : Type} [Field F] {ι : Type*}

@[expose] noncomputable def eigClass (d : ι → Fin (m + 1) → Fˣ) (i : Fin (m + 1)) :
    Finset (Fin (m + 1)) :=
  open Classical in Finset.univ.filter fun j => ∀ k, d k j = d k i

theorem mem_eigClass {d : ι → Fin (m + 1) → Fˣ} {i j : Fin (m + 1)} :
    j ∈ eigClass d i ↔ ∀ k, d k j = d k i := by
  simp [eigClass]

theorem self_mem_eigClass (d : ι → Fin (m + 1) → Fˣ) (i : Fin (m + 1)) : i ∈ eigClass d i :=
  mem_eigClass.mpr fun _ => rfl

theorem eq_of_mem_eigClass {d : ι → Fin (m + 1) → Fˣ} {i j l : Fin (m + 1)}
    (hj : j ∈ eigClass d i) (hl : l ∈ eigClass d i) (k : ι) : d k j = d k l :=
  (mem_eigClass.mp hj k).trans (mem_eigClass.mp hl k).symm

@[expose] noncomputable def diagCentSL (d : ι → Fin (m + 1) → Fˣ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
  ⨅ k, (InnerDiagA.conjSL (InnerDiagA.diagGL (d k))).eqLocus (MonoidHom.id _)

theorem mem_diagCentSL {d : ι → Fin (m + 1) → Fˣ}
    {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    u ∈ diagCentSL d ↔ ∀ k, InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) u = u := by
  rw [diagCentSL, Subgroup.mem_iInf]
  rfl

theorem conjSL_diagGL_apply (e : Fin (m + 1) → Fˣ)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) (i j : Fin (m + 1)) :
    (InnerDiagA.conjSL (InnerDiagA.diagGL e) u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
      (e i : F) * (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j * (((e j)⁻¹ : Fˣ) : F) := by
  rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv, mul_diagonal,
    diagonal_mul]

theorem conjSL_diagGL_eq_self_iff {e : Fin (m + 1) → Fˣ}
    {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    InnerDiagA.conjSL (InnerDiagA.diagGL e) u = u ↔
      ∀ i j, e i ≠ e j → (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
  constructor
  · intro h i j hij
    have h1 : (InnerDiagA.conjSL (InnerDiagA.diagGL e) u :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j := by rw [h]
    rw [conjSL_diagGL_apply] at h1
    by_contra hx
    apply hij
    have h2 : ((e i : F) * (((e j)⁻¹ : Fˣ) : F)) * (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
        1 * (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j := by
      rw [one_mul]
      calc (e i : F) * (((e j)⁻¹ : Fˣ) : F) * (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
          (e i : F) * (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j * (((e j)⁻¹ : Fˣ) : F) := by
            ring
        _ = _ := h1
    have h3 := mul_right_cancel₀ hx h2
    have h4 : e i * (e j)⁻¹ = 1 := Units.ext (by rw [Units.val_mul, h3, Units.val_one])
    exact mul_inv_eq_one.mp h4
  · intro h
    apply Subtype.ext
    ext i j
    rw [conjSL_diagGL_apply]
    by_cases hij : e i = e j
    · rw [hij, mul_comm (e j : F), mul_assoc, Units.mul_inv, mul_one]
    · rw [h i j hij, mul_zero, zero_mul]

theorem mem_diagCentSL_iff {d : ι → Fin (m + 1) → Fˣ}
    {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    u ∈ diagCentSL d ↔
      ∀ i j, (∃ k, d k i ≠ d k j) → (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
  rw [mem_diagCentSL]
  simp only [conjSL_diagGL_eq_self_iff]
  constructor
  · rintro h i j ⟨k, hk⟩
    exact h k i j hk
  · intro h k i j hk
    exact h i j ⟨k, hk⟩

theorem commutatorElement_mem_diagCentSL {d : ι → Fin (m + 1) → Fˣ}
    {u v : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hu : ∀ k, u⁻¹ * InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) u ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hv : ∀ k, v⁻¹ * InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) v ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    ⁅u, v⁆ ∈ diagCentSL d := by
  rw [mem_diagCentSL]
  intro k
  rw [map_commutatorElement]
  have hu' : InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) u =
      u * (u⁻¹ * InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) u) := by group
  have hv' : InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) v =
      v * (v⁻¹ * InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) v) := by group
  rw [hu', hv',
    CFSG.ComponentClassification.CentralExtensions.commutator_mul_center_left _ _ _ (hu k),
    CFSG.ComponentClassification.CentralExtensions.commutator_mul_center_right _ _ _ (hv k)]

theorem conj_mem_diagCentSL {d : ι → Fin (m + 1) → Fˣ}
    {u v : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hu : u ∈ diagCentSL d)
    (hv : ∀ k, v⁻¹ * InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) v ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) :
    v * u * v⁻¹ ∈ diagCentSL d := by
  rw [mem_diagCentSL] at hu ⊢
  intro k
  obtain ⟨z, hzc, hvz⟩ : ∃ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F),
      InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) v = v * z := ⟨_, hv k, by group⟩
  have hz := Subgroup.mem_center_iff.mp hzc
  rw [map_mul, map_mul, map_inv, hu k, hvz]
  calc v * z * u * (v * z)⁻¹ = v * (z * u) * z⁻¹ * v⁻¹ := by group
    _ = v * (u * z) * z⁻¹ * v⁻¹ := by rw [hz u]
    _ = v * u * v⁻¹ := by group

theorem blockComplProj_eigClass_mul_comm {d : ι → Fin (m + 1) → Fˣ}
    {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hu : u ∈ diagCentSL d) (i : Fin (m + 1)) :
    blockComplProj (eigClass d i) * (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * blockComplProj (eigClass d i) := by
  rw [mem_diagCentSL_iff] at hu
  ext a b
  rw [blockComplProj, diagonal_mul, mul_diagonal]
  by_cases hab : ∀ k, d k a = d k b
  · have hiff : a ∈ eigClass d i ↔ b ∈ eigClass d i := by
      simp only [mem_eigClass, hab]
    by_cases ha : a ∈ eigClass d i
    · simp [ha, hiff.mp ha]
    · simp [ha, mt hiff.mpr ha]
  · rw [hu a b (not_forall.mp hab), mul_zero, zero_mul]

theorem conj_mem_blockSpecialLinear_eigClass {d : ι → Fin (m + 1) → Fˣ}
    {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hu : u ∈ diagCentSL d) (i : Fin (m + 1))
    {s : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hs : s ∈ blockSpecialLinear (eigClass d i)) :
    u * s * u⁻¹ ∈ blockSpecialLinear (eigClass d i) := by
  have h := map_conj_blockSpecialLinear_of_mul_eq u (blockComplProj_eigClass_mul_comm hu i)
  rw [← h]
  exact ⟨s, hs, rfl⟩

theorem blockSpecialLinear_eigClass_le_diagCentSL (d : ι → Fin (m + 1) → Fˣ)
    (i : Fin (m + 1)) : blockSpecialLinear (K := F) (eigClass d i) ≤ diagCentSL d := by
  intro s hs
  rw [mem_diagCentSL_iff]
  rintro a b ⟨k, hk⟩
  have hne : a ≠ b := fun h => hk (h ▸ rfl)
  have hout : a ∉ eigClass d i ∨ b ∉ eigClass d i := by
    by_cases ha : a ∈ eigClass d i
    · exact Or.inr fun hb => hk (eq_of_mem_eigClass ha hb k)
    · exact Or.inl ha
  rw [hs a b hout, one_apply_ne hne]

theorem transvection_mem_blockSpecialLinear_eigClass {d : ι → Fin (m + 1) → Fˣ}
    {j l : Fin (m + 1)} (hjl : j ≠ l) (hd : ∀ k, d k j = d k l) (c : F) :
    Matrix.SpecialLinearGroup.transvection hjl c ∈ blockSpecialLinear (eigClass d j) :=
  transvection_mem_blockSpecialLinear hjl (self_mem_eigClass d j)
    (mem_eigClass.mpr fun k => (hd k).symm) c

theorem apply_eq_zero_of_mul_transvection_comm {n : ℕ} {i j : Fin n} (hji : j ≠ i)
    {u : Matrix.SpecialLinearGroup (Fin n) F}
    (h : u * Matrix.SpecialLinearGroup.transvection hji (1 : F) =
      Matrix.SpecialLinearGroup.transvection hji 1 * u) :
    (u : Matrix (Fin n) (Fin n) F) i j = 0 := by
  have h1 : (u : Matrix (Fin n) (Fin n) F) * (1 + single j i 1) =
      (1 + single j i 1) * (u : Matrix (Fin n) (Fin n) F) := by
    rw [← Matrix.SpecialLinearGroup.transvection_coe hji, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, h]
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    Matrix.add_apply, mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ (Ne.symm hji),
    mul_one, add_zero] at h2
  exact add_eq_left.mp h2

theorem isDiag_of_commute_transvection {d : ι → Fin (m + 1) → Fˣ}
    {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hu : u ∈ diagCentSL d)
    (h : ∀ j l (hjl : j ≠ l), (∀ k, d k j = d k l) →
      u * Matrix.SpecialLinearGroup.transvection hjl (1 : F) =
        Matrix.SpecialLinearGroup.transvection hjl 1 * u) :
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
  intro i j hij
  by_cases hd : ∀ k, d k i = d k j
  · exact apply_eq_zero_of_mul_transvection_comm (Ne.symm hij)
      (h j i (Ne.symm hij) fun k => (hd k).symm)
  · exact mem_diagCentSL_iff.mp hu i j (not_forall.mp hd)

theorem mul_comm_of_isDiag {n : ℕ} {u v : Matrix.SpecialLinearGroup (Fin n) F}
    (hu : (u : Matrix (Fin n) (Fin n) F).IsDiag) (hv : (v : Matrix (Fin n) (Fin n) F).IsDiag) :
    u * v = v * u := by
  have h : (u : Matrix (Fin n) (Fin n) F) * (v : Matrix (Fin n) (Fin n) F) =
      (v : Matrix (Fin n) (Fin n) F) * (u : Matrix (Fin n) (Fin n) F) := by
    rw [← hu.diagonal_diag, ← hv.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h]

theorem transvection_one_mul_self [CharP F 2] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : F) *
      Matrix.SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero]
  ext a b
  rw [Matrix.SpecialLinearGroup.transvection_coe, single_zero, add_zero,
    Matrix.SpecialLinearGroup.coe_one]

theorem sq_commutatorElement_eq_one {G : Type*} [Group G] {u t : G} (htt : t * t = 1)
    (h : ⁅u, t⁆ ∈ Subgroup.center G) : ⁅u, t⁆ ^ 2 = 1 := by
  have hc : ⁅u, t⁆ = u * t * u⁻¹ * t⁻¹ := commutatorElement_def u t
  generalize ⁅u, t⁆ = c at h hc ⊢
  have hcen := Subgroup.mem_center_iff.mp h
  have e1 : c * t = u * t * u⁻¹ := by rw [hc]; group
  calc c ^ 2 = c * c * (t * t) := by rw [htt, mul_one, pow_two]
    _ = c * (c * t) * t := by group
    _ = c * (t * c) * t := by rw [hcen t]
    _ = (c * t) * (c * t) := by group
    _ = (u * t * u⁻¹) * (u * t * u⁻¹) := by rw [e1]
    _ = u * (t * t) * u⁻¹ := by group
    _ = 1 := by rw [htt, mul_one, mul_inv_cancel]

theorem commute_of_commutatorElement_transvection_mem_center [CharP F 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) {u : Matrix.SpecialLinearGroup (Fin n) F}
    (h : ⁅u, Matrix.SpecialLinearGroup.transvection hij (1 : F)⁆ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) :
    u * Matrix.SpecialLinearGroup.transvection hij (1 : F) =
      Matrix.SpecialLinearGroup.transvection hij 1 * u :=
  commutatorElement_eq_one_iff_mul_comm.mp (eq_one_of_mem_center_of_sq_eq_one h
    (sq_commutatorElement_eq_one (transvection_one_mul_self hij) h))

theorem blockSpecialLinear_commute_of_card_le_one {n : ℕ} {I : Finset (Fin n)}
    (hI : I.card ≤ 1) {s s' : Matrix.SpecialLinearGroup (Fin n) F}
    (hs : s ∈ blockSpecialLinear I) (hs' : s' ∈ blockSpecialLinear I) : s * s' = s' * s := by
  have hdiag : ∀ x ∈ blockSpecialLinear (K := F) I,
      (x : Matrix (Fin n) (Fin n) F).IsDiag := by
    intro x hx a b hab
    have hout : a ∉ I ∨ b ∉ I := by
      by_cases ha : a ∈ I
      · exact Or.inr fun hb => hab (Finset.card_le_one.mp hI a ha b hb)
      · exact Or.inl ha
    rw [hx a b hout, one_apply_ne hab]
  exact mul_comm_of_isDiag (hdiag s hs) (hdiag s' hs')

end LinSemisimple

end CFSG.StandardType
