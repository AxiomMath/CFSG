module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.SeitzReduction.LinearPilot
open scoped commutatorElement

namespace LinTorus

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem commutatorElement_mul_left_of_mem_center {H : Type*} [Group H] {c : H}
    (hc : c ∈ Subgroup.center H) (x y : H) : ⁅c * x, y⁆ = ⁅x, y⁆ := by
  have h1 : (x * y * x⁻¹) * c = c * (x * y * x⁻¹) := Subgroup.mem_center_iff.mp hc _
  rw [commutatorElement_def, commutatorElement_def]
  calc c * x * y * (c * x)⁻¹ * y⁻¹ = c * (x * y * x⁻¹) * c⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * c * c⁻¹ * y⁻¹ := by rw [← h1]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_right_of_mem_center {H : Type*} [Group H] {c : H}
    (hc : c ∈ Subgroup.center H) (x y : H) : ⁅x, c * y⁆ = ⁅x, y⁆ := by
  have h1 : (x * y * x⁻¹ * y⁻¹) * c = c * (x * y * x⁻¹ * y⁻¹) := Subgroup.mem_center_iff.mp hc _
  have h2 : x * c = c * x := (Subgroup.mem_center_iff.mp hc x)
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (c * y) * x⁻¹ * (c * y)⁻¹ = (x * c) * y * x⁻¹ * y⁻¹ * c⁻¹ := by group
    _ = c * (x * y * x⁻¹ * y⁻¹) * c⁻¹ := by rw [h2]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [← h1]; group

theorem eq_of_map_eq_of_mul_self [CharP F 2] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {s t : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hs : s * s = 1) (ht : t * t = 1)
    (h : ψ s = ψ t) : s = t := by
  set z := s⁻¹ * t with hz
  have hzc : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])
  have hts : t = s * z := by rw [hz, mul_inv_cancel_left]
  have hzs : z * s = s * z := (Subgroup.mem_center_iff.mp hzc s).symm
  have hz2 : z ^ 2 = 1 := by
    calc z ^ 2 = (s * s) * (z * z) := by rw [hs, one_mul, pow_two]
      _ = s * (z * s) * z := by rw [hzs]; group
      _ = t * t := by rw [hts]; group
      _ = 1 := ht
  rw [hts, eq_one_of_mem_center_of_sq_eq_one hzc hz2, mul_one]

theorem mul_transvection_comm_of_map [CharP F 2]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {z : Matrix.SpecialLinearGroup (Fin (m + 1)) F} {i j : Fin (m + 1)} (hij : i ≠ j)
    (h : ψ z * ψ (Matrix.SpecialLinearGroup.transvection hij 1) =
      ψ (Matrix.SpecialLinearGroup.transvection hij 1) * ψ z) :
    z * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * z := by
  set t := Matrix.SpecialLinearGroup.transvection hij (1 : F) with ht
  have ht2 : t * t = 1 := transvection_mul_self hij
  have hs2 : (z * t * z⁻¹) * (z * t * z⁻¹) = 1 := by
    calc (z * t * z⁻¹) * (z * t * z⁻¹) = z * (t * t) * z⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hst := eq_of_map_eq_of_mul_self hker hs2 ht2
    (by rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right])
  calc z * t = z * t * z⁻¹ * z := by group
    _ = t * z := by rw [hst]

@[expose] noncomputable def diagClass (S : Set G) (δ : G → Fin (m + 1) → Fˣ) (i : Fin (m + 1)) :
    Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter fun j => ∀ e ∈ S, δ e j = δ e i

omit [Group G] in
theorem mem_diagClass {S : Set G} {δ : G → Fin (m + 1) → Fˣ} {i j : Fin (m + 1)} :
    j ∈ diagClass S δ i ↔ ∀ e ∈ S, δ e j = δ e i := by
  unfold diagClass
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [Group G] in
theorem self_mem_diagClass (S : Set G) (δ : G → Fin (m + 1) → Fˣ) (i : Fin (m + 1)) :
    i ∈ diagClass S δ i :=
  mem_diagClass.mpr fun _ _ => rfl

omit [Group G] in
theorem eq_of_mem_diagClass {S : Set G} {δ : G → Fin (m + 1) → Fˣ} {i j k : Fin (m + 1)}
    (hj : j ∈ diagClass S δ i) (hk : k ∈ diagClass S δ i) {e : G} (he : e ∈ S) :
    δ e j = δ e k :=
  (mem_diagClass.mp hj e he).trans (mem_diagClass.mp hk e he).symm

theorem coe_conjSL_diagGL_apply (d : Fin (m + 1) → Fˣ)
    (z : Matrix.SpecialLinearGroup (Fin (m + 1)) F) (i j : Fin (m + 1)) :
    ((InnerDiagA.conjSL (InnerDiagA.diagGL d) z : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
      (d i : F) * (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j * (((d j)⁻¹ : Fˣ) : F) := by
  rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv, mul_diagonal,
    diagonal_mul]

variable (F) in
@[expose] def diagCent (S : Set G) (δ : G → Fin (m + 1) → Fˣ) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F) where
  carrier := {z | ∀ e ∈ S, InnerDiagA.conjSL (InnerDiagA.diagGL (δ e)) z = z}
  one_mem' := fun _ _ => map_one _
  mul_mem' := fun ha hb e he => by rw [map_mul, ha e he, hb e he]
  inv_mem' := fun ha e he => by rw [map_inv, ha e he]

omit [Group G] in
theorem mem_diagCent {S : Set G} {δ : G → Fin (m + 1) → Fˣ}
    {z : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    z ∈ diagCent F S δ ↔ ∀ e ∈ S, InnerDiagA.conjSL (InnerDiagA.diagGL (δ e)) z = z :=
  Iff.rfl

omit [Group G] in
theorem eq_of_mem_diagCent {S : Set G} {δ : G → Fin (m + 1) → Fˣ}
    {z : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hz : z ∈ diagCent F S δ) {i j : Fin (m + 1)}
    (hij : (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j ≠ 0) {e : G} (he : e ∈ S) :
    δ e i = δ e j := by
  have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
    (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) (hz e he)
  simp only [coe_conjSL_diagGL_apply] at h
  set w := (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j
  have h' : (δ e i : F) * w = w * δ e j := by
    calc (δ e i : F) * w = (δ e i : F) * w * (((δ e j)⁻¹ : Fˣ) : F) * (δ e j : F) := by
          rw [mul_assoc _ (((δ e j)⁻¹ : Fˣ) : F), Units.inv_mul, mul_one]
      _ = w * δ e j := by rw [h]
  have h2 : ((δ e i : F) - δ e j) * w = 0 := by
    rw [sub_mul, h', mul_comm w, sub_self]
  exact Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hij))

omit [Group G] in
theorem blockSpecialLinear_le_diagCent (S : Set G) (δ : G → Fin (m + 1) → Fˣ)
    (i : Fin (m + 1)) : blockSpecialLinear (K := F) (diagClass S δ i) ≤ diagCent F S δ :=
  fun _ hu _ he => LinFusion.conjSL_diagGL_of_mem_blockSpecialLinear
    (fun _ hj _ hk => eq_of_mem_diagClass hj hk he) hu

omit [Group G] in
theorem blockComplProj_mul_eq_of_mem_diagCent {S : Set G} {δ : G → Fin (m + 1) → Fˣ}
    {z : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hz : z ∈ diagCent F S δ) (i : Fin (m + 1)) :
    blockComplProj (diagClass S δ i) * (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * blockComplProj (diagClass S δ i) := by
  ext a b
  rw [blockComplProj, diagonal_mul, mul_diagonal]
  by_cases hab : (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = 0
  · rw [hab, mul_zero, zero_mul]
  · have hiff : a ∈ diagClass S δ i ↔ b ∈ diagClass S δ i := by
      rw [mem_diagClass, mem_diagClass]
      constructor
      · intro ha e he
        rw [← eq_of_mem_diagCent hz hab he]
        exact ha e he
      · intro hb e he
        rw [eq_of_mem_diagCent hz hab he]
        exact hb e he
    by_cases ha : a ∈ diagClass S δ i
    · rw [ite_eq_left ha, ite_eq_left (hiff.mp ha), zero_mul, mul_zero]
    · rw [ite_eq_right ha, ite_eq_right fun hb => ha (hiff.mpr hb), one_mul, mul_one]

omit [Group G] in
theorem conj_mem_blockSpecialLinear_of_mem_diagCent {S : Set G} {δ : G → Fin (m + 1) → Fˣ}
    {i : Fin (m + 1)} {z u : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hz : z ∈ diagCent F S δ) (hu : u ∈ blockSpecialLinear (diagClass S δ i)) :
    z * u * z⁻¹ ∈ blockSpecialLinear (diagClass S δ i) := by
  have h := map_conj_blockSpecialLinear_of_mul_eq z (blockComplProj_mul_eq_of_mem_diagCent hz i)
  rw [← h]
  exact ⟨u, hu, rfl⟩


theorem mul_comm_of_offDiag_eq_zero {z w : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hz : ∀ a b, a ≠ b → (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = 0)
    (hw : ∀ a b, a ≠ b → (w : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = 0) :
    z * w = w * z := by
  have e1 := TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero hz
  have e2 := TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero hw
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, e1, e2,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  by_cases hab : a = b
  · subst hab
    rw [diagonal_apply_eq, diagonal_apply_eq, mul_comm]
  · rw [diagonal_apply_ne _ hab, diagonal_apply_ne _ hab]

theorem blockSpecialLinear_singleton (i : Fin (m + 1)) :
    blockSpecialLinear (K := F) ({i} : Finset (Fin (m + 1))) = ⊥ := by
  refine eq_bot_iff.mpr fun u hu => ?_
  have hout : ∀ a b, (a ≠ i ∨ b ≠ i) → (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b := fun a b hab =>
    hu a b (by simpa only [Finset.mem_singleton] using hab)
  have hoff : ∀ a b, a ≠ b → (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = 0 := by
    intro a b hab
    rw [hout a b (by by_contra h; push Not at h; exact hab (h.1.trans h.2.symm)),
      one_apply_ne hab]
  have hdet := u.2
  rw [TypeA.PGLTor.eq_diagonal_of_offDiag_eq_zero hoff, det_diagonal,
    Finset.prod_eq_single i (fun k _ hk => by rw [hout k k (Or.inl hk), one_apply_eq])
      (fun h => absurd (Finset.mem_univ i) h)] at hdet
  rw [Subgroup.mem_bot]
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = i
    · subst ha
      rw [hdet, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
    · rw [hout a a (Or.inl ha), Matrix.SpecialLinearGroup.coe_one]
  · rw [hoff a b hab, Matrix.SpecialLinearGroup.coe_one, one_apply_ne hab]

section Psi

variable {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {S : Set G}
  {δ : G → Fin (m + 1) → Fˣ}

theorem mem_centralizer_map_blockSpecialLinear {e : G} {d : Fin (m + 1) → Fˣ}
    (he : (e, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ) {I : Finset (Fin (m + 1))}
    (hd : ∀ i ∈ I, ∀ j ∈ I, d i = d j) :
    e ∈ Subgroup.centralizer (((blockSpecialLinear (K := F) I).map ψ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  have h1 := LinFusion.mem_ggInducedPairs.mp he u
  rw [LinFusion.conjSL_diagGL_of_mem_blockSpecialLinear hd hu] at h1
  calc ψ u * e = e * ψ u * e⁻¹ * e := by rw [h1]
    _ = e * ψ u := by group

theorem map_diagCent_le
    (hδ : ∀ e ∈ S, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ) :
    (diagCent F S δ).map ψ ≤ ψ.range ⊓ Subgroup.centralizer S := by
  rintro _ ⟨z, hz, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
  have h := LinFusion.mem_ggInducedPairs.mp (hδ e he) z
  rw [hz e he] at h
  calc e * ψ z = e * ψ z * e⁻¹ * e := by group
    _ = ψ z * e := by rw [h]

theorem conjSL_mul_inv_mem_center
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hδ : ∀ e ∈ S, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ)
    {w : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hw : ψ w ∈ Subgroup.centralizer S)
    {e : G} (he : e ∈ S) :
    InnerDiagA.conjSL (InnerDiagA.diagGL (δ e)) w * w⁻¹ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
  apply hker
  have h := LinFusion.mem_ggInducedPairs.mp (hδ e he) w
  have hc : e * ψ w = ψ w * e := Subgroup.mem_centralizer_iff.mp hw e he
  rw [MonoidHom.mem_ker, map_mul, map_inv, ← h, hc, mul_inv_cancel_right, mul_inv_cancel]

theorem conj_mem_diagCent
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hδ : ∀ e ∈ S, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ)
    {w : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hw : ψ w ∈ Subgroup.centralizer S)
    {z : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hz : z ∈ diagCent F S δ) :
    w * z * w⁻¹ ∈ diagCent F S δ := by
  intro e he
  set c := InnerDiagA.conjSL (InnerDiagA.diagGL (δ e)) w * w⁻¹ with hc
  have hcz := conjSL_mul_inv_mem_center hker hδ hw he
  have hw' : InnerDiagA.conjSL (InnerDiagA.diagGL (δ e)) w = c * w := by
    rw [hc, inv_mul_cancel_right]
  rw [map_mul, map_mul, map_inv, hw', hz e he]
  have h1 : (w * z * w⁻¹) * c = c * (w * z * w⁻¹) := Subgroup.mem_center_iff.mp hcz _
  calc c * w * z * (c * w)⁻¹ = c * (w * z * w⁻¹) * c⁻¹ := by group
    _ = w * z * w⁻¹ := by rw [← h1]; group

theorem isSubnormal_map_diagCent
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hδ : ∀ e ∈ S, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ) :
    IsSubnormal ((diagCent F S δ).map ψ) (ψ.range ⊓ Subgroup.centralizer S) := by
  refine IsSubnormal.step (map_diagCent_le hδ) ⟨fun x hx y => ?_⟩ (IsSubnormal.refl _)
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨⟨w, hw⟩, hyC⟩ := Subgroup.mem_inf.mp y.2
  refine ⟨w * z * w⁻¹, conj_mem_diagCent hker hδ (by rw [hw]; exact hyC) hz, ?_⟩
  simp only [map_mul, map_inv, hw, hzx, Subgroup.coe_mul, Subgroup.coe_inv]

theorem isSubnormal_map_blockSpecialLinear
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hδ : ∀ e ∈ S, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ) (i : Fin (m + 1)) :
    IsSubnormal ((blockSpecialLinear (K := F) (diagClass S δ i)).map ψ)
      (ψ.range ⊓ Subgroup.centralizer S) := by
  refine IsSubnormal.step (Subgroup.map_mono (blockSpecialLinear_le_diagCent S δ i))
    ⟨fun x hx y => ?_⟩ (isSubnormal_map_diagCent hker hδ)
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨u, hu, hux⟩ := hx
  obtain ⟨z, hz, hzy⟩ := y.2
  refine ⟨z * u * z⁻¹, conj_mem_blockSpecialLinear_of_mem_diagCent hz hu, ?_⟩
  simp only [map_mul, map_inv, hzy, hux, Subgroup.coe_mul, Subgroup.coe_inv]

theorem commutator_comap_centralizer_le
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hδ : ∀ e ∈ S, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ) :
    ⁅(Subgroup.centralizer S).comap ψ, (Subgroup.centralizer S).comap ψ⁆ ≤ diagCent F S δ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy e he
  have key : ∀ w : Matrix.SpecialLinearGroup (Fin (m + 1)) F, ψ w ∈ Subgroup.centralizer S →
      ∃ c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F),
        InnerDiagA.conjSL (InnerDiagA.diagGL (δ e)) w = c * w :=
    fun w hw => ⟨_, conjSL_mul_inv_mem_center hker hδ hw he, by group⟩
  obtain ⟨c, hc, hcx⟩ := key x hx
  obtain ⟨c', hc', hcy⟩ := key y hy
  rw [map_commutatorElement, hcx, hcy, commutatorElement_mul_left_of_mem_center hc,
    commutatorElement_mul_right_of_mem_center hc']

theorem le_map_diagCent
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hδ : ∀ e ∈ S, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ) {J : Subgroup G}
    (hJY : J ≤ ψ.range ⊓ Subgroup.centralizer S) (hJJ : ⁅J, J⁆ = J) :
    J ≤ (diagCent F S δ).map ψ := by
  have hJr : J ≤ ψ.range := hJY.trans inf_le_left
  have hJC : J.comap ψ ≤ (Subgroup.centralizer S).comap ψ :=
    Subgroup.comap_mono (hJY.trans inf_le_right)
  calc J = ⁅J, J⁆ := hJJ.symm
    _ = ⁅(J.comap ψ).map ψ, (J.comap ψ).map ψ⁆ := by rw [Subgroup.map_comap_eq_self hJr]
    _ = (⁅J.comap ψ, J.comap ψ⁆).map ψ := (Subgroup.map_commutator _ _ _).symm
    _ ≤ (diagCent F S δ).map ψ := Subgroup.map_mono
      ((Subgroup.commutator_mono hJC hJC).trans (commutator_comap_centralizer_le hker hδ))

theorem offDiag_eq_zero_of_mem_centralizer [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {z : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hz : z ∈ diagCent F S δ)
    (hc : ∀ i, ψ z ∈ Subgroup.centralizer
      (((blockSpecialLinear (K := F) (diagClass S δ i)).map ψ : Subgroup G) : Set G))
    (a b : Fin (m + 1)) (hab : a ≠ b) : (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = 0 := by
  by_contra h0
  have hba : b ≠ a := Ne.symm hab
  have hmem : a ∈ diagClass S δ b :=
    mem_diagClass.mpr fun e he => eq_of_mem_diagCent hz h0 he
  have ht : Matrix.SpecialLinearGroup.transvection hba (1 : F) ∈
      blockSpecialLinear (diagClass S δ b) :=
    transvection_mem_blockSpecialLinear hba (self_mem_diagClass S δ b) hmem 1
  have h1 := Subgroup.mem_centralizer_iff.mp (hc b) _ ⟨_, ht, rfl⟩
  have h2 := mul_transvection_comm_of_map hker hba h1.symm
  have h3 : (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (1 + single b a 1) =
      (1 + single b a 1) * (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) h2
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
      using h
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h3
  have h5 := add_left_cancel h3
  have h4 := congrFun (congrFun h5 a) a
  rw [mul_single_apply_same, mul_one, single_mul_apply_of_ne _ _ _ _ _ hab] at h4
  exact h0 h4

theorem exists_le_map_blockSpecialLinear [CharP F 2] [Finite G]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hδ : ∀ e ∈ S, (e, InnerDiagA.diagGL (δ e)) ∈ LinFusion.ggInducedPairs ψ) {J : Subgroup G}
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer S)) :
    ∃ i, J ≤ (blockSpecialLinear (K := F) (diagClass S δ i)).map ψ := by
  by_contra hno
  push Not at hno
  have hcomm : ∀ i, ⁅J, (blockSpecialLinear (K := F) (diagClass S δ i)).map ψ⁆ = ⊥ := fun i =>
    (isComponentOf_le_or_commutator_eq_bot hJ
      (isSubnormal_map_blockSpecialLinear hker hδ i)).resolve_left (hno i)
  have hJD := le_map_diagCent hker hδ hJ.1 (commutator_self_eq_of_isQuasisimple hJ.2.2)
  have hdiag : ∀ x ∈ J, ∃ z : Matrix.SpecialLinearGroup (Fin (m + 1)) F, ψ z = x ∧
      ∀ a b, a ≠ b → (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hJD hx
    exact ⟨z, rfl, offDiag_eq_zero_of_mem_centralizer hker hz fun i =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm i) hx⟩
  apply commutator_ne_bot_of_isQuasisimple hJ.2.2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨z₁, rfl, hz₁⟩ := hdiag x hx
  obtain ⟨z₂, rfl, hz₂⟩ := hdiag y hy
  rw [← map_mul, ← map_mul, mul_comm_of_offDiag_eq_zero hz₂ hz₁]

end Psi

end LinTorus

end CFSG.StandardType
