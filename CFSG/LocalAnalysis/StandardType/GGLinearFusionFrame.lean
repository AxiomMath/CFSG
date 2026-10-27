module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.LinearPilot Matrix

section Abstract

variable {G : Type*} [Group G]

theorem mem_normalizer_of_le_abelian {p : ℕ} {Bs T : Subgroup G} (hBT : Bs ≤ T)
    (hT : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) {w : G}
    (hw : w ∈ Subgroup.normalizer (T : Set G)) : w ∈ Subgroup.normalizer (Bs : Set G) := by
  have key : ∀ v ∈ Subgroup.normalizer (T : Set G), ∀ b ∈ Bs, v * b * v⁻¹ ∈ Bs := by
    intro v hv b hb
    have hk : v * b * v⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hv b).mp (hBT hb)
    refine hSC _ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact hT c (hBT hc) _ hk
    · rw [conj_pow, hexp b hb, mul_one, mul_inv_cancel]
  refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨key w hw b, fun hb => ?_⟩
  have h := key w⁻¹ (Subgroup.inv_mem _ hw) _ hb
  rwa [inv_inv, show w⁻¹ * (w * b * w⁻¹) * w = b by group] at h

end Abstract

namespace LinFusion

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem diagGL_one : InnerDiagA.diagGL (1 : Fin (m + 1) → Fˣ) = 1 := by
  apply Units.ext
  rw [InnerDiagA.coe_diagGL]
  simp

theorem diagGL_mul (d e : Fin (m + 1) → Fˣ) :
    InnerDiagA.diagGL (d * e) = InnerDiagA.diagGL d * InnerDiagA.diagGL e := by
  apply Units.ext
  rw [Units.val_mul, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL,
    diagonal_mul_diagonal]
  simp

theorem diagGL_inv (d : Fin (m + 1) → Fˣ) :
    InnerDiagA.diagGL d⁻¹ = (InnerDiagA.diagGL d)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagGL_mul, inv_mul_cancel, diagGL_one])

theorem diagGL_mul_comm (d e : Fin (m + 1) → Fˣ) :
    InnerDiagA.diagGL d * InnerDiagA.diagGL e = InnerDiagA.diagGL e * InnerDiagA.diagGL d := by
  rw [← diagGL_mul, ← diagGL_mul, mul_comm]

@[expose] noncomputable def ggFrameDiag (P : GL (Fin (m + 1)) F) (d : Fin (m + 1) → Fˣ) :
    GL (Fin (m + 1)) F :=
  P⁻¹ * InnerDiagA.diagGL d * P

theorem ggFrameDiag_mul (P : GL (Fin (m + 1)) F) (d e : Fin (m + 1) → Fˣ) :
    ggFrameDiag P (d * e) = ggFrameDiag P d * ggFrameDiag P e := by
  simp only [ggFrameDiag, diagGL_mul]
  group

theorem ggFrameDiag_inv (P : GL (Fin (m + 1)) F) (d : Fin (m + 1) → Fˣ) :
    ggFrameDiag P d⁻¹ = (ggFrameDiag P d)⁻¹ := by
  simp only [ggFrameDiag, diagGL_inv]
  group

theorem ggFrameDiag_mul_comm (P : GL (Fin (m + 1)) F) (d e : Fin (m + 1) → Fˣ) :
    ggFrameDiag P d * ggFrameDiag P e = ggFrameDiag P e * ggFrameDiag P d := by
  rw [← ggFrameDiag_mul, ← ggFrameDiag_mul, mul_comm]

theorem mem_centralizer_of_mem_ggInducedPairs_one {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    {z : G} (h : (z, (1 : GL (Fin (m + 1)) F)) ∈ ggInducedPairs ψ) :
    z ∈ Subgroup.centralizer (ψ.range : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  have h1 := mem_ggInducedPairs.mp h u
  rw [conjSL_one] at h1
  calc ψ u * z = z * ψ u * z⁻¹ * z := by rw [h1]
    _ = z * ψ u := by group

variable (F) in
@[expose] def ggFrameTorus (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (P : GL (Fin (m + 1)) F) : Subgroup G where
  carrier := {g | ∃ d : Fin (m + 1) → Fˣ, (g, ggFrameDiag P d) ∈ ggInducedPairs ψ}
  one_mem' := ⟨1, by
    rw [ggFrameDiag, diagGL_one, mul_one, inv_mul_cancel]
    exact (ggInducedPairs ψ).one_mem⟩
  mul_mem' := by
    rintro g h ⟨d, hd⟩ ⟨e, he⟩
    refine ⟨d * e, ?_⟩
    rw [ggFrameDiag_mul]
    exact (ggInducedPairs ψ).mul_mem hd he
  inv_mem' := by
    rintro g ⟨d, hd⟩
    refine ⟨d⁻¹, ?_⟩
    rw [ggFrameDiag_inv]
    exact (ggInducedPairs ψ).inv_mem hd

theorem ggFrameTorus_comm {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {P : GL (Fin (m + 1)) F} {g h : G}
    (hg : g ∈ ggFrameTorus F ψ P) (hh : h ∈ ggFrameTorus F ψ P) : g * h = h * g := by
  obtain ⟨d, hd⟩ := hg
  obtain ⟨e, he⟩ := hh
  have hc := (ggInducedPairs ψ).mul_mem ((ggInducedPairs ψ).mul_mem hd he)
    ((ggInducedPairs ψ).inv_mem ((ggInducedPairs ψ).mul_mem he hd))
  have h1 : ((g, ggFrameDiag P d) * (h, ggFrameDiag P e) *
      ((h, ggFrameDiag P e) * (g, ggFrameDiag P d))⁻¹ : G × GL (Fin (m + 1)) F) =
      (g * h * (h * g)⁻¹, 1) := by
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, ggFrameDiag_mul_comm P d e,
      mul_inv_cancel]
  rw [h1] at hc
  have h2 := mem_centralizer_of_mem_ggInducedPairs_one hc
  rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at h2
  exact h2

theorem permMatrix_mul_mul_permMatrix_inv (σ : Equiv.Perm (Fin (m + 1)))
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    σ.permMatrix F * A * (σ⁻¹).permMatrix F = A.submatrix σ σ := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem toGL_ggPermSL_conj_diagGL [CharP F 2] (σ : Equiv.Perm (Fin (m + 1)))
    (d : Fin (m + 1) → Fˣ) :
    (SpecialLinearGroup.toGL (ggPermSL (F := F) σ))⁻¹ * InnerDiagA.diagGL d *
      SpecialLinearGroup.toGL (ggPermSL σ) = InnerDiagA.diagGL (fun k => d (σ⁻¹ k)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, ggPermSL_inv,
    SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_GL_coe_matrix,
    InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL]
  change (σ⁻¹).permMatrix F * _ * σ.permMatrix F = _
  have h := permMatrix_mul_mul_permMatrix_inv σ⁻¹ (diagonal fun k => (d k : F))
  rw [inv_inv] at h
  rw [h, submatrix_diagonal_equiv]
  rfl

variable (F) in
@[expose] noncomputable def ggFramePermSL [CharP F 2] (P : GL (Fin (m + 1)) F)
    (σ : Equiv.Perm (Fin (m + 1))) : SpecialLinearGroup (Fin (m + 1)) F :=
  InnerDiagA.conjSL P⁻¹ (ggPermSL σ)

theorem toGL_ggFramePermSL [CharP F 2] (P : GL (Fin (m + 1)) F) (σ : Equiv.Perm (Fin (m + 1))) :
    SpecialLinearGroup.toGL (ggFramePermSL F P σ) =
      P⁻¹ * SpecialLinearGroup.toGL (ggPermSL σ) * P := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, ggFramePermSL, InnerDiagA.coe_conjSL, inv_inv,
    Units.val_mul, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix]

theorem ggFramePermSL_inv [CharP F 2] (P : GL (Fin (m + 1)) F) (σ : Equiv.Perm (Fin (m + 1))) :
    ggFramePermSL F P σ⁻¹ = (ggFramePermSL F P σ)⁻¹ := by
  rw [ggFramePermSL, ggFramePermSL, ← ggPermSL_inv, map_inv]

theorem toGL_ggFramePermSL_conj [CharP F 2] (P : GL (Fin (m + 1)) F)
    (σ : Equiv.Perm (Fin (m + 1))) (d : Fin (m + 1) → Fˣ) :
    (SpecialLinearGroup.toGL (ggFramePermSL F P σ))⁻¹ * ggFrameDiag P d *
      SpecialLinearGroup.toGL (ggFramePermSL F P σ) = ggFrameDiag P (fun k => d (σ⁻¹ k)) := by
  rw [toGL_ggFramePermSL, ggFrameDiag, ggFrameDiag, ← toGL_ggPermSL_conj_diagGL σ d]
  group

theorem mem_ggInducedPairs_toGL (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (s : SpecialLinearGroup (Fin (m + 1)) F) :
    (ψ s, SpecialLinearGroup.toGL s) ∈ ggInducedPairs ψ := by
  intro u
  show ψ s * ψ u * (ψ s)⁻¹ = ψ (InnerDiagA.conjSL (SpecialLinearGroup.toGL s) u)
  rw [conjSL_toGL, map_mul, map_mul, map_inv]

theorem inv_mul_mul_mem_ggFrameTorus [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    {P : GL (Fin (m + 1)) F} (σ : Equiv.Perm (Fin (m + 1))) {g : G}
    (hg : g ∈ ggFrameTorus F ψ P) :
    (ψ (ggFramePermSL F P σ))⁻¹ * g * ψ (ggFramePermSL F P σ) ∈ ggFrameTorus F ψ P := by
  obtain ⟨d, hd⟩ := hg
  refine ⟨fun k => d (σ⁻¹ k), ?_⟩
  have h := (ggInducedPairs ψ).mul_mem ((ggInducedPairs ψ).mul_mem
    ((ggInducedPairs ψ).inv_mem (mem_ggInducedPairs_toGL ψ (ggFramePermSL F P σ))) hd)
    (mem_ggInducedPairs_toGL ψ (ggFramePermSL F P σ))
  rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, toGL_ggFramePermSL_conj] at h
  exact h

theorem ggFramePerm_mem_normalizer [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    {P : GL (Fin (m + 1)) F} (σ : Equiv.Perm (Fin (m + 1))) :
    ψ (ggFramePermSL F P σ) ∈ Subgroup.normalizer (ggFrameTorus F ψ P : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · have h := inv_mul_mul_mem_ggFrameTorus σ⁻¹ hg
    rwa [ggFramePermSL_inv, map_inv, inv_inv] at h
  · have h := inv_mul_mul_mem_ggFrameTorus σ hg
    rwa [show (ψ (ggFramePermSL F P σ))⁻¹ * (ψ (ggFramePermSL F P σ) * g *
      (ψ (ggFramePermSL F P σ))⁻¹) * ψ (ggFramePermSL F P σ) = g by group] at h

variable (F) in
@[expose] noncomputable def ggFrameBlock (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (P : GL (Fin (m + 1)) F) (I : Finset (Fin (m + 1))) : Subgroup G :=
  (blockSpecialLinear (K := F) I).map (ψ.comp (InnerDiagA.conjSL P⁻¹))

theorem conjSL_diagGL_of_mem_blockSpecialLinear {e : Fin (m + 1) → Fˣ} {I : Finset (Fin (m + 1))}
    (he : ∀ i ∈ I, ∀ j ∈ I, e i = e j) {u : SpecialLinearGroup (Fin (m + 1)) F}
    (hu : u ∈ blockSpecialLinear I) : InnerDiagA.conjSL (InnerDiagA.diagGL e) u = u := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases hab : a ∈ I ∧ b ∈ I
  · rw [he a hab.1 b hab.2, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  · have h1 := hu a b (not_and_or.mp hab)
    rw [h1]
    by_cases hab' : a = b
    · subst hab'
      rw [one_apply_eq, mul_one, Units.mul_inv]
    · rw [one_apply_ne hab', mul_zero, zero_mul]

theorem mem_centralizer_ggFrameBlock {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    {P : GL (Fin (m + 1)) F} {I : Finset (Fin (m + 1))} {g : G} {e : Fin (m + 1) → Fˣ}
    (hg : (g, ggFrameDiag P e) ∈ ggInducedPairs ψ) (he : ∀ i ∈ I, ∀ j ∈ I, e i = e j) :
    g ∈ Subgroup.centralizer (ggFrameBlock F ψ P I : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  have h1 := mem_ggInducedPairs.mp hg (InnerDiagA.conjSL P⁻¹ u)
  rw [← conjSL_mul, ggFrameDiag, mul_assoc, mul_assoc, mul_inv_cancel, mul_one, conjSL_mul,
    conjSL_diagGL_of_mem_blockSpecialLinear he hu] at h1
  simp only [MonoidHom.comp_apply]
  calc ψ (InnerDiagA.conjSL P⁻¹ u) * g = g * (ψ (InnerDiagA.conjSL P⁻¹ u) * g⁻¹) * g := by
        rw [h1]
    _ = g * ψ (InnerDiagA.conjSL P⁻¹ u) := by group

theorem exists_perm_mapsTo {n : ℕ} {I₀ I : Finset (Fin n)} (h : I₀.card ≤ I.card) :
    ∃ τ : Equiv.Perm (Fin n), ∀ i ∈ I₀, τ i ∈ I := by
  classical
  obtain ⟨I', hI'I, hcard⟩ := Finset.exists_subset_card_eq h
  have hc : Fintype.card {x // x ∈ I₀} = Fintype.card {x // x ∈ I'} := by
    rw [Fintype.card_coe, Fintype.card_coe, hcard]
  let e : {x // x ∈ I₀} ≃ {x // x ∈ I'} := Fintype.equivOfCardEq hc
  exact ⟨e.extendSubtype, fun i hi => hI'I (Equiv.extendSubtype_mem e i hi)⟩

theorem exists_frame_conj_mem [CharP F 2] {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {P : GL (Fin (m + 1)) F} {p : ℕ}
    {Bs : Subgroup G} (hBT : Bs ≤ ggFrameTorus F ψ P) (hexp : ∀ b ∈ Bs, b ^ p = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {I₀ I : Finset (Fin (m + 1))} (hcard : I₀.card ≤ I.card) {b : G} (hbB : b ∈ Bs)
    {d : Fin (m + 1) → Fˣ} (hb : (b, ggFrameDiag P d) ∈ ggInducedPairs ψ)
    (hdI : ∀ i ∈ I, ∀ j ∈ I, d i = d j) :
    ∃ w ∈ Subgroup.normalizer (Bs : Set G), w ∈ ψ.range ∧ w⁻¹ * b * w ∈ Bs ∧
      w⁻¹ * b * w ∈ Subgroup.centralizer (ggFrameBlock F ψ P I₀ : Set G) := by
  obtain ⟨τ, hτ⟩ := exists_perm_mapsTo hcard
  set w := ψ (ggFramePermSL F P τ⁻¹) with hw
  have hwN : w ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_le_abelian hBT (fun g hg h hh => ggFrameTorus_comm hC hg hh) hexp hSC
      (ggFramePerm_mem_normalizer τ⁻¹)
  refine ⟨w, hwN, ⟨_, rfl⟩, ?_, ?_⟩
  · have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) b).mp hbB
    rwa [inv_inv] at h
  · have h := (ggInducedPairs ψ).mul_mem ((ggInducedPairs ψ).mul_mem
      ((ggInducedPairs ψ).inv_mem (mem_ggInducedPairs_toGL ψ (ggFramePermSL F P τ⁻¹))) hb)
      (mem_ggInducedPairs_toGL ψ (ggFramePermSL F P τ⁻¹))
    rw [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, toGL_ggFramePermSL_conj] at h
    refine mem_centralizer_ggFrameBlock h fun i hi j hj => ?_
    simp only [inv_inv]
    exact hdI _ (hτ i hi) _ (hτ j hj)

end LinFusion

end CFSG.StandardType
