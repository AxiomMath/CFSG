module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUCompBasic
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSU
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.SeitzReduction.LinearPilot
open scoped commutatorElement

namespace UFusion

open InnerDiagSU

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ} {G : Type*} [Group G]

section Cent

noncomputable abbrev frameHom (Q : GL (Fin (m + 1)) F) : SU σ (m + 1) →* GL (Fin (m + 1)) F :=
  (MulAut.conj Q).toMonoidHom.comp (SU σ (m + 1)).subtype

omit [CharP F 2] in
theorem frameHom_apply (Q : GL (Fin (m + 1)) F) (u : SU σ (m + 1)) :
    frameHom Q u = Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ :=
  rfl

@[expose] def inducedDiag (ψ : SU σ (m + 1) →* G) (Q : GL (Fin (m + 1)) F) (S : Set G) :
    Set (GL (Fin (m + 1)) F) :=
  {A | ∃ g ∈ S, ∃ e : Fin (m + 1) → Fˣ, A = InnerDiagA.diagGL e ∧
    (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ}

@[expose] noncomputable def frameCent (Q : GL (Fin (m + 1)) F) (Δ : Set (GL (Fin (m + 1)) F)) :
    Subgroup (SU σ (m + 1)) :=
  (Subgroup.centralizer Δ).comap (frameHom Q)

omit [CharP F 2] in
theorem mem_frameCent {Q : GL (Fin (m + 1)) F} {Δ : Set (GL (Fin (m + 1)) F)}
    {u : SU σ (m + 1)} :
    u ∈ frameCent Q Δ ↔ ∀ A ∈ Δ, A * (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) =
      (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) * A :=
  Subgroup.mem_centralizer_iff

omit [CharP F 2] in
theorem conjSU_frameDiag_eq_self_iff {Q : GL (Fin (m + 1)) F} {e : Fin (m + 1) → Fˣ}
    (hA : IsJUnitary σ (LinFusion.ggFrameDiag Q e)) (w : SU σ (m + 1)) :
    conjSU (LinFusion.ggFrameDiag Q e) hA w = w ↔
      InnerDiagA.diagGL e * (Q * (w : GL (Fin (m + 1)) F) * Q⁻¹) =
        (Q * (w : GL (Fin (m + 1)) F) * Q⁻¹) * InnerDiagA.diagGL e := by
  rw [Subtype.ext_iff, coe_conjSU, LinFusion.ggFrameDiag]
  constructor
  · intro h
    calc InnerDiagA.diagGL e * (Q * (w : GL (Fin (m + 1)) F) * Q⁻¹) =
        Q * (Q⁻¹ * InnerDiagA.diagGL e * Q * (w : GL (Fin (m + 1)) F) *
          (Q⁻¹ * InnerDiagA.diagGL e * Q)⁻¹) * Q⁻¹ * InnerDiagA.diagGL e := by group
      _ = (Q * (w : GL (Fin (m + 1)) F) * Q⁻¹) * InnerDiagA.diagGL e := by rw [h]
  · intro h
    calc Q⁻¹ * InnerDiagA.diagGL e * Q * (w : GL (Fin (m + 1)) F) *
        (Q⁻¹ * InnerDiagA.diagGL e * Q)⁻¹ =
        Q⁻¹ * (InnerDiagA.diagGL e * (Q * (w : GL (Fin (m + 1)) F) * Q⁻¹)) *
          (InnerDiagA.diagGL e)⁻¹ * Q := by group
      _ = Q⁻¹ * ((Q * (w : GL (Fin (m + 1)) F) * Q⁻¹) * InnerDiagA.diagGL e) *
          (InnerDiagA.diagGL e)⁻¹ * Q := by rw [h]
      _ = (w : GL (Fin (m + 1)) F) := by group

omit [CharP F 2] in
theorem commutatorElement_central_mul {H : Type*} [Group H] {z z' : H}
    (hz : z ∈ Subgroup.center H) (hz' : z' ∈ Subgroup.center H) (u v : H) :
    ⁅z * u, z' * v⁆ = ⁅u, v⁆ := by
  have h1 := Subgroup.mem_center_iff.mp hz
  have h2 := Subgroup.mem_center_iff.mp hz'
  rw [commutatorElement_def, commutatorElement_def]
  calc z * u * (z' * v) * (z * u)⁻¹ * (z' * v)⁻¹ =
      z * (u * (z' * v) * u⁻¹) * z⁻¹ * v⁻¹ * z'⁻¹ := by group
    _ = (u * (z' * v) * u⁻¹) * z * z⁻¹ * v⁻¹ * z'⁻¹ := by rw [h1]
    _ = u * (z' * v) * u⁻¹ * v⁻¹ * z'⁻¹ := by group
    _ = u * (v * z') * u⁻¹ * v⁻¹ * z'⁻¹ := by rw [h2 v]
    _ = u * v * (z' * (u⁻¹ * v⁻¹)) * z'⁻¹ := by group
    _ = u * v * ((u⁻¹ * v⁻¹) * z') * z'⁻¹ := by rw [h2]
    _ = u * v * u⁻¹ * v⁻¹ := by group

omit [CharP F 2] in
theorem conjSU_mul_inv_mem_center {ψ : SU σ (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1))) {g : G} {A : GL (Fin (m + 1)) F}
    (hA : IsJUnitary σ A) (hg : ∀ u, g * ψ u * g⁻¹ = ψ (conjSU A hA u)) {u : SU σ (m + 1)}
    (hu : g * ψ u = ψ u * g) : conjSU A hA u * u⁻¹ ∈ Subgroup.center (SU σ (m + 1)) := by
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, ← hg u, hu, mul_inv_cancel_right, mul_inv_cancel]

end Cent

section Main

variable {ψ : SU σ (m + 1) →* G} {Q : GL (Fin (m + 1)) F} {S : Set G}

omit [CharP F 2] in
theorem commutator_le_map_frameCent (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1))) :
    ⁅ψ.range ⊓ Subgroup.centralizer S, ψ.range ⊓ Subgroup.centralizer S⁆ ≤
      (frameCent Q (inducedDiag ψ Q S)).map ψ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨⟨u, rfl⟩, hxS⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨⟨v, rfl⟩, hyS⟩ := Subgroup.mem_inf.mp hy
  refine ⟨⁅u, v⁆, ?_, map_commutatorElement ψ u v⟩
  rw [SetLike.mem_coe, mem_frameCent]
  rintro _ ⟨g, hgS, e, rfl, hA, hg⟩
  have hu := conjSU_mul_inv_mem_center hker hA hg (Subgroup.mem_centralizer_iff.mp hxS g hgS)
  have hv := conjSU_mul_inv_mem_center hker hA hg (Subgroup.mem_centralizer_iff.mp hyS g hgS)
  rw [← conjSU_frameDiag_eq_self_iff hA, map_commutatorElement,
    show conjSU (LinFusion.ggFrameDiag Q e) hA u =
      (conjSU (LinFusion.ggFrameDiag Q e) hA u * u⁻¹) * u by group,
    show conjSU (LinFusion.ggFrameDiag Q e) hA v =
      (conjSU (LinFusion.ggFrameDiag Q e) hA v * v⁻¹) * v by group]
  exact commutatorElement_central_mul hu hv u v

omit [CharP F 2] in
theorem map_frameCent_le (hS : S ⊆ uFrameTorus ψ Q) :
    (frameCent Q (inducedDiag ψ Q S)).map ψ ≤ ψ.range ⊓ Subgroup.centralizer S := by
  rintro _ ⟨u, hu, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  obtain ⟨e, hA, he⟩ := hS hg
  have h1 := he u
  rw [(conjSU_frameDiag_eq_self_iff hA u).mpr
    (mem_frameCent.mp hu _ ⟨g, hg, e, rfl, hA, he⟩)] at h1
  calc g * ψ u = g * ψ u * g⁻¹ * g := by group
    _ = ψ u * g := by rw [h1]

@[expose] def uRel (ψ : SU σ (m + 1) →* G) (Q : GL (Fin (m + 1)) F) (S : Set G)
    (a b : Fin (m + 1)) : Prop :=
  ∀ g ∈ S, ∀ e : Fin (m + 1) → Fˣ, (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ → e a = e b

@[expose] noncomputable def uClass (ψ : SU σ (m + 1) →* G) (Q : GL (Fin (m + 1)) F) (S : Set G)
    (a : Fin (m + 1)) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter (uRel ψ Q S a)

omit [CharP F 2] in
theorem mem_uClass {a b : Fin (m + 1)} : b ∈ uClass ψ Q S a ↔ uRel ψ Q S a b := by
  classical
  unfold uClass
  simp

omit [CharP F 2] in
theorem self_mem_uClass (a : Fin (m + 1)) : a ∈ uClass ψ Q S a :=
  mem_uClass.mpr fun _ _ _ _ => rfl

omit [CharP F 2] in
theorem const_on_uClass {g : G} (hg : g ∈ S) {e : Fin (m + 1) → Fˣ}
    (he : (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ) (a : Fin (m + 1)) :
    ∀ i ∈ uClass ψ Q S a, ∀ j ∈ uClass ψ Q S a, e i = e j := fun _ hi _ hj =>
  ((mem_uClass.mp hi) g hg e he).symm.trans ((mem_uClass.mp hj) g hg e he)

omit [CharP F 2] in
theorem exists_ne_of_notMem_uClass {a b : Fin (m + 1)} (hb : b ∉ uClass ψ Q S a) :
    ∃ g ∈ S, ∃ e : Fin (m + 1) → Fˣ, (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ ∧
      e a ≠ e b := by
  rw [mem_uClass] at hb
  unfold uRel at hb
  simp only [not_forall] at hb
  obtain ⟨g, hg, e, he, hne⟩ := hb
  exact ⟨g, hg, e, he, hne⟩

omit [CharP F 2] in
theorem apply_eq_zero_of_comm_diagGL {e : Fin (m + 1) → Fˣ} {X : GL (Fin (m + 1)) F}
    (h : InnerDiagA.diagGL e * X = X * InnerDiagA.diagGL e) {i j : Fin (m + 1)}
    (hij : e i ≠ e j) : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
  have h1 := congrArg
    (fun A : GL (Fin (m + 1)) F => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j) h
  simp only [Units.val_mul, InnerDiagA.coe_diagGL, diagonal_mul, mul_diagonal] at h1
  have h2 : (((e i : Fˣ) : F) - ((e j : Fˣ) : F)) *
      (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
    rw [sub_mul, h1, mul_comm, sub_self]
  have h3 : ((e i : Fˣ) : F) - ((e j : Fˣ) : F) ≠ 0 := sub_ne_zero.mpr fun h => hij (Units.ext h)
  exact (mul_eq_zero.mp h2).resolve_left h3

omit [CharP F 2] in
theorem suBlock_uClass_le_frameCent (a : Fin (m + 1)) :
    suBlock (σ := σ) Q (uClass ψ Q S a) ≤ frameCent Q (inducedDiag ψ Q S) := by
  intro v hv
  rw [mem_frameCent]
  rintro _ ⟨g, hg, e, rfl, he⟩
  exact diagGL_mul_comm_of_mem_glBlock (const_on_uClass hg he a) (mem_suBlock.mp hv)

omit [CharP F 2] in
theorem comm_blockComplProj_of_mem_frameCent {u : SU σ (m + 1)}
    (hu : u ∈ frameCent Q (inducedDiag ψ Q S)) (a : Fin (m + 1)) :
    ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) * blockComplProj (uClass ψ Q S a) =
      blockComplProj (uClass ψ Q S a) *
        ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  ext i j
  rw [blockComplProj, mul_diagonal, diagonal_mul]
  by_cases hij : (i ∈ uClass ψ Q S a ↔ j ∈ uClass ψ Q S a)
  · rw [if_congr hij rfl rfl, mul_comm]
  · have hzero : ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
      by_cases hi : i ∈ uClass ψ Q S a
      · have hj : j ∉ uClass ψ Q S a := fun hj => hij ⟨fun _ => hj, fun _ => hi⟩
        obtain ⟨g, hg, e, he, hne⟩ := exists_ne_of_notMem_uClass hj
        refine apply_eq_zero_of_comm_diagGL (mem_frameCent.mp hu _ ⟨g, hg, e, rfl, he⟩) ?_
        rw [← (mem_uClass.mp hi) g hg e he]
        exact hne
      · have hj : j ∈ uClass ψ Q S a := by
          by_contra hj
          exact hij ⟨fun h => absurd h hi, fun h => absurd h hj⟩
        obtain ⟨g, hg, e, he, hne⟩ := exists_ne_of_notMem_uClass hi
        refine apply_eq_zero_of_comm_diagGL (mem_frameCent.mp hu _ ⟨g, hg, e, rfl, he⟩) ?_
        rw [← (mem_uClass.mp hj) g hg e he]
        exact fun h => hne h.symm
    rw [hzero, zero_mul, mul_zero]

omit [CharP F 2] in
theorem conj_mem_suBlock_uClass {u v : SU σ (m + 1)} (hu : u ∈ frameCent Q (inducedDiag ψ Q S))
    (a : Fin (m + 1)) (hv : v ∈ suBlock Q (uClass ψ Q S a)) :
    u * v * u⁻¹ ∈ suBlock Q (uClass ψ Q S a) := by
  rw [mem_suBlock] at hv ⊢
  set X := Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ with hX
  set Y := Q * (v : GL (Fin (m + 1)) F) * Q⁻¹ with hY
  have e : Q * ((u * v * u⁻¹ : SU σ (m + 1)) : GL (Fin (m + 1)) F) * Q⁻¹ = X * Y * X⁻¹ := by
    rw [hX, hY, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  set P := blockComplProj (K := F) (uClass ψ Q S a)
  have hXP : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * P = P * X :=
    comm_blockComplProj_of_mem_frameCent hu a
  have hXX : ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXX' : (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hXiP : ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * P =
      P * ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    calc ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * P =
        ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (P *
          ((X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F))) := by
          rw [hXX', Matrix.mul_one]
      _ = ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          ((X : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * P) *
            ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
          rw [hXP]; simp only [Matrix.mul_assoc]
      _ = P * ((X⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
          rw [← Matrix.mul_assoc, hXX, Matrix.one_mul]
  obtain ⟨hY1, hY2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hXiP, ← Matrix.mul_assoc,
      Matrix.mul_assoc (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F), hY1, hXP, Matrix.mul_assoc,
      hXX', Matrix.mul_one]
  · rw [Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hXP,
      Matrix.mul_assoc (X : Matrix (Fin (m + 1)) (Fin (m + 1)) F), hY2, hXP, Matrix.mul_assoc,
      hXX', Matrix.mul_one]

omit [CharP F 2] in
theorem normal_subgroupOf_uFrameBlock_uClass (a : Fin (m + 1)) :
    ((uFrameBlock ψ Q (uClass ψ Q S a)).subgroupOf
      ((frameCent Q (inducedDiag ψ Q S)).map ψ)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨s, hs, hsn⟩ := hn
  obtain ⟨u, hu, hug⟩ := g.2
  refine ⟨u * s * u⁻¹, conj_mem_suBlock_uClass hu a hs, ?_⟩
  simp only [map_mul, map_inv, hsn, hug, Subgroup.coe_mul, Subgroup.coe_inv]

omit [CharP F 2] in
theorem le_or_commutator_eq_bot_uClass [Finite G] {L₁ : Subgroup G}
    (hLC : L₁ ≤ (frameCent Q (inducedDiag ψ Q S)).map ψ)
    (hcomp : IsComponentOf L₁ ((frameCent Q (inducedDiag ψ Q S)).map ψ)) (a : Fin (m + 1)) :
    L₁ ≤ uFrameBlock ψ Q (uClass ψ Q S a) ∨ ⁅L₁, uFrameBlock ψ Q (uClass ψ Q S a)⁆ = ⊥ := by
  have hc :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLC).mp hcomp
  rcases CFSG.LocalAnalysis.ComponentInitial.component_normal_subgroup hc
      (normal_subgroupOf_uFrameBlock_uClass a) with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hLC h)
  · right
    have h' := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hLC h
    have hle : uFrameBlock ψ Q (uClass ψ Q S a) ≤ (frameCent Q (inducedDiag ψ Q S)).map ψ :=
      Subgroup.map_mono (suBlock_uClass_le_frameCent a)
    rwa [inf_eq_left.mpr hle] at h'

omit [CharP F 2] in
theorem diagGL_mem_glBlock {e : Fin (m + 1) → Fˣ} {I : Finset (Fin (m + 1))}
    (he : ∀ k, k ∉ I → e k = 1) : InnerDiagA.diagGL e ∈ glBlock I := by
  rw [mem_glBlock]
  intro i j hij
  rw [InnerDiagA.coe_diagGL]
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, one_apply_eq]
    rcases hij with hi | hi <;> rw [he i hi, Units.val_one]
  · rw [diagonal_apply_ne _ h, one_apply_ne h]

theorem apply_eq_zero_of_forall_commute (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1)))
    (hQ : IsUFrame σ Q) {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζσ : σ (ζ : F) * ζ = 1) {u : SU σ (m + 1)}
    (hu : u ∈ frameCent Q (inducedDiag ψ Q S))
    (hcomm : ∀ a, ∀ s ∈ suBlock Q (uClass ψ Q S a), ψ u * ψ s = ψ s * ψ u) {i j : Fin (m + 1)}
    (hij : i ≠ j) :
    ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) j i = 0 := by
  have h1σ : σ ((1 : Fˣ) : F) * ((1 : Fˣ) : F) = 1 := by
    rw [Units.val_one, map_one, one_mul]
  by_cases hj : j ∈ uClass ψ Q S i
  · have hcs : ∀ c : Fˣ, ∀ hc : σ (c : F) * c = 1,
        ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            ((twistGL i j c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          ((twistGL i j c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
      intro c hc
      set s := twistSU hQ i j hc with hs
      have hsB : s ∈ suBlock Q (uClass ψ Q S i) := by
        rw [mem_suBlock, hs, coe_frameSU,
          show Q * (Q⁻¹ * twistGL i j c * Q) * Q⁻¹ = twistGL i j c by group]
        refine (glBlock _).mul_mem (permGL_swap_mem_glBlock (self_mem_uClass i) hj)
          (diagGL_mem_glBlock fun k hk => ?_)
        exact twistVec_other (fun h : k = i => hk (by rw [h]; exact self_mem_uClass i))
          (fun h : k = j => hk (by rw [h]; exact hj)) c
      have h1 := hcomm i s hsB
      have hz : u * s * u⁻¹ * s⁻¹ ∈ Subgroup.center (SU σ (m + 1)) := by
        apply hker
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      have hss : s * s = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hs, coe_frameSU, Subgroup.coe_one]
        calc Q⁻¹ * twistGL i j c * Q * (Q⁻¹ * twistGL i j c * Q) =
            Q⁻¹ * (twistGL i j c * twistGL i j c) * Q := by group
          _ = 1 := by rw [twistGL_mul_self hij]; group
      have hus := commute_of_commutator_mem_center hQ hζ1 hζσ hss hz
      exact comm_of_comm_frameSU hQ _ _ hus
    exact eq_zero_of_comm_twistGL hij (Ne.symm hζ1) (hcs 1 h1σ) (hcs ζ hζσ)
  · obtain ⟨g, hg, e, he, hne⟩ := exists_ne_of_notMem_uClass hj
    exact apply_eq_zero_of_comm_diagGL (mem_frameCent.mp hu _ ⟨g, hg, e, rfl, he⟩)
      fun h => hne h.symm

omit [CharP F 2] in
theorem mul_comm_of_offDiag {X Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hX : ∀ i j, i ≠ j → X j i = 0) (hY : ∀ i j, i ≠ j → Y j i = 0) : X * Y = Y * X := by
  have hXd : X.IsDiag := fun i j hij => hX j i (Ne.symm hij)
  have hYd : Y.IsDiag := fun i j hij => hY j i (Ne.symm hij)
  rw [← hXd.diagonal_diag, ← hYd.diagonal_diag, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem exists_le_uClass_of_isComponentOf [Finite G]
    (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1))) (hQ : IsUFrame σ Q) {ζ : Fˣ} (hζ1 : ζ ≠ 1)
    (hζσ : σ (ζ : F) * ζ = 1) (hS : S ⊆ uFrameTorus ψ Q) {L₁ : Subgroup G}
    (hL : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer S)) :
    ∃ a : Fin (m + 1), L₁ ≤ uFrameBlock ψ Q (uClass ψ Q S a) := by
  have hLC₀ : L₁ ≤ (frameCent Q (inducedDiag ψ Q S)).map ψ := by
    rw [← LinSemisimple.commutator_eq_self_of_isQuasisimple hL.2.2]
    exact (Subgroup.commutator_mono hL.1 hL.1).trans (commutator_le_map_frameCent hker)
  have hcomp : IsComponentOf L₁ ((frameCent Q (inducedDiag ψ Q S)).map ψ) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL hLC₀ (map_frameCent_le hS)
  by_cases hex : ∃ a, L₁ ≤ uFrameBlock ψ Q (uClass ψ Q S a)
  · obtain ⟨a, ha⟩ := hex
    exact ⟨a, ha⟩
  · exfalso
    have hcomm : ∀ a, ⁅L₁, uFrameBlock ψ Q (uClass ψ Q S a)⁆ = ⊥ := fun a =>
      (le_or_commutator_eq_bot_uClass hLC₀ hcomp a).resolve_left fun h => hex ⟨a, h⟩
    have hdiag : ∀ w ∈ frameCent Q (inducedDiag ψ Q S), ψ w ∈ L₁ → ∀ i j : Fin (m + 1), i ≠ j →
        ((Q * (w : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) j i = 0 := by
      intro w hw hwL i j hij
      refine apply_eq_zero_of_forall_commute hker hQ hζ1 hζσ hw (fun a s hs => ?_) hij
      have hsN : ψ s ∈ uFrameBlock ψ Q (uClass ψ Q S a) := Subgroup.mem_map_of_mem ψ hs
      have h1 := Subgroup.commutator_mem_commutator hwL hsN
      rw [hcomm a, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    apply LinSemisimple.false_of_isQuasisimple_of_commute hL.2.2
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := hLC₀ hx
    obtain ⟨v, hv, rfl⟩ := hLC₀ hy
    have hXY := mul_comm_of_offDiag (hdiag u hu hx) (hdiag v hv hy)
    have hXY' : (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) * (Q * (v : GL (Fin (m + 1)) F) * Q⁻¹) =
        (Q * (v : GL (Fin (m + 1)) F) * Q⁻¹) * (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) :=
      Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hXY)
    have huv : u * v = v * u := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      calc (u : GL (Fin (m + 1)) F) * v =
          Q⁻¹ * ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) * (Q * (v : GL (Fin (m + 1)) F) * Q⁻¹)) *
            Q := by group
        _ = Q⁻¹ * ((Q * (v : GL (Fin (m + 1)) F) * Q⁻¹) *
            (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹)) * Q := by rw [hXY']
        _ = (v : GL (Fin (m + 1)) F) * u := by group
    rw [← map_mul, huv, map_mul]

theorem exists_le_uFrameBlock_of_isComponentOf [Finite G]
    (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1))) (hQ : IsUFrame σ Q) {ζ : Fˣ} (hζ1 : ζ ≠ 1)
    (hζσ : σ (ζ : F) * ζ = 1) (hS : S ⊆ uFrameTorus ψ Q) {L₁ : Subgroup G}
    (hL : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer S)) :
    ∃ I : Finset (Fin (m + 1)), L₁ ≤ uFrameBlock ψ Q I ∧
      ∀ g ∈ S, ∃ e : Fin (m + 1) → Fˣ, (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ ∧
        ∀ i ∈ I, ∀ j ∈ I, e i = e j := by
  obtain ⟨a, ha⟩ :=
    exists_le_uClass_of_isComponentOf hker hQ hζ1 hζσ hS hL
  refine ⟨uClass ψ Q S a, ha, fun g hg => ?_⟩
  obtain ⟨e, he⟩ := hS hg
  exact ⟨e, he, const_on_uClass hg he a⟩

end Main

end UFusion

theorem ggUnitarySemisimpleComponentInput_holds : GGUnitarySemisimpleComponentInput := by
  intro G _ _ m f hf ψ hker Q hQ S hS L₁ hL
  have h2 : 0 < 2 ^ f := by positivity
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ f + 1 ≠ 1 by omega)
  obtain ⟨ζ, hζ1, -, hζσ⟩ := UFusion.exists_zeta hf hr hrd
  exact UFusion.exists_le_uFrameBlock_of_isComponentOf hker hQ hζ1 hζσ hS hL

section Inputs

theorem ggStepTwoUnitaryFusionEqInput_of_bstarFrame (hT : GGUnitaryBstarFrameInput) :
    GGStepTwoUnitaryFusionEqInput :=
  ggStepTwoUnitaryFusionEqInput_of_frame hT ggUnitarySemisimpleComponentInput_holds

theorem ggStepTwoLinearFusionEqInput_of_bstarFrame (hT : GGUnitaryBstarFrameInput) :
    GGStepTwoLinearFusionEqInput :=
  ggStepTwoLinearFusionEqInput_of_frame hT ggUnitarySemisimpleComponentInput_holds

theorem ggStepTwoUnitaryFusionLargeInput_of_bstarFrame (hT : GGUnitaryBstarFrameInput)
    (hI1 : GGUnitaryBstarCentralizerInput) : GGStepTwoUnitaryFusionLargeInput :=
  ggStepTwoUnitaryFusionLargeInput_of_frame hT ggUnitarySemisimpleComponentInput_holds hI1

end Inputs

end CFSG.StandardType
