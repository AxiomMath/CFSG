module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSU
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionRich

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LieType.Universal.Unitary

namespace UFusion

open InnerDiagSU

section Unitary

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem isJUnitary_one : IsJUnitary σ (1 : GL (Fin n) F) := by
  unfold IsJUnitary
  rw [Units.val_one, conjTr_one, Matrix.one_mul, Matrix.mul_one]

theorem isJUnitary_mul {A B : GL (Fin n) F} (hA : IsJUnitary σ A) (hB : IsJUnitary σ B) :
    IsJUnitary σ (A * B) := by
  unfold IsJUnitary at hA hB ⊢
  rw [Units.val_mul, conjTr_mul]
  calc conjTr σ (B : Matrix (Fin n) (Fin n) F) * conjTr σ (A : Matrix (Fin n) (Fin n) F) *
        antidiag n * ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F))
      = conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
            (A : Matrix (Fin n) (Fin n) F)) * (B : Matrix (Fin n) (Fin n) F) := by
        simp only [Matrix.mul_assoc]
    _ = antidiag n := by rw [hA, hB]

theorem conjSU_one (u : SU σ n) : conjSU (1 : GL (Fin n) F) isJUnitary_one u = u :=
  Subtype.ext (by rw [coe_conjSU, one_mul, inv_one, mul_one])

theorem conjSU_mul {A B : GL (Fin n) F} (hA : IsJUnitary σ A) (hB : IsJUnitary σ B)
    (u : SU σ n) : conjSU (A * B) (isJUnitary_mul hA hB) u = conjSU A hA (conjSU B hB u) :=
  Subtype.ext (by rw [coe_conjSU, coe_conjSU, coe_conjSU]; group)

theorem conjSU_conjSU_inv {A : GL (Fin n) F} (hA : IsJUnitary σ A) (u : SU σ n) :
    conjSU A hA (conjSU A⁻¹ hA.inv u) = u :=
  Subtype.ext (by rw [coe_conjSU, coe_conjSU]; group)

theorem isJUnitary_coe (s : SU σ n) : IsJUnitary σ (s : GL (Fin n) F) :=
  (mem_SU.mp s.2).2

theorem conjSU_coe (s u : SU σ n) : conjSU (s : GL (Fin n) F) (isJUnitary_coe s) u = s * u * s⁻¹ :=
  Subtype.ext (by rw [coe_conjSU, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv])

@[expose] def IsUFrame (σ : F ≃+* F) (Q : GL (Fin n) F) : Prop :=
  conjTr σ (Q : Matrix (Fin n) (Fin n) F) * (Q : Matrix (Fin n) (Fin n) F) = antidiag n

theorem isJUnitary_frame {Q M : GL (Fin n) F} (hQ : IsUFrame σ Q) (hM : IsIdUnitary σ M) :
    IsJUnitary σ (Q⁻¹ * M * Q) := by
  unfold IsJUnitary
  unfold IsIdUnitary at hM
  unfold IsUFrame at hQ
  rw [Units.val_mul, Units.val_mul]
  set Qm := (Q : Matrix (Fin n) (Fin n) F)
  set Qi := ((Q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Mm := (M : Matrix (Fin n) (Fin n) F)
  have hQQ : Qm * Qi = 1 := val_mul_val_inv Q
  calc conjTr σ (Qi * Mm * Qm) * antidiag n * (Qi * Mm * Qm)
      = conjTr σ (Qi * Mm * Qm) * (conjTr σ Qm * Qm) * (Qi * Mm * Qm) := by rw [hQ]
    _ = conjTr σ Qm * (conjTr σ Mm * (conjTr σ (Qm * Qi) * (Qm * Qi)) * Mm) * Qm := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = antidiag n := by
        rw [hQQ, conjTr_one, Matrix.one_mul, Matrix.mul_one, hM, Matrix.mul_one, hQ]

theorem isIdUnitary_diagGL {m : ℕ} {d : Fin (m + 1) → Fˣ} (hd : ∀ i, σ (d i) * d i = 1) :
    IsIdUnitary σ (InnerDiagA.diagGL d) := by
  unfold IsIdUnitary
  rw [InnerDiagA.coe_diagGL, conjTr, diagonal_map (map_zero σ), diagonal_transpose,
    diagonal_mul_diagonal]
  have h : (fun i => σ ((d i : Fˣ) : F) * ((d i : Fˣ) : F)) = fun _ => (1 : F) := funext hd
  rw [h, diagonal_one]

theorem permMatrix_map (τ : Equiv.Perm (Fin n)) : (τ.permMatrix F).map σ = τ.permMatrix F := by
  ext i j
  rw [Matrix.map_apply]
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem conjTr_permMatrix_mul (τ : Equiv.Perm (Fin n)) :
    conjTr σ (τ.permMatrix F) * τ.permMatrix F = 1 := by
  rw [conjTr, permMatrix_map, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel,
    permMatrix_one]

end Unitary

section Induced

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ} {G : Type*} [Group G]

@[expose] def suInducedPairs (ψ : SU σ n →* G) : Subgroup (G × GL (Fin n) F) where
  carrier := {q | ∃ hA : IsJUnitary σ q.2, ∀ u, q.1 * ψ u * q.1⁻¹ = ψ (conjSU q.2 hA u)}
  one_mem' := ⟨isJUnitary_one, fun u => by
    rw [Prod.fst_one, one_mul, inv_one, mul_one]
    exact congrArg ψ (conjSU_one u).symm⟩
  mul_mem' := by
    rintro ⟨a, A⟩ ⟨b, B⟩ ⟨hA, ha⟩ ⟨hB, hb⟩
    refine ⟨isJUnitary_mul hA hB, fun u => ?_⟩
    show a * b * ψ u * (a * b)⁻¹ = ψ (conjSU (A * B) _ u)
    rw [conjSU_mul hA hB, ← ha, ← hb]
    group
  inv_mem' := by
    rintro ⟨a, A⟩ ⟨hA, ha⟩
    refine ⟨hA.inv, fun u => ?_⟩
    show a⁻¹ * ψ u * a⁻¹⁻¹ = ψ (conjSU A⁻¹ hA.inv u)
    have h : a * ψ (conjSU A⁻¹ hA.inv u) * a⁻¹ = ψ u := by
      have h1 := ha (conjSU A⁻¹ hA.inv u)
      rwa [conjSU_conjSU_inv] at h1
    rw [← h]
    group

theorem mem_suInducedPairs {ψ : SU σ n →* G} {y : G} {A : GL (Fin n) F} :
    (y, A) ∈ suInducedPairs ψ ↔
      ∃ hA : IsJUnitary σ A, ∀ u, y * ψ u * y⁻¹ = ψ (conjSU A hA u) :=
  Iff.rfl

theorem mem_suInducedPairs_coe (ψ : SU σ n →* G) (s : SU σ n) :
    (ψ s, (s : GL (Fin n) F)) ∈ suInducedPairs ψ :=
  ⟨isJUnitary_coe s, fun u => by rw [conjSU_coe, map_mul, map_mul, map_inv]⟩

theorem mem_centralizer_of_mem_suInducedPairs_one {ψ : SU σ n →* G} {z : G}
    (h : (z, (1 : GL (Fin n) F)) ∈ suInducedPairs ψ) :
    z ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨h1, h⟩ := h
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  have h2 := h u
  rw [show conjSU (1 : GL (Fin n) F) h1 u = u from conjSU_one u] at h2
  calc ψ u * z = z * ψ u * z⁻¹ * z := by rw [h2]
    _ = z * ψ u := by group

theorem conj_mem_suInducedPairs {ψ : SU σ n →* G} {y : G} {A : GL (Fin n) F}
    (h : (y, A) ∈ suInducedPairs ψ) (s : SU σ n) :
    ((ψ s)⁻¹ * y * ψ s, (s : GL (Fin n) F)⁻¹ * A * s) ∈ suInducedPairs ψ := by
  have h1 := (suInducedPairs ψ).mul_mem ((suInducedPairs ψ).mul_mem
    ((suInducedPairs ψ).inv_mem (mem_suInducedPairs_coe ψ s)) h) (mem_suInducedPairs_coe ψ s)
  rwa [Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk] at h1

end Induced

section Torus

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ} {G : Type*} [Group G]

@[expose] def uFrameTorus (ψ : SU σ (m + 1) →* G) (Q : GL (Fin (m + 1)) F) : Subgroup G where
  carrier := {g | ∃ d : Fin (m + 1) → Fˣ, (g, LinFusion.ggFrameDiag Q d) ∈ suInducedPairs ψ}
  one_mem' := ⟨1, by
    rw [LinFusion.ggFrameDiag_one, ← Prod.one_eq_mk]
    exact (suInducedPairs ψ).one_mem⟩
  mul_mem' := by
    rintro g h ⟨d, hd⟩ ⟨e, he⟩
    have h1 := (suInducedPairs ψ).mul_mem hd he
    rw [Prod.mk_mul_mk, ← LinFusion.ggFrameDiag_mul] at h1
    exact ⟨d * e, h1⟩
  inv_mem' := by
    rintro g ⟨d, hd⟩
    have h1 := (suInducedPairs ψ).inv_mem hd
    rw [Prod.inv_mk, ← LinFusion.ggFrameDiag_inv] at h1
    exact ⟨d⁻¹, h1⟩

theorem uFrameTorus_comm {ψ : SU σ (m + 1) →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Q : GL (Fin (m + 1)) F} {g h : G}
    (hg : g ∈ uFrameTorus ψ Q) (hh : h ∈ uFrameTorus ψ Q) : g * h = h * g := by
  obtain ⟨d, hd⟩ := hg
  obtain ⟨e, he⟩ := hh
  have hc := (suInducedPairs ψ).mul_mem ((suInducedPairs ψ).mul_mem hd he)
    ((suInducedPairs ψ).inv_mem ((suInducedPairs ψ).mul_mem he hd))
  have h1 : ((g, LinFusion.ggFrameDiag Q d) * (h, LinFusion.ggFrameDiag Q e) *
      ((h, LinFusion.ggFrameDiag Q e) * (g, LinFusion.ggFrameDiag Q d))⁻¹ :
        G × GL (Fin (m + 1)) F) = (g * h * (h * g)⁻¹, 1) := by
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk,
      LinFusion.ggFrameDiag_mul_comm Q d e, mul_inv_cancel]
  rw [h1] at hc
  have h2 := mem_centralizer_of_mem_suInducedPairs_one hc
  rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at h2
  exact h2

end Torus

section Perm

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ} {G : Type*} [Group G]

noncomputable abbrev permGL (τ : Equiv.Perm (Fin (m + 1))) : GL (Fin (m + 1)) F :=
  Matrix.SpecialLinearGroup.toGL (ggPermSL τ)

theorem coe_permGL (τ : Equiv.Perm (Fin (m + 1))) :
    ((permGL τ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      τ.permMatrix F :=
  rfl

theorem permGL_inv (τ : Equiv.Perm (Fin (m + 1))) :
    permGL (F := F) τ⁻¹ = (permGL τ)⁻¹ := by
  rw [permGL, permGL, ← ggPermSL_inv, map_inv]

theorem isIdUnitary_permGL (τ : Equiv.Perm (Fin (m + 1))) :
    IsIdUnitary σ (permGL (F := F) τ) :=
  conjTr_permMatrix_mul τ

omit [CharP F 2] in
theorem det_frame_conj (Q M : GL (Fin (m + 1)) F) :
    ((Q⁻¹ * M * Q : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det =
      (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det := by
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]

@[expose] noncomputable def uFramePerm {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q)
    (τ : Equiv.Perm (Fin (m + 1))) : SU σ (m + 1) :=
  ⟨Q⁻¹ * permGL τ * Q, mem_SU.mpr ⟨by rw [det_frame_conj]; exact det_permMatrix_charTwo τ,
    isJUnitary_frame hQ (isIdUnitary_permGL τ)⟩⟩

theorem coe_uFramePerm {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q)
    (τ : Equiv.Perm (Fin (m + 1))) :
    ((uFramePerm hQ τ : SU σ (m + 1)) : GL (Fin (m + 1)) F) = Q⁻¹ * permGL τ * Q :=
  rfl

theorem uFramePerm_inv {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q)
    (τ : Equiv.Perm (Fin (m + 1))) : uFramePerm hQ τ⁻¹ = (uFramePerm hQ τ)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, coe_uFramePerm, coe_uFramePerm, permGL_inv]
  group

theorem uFramePerm_conj {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q)
    (τ : Equiv.Perm (Fin (m + 1))) (d : Fin (m + 1) → Fˣ) :
    ((uFramePerm hQ τ : SU σ (m + 1)) : GL (Fin (m + 1)) F)⁻¹ * LinFusion.ggFrameDiag Q d *
      (uFramePerm hQ τ : SU σ (m + 1)) = LinFusion.ggFrameDiag Q (fun k => d (τ⁻¹ k)) := by
  rw [coe_uFramePerm, LinFusion.ggFrameDiag, LinFusion.ggFrameDiag,
    ← LinFusion.toGL_ggPermSL_conj_diagGL τ d]
  group

theorem inv_mul_mul_mem_uFrameTorus {ψ : SU σ (m + 1) →* G} {Q : GL (Fin (m + 1)) F}
    (hQ : IsUFrame σ Q) (τ : Equiv.Perm (Fin (m + 1))) {g : G} (hg : g ∈ uFrameTorus ψ Q) :
    (ψ (uFramePerm hQ τ))⁻¹ * g * ψ (uFramePerm hQ τ) ∈ uFrameTorus ψ Q := by
  obtain ⟨d, hd⟩ := hg
  refine ⟨fun k => d (τ⁻¹ k), ?_⟩
  have h := conj_mem_suInducedPairs hd (uFramePerm hQ τ)
  rwa [uFramePerm_conj] at h

theorem uFramePerm_mem_normalizer {ψ : SU σ (m + 1) →* G} {Q : GL (Fin (m + 1)) F}
    (hQ : IsUFrame σ Q) (τ : Equiv.Perm (Fin (m + 1))) :
    ψ (uFramePerm hQ τ) ∈ Subgroup.normalizer (uFrameTorus ψ Q : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · have h := inv_mul_mul_mem_uFrameTorus hQ τ⁻¹ hg
    rwa [uFramePerm_inv, map_inv, inv_inv] at h
  · have h := inv_mul_mul_mem_uFrameTorus hQ τ hg
    rwa [show (ψ (uFramePerm hQ τ))⁻¹ * (ψ (uFramePerm hQ τ) * g * (ψ (uFramePerm hQ τ))⁻¹) *
      ψ (uFramePerm hQ τ) = g by group] at h

end Perm

section Block

open CFSG.SeitzReduction.LinearPilot

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ} {G : Type*} [Group G]

@[expose] def glBlock (I : Finset (Fin (m + 1))) : Subgroup (GL (Fin (m + 1)) F) where
  carrier := {A | (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * blockComplProj I =
    blockComplProj I ∧ blockComplProj I * (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      blockComplProj I}
  one_mem' := ⟨by rw [Units.val_one, Matrix.one_mul], by rw [Units.val_one, Matrix.mul_one]⟩
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.mul_assoc, hB1, hA1]
    · rw [Units.val_mul, ← Matrix.mul_assoc, hA2, hB2]
  inv_mem' := by
    rintro A ⟨hA1, hA2⟩
    have h1 : ((A⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hA1, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    · conv_lhs => rw [← hA2, Matrix.mul_assoc, val_mul_val_inv A, Matrix.mul_one]

theorem mem_glBlock {I : Finset (Fin (m + 1))} {A : GL (Fin (m + 1)) F} :
    A ∈ glBlock I ↔ ∀ i j, (i ∉ I ∨ j ∉ I) →
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j :=
  (agrees_one_iff I _).symm

@[expose] def suBlock (Q : GL (Fin (m + 1)) F) (I : Finset (Fin (m + 1))) :
    Subgroup (SU σ (m + 1)) :=
  (glBlock I).comap ((MulAut.conj Q).toMonoidHom.comp (SU σ (m + 1)).subtype)

theorem mem_suBlock {Q : GL (Fin (m + 1)) F} {I : Finset (Fin (m + 1))} {u : SU σ (m + 1)} :
    u ∈ suBlock Q I ↔ Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ ∈ glBlock I :=
  Iff.rfl

@[expose] def uFrameBlock (ψ : SU σ (m + 1) →* G) (Q : GL (Fin (m + 1)) F)
    (I : Finset (Fin (m + 1))) : Subgroup G :=
  (suBlock Q I).map ψ

theorem diagGL_mul_comm_of_mem_glBlock {e : Fin (m + 1) → Fˣ} {I : Finset (Fin (m + 1))}
    (he : ∀ i ∈ I, ∀ j ∈ I, e i = e j) {A : GL (Fin (m + 1)) F} (hA : A ∈ glBlock I) :
    InnerDiagA.diagGL e * A = A * InnerDiagA.diagGL e := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL]
  ext a b
  rw [diagonal_mul, mul_diagonal]
  by_cases hab : a ∈ I ∧ b ∈ I
  · rw [he a hab.1 b hab.2, mul_comm]
  · rw [mem_glBlock.mp hA a b (not_and_or.mp hab)]
    by_cases h : a = b
    · rw [h, one_apply_eq, mul_one, one_mul]
    · rw [one_apply_ne h, mul_zero, zero_mul]

theorem conjSU_frameDiag_of_mem_suBlock {Q : GL (Fin (m + 1)) F} {e : Fin (m + 1) → Fˣ}
    (hA : IsJUnitary σ (LinFusion.ggFrameDiag Q e)) {I : Finset (Fin (m + 1))}
    (he : ∀ i ∈ I, ∀ j ∈ I, e i = e j) {u : SU σ (m + 1)} (hu : u ∈ suBlock Q I) :
    conjSU (LinFusion.ggFrameDiag Q e) hA u = u := by
  apply Subtype.ext
  rw [coe_conjSU, LinFusion.ggFrameDiag]
  have h := diagGL_mul_comm_of_mem_glBlock he (mem_suBlock.mp hu)
  calc Q⁻¹ * InnerDiagA.diagGL e * Q * (u : GL (Fin (m + 1)) F) *
        (Q⁻¹ * InnerDiagA.diagGL e * Q)⁻¹ =
      Q⁻¹ * (InnerDiagA.diagGL e * (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹)) *
        (InnerDiagA.diagGL e)⁻¹ * Q := by group
    _ = Q⁻¹ * ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) * InnerDiagA.diagGL e) *
        (InnerDiagA.diagGL e)⁻¹ * Q := by rw [h]
    _ = u := by group

theorem mem_centralizer_uFrameBlock {ψ : SU σ (m + 1) →* G} {Q : GL (Fin (m + 1)) F}
    {I : Finset (Fin (m + 1))} {g : G} {e : Fin (m + 1) → Fˣ}
    (hg : (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ) (he : ∀ i ∈ I, ∀ j ∈ I, e i = e j) :
    g ∈ Subgroup.centralizer (uFrameBlock ψ Q I : Set G) := by
  obtain ⟨hA, hg⟩ := hg
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  have h1 := hg u
  rw [conjSU_frameDiag_of_mem_suBlock hA he hu] at h1
  calc ψ u * g = g * ψ u * g⁻¹ * g := by rw [h1]
    _ = g * ψ u := by group

theorem eq_one_of_mem_glBlock_of_card_le_one {I : Finset (Fin (m + 1))} (hI : I.card ≤ 1)
    {A : GL (Fin (m + 1)) F} (hA : A ∈ glBlock I)
    (hdet : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1) : A = 1 := by
  have hsub : ∀ a ∈ I, ∀ b ∈ I, a = b := fun a ha b hb =>
    Finset.card_le_one.mp hI a ha b hb
  have hoff : ∀ k l, k ≠ l → (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k l = 0 := by
    intro k l hkl
    have h := mem_glBlock.mp hA k l
      (not_and_or.mp fun hcon => hkl (hsub k hcon.1 l hcon.2))
    rwa [one_apply_ne hkl] at h
  have hdiag : ∀ k, k ∉ I → (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k k = 1 := by
    intro k hk
    rw [mem_glBlock.mp hA k k (Or.inl hk), one_apply_eq]
  have hAd : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal fun k => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k k := by
    ext k l
    by_cases hkl : k = l
    · rw [hkl, diagonal_apply_eq]
    · rw [hoff k l hkl, diagonal_apply_ne _ hkl]
  apply Units.ext
  rw [Units.val_one, hAd]
  ext k l
  by_cases hkl : k = l
  · subst hkl
    rw [diagonal_apply_eq, one_apply_eq]
    by_cases hk : k ∈ I
    · rw [hAd, det_diagonal, Finset.prod_eq_single k (fun b _ hbk => hdiag b fun hb =>
        hbk (hsub b hb k hk)) (fun h => absurd (Finset.mem_univ k) h)] at hdet
      exact hdet
    · exact hdiag k hk
  · rw [diagonal_apply_ne _ hkl, one_apply_ne hkl]

theorem uFrameBlock_eq_bot_of_card_le_one (ψ : SU σ (m + 1) →* G) (Q : GL (Fin (m + 1)) F)
    {I : Finset (Fin (m + 1))} (hI : I.card ≤ 1) : uFrameBlock ψ Q I = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, hu, rfl⟩
  have hdet : ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1 := by
    have h := det_frame_conj Q⁻¹ (u : GL (Fin (m + 1)) F)
    rw [inv_inv] at h
    rw [h]
    exact (mem_SU.mp u.2).1
  have h1 := eq_one_of_mem_glBlock_of_card_le_one hI (mem_suBlock.mp hu) hdet
  have hu1 : u = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_one]
    calc (u : GL (Fin (m + 1)) F) = Q⁻¹ * (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) * Q := by group
      _ = 1 := by rw [h1]; group
  rw [hu1, map_one]
  exact Subgroup.one_mem _

theorem uFrameBlock_univ (ψ : SU σ (m + 1) →* G) (Q : GL (Fin (m + 1)) F) :
    uFrameBlock ψ Q Finset.univ = ψ.range := by
  have h : suBlock (σ := σ) Q Finset.univ = ⊤ := by
    refine eq_top_iff.mpr fun u _ => mem_suBlock.mpr (mem_glBlock.mpr fun i j hij => ?_)
    simp at hij
  rw [uFrameBlock, h, ← MonoidHom.range_eq_map]

end Block

section Converse

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ} {G : Type*} [Group G]

omit [CharP F 2] in
theorem diagGL_injective {a b : Fin (m + 1) → Fˣ}
    (h : InnerDiagA.diagGL (F := F) a = InnerDiagA.diagGL b) : a = b := by
  funext k
  apply Units.ext
  have h1 := congrArg
    (fun A : GL (Fin (m + 1)) F => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k k) h
  simpa only [InnerDiagA.coe_diagGL, diagonal_apply_eq] using h1

theorem permGL_swap_mem_glBlock {I : Finset (Fin (m + 1))} {i j : Fin (m + 1)} (hi : i ∈ I)
    (hj : j ∈ I) : permGL (F := F) (Equiv.swap i j) ∈ glBlock I := by
  rw [mem_glBlock]
  intro a b hab
  simp only [coe_permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some_inj, one_apply]
  rcases hab with ha | hb
  · simp only [Equiv.swap_apply_of_ne_of_ne (fun h : a = i => ha (h ▸ hi))
      (fun h : a = j => ha (h ▸ hj))]
  · simp only [Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_of_ne_of_ne (fun h : b = i => hb (h ▸ hi)) (fun h : b = j => hb (h ▸ hj))]

theorem eq_of_comm_swap {i j : Fin (m + 1)} (e : Fin (m + 1) → Fˣ)
    (h : permGL (F := F) (Equiv.swap i j) *
        (InnerDiagA.diagGL e * permGL (Equiv.swap i j) * (InnerDiagA.diagGL e)⁻¹ *
          (permGL (Equiv.swap i j))⁻¹) =
      (InnerDiagA.diagGL e * permGL (Equiv.swap i j) * (InnerDiagA.diagGL e)⁻¹ *
          (permGL (Equiv.swap i j))⁻¹) * permGL (Equiv.swap i j)) :
    e i = e j := by
  set τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j with hτ
  set r : Fin (m + 1) → Fˣ := fun k => e k * (e (τ k))⁻¹ with hr
  have hX : InnerDiagA.diagGL e * permGL (F := F) τ * (InnerDiagA.diagGL e)⁻¹ *
      (permGL τ)⁻¹ = InnerDiagA.diagGL r := by
    have h1 := LinFusion.toGL_ggPermSL_conj_diagGL (F := F) τ⁻¹ e⁻¹
    rw [show Matrix.SpecialLinearGroup.toGL (ggPermSL (F := F) τ⁻¹) = (permGL τ)⁻¹ from
      permGL_inv τ, inv_inv, LinFusion.diagGL_inv] at h1
    rw [show InnerDiagA.diagGL e * permGL (F := F) τ * (InnerDiagA.diagGL e)⁻¹ *
      (permGL τ)⁻¹ = InnerDiagA.diagGL e * (permGL τ * (InnerDiagA.diagGL e)⁻¹ *
        (permGL τ)⁻¹) by group, h1, ← LinFusion.diagGL_mul]
    rfl
  rw [hX] at h
  have h2 : (permGL (F := F) τ)⁻¹ * InnerDiagA.diagGL r * permGL τ = InnerDiagA.diagGL r := by
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  rw [LinFusion.toGL_ggPermSL_conj_diagGL τ r] at h2
  have h3 := congrFun (diagGL_injective h2) i
  simp only [hτ, Equiv.swap_inv, Equiv.swap_apply_left, hr, Equiv.swap_apply_right] at h3
  have h4 : (e i * (e j)⁻¹) * (e i * (e j)⁻¹) = 1 := by
    calc (e i * (e j)⁻¹) * (e i * (e j)⁻¹) = (e i * (e j)⁻¹) * (e j * (e i)⁻¹) := by rw [h3]
      _ = 1 := by group
  have h5 : ((e i * (e j)⁻¹ : Fˣ) : F) * ((e i * (e j)⁻¹ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, h4, Units.val_one]
  have h6 : ((e i * (e j)⁻¹ : Fˣ) : F) = 1 := by
    rcases mul_self_eq_one_iff.mp h5 with h7 | h7
    · exact h7
    · rw [h7, CharTwo.neg_eq]
  have h8 : e i * (e j)⁻¹ = 1 := Units.ext (by rw [h6, Units.val_one])
  exact mul_inv_eq_one.mp h8

theorem eq_of_mem_centralizer_uFrameBlock {ψ : SU σ (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU σ (m + 1))) {Q : GL (Fin (m + 1)) F}
    (hQ : IsUFrame σ Q) {I : Finset (Fin (m + 1))} {g : G} {e : Fin (m + 1) → Fˣ}
    (hg : (g, LinFusion.ggFrameDiag Q e) ∈ suInducedPairs ψ)
    (hgc : g ∈ Subgroup.centralizer (uFrameBlock ψ Q I : Set G)) {i j : Fin (m + 1)}
    (hi : i ∈ I) (hj : j ∈ I) : e i = e j := by
  set τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j with hτ
  set s := uFramePerm hQ τ with hs
  have hsB : s ∈ suBlock Q I := by
    rw [mem_suBlock, hs, coe_uFramePerm, show Q * (Q⁻¹ * permGL τ * Q) * Q⁻¹ = permGL τ by group]
    exact permGL_swap_mem_glBlock hi hj
  have hcomm : ψ s * g = g * ψ s := Subgroup.mem_centralizer_iff.mp hgc (ψ s) ⟨s, hsB, rfl⟩
  obtain ⟨hA, hg'⟩ := hg
  have h1 := hg' s
  set c : SU σ (m + 1) := conjSU _ hA s * s⁻¹ with hc
  have hc1 : ψ c = 1 := by
    rw [hc, map_mul, map_inv, ← h1, ← hcomm]
    group
  have hcz := Subgroup.mem_center_iff.mp (hker hc1) s
  have hcGL := congrArg (fun x : SU σ (m + 1) => (x : GL (Fin (m + 1)) F)) hcz
  simp only [hc, Subgroup.coe_mul, coe_conjSU, Subgroup.coe_inv, hs, coe_uFramePerm,
    LinFusion.ggFrameDiag] at hcGL
  refine eq_of_comm_swap e ?_
  have hQ' : ∀ X Y : GL (Fin (m + 1)) F, Q⁻¹ * X * Q = Q⁻¹ * Y * Q → X = Y := by
    intro X Y hXY
    calc X = Q * (Q⁻¹ * X * Q) * Q⁻¹ := by group
      _ = Y := by rw [hXY]; group
  apply hQ'
  calc Q⁻¹ * (permGL τ * (InnerDiagA.diagGL e * permGL τ * (InnerDiagA.diagGL e)⁻¹ *
        (permGL τ)⁻¹)) * Q = Q⁻¹ * permGL τ * Q * (Q⁻¹ * InnerDiagA.diagGL e * Q *
        (Q⁻¹ * permGL τ * Q) * (Q⁻¹ * InnerDiagA.diagGL e * Q)⁻¹ * (Q⁻¹ * permGL τ * Q)⁻¹) := by
        group
    _ = Q⁻¹ * InnerDiagA.diagGL e * Q * (Q⁻¹ * permGL τ * Q) *
        (Q⁻¹ * InnerDiagA.diagGL e * Q)⁻¹ * (Q⁻¹ * permGL τ * Q)⁻¹ * (Q⁻¹ * permGL τ * Q) := by
        rw [hcGL]
    _ = Q⁻¹ * (InnerDiagA.diagGL e * permGL τ * (InnerDiagA.diagGL e)⁻¹ * (permGL τ)⁻¹ *
        permGL τ) * Q := by group

end Converse
